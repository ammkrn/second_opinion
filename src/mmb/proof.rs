use bumpalo::collections::Vec as BumpVec;
use mm0b_parser::{ ProofIter, Type, ProofCmd, TYPE_BOUND_MASK };
use mm0_util::{ Modifiers, SortId, TermId, ThmId };
use crate::mmb::sorts_compatible;
use crate::mmb::unify::UMode;
use crate::util::{ 
    VerifErr,
    Res,
};
use crate::mmb::{
    MmbState,
    MmbItem,
    MmbExpr
};
use crate::none_err;
use crate::localize;
use crate::make_sure;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Def,
    Thm,
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn run_proof(
        &mut self, 
        mode: Mode,
        proof: ProofIter
    ) -> Res<()> {    
        for maybe_cmd in proof {
            match maybe_cmd.map_err(|e| VerifErr::Msg(format!("{:?}", e)))? {
                ProofCmd::Ref(i) => self.proof_ref(i)?,
                ProofCmd::Dummy(sort_num) => self.proof_dummy(sort_num)?,
                ProofCmd::Term { tid, save } => self.proof_term(mode, tid, save)?,
                ProofCmd::Thm { tid, save } => self.proof_thm(tid, save)?,
                ProofCmd::Hyp => self.proof_hyp(mode)?,
                ProofCmd::Conv => self.proof_conv()?,
                ProofCmd::Refl=> self.proof_refl()?,
                ProofCmd::Sym => self.proof_sym()?,
                ProofCmd::Cong => self.proof_cong()?,
                ProofCmd::Unfold => self.proof_unfold()?,
                ProofCmd::ConvCut => self.proof_conv_cut()?,
                ProofCmd::ConvSave => self.proof_conv_save()?,
                ProofCmd::Save => self.proof_save()?,
                ProofCmd::Sorry => self.proof_sorry()?,
            }
        }
        Ok(())
    }    

    fn proof_ref(&mut self, i: u32) -> Res<()> {
        match none_err!(self.heap.get(i as usize).copied())? {
            MmbItem::Conv(c1, c2) => {
                let stack_coconv = none_err!(self.stack.pop())?;
                if let MmbItem::CoConv(cc1, cc2) = stack_coconv {
                    make_sure!(c1 == cc1);
                    Ok(make_sure!(c2 == cc2))
                } else {
                    return Err(VerifErr::Unreachable(file!(), line!()));
                }
            }
            heap_elem => Ok(self.stack.push(heap_elem))
        }
    }

    fn proof_dummy(&mut self, sort_num: SortId) -> Res<()> {
        make_sure!(sort_num.into_inner() < self.outline.file_view.mmb.header.num_sorts);
        make_sure!(!(self.outline.file_view.mmb_sort_mods(sort_num)?.contains(Modifiers::STRICT)));
        // Owise too many bound variables.
        make_sure!(self.next_bv >> 56 == 0);

        let ty = Type::from(TYPE_BOUND_MASK | ((sort_num.into_inner() as u64) << 56) | self.take_next_bv());

        let e = self.alloc(MmbItem::Expr(self.alloc(MmbExpr::Var { idx: self.heap.len(), ty })));
        self.stack.push(e);
        Ok(self.heap.push(e))
    }        


    fn proof_term(
        &mut self, 
        mode: Mode,
        term_num: TermId,
        save: bool
    ) -> Res<()> {
        make_sure!(term_num.into_inner() < self.outline.file_view.mmb.header.num_terms.get());
        let termref = none_err!(self.outline.file_view.mmb.term(term_num))?;
        
        // remove ebar from the stack; either variables or applications.
        // We don't actually drain the elements from the stack until the end
        // in order to avoid an allocation.
        let drain_from = self.stack.len() - (termref.args().len());
        let stack_args = &self.stack[drain_from..];

        // (sig_args, stack_args)
        let all_args = || { termref.args().iter().zip(stack_args.iter()) };

        // Arguments from the stack (and their positions, starting from 1) that the stack demands be bound.
        let stack_bound_by_sig = all_args().filter_map(|(sig, stack)| {
            if sig.bound() {
                Some(stack.get_bound_digit())
            } else {
                None
            }
        });

        // For all of the args, make sure the stack and sig items have compatible sorts.
        for (sig_arg, stack_arg) in all_args() {
            make_sure!(sorts_compatible(stack_arg.get_ty()?, *sig_arg)) 
        }

        // Start building the new return type now that we know we have the right sort.
        let mut new_type_accum = Type::new_of_sort(termref.sort().into_inner());

        // For the args not bound by the signature...
        for (sig_unbound, stack_arg) in all_args().filter(|(sig, _)| !sig.bound()) {
            let mut stack_lowbits = stack_arg.get_deps().or(stack_arg.get_bound_digit())?;
            if mode == Mode::Def {
                for (idx, dep) in stack_bound_by_sig.clone().enumerate() {
                    if sig_unbound.depends_on((idx) as u64) {
                        stack_lowbits &= !(dep?);
                    }
                }
            }
            new_type_accum |= stack_lowbits
        }

        // For definitions with dependent return types, add the appropriate dependencies
        // to the type accumulator.
        if mode == Mode::Def && termref.ret().has_deps() {
            for (idx, bvar) in stack_bound_by_sig.enumerate() {
                if termref.ret().depends_on((idx) as u64) {
                    new_type_accum |= bvar?;
                }
            }
        }        

        // I think this will get around it.
        let drain = self.stack.drain((self.stack.len() - (termref.args().len()))..);
        let mut stack_args_out = BumpVec::new_in(self.bump);
        for elem in drain {
            stack_args_out.push(elem);
        }

        let t = self.alloc(MmbItem::Expr(self.alloc(MmbExpr::App {
            term_num,
            ty: new_type_accum,
            args: self.alloc(stack_args_out),
        })));

        if save {
            self.heap.push(t);
        }        
        Ok(self.stack.push(t))
    }       

    fn proof_thm(
        &mut self, 
        thm_num: ThmId,
        save: bool
    ) -> Res<()> {
        make_sure!(thm_num.into_inner() < self.outline.file_view.mmb.header.num_thms.get());
        let thmref = none_err!(self.outline.file_view.mmb.thm(thm_num))?;
        let sig_args = thmref.args();

        let a = none_err!(self.stack.pop())?;

        // Wait to remove these in order to save an allocation.
        let drain_from = self.stack.len() - sig_args.len();
        let stack_args = &self.stack[drain_from..];

        let bound_by_sig = sig_args.iter().zip(stack_args).enumerate().filter(|(_, (sig, _))| sig.bound());

        self.uheap.extend(stack_args.into_iter());

        let mut bound_len = 0usize;
        // For each variable bound by the signature...
        for (idx, (_, stack_a)) in bound_by_sig.clone() {
            bound_len += 1;
            for j in 0..idx {
                make_sure!(*&self.uheap[j].get_ty().unwrap().disjoint(stack_a.low_bits()))
            }
        }

        // For the args not bound in the signature
        for (sig_a, stack_a) in  sig_args.iter().zip(stack_args).filter(|(sig, _)| !sig.bound()) {
            for j in 0..bound_len {
                make_sure!(
                    !(sig_a.disjoint(Type::from(1 << j)))
                    || bound_by_sig.clone().nth(j).unwrap().1.1.clone().low_bits().disjoint(stack_a.low_bits())
                )
            }
        }

        // Now we actually remove the stack_args from the stack
        self.stack.truncate(drain_from);
        self.run_unify(UMode::UThm, thmref.unify(), a)?;

        let proof = self.alloc(MmbItem::Proof(a));
        if save {
            self.heap.push(proof);
        }
        Ok(self.stack.push(proof))
    }          
    

    fn proof_hyp(
        &mut self, 
        mode: Mode,
    ) -> Res<()> {
        make_sure!(mode != Mode::Def);
        let e = none_err!(self.stack.pop())?;
        //assert that e is in a provable sort since it's a hyp
        make_sure!(self.outline.file_view.mmb_sort_mods(e.get_ty()?.sort())?.contains(Modifiers::PROVABLE));
        self.hstack.push(e);
        let proof = self.alloc(MmbItem::Proof(e));
        Ok(self.heap.push(proof))
    }      


    fn proof_conv(&mut self) -> Res<()> {
        let e2proof = none_err!(self.stack.pop())?;
        let e1 = none_err!(self.stack.pop())?;
        match e2proof {
            MmbItem::Proof(conc) => {
                let e1proof = self.alloc(MmbItem::Proof(e1));
                self.stack.push(e1proof);
                let coconv_e1_e2 = self.alloc(MmbItem::CoConv(e1, conc));
                Ok(self.stack.push(coconv_e1_e2))
            },
            _ => return Err(VerifErr::Unreachable(file!(), line!()))
        }        
    }      

    fn proof_refl(&mut self) -> Res<()> {
        let e = none_err!(self.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = e {
            Ok(make_sure!((*cc1) as *const _ == (*cc2) as *const _))
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }      

    fn proof_sym(&mut self) -> Res<()> {
        let e = none_err!(self.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = e {
            let swapped = self.alloc(MmbItem::CoConv(cc2, cc1));
            Ok(self.stack.push(swapped))
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }      

    fn proof_cong(&mut self) -> Res<()> {
        if let Some(MmbItem::CoConv(cc1, cc2)) = self.stack.pop()  {
            match (cc1, cc2) {
                (MmbItem::Expr(MmbExpr::App { term_num: n1, args: as1, .. }), MmbItem::Expr(MmbExpr::App { term_num: n2, args: as2, .. })) => {
                    make_sure!(n1 == n2);
                    make_sure!(as1.len() == as2.len());
                    for (lhs, rhs) in as1.iter().zip(as2.iter()).rev() {
                        let cc = self.alloc(MmbItem::CoConv(lhs, rhs));
                        self.stack.push(cc);
                    }
                    Ok(())
                },
                _ => return Err(VerifErr::Unreachable(file!(), line!()))
            }
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }      

    fn proof_unfold(&mut self) -> Res<()> {
        let e_prime = none_err!(self.stack.pop())?;
        let cc = none_err!(self.stack.pop())?;

        let (term_num, ebar, e_doubleprime) = match cc {
            MmbItem::CoConv(MmbItem::Expr(MmbExpr::App{ term_num, args, .. }), e_doubleprime) => {
                (term_num, args.clone(), e_doubleprime)
            }
            _ => return Err(VerifErr::Unreachable(file!(), line!()))
        };

        make_sure!(self.uheap.is_empty());
        self.uheap.extend(ebar);

        self.run_unify(
            crate::mmb::unify::UMode::UDef,
            none_err!(self.outline.file_view.mmb.term(*term_num))?.unify(),
            e_prime,
        )?;

        let coconv = self.alloc(MmbItem::CoConv(e_prime, e_doubleprime));
        Ok(self.stack.push(coconv))
    }      

    fn proof_conv_cut(&mut self) -> Res<()> {
        let p = none_err!(self.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = p {
            let p1 = self.alloc(MmbItem::Conv(cc1, cc2));
            self.stack.push(p1);
            Ok(self.stack.push(p))
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }      

    fn proof_conv_save(&mut self) -> Res<()> {
        let p = localize!(none_err!(self.stack.pop()))?;
        make_sure!(matches!(p, MmbItem::Conv {..}));
        Ok(self.heap.push(p))
    }    

    fn proof_save(&mut self) -> Res<()> {
        let last = none_err!(self.stack.last().copied())?;
        match last {
            MmbItem::CoConv {..} => Err(VerifErr::Msg(format!("Can't save co-conv"))),
            _ => Ok(self.heap.push(last))
        }        
    }    
    
    fn proof_sorry(&mut self) -> Res<()> {
        match none_err!(self.stack.pop())? {
            e @ MmbItem::Expr(_) => {
                let proof = self.alloc(MmbItem::Proof(e));
                Ok(self.stack.push(proof))
            },
            MmbItem::Conv(..) => Ok(()),
            owise => Err(VerifErr::Msg(format!("ProofCmd::Sorry is only valid when the stack has an Expr or Conv on top. Top element was {:?}", owise)))
        }
    }  
}
