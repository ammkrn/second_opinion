use crate::mmb::sorts_compatible;
use crate::mmb::unify::UMode;
use crate::util::{ 
    VerifErr,
    try_next_cmd,
    Res,
    Type,
};
use crate::mmb::{
    MmbState,
    MmbItem,
    MmbListPtr,
    MmbList::*,
};

pub const TYPE_BOUND_MASK: u64 = 1 << 63;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Def,
    Thm,
}
use crate::none_err;
use crate::localize;
use crate::make_sure;


/// `PROOF_TERM = 0x10`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_TERM: u8 = 0x10;
/// `PROOF_TERM_SAVE = 0x11`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_TERM_SAVE: u8 = 0x11;
/// `PROOF_REF = 0x12`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_REF: u8 = 0x12;
/// `PROOF_DUMMY = 0x13`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_DUMMY: u8 = 0x13;
/// `PROOF_THM = 0x14`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_THM: u8 = 0x14;
/// `PROOF_THM_SAVE = 0x15`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_THM_SAVE: u8 = 0x15;
/// `PROOF_HYP = 0x16`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_HYP: u8 = 0x16;
/// `PROOF_CONV = 0x17`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_CONV: u8 = 0x17;
/// `PROOF_REFL = 0x18`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_REFL: u8 = 0x18;
/// `PROOF_SYMM = 0x19`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_SYMM: u8 = 0x19;
/// `PROOF_CONG = 0x1A`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_CONG: u8 = 0x1A;
/// `PROOF_UNFOLD = 0x1B`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_UNFOLD: u8 = 0x1B;
/// `PROOF_CONV_CUT = 0x1C`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_CONV_CUT: u8 = 0x1C;
/// `PROOF_CONV_REF = 0x1D`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_CONV_REF: u8 = 0x1D;
/// `PROOF_CONV_SAVE = 0x1E`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_CONV_SAVE: u8 = 0x1E;
/// `PROOF_SAVE = 0x1F`: See [`ProofCmd`](super::ProofCmd).
pub const PROOF_SAVE: u8 = 0x1F;



/// A proof command, which acts on a stack machine with the following components:
///
/// * `H: Vec<StackEl>`: a "heap" consisting of indexable elements that can be copied
///   onto the stack using [`Ref`](ProofCmd::Ref)
/// * `S: Stack<StackEl>`: The main stack, which most operations push and pop from.
/// * `HS: Vec<Expr>`: The hypothesis list, which grows only on [`Hyp`](ProofCmd::Hyp)
///   operations and collects the hypotheses of the theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofCmd {
    /// ```text
    /// Term t: H; S, e1, ..., en --> H; S, (t e1 .. en)
    /// Save: H; S, e --> H, e; S, e
    /// TermSave t = Term t; Save:
    ///   H; S, e1, ..., en --> H, (t e1 .. en); S, (t e1 .. en)
    /// ```
    ///
    /// Pop `n` elements from the stack and allocate a new term `t` applied to those
    /// expressions. When `save` is used, the new term is also saved to the heap
    /// (this is used if the term will ever be needed more than once).
    Term {
        /** The term to construct */
        term_num: u32,
        /** True if we should save to the heap */
        save: bool,
    },
    /// ```text
    /// Ref i: H; S --> H; S, Hi
    /// ```
    /// Get the `i`-th heap element and push it on the stack.
    Ref(u32),
    /// ```text
    /// Dummy s: H; S --> H, x; S, x    alloc(x:s)
    /// ```
    /// Allocate a new variable `x` of sort `s`, and push it to the stack and the heap.
    Dummy { sort_num: u8 },
    /// ```text
    /// Thm T: H; S, e1, ..., en, e --> H; S', |- e
    ///   (where Unify(T): S; e1, ... en; e --> S'; H'; .)
    /// Save: H; S, |- e --> H, |- e; S, |- e
    /// ```
    /// Pop `n` elements from the stack and put them on the unify heap, then call the
    /// unifier for `T` with `e` as the target. The unifier will pop additional
    /// proofs from the stack if the UHyp command is used, and when it is done,
    /// the conclusion is pushed as a proven statement.
    ///
    /// When Save is used, the proven statement is also saved to the heap.
    Thm {
        /** The theorem to apply */
        thm_num: u32,
        /** True if we should save to the heap */
        save: bool,
    },
    /// ```text
    /// Hyp: HS; H; S, e --> HS, e; H, |- e; S
    /// ```
    /// This command means that we are finished constructing the expression `e`
    /// which denotes a statement, and wish to assume it as a hypothesis.
    /// Push `e` to the hypothesis stack, and push `|- e` to the heap.
    Hyp,
    /// ```text
    /// Conv: S, e1, |- e2 --> S, |- e1, e1 =?= e2
    /// ```
    /// Pop `e1` and `|- e2`, and push `|- e1`, guarded by a convertibility obligation
    /// `e1 =?= e2`.
    Conv,
    /// ```text
    /// Refl: S, e =?= e --> S
    /// ```
    /// Pop a convertibility obligation where the two sides are equal.
    Refl,
    /// ```text
    /// Symm: S, e1 =?= e2 --> S, e2 =?= e1
    /// ```
    /// Swap the direction of a convertibility obligation.
    Sym,
    /// ```text
    /// Cong: S, (t e1 ... en) =?= (t e1' ... en') --> S, en =?= en', ..., e1 =?= e1'
    /// ```
    /// Pop a convertibility obligation for two term expressions, and
    /// push convertibility obligations for all the parts.
    /// The parts are pushed in reverse order so that they are dealt with
    /// in declaration order in the proof stream.
    Cong,
    /// ```text
    /// Unfold: S, (t e1 ... en) =?= e', (t e1 ... en), e --> S, e =?= e'
    ///   (where Unify(t): e1, ..., en; e --> H'; .)
    /// ```
    /// Pop terms `(t e1 ... en)`, `e` from the stack and run the unifier for `t`
    /// (which should be a definition) to make sure that `(t e1 ... en)` unfolds to `e`.
    /// Then pop `(t e1 ... en) =?= e'` and push `e =?= e'`.
    Unfold,
    /// ```text
    /// ConvCut: S, e1 =?= e2 --> S, e1 = e2, e1 =?= e2
    /// ```
    /// Pop a convertibility obligation `e1 =?= e2`, and
    /// push a convertability assertion `e1 = e2` guarded by `e1 =?= e2`.
    ConvCut,
    /// ```text
    /// ConvRef i: H; S, e1 =?= e2 --> H; S   (where Hi is e1 = e2)
    /// ```
    /// Pop a convertibility obligation `e1 =?= e2`, where `e1 = e2` is
    /// `i`-th on the heap.
    ConvRef(u32),
    /// ```text
    /// ConvSave: H; S, e1 = e2 --> H, e1 = e2; S
    /// ```
    /// Pop a convertibility proof `e1 = e2` and save it to the heap.
    ConvSave,
    /// ```text
    /// Save: H; S, s --> H, s; S, s
    /// ```
    /// Save the outline of the stack to the heap, without popping it.
    Save,
}

impl std::convert::TryFrom<(u8, u32)> for ProofCmd {
    type Error = VerifErr;
    fn try_from((cmd, data): (u8, u32)) -> Result<Self, Self::Error> {
        Ok(match cmd {
            PROOF_TERM => ProofCmd::Term {
                term_num: data,
                save: false,
            },
            PROOF_TERM_SAVE => ProofCmd::Term {
                term_num: data,
                save: true,
            },
            PROOF_REF => ProofCmd::Ref(data),
            PROOF_DUMMY => {
                let sort_num = u8::try_from(data).map_err(|_| {
                    VerifErr::Msg("Failure to shrink u32 to u8 in proof_cmd try from".to_string())
                })?;
                ProofCmd::Dummy { sort_num }
            }
            PROOF_THM => ProofCmd::Thm {
                thm_num: data,
                save: false,
            },
            PROOF_THM_SAVE => ProofCmd::Thm {
                thm_num: data,
                save: true,
            },
            PROOF_HYP => ProofCmd::Hyp,
            PROOF_CONV => ProofCmd::Conv,
            PROOF_REFL => ProofCmd::Refl,
            PROOF_SYMM => ProofCmd::Sym,
            PROOF_CONG => ProofCmd::Cong,
            PROOF_UNFOLD => ProofCmd::Unfold,
            PROOF_CONV_CUT => ProofCmd::ConvCut,
            PROOF_CONV_REF => ProofCmd::ConvRef(data),
            PROOF_CONV_SAVE => ProofCmd::ConvSave,
            PROOF_SAVE => ProofCmd::Save,
            owise => {
                println!("Failed to convert {:?}\n", owise);
                return Err(VerifErr::Msg("try_from for ProofCmd failed match".to_string()));
            }
        })
    }
}

/// An iterator over a proof command stream.
#[derive(Debug, Clone, Copy)]
pub struct ProofIter<'a> {
    /// The full source file, but trimmed such that the end
    /// is the expected end of the proof stream. The final call to `next`
    /// will fail if it does not hit the expected end when the
    /// proof stream runs out.
    pub buf: &'a [u8],
    /// The index of the current proof command in the file.
    pub pos: usize,
    /// Mark `ends_at` instead of giving ProofIter a truncated slice just so
    /// the behvaior wrt `try_next_cmd` is identical.
    pub ends_at: usize,
}

impl<'a> ProofIter<'a> {
    /// True if this iterator is "null", meaning that it has zero commands.
    /// This is not the same as being empty, which happens when there is one command
    /// which is the terminating `CMD_END` command.
    pub fn is_null(&self) -> bool {
        //self.buf.len() == self.pos
        self.pos == self.ends_at
    }
}

impl<'a> Iterator for ProofIter<'a> {
    type Item = Result<ProofCmd, VerifErr>;
    fn next(&mut self) -> Option<Self::Item> {
        match try_next_cmd(self.buf, self.pos) {
            // An actual error.
            Err(e) => Some(Err(e)),
            // `try_next_cmd` got `Ok(None)` by receiving a 0 command at the correct position
            Ok(None) if self.ends_at == self.pos + 1 => None,
            // `try_next_cmd` got `Ok(None)` by receiving a 0 command at the WRONG position
            Ok(None) => Some(Err(VerifErr::Msg(format!("Proof iter err @ {}", self.pos)))),
            // `try_next_cmd` parsed a new command.
            Ok(Some((stmt, rest))) => {
                self.pos = rest;
                Some(Ok(stmt))
            }
        }
    }
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn run_proof(
        &mut self, 
        mode: Mode,
        proof: ProofIter
    ) -> Res<()> {    
        for maybe_cmd in proof {
            match maybe_cmd? {
                ProofCmd::Ref(i) => self.proof_ref(i)?,
                ProofCmd::Dummy { sort_num } => self.proof_dummy(sort_num)?,
                ProofCmd::Term { term_num, save } => self.proof_term(mode, term_num, save)?,
                ProofCmd::Thm { thm_num, save } => self.proof_thm(thm_num, save)?,
                ProofCmd::Hyp => self.proof_hyp(mode)?,
                ProofCmd::Conv => self.proof_conv()?,
                ProofCmd::Refl=> self.proof_refl()?,
                ProofCmd::Sym => self.proof_sym()?,
                ProofCmd::Cong => self.proof_cong()?,
                ProofCmd::Unfold => self.proof_unfold()?,
                ProofCmd::ConvCut => self.proof_conv_cut()?,
                ProofCmd::ConvRef(i) => self.proof_conv_ref(i)?,
                ProofCmd::ConvSave => self.proof_conv_save()?,
                ProofCmd::Save => self.proof_save()?,
            }
        }
        Ok(())
    }    

    fn proof_ref(&mut self, i: u32) -> Res<()> {
        let heap_elem = *&self.mem.heap[i as usize];
        Ok(self.mem.stack.push(heap_elem))
    }

    fn proof_dummy(&mut self, sort_num: u8) -> Res<()> {
        make_sure!(sort_num < self.mem.outline.header.num_sorts);
        make_sure!(self.mem.outline.get_sort_mods(sort_num as usize).unwrap().inner & crate::mmb::SORT_STRICT == 0);
        // Owise too many bound variables.
        make_sure!(self.next_bv >> 56 == 0);

        let ty = Type { inner: TYPE_BOUND_MASK | ((sort_num as u64) << 56) | self.take_next_bv() };

        let e = MmbItem::Var { idx: self.mem.heap.len(), ty }.alloc(self);
        self.mem.stack.push(e);
        Ok(self.mem.heap.push(e))
    }        


    fn proof_term(
        &mut self, 
        mode: Mode,
        term_num: u32,
        save: bool
    ) -> Res<()> {
        make_sure!(term_num < self.mem.outline.header.num_terms);
        let termref = self.mem.outline.get_term_by_num(term_num)?;
        
        // remove ebar from the stack; either variables or applications.
        // We don't actually drain the elements from the stack until the end
        // in order to avoid an allocation.
        let drain_from = self.mem.stack.len() - (termref.num_args_no_ret() as usize);
        let stack_args = &self.mem.stack[drain_from..];

        // (sig_args, stack_args)
        let all_args = || { termref.args_no_ret().zip(stack_args.iter()) };

        // Arguments from the stack (and their positions, starting from 1) that the stack demands be bound.
        let stack_bound_by_sig = all_args().filter_map(|(sig, stack)| {
            if sig.is_bound() {
                Some(stack.get_bound_digit(self))
            } else {
                None
            }
        });


        // For all of the args, make sure the stack and sig items have compatible sorts.
        for (sig_arg, stack_arg) in all_args() {
            make_sure!(sorts_compatible(stack_arg.get_ty(self)?, sig_arg)) 
        }

        // Start building the new return type now that we know we have the right sort.
        let mut new_type_accum = Type::new_with_sort(termref.sort());

        // For the args not bound by the signature...
        for (sig_unbound, stack_arg) in all_args().filter(|(sig, _)| !sig.is_bound()) {
            let mut stack_lowbits = stack_arg.get_deps(self).or(stack_arg.get_bound_digit(self))?;
            if mode == Mode::Def {
                for (idx, dep) in stack_bound_by_sig.clone().enumerate() {
                    if sig_unbound.depends_on_((idx + 1) as u64) {
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
                if termref.ret().depends_on_((idx + 1) as u64) {
                    new_type_accum |= bvar?;
                }
            }
        }        

        // I think this will get around it.
        let mut stack_args_out = Nil.alloc(self);
        for _ in 0..termref.num_args_no_ret() {
            let hd = none_err!(self.mem.stack.pop())?;
            stack_args_out = Cons(hd, stack_args_out).alloc(self);
        }   

        let t = MmbItem::App {
            term_num,
            ty: new_type_accum,
            args: stack_args_out,
        }.alloc(self);

        if save {
            self.mem.heap.push(t);
        }        
        Ok(self.mem.stack.push(t))
    }       

    fn proof_thm(
        &mut self, 
        thm_num: u32,
        save: bool
    ) -> Res<()> {
        make_sure!(thm_num < self.mem.outline.header.num_thms);
        let thmref = self.mem.outline.get_assert_by_num(thm_num)?;
        let sig_args = thmref.args();

        let a = none_err!(self.mem.stack.pop())?;

        // Wait to remove these in order to save an allocation.
        let drain_from = self.mem.stack.len() - sig_args.len();
        let stack_args = &self.mem.stack[drain_from..];

        let bound_by_sig = sig_args.zip(stack_args).enumerate().filter(|(_, (sig, _))| sig.is_bound());

        self.mem.uheap.extend(stack_args.into_iter());

        let mut bound_len = 0usize;
        // For each variable bound by the signature...
        for (idx, (_, stack_a)) in bound_by_sig.clone() {
            bound_len += 1;
            for j in 0..idx {
                make_sure!(*&self.mem.uheap[j].get_ty(self).unwrap().disjoint(stack_a.low_bits(self)))
            }
        }

        // For the args not bound in the signature
        for (sig_a, stack_a) in  sig_args.zip(stack_args).filter(|(sig, _)| !sig.is_bound()) {
            for j in 0..bound_len {
                make_sure!(
                    !(sig_a.disjoint(Type { inner: 1 << j }))
                    || bound_by_sig.clone().nth(j).unwrap().1.1.clone().low_bits(self).disjoint(stack_a.low_bits(self))
                )
            }
        }

        // Now we actually remove the stack_args from the stack
        self.mem.stack.truncate(drain_from);
        self.run_unify(UMode::UThm, thmref.unify(), a)?;

        let proof = MmbItem::Proof(a).alloc(self);
        if save {
            self.mem.heap.push(proof);
        }
        Ok(self.mem.stack.push(proof))
    }          
    

    fn proof_hyp(
        &mut self, 
        mode: Mode,
    ) -> Res<()> {
        make_sure!(mode != Mode::Def);
        let e = none_err!(self.mem.stack.pop())?;
        //assert that e is in a provable sort since it's a hyp
        let e_sort_numx = e.get_ty(self)?.sort();
        let e_sort_mods = self.mem.outline.get_sort_mods(e_sort_numx as usize).unwrap().inner;
        make_sure!(e_sort_mods & crate::mmb::SORT_PROVABLE != 0);
        self.mem.hstack.push(e);
        let proof = MmbItem::Proof(e).alloc(self);
        Ok(self.mem.heap.push(proof))
    }      


    fn proof_conv(&mut self) -> Res<()> {
        let e2proof = none_err!(self.mem.stack.pop())?;
        let e1 = none_err!(self.mem.stack.pop())?;
        match e2proof.read(self) {
            MmbItem::Proof(conc) => {
                let e1proof = MmbItem::Proof(e1).alloc(self);
                self.mem.stack.push(e1proof);
                let coconv_e1_e2 = MmbItem::CoConv(e1, conc).alloc(self);
                Ok(self.mem.stack.push(coconv_e1_e2))
            },
            _ => unreachable!()
        }        
    }      

    fn proof_refl(&mut self) -> Res<()> {
        let e = none_err!(self.mem.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = e.read(self) {
            Ok(make_sure!(cc1 == cc2))
        } else {
            unreachable!()
        }
    }      

    fn proof_sym(&mut self) -> Res<()> {
        let e = none_err!(self.mem.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = e.read(self) {
            let rev = MmbItem::CoConv(cc2, cc1).alloc(self);
            Ok(self.mem.stack.push(rev))
        } else {
            unreachable!()
        }
    }      

    fn proof_cong(&mut self) -> Res<()> {
        let e = none_err!(self.mem.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = e.read(self)  {
            match (cc1.read(self), cc2.read(self)) {
                (MmbItem::App { term_num: n1, args: as1, .. }, MmbItem::App { term_num: n2, args: as2, .. }) => {
                    make_sure!(n1 == n2);
                    self.cong_push_rev((as1, as2))
                },
                _ => unreachable!()
            }
        } else {
            unreachable!()
        }
    }      

    // This is just a helper 
    fn cong_push_rev(&mut self, (args1, args2): (MmbListPtr<'a>, MmbListPtr<'a>)) -> Res<()> {
        match (args1.read(self), args2.read(self)) {
            (Cons(h1, t1), Cons(h2, t2)) => {
                self.cong_push_rev((t1, t2))?;
                let cc = MmbItem::CoConv(h1, h2).alloc(self);
                Ok(self.mem.stack.push(cc))
            },
            _ => {
                make_sure!(args1.read(self) == Nil);
                Ok(make_sure!(args2.read(self) == Nil))
            }
        }
    }

    fn proof_unfold(&mut self) -> Res<()> {
        let e_prime = none_err!(self.mem.stack.pop())?;
        let f_ebar = none_err!(self.mem.stack.pop())?;
        let (term_num, ebar) = match f_ebar.read(self) {
            MmbItem::App{ term_num, args, .. } => (term_num, args.clone()),
            _ => unreachable!()
        };

        let mut ebar_ = ebar;
        make_sure!(self.mem.uheap.is_empty());
        while let Cons(hd, tl) = ebar_.read(self) {
            ebar_ = tl;
            self.mem.uheap.push(hd);
        }

        self.run_unify(
            crate::mmb::unify::UMode::UDef,
            self.mem.outline.get_term_by_num(term_num)?.unify(),
            e_prime,
        )?;

        let cc = none_err!(self.mem.stack.pop())?;
        if let MmbItem::CoConv(f_ebar2, e_doubleprime) = cc.read(self) {
                make_sure!(f_ebar == f_ebar2);
                let coconv = MmbItem::CoConv(e_prime, e_doubleprime).alloc(self);
                Ok(self.mem.stack.push(coconv))
        } else {
            unreachable!()
        }
    }      

    fn proof_conv_cut(&mut self) -> Res<()> {
        let p = none_err!(self.mem.stack.pop())?;
        if let MmbItem::CoConv(cc1, cc2) = p.read(self) {
            let p1 = MmbItem::Conv(cc1, cc2).alloc(self);
            self.mem.stack.push(p1);
            Ok(self.mem.stack.push(p))
        } else {
            unreachable!()
        }
    }      

    fn proof_conv_ref(&mut self, i: u32) -> Res<()> {
        let heap_conv = none_err!(self.mem.heap.get(i as usize).copied())?;
        let stack_coconv = none_err!(self.mem.stack.pop())?;
        if let (MmbItem::Conv(c1, c2), MmbItem::CoConv(cc1, cc2)) = (heap_conv.read(self), stack_coconv.read(self)) {
            make_sure!(c1 == cc1);
            Ok(make_sure!(c2 == cc2))
        } else {
            unreachable!()
        }
    }    

    fn proof_conv_save(&mut self) -> Res<()> {
        let p = localize!(none_err!(self.mem.stack.pop()))?;
        make_sure!(matches!(p.read(self), MmbItem::Conv {..}));
        Ok(self.mem.heap.push(p))
    }    

    fn proof_save(&mut self) -> Res<()> {
        let last = none_err!(self.mem.stack.last().copied())?;
        match last.read(self) {
            MmbItem::CoConv {..} => panic!("Can't save co-conv"),
            _ => Ok(self.mem.heap.push(last))
        }        
    }    
}


