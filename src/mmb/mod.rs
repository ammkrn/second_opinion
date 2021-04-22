use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;
use crate::Outline;
use crate::util::{ Res, VerifErr };
use crate::none_err;
use crate::make_sure;
use mm0_util::{ Modifiers, TermId };
use mm0b_parser::{ TYPE_BOUND_MASK, TYPE_DEPS_MASK, NumdStmtCmd, Type, Arg, ProofIter, TermRef, ThmRef };

pub mod proof;
pub mod unify;

// Returns true if a value with type 'from' can be cast to a value of type 'to'.
// This requires that the sorts be the same, and additionally if 'to' is a
// name then so is 'from'.
pub fn sorts_compatible(from: Type, to: Type) -> bool {
  let (from, to) = (from.into_inner(), to.into_inner());
  let diff = from ^ to;
  let c1 = || (diff & !TYPE_DEPS_MASK) == 0;
  let c2 = || (diff & !TYPE_BOUND_MASK & !TYPE_DEPS_MASK) == 0;
  let c3 = || ((from & TYPE_BOUND_MASK) != 0);
  c1() || (c2() && c3())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmbExpr<'b> {
    Var {
        idx: usize,
        ty: Type
    },
    App {
        term_num: TermId,
        args: &'b [&'b MmbItem<'b>],
        ty: Type,
    },
}

// Stack item
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmbItem<'b> {
    Expr(&'b MmbExpr<'b>),
    Proof(&'b MmbItem<'b>),
    Conv(&'b MmbItem<'b>, &'b MmbItem<'b>),
    CoConv(&'b MmbItem<'b>, &'b MmbItem<'b>)
}

impl<'b> MmbItem<'b> {
    pub fn get_ty(&self) -> Res<Type> {
        match self {
            | MmbItem::Expr(MmbExpr::Var { ty, .. })
            | MmbItem::Expr(MmbExpr::App { ty, ..}) => Ok(*ty),
            _ => Err(VerifErr::Msg(format!("Can't get type from a non-expr MmbItem")))
        }
    }

    pub fn get_deps(&self) -> Res<Type> {
        self.get_ty()
        .and_then(|ty| none_err!(ty.deps()))
        .map(|deps| Type::from(deps))
    }

    pub fn get_bound_digit(&self) -> Res<Type> {
        self.get_ty()
        .and_then(|ty| none_err!(ty.bound_digit()))
        .map(|bound_idx| Type::from(bound_idx))
    }

    pub fn low_bits(&self) -> Type {
        self.get_deps().or(self.get_bound_digit()).unwrap()
    }    
}

pub struct MmbState<'b, 'a: 'b> {
    pub outline: &'a Outline<'a>,
    pub bump: &'b Bump,
    pub stack: BumpVec<'b, &'b MmbItem<'b>>,
    pub heap: BumpVec<'b, &'b MmbItem<'b>>,
    pub ustack: BumpVec<'b, &'b MmbItem<'b>>,
    pub uheap: BumpVec<'b, &'b MmbItem<'b>>,
    pub hstack: BumpVec<'b, &'b MmbItem<'b>>,     
    pub next_bv: u64    
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn new_from(outline: &'a Outline, bump: &'b mut Bump) -> MmbState<'b, 'a> {
        bump.reset();
        MmbState {
            outline,
            bump: &*bump,
            stack: BumpVec::new_in(&*bump),
            heap: BumpVec::new_in(&*bump),
            ustack: BumpVec::new_in(&*bump),
            uheap: BumpVec::new_in(&*bump),
            hstack: BumpVec::new_in(&*bump),
            next_bv: 1u64            
        }
    }    

    pub fn verify1(outline: &'a Outline<'a>, bump: &mut Bump, stmt: NumdStmtCmd, proof: ProofIter<'a>) -> Res<()> {
        match stmt {
            NumdStmtCmd::Sort {..} => { 
                if !proof.is_null() {
                    return Err(VerifErr::Msg(format!("mmb sorts must have null proof iterators")));
                }
            },
            NumdStmtCmd::TermDef { term_id, .. } => {
                let term = none_err!(outline.file_view.mmb.term(term_id))?;
                if !term.def() && !proof.is_null() {
                    return Err(VerifErr::Msg(format!("mmb terms must have null proof iterators")));
                }
                MmbState::new_from(outline, bump).verify_termdef(stmt, term, proof)?;
            }
            NumdStmtCmd::Axiom { thm_id, .. } | NumdStmtCmd::Thm { thm_id, .. } => {
                let assert = none_err!(outline.file_view.mmb.thm(thm_id))?;
                MmbState::new_from(outline, bump).verify_assert(stmt, assert, proof)?;
            }            
        }
        Ok(outline.add_declar(stmt))
    }    

    pub fn alloc<A>(&self, item: A) -> &'b A {
        &*self.bump.alloc(item)
    }
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn take_next_bv(&mut self) -> u64 {
        let outgoing = self.next_bv;
        // Assert we're under the limit of 55 bound variables.
        assert!(outgoing >> 55 == 0);
        self.next_bv *= 2;
        outgoing
    }    

    fn load_args(&mut self, args: &[Arg], stmt: NumdStmtCmd) -> Res<()> {
        make_sure!(self.heap.len() == 0);
        make_sure!(self.next_bv == 1);

        for (idx, arg) in args.iter().enumerate() {
            if arg.bound() {
                // b/c we have a bound var, assert the arg's sort is not strict
                make_sure!(!(self.outline.file_view.mmb_sort_mods(arg.sort())?.contains(Modifiers::STRICT)));

                // increment the bv counter/checker
                let this_bv = self.take_next_bv();
                // assert that the mmb file has the right/sequential bv idx for this bound var
                make_sure!(none_err!(arg.bound_digit())? == this_bv);
            } else {
                // assert that this doesn't have any dependencies with a bit pos/idx greater
                // than the number of bvs that have been declared/seen.
                make_sure!(0 == (arg.deps().unwrap() & !(self.next_bv - 1)));
            }

            self.heap.push(self.alloc(MmbItem::Expr(self.alloc(MmbExpr::Var { idx, ty: *arg }))));
        }
        // For termdefs, pop the last item (which is the return) off the stack.
        if let NumdStmtCmd::TermDef {..} = stmt {
            self.heap.pop();
        }
        Ok(())
    }       

    pub fn verify_termdef(
        &mut self, 
        stmt: NumdStmtCmd,
        term: TermRef<'a>,
        proof: ProofIter,
    ) -> Res<()> {
        self.load_args(term.args_and_ret(), stmt)?;
        if term.def() {
            self.run_proof(crate::mmb::proof::Mode::Def, proof)?;
            let final_val = none_err!(self.stack.pop())?;
            let ty = final_val.get_ty()?;
            make_sure!(self.stack.is_empty());
            make_sure!(sorts_compatible(ty, term.ret()));
            make_sure!(self.uheap.is_empty());
            for arg in self.heap.iter().take(term.args().len()) {
                self.uheap.push(*arg);
            }

            self.run_unify(crate::mmb::unify::UMode::UDef, term.unify(), final_val)?;
        }
        Ok(())
    }

    pub fn verify_assert(
        &mut self, 
        stmt: NumdStmtCmd,
        assert: ThmRef<'a>,
        proof: ProofIter,
    ) -> Res<()> {
        self.load_args(assert.args(), stmt)?;
        self.run_proof(crate::mmb::proof::Mode::Thm, proof)?;

        let final_val = match none_err!(self.stack.pop())? {
            MmbItem::Proof(p) if matches!(stmt, NumdStmtCmd::Thm {..}) => p,
            owise if matches!(stmt, NumdStmtCmd::Axiom {..}) => owise,
            owise => return Err(VerifErr::Msg(format!("Expected a proof; got {:?}", owise)))
        };

        make_sure!(self.stack.is_empty());
        make_sure!(self.uheap.is_empty());
        for arg in self.heap.iter().take(assert.args().len()) {
            self.uheap.push(*arg);
        }
        self.run_unify(crate::mmb::unify::UMode::UThmEnd, assert.unify(), final_val)
    }
}


