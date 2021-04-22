use crate::util::{
    VerifErr,
    Res,
};
use crate::mmb::{
    MmbItem,
    MmbState,
    MmbExpr
};
use mm0b_parser::{ UnifyIter, UnifyCmd };
use mm0_util::{ SortId, TermId };

use crate::none_err;
use crate::make_sure;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UMode {
    UThm,
    UDef,
    UThmEnd
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn run_unify(
        &mut self, 
        mode: UMode,
        unify: UnifyIter,
        tgt: &'b MmbItem<'b>,
    ) -> Res<()> {    
        self.ustack.push(tgt);

        for maybe_cmd in unify {
            match maybe_cmd.map_err(|e| VerifErr::Msg(format!("{:?}", e)))? {
                UnifyCmd::Ref(i) => self.unify_ref(i)?,
                UnifyCmd::Term { tid, save } => self.unify_term(tid, save)?,
                UnifyCmd::Dummy(sort_id) => self.unify_dummy(mode, sort_id)?,
                UnifyCmd::Hyp => self.unify_hyp(mode)?,
            }
        }

        make_sure!(self.ustack.is_empty());
        if mode == UMode::UThmEnd {
            make_sure!(self.hstack.is_empty());
        }
        Ok(self.uheap.clear())
    }

    fn unify_ref(&mut self, i: u32) -> Res<()> {
        let heap_elem = none_err!(self.uheap.get(i as usize).copied())?;
        let ustack_elem = none_err!(self.ustack.pop())?;
        if heap_elem != ustack_elem {
            Err(VerifErr::Msg(format!("Bad unify ref")))
        } else {
            Ok(())
        }
    }

    fn unify_term(
        &mut self,
        term_num: TermId,
        save: bool
    ) -> Res<()> {
        let p = none_err!(self.ustack.pop())?;
        if let MmbItem::Expr(MmbExpr::App { term_num:id2, args, .. }) = p {
            make_sure!(term_num == *id2);
            for arg in args.iter().rev() {
                self.ustack.push(arg)
            }
            if save {
                self.uheap.push(p)
            }
            Ok(())
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }        

    fn unify_dummy(
        &mut self,
        mode: UMode,
        sort_id: SortId,
    ) -> Res<()> {
        make_sure!(mode == UMode::UDef);
        let p = self.ustack.pop().unwrap();
        if let MmbItem::Expr(MmbExpr::Var { ty, .. }) = p {
            make_sure!(sort_id == ty.sort());
            // assert that ty is bound, and get its bv idx (0-55);
            let bound_idx = none_err!(ty.bound_digit())?;
            // ty has no dependencies
            for heap_elem in self.uheap.iter() {
                let ty = heap_elem.get_ty().unwrap();
                make_sure!(ty.into_inner() & bound_idx == 0);
            }

            Ok(self.uheap.push(p))
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }    

    fn unify_hyp(&mut self, mode: UMode) -> Res<()> {
        if let UMode::UThm = mode {
            let proof = none_err!(self.stack.pop())?;
            if let MmbItem::Proof(e) = proof {
                Ok(self.ustack.push(e))
            } else {
                return Err(VerifErr::Unreachable(file!(), line!()));
            }
        } else if let UMode::UThmEnd = mode {
            make_sure!(self.ustack.is_empty());
            let elem = self.hstack.pop().unwrap();
            Ok(self.ustack.push(elem))
        } else {
            return Err(VerifErr::Unreachable(file!(), line!()));
        }
    }    

}
