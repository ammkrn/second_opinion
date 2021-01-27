use crate::util::{
    VerifErr,
    Res,
};
use crate::mmb::{
    MmbItem,
    MmbList::*,
    MmbState,
    MmbPtr,
    MmbListPtr,
};

use crate::util::try_next_cmd;
use crate::none_err;
use crate::make_sure;


/// `UNIFY_TERM = 0x30`: See [`UnifyCmd`](super::UnifyCmd).
pub const UNIFY_TERM: u8 = 0x30;
/// `UNIFY_TERM_SAVE = 0x31`: See [`UnifyCmd`](super::UnifyCmd).
pub const UNIFY_TERM_SAVE: u8 = 0x31;
/// `UNIFY_REF = 0x32`: See [`UnifyCmd`](super::UnifyCmd).
pub const UNIFY_REF: u8 = 0x32;
/// `UNIFY_DUMMY = 0x33`: See [`UnifyCmd`](super::UnifyCmd).
pub const UNIFY_DUMMY: u8 = 0x33;
/// `UNIFY_HYP = 0x36`: See [`UnifyCmd`](super::UnifyCmd).
pub const UNIFY_HYP: u8 = 0x36;

/// Unify commands appear in the header data for a `def` or `axiom`/`theorem`.
/// They are executed by the [`ProofCmd::Thm`] command in order to perform
/// substitutions. The state of the unify stack machine is:
///
/// * `MS: Stack<StackEl>`: The main stack, called `S` in the [`ProofCmd`]
///   documentation.
///   Since a unification is called as a subroutine during a proof command,
///   the main stack is available, but most operations don't use it.
/// * `S: Stack<Expr>`: The unify stack, which contains expressions
///   from the target context that are being destructured.
/// * `H: Vec<Expr>: The unify heap, also known as the substitution. This is
///   initialized with the expressions that the target context would like to
///   substitute for the variable names in the theorem being applied, but
///   it can be extended in order to support substitutions with sharing
///   as well as dummy variables.
#[derive(Debug, Clone, Copy)]
pub enum UnifyCmd {
    /// ```text
    /// UTerm t: S, (t e1 ... en) --> S, en, ..., e1
    /// USave: H; S, e --> H, e; S, e
    /// UTermSave t = USave; UTerm t:
    ///   H; S, (t e1 ... en) --> H, (t e1 ... en); S, en, ..., e1
    /// ```
    /// Pop an element from the stack, ensure that the head is `t`, then
    /// push the `n` arguments to the term (in reverse order, so that they
    /// are dealt with in the correct order in the command stream).
    /// `UTermSave` does the same thing but saves the term to the unify heap
    /// before the destructuring.
    Term {
        /** The term that should be at the head */
        term_num: u32,
        /** True if we want to recall this substitution for later */
        save: bool,
    },
    /// ```text
    /// URef i: H; S, Hi --> H; S
    /// ```
    /// Get the `i`-th element from the unify heap (the substitution),
    /// and match it against the head of the unify stack.
    Ref(u32),
    /// ```text
    /// UDummy s: H; S, x --> H, x; S   (where x:s)
    /// ```
    /// Pop a variable from the unify stack (ensure that it is a name of
    /// the appropriate sort) and push it to the heap (ensure that it is
    /// distinct from everything else in the substitution).
    Dummy { sort_id: u8 },
    /// ```text
    /// UHyp (UThm mode):  MS, |- e; S --> MS; S, e
    /// UHyp (UThmEnd mode):  HS, e; S --> HS; S, e
    /// ```
    /// `UHyp` is a command that is used in theorem declarations to indicate that
    /// we are about to read a hypothesis. There are two contexts where we read
    /// this, when we are first declaring the theorem and check the statement (`UThmEnd` mode),
    /// and later when we are applying the theorem and have to apply a substitution (`UThm` mode).
    /// When we are applying the theorem, we have `|- e` on the main stack, and we
    /// pop that and load the expression onto the unify stack.
    /// When we are checking a theorem, we have been pushing hypotheses onto the
    /// hypothesis stack, so we pop it from there instead.
    Hyp,
}

impl std::convert::TryFrom<(u8, u32)> for UnifyCmd {
    type Error = VerifErr;
    fn try_from((cmd, data): (u8, u32)) -> Result<Self, VerifErr> {
        Ok(match cmd {
            UNIFY_TERM => UnifyCmd::Term {
                term_num: data,
                save: false,
            },
            UNIFY_TERM_SAVE => UnifyCmd::Term {
                term_num: data,
                save: true,
            },
            UNIFY_REF => UnifyCmd::Ref(data),
            UNIFY_DUMMY => {
                let sort_id = u8::try_from(data).map_err(|_| {
                    VerifErr::Msg("Failure to shrink u32 to u8 in proof_cmd try from".to_string())
                })?;
                UnifyCmd::Dummy { sort_id }
            }
            UNIFY_HYP => UnifyCmd::Hyp,
            _ => return Err(VerifErr::Msg("Unrecognized try_form in try from unifycmd".to_string())),
        })
    }
}

/// An iterator over a unify command stream.
#[derive(Debug, Clone, Copy)]
pub struct UnifyIter<'a> {
    /// The full source file.
    pub buf: &'a [u8],
    /// The index of the current declaration in the file.
    pub pos: usize,
}


impl<'a> Iterator for UnifyIter<'a> {
    type Item = Result<UnifyCmd, VerifErr>;
    fn next(&mut self) -> Option<Self::Item> {
        match try_next_cmd(self.buf, self.pos) {
            // err
            Err(e) => Some(Err(e)),
            // Exhausted
            Ok(None) => None,
            // next
            Ok(Some((stmt, rest))) => {
                self.pos = rest;
                Some(Ok(stmt))
            }            
        }
    }
}

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
        tgt: MmbPtr<'a>,
    ) -> Res<()> {    
        self.mem.ustack.push(tgt);

        for maybe_cmd in unify {
            match maybe_cmd? {
                UnifyCmd::Ref(i) => self.unify_ref(i)?,
                UnifyCmd::Term { term_num, save } => self.unify_term(term_num, save)?,
                UnifyCmd::Dummy { sort_id } => self.unify_dummy(mode, sort_id)?,
                UnifyCmd::Hyp => self.unify_hyp(mode)?,
            }
        }

        make_sure!(self.mem.ustack.is_empty());
        if mode == UMode::UThmEnd {
            make_sure!(self.mem.hstack.is_empty());
        }
        Ok(self.mem.uheap.clear())
    }

    fn unify_ref(&mut self, i: u32) -> Res<()> {
        let heap_elem = none_err!(self.mem.uheap.get(i as usize).copied())?;
        let ustack_elem = none_err!(self.mem.ustack.pop())?;
        if heap_elem != ustack_elem {
            Err(VerifErr::Msg(format!("Bad unify ref")))
        } else {
            Ok(())
        }
    }

    pub fn push_ustack_rev_mmb(&mut self, items: MmbListPtr<'a>) {
        if let Cons(hd, tl) = items.read(self) {
            self.push_ustack_rev_mmb(tl);
            self.mem.ustack.push(hd);
        }
    }

    fn unify_term(
        &mut self,
        term_num: u32,
        save: bool
    ) -> Res<()> {
        let p = none_err!(self.mem.ustack.pop())?;
        if let MmbItem::App { term_num:id2, args, .. } = p.read(self) {
            make_sure!(term_num == id2);
            self.push_ustack_rev_mmb(args);
            if save {
                self.mem.uheap.push(p)
            }
            Ok(())
        } else {
            unreachable!()
        }
    }        

    fn unify_dummy(
        &mut self,
        mode: UMode,
        sort_id: u8,
    ) -> Res<()> {
        make_sure!(mode == UMode::UDef);
        let p = self.mem.ustack.pop().unwrap();
        if let MmbItem::Var { ty, .. } = p.read(self) {
            make_sure!(sort_id == ty.sort());
            // assert that ty is bound, and get its bv idx (0-55);
            let bound_idx = ty.bound_digit()?;
            // ty has no dependencies
            for heap_elem in self.mem.uheap.iter() {
                let ty = heap_elem.get_ty(self).unwrap();
                make_sure!(ty.inner & bound_idx == 0);
            }

            Ok(self.mem.uheap.push(p))
        } else {
            unreachable!()
        }
    }    

    fn unify_hyp(&mut self, mode: UMode) -> Res<()> {
        if let UMode::UThm = mode {
            let proof = none_err!(self.mem.stack.pop())?;
            if let MmbItem::Proof(e) = proof.read(self) {
                Ok(self.mem.ustack.push(e))
            } else {
                unreachable!()
            }
        } else if let UMode::UThmEnd = mode {
            make_sure!(self.mem.ustack.is_empty());
            let elem = self.mem.hstack.pop().unwrap();
            Ok(self.mem.ustack.push(elem))
        } else {
            unreachable!()
        }
    }    

}
