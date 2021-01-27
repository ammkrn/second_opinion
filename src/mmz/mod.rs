pub mod parse;
pub mod math_parser;

use std::convert::TryFrom;
use std::collections::BTreeMap as Bmap;
use std::sync::Arc;
use std::marker::PhantomData;

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

use crate::none_err;
use crate::conv_err;
use crate::Outline;
use crate::util::{ 
    Either::*,
    FxIndexSet,
    FxMap,
    Str,
    SortNum,
    TermNum,
    AssertNum,
    SortIdent,
    TermIdent,
    AssertIdent,
    Ptr,
    VerifErr,
    Res,
    Type,
    Term
};
use crate::mmb::stmt::StmtCmd;

use MathStr::*;


pub type MathStrPtr<'a> = Ptr<'a, MathStr<'a>>;

// A formula is a L -> R list of Str elements
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MathStr<'a> {
    Empty,
    Cont(MathStrPtr<'a>, Str<'a>)
}


impl<'b, 'a: 'b> MathStr<'a> {
    pub fn alloc(self, st: &mut MmzState<'b, 'a>) -> MathStrPtr<'a> {
        let (idx, _) = st.mem.math_strs.insert_full(self);
        Ptr(u32::try_from(idx).unwrap(), PhantomData)
    }
    //pub fn read(self, _: &St<'a>) -> MathStr<'a> { self }
}

impl<'b, 'a: 'b> MathStrPtr<'a> {
    pub fn read(self, st: &MmzState<'b, 'a>) -> MathStr<'a> {
        st.mem.math_strs.get_index(self.0 as usize).copied().unwrap()
    }
    //pub fn alloc(self, _: &mut St<'a>) -> MathStrPtr<'a> { self }
}



pub type MmzListPtr<'a> = Ptr<'a, MmzList<'a>>;
pub type MmzPtr<'a> = Ptr<'a, MmzItem<'a>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmzList<'a> {
    Nil,
    Cons(MmzPtr<'a>, MmzListPtr<'a>)
}

// Stack item
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmzItem<'a> {
    Var {
        pos: usize,
        ty: Type,
        is_dummy: bool
    },
    App {
        term_num: u32,
        num_args: u16,
        args: MmzList<'a>
    },
}

impl<'b, 'a: 'b> MmzItem<'a> {
    pub fn alloc(self, st: &mut MmzState<'b, 'a>) -> MmzPtr<'a> {
        let (idx, _) = st.mem.mmz_items.insert_full(self);
        Ptr(u32::try_from(idx).unwrap(), PhantomData)
    }
}

impl<'b, 'a: 'b> MmzPtr<'a> {
    pub fn read(self, st: &MmzState<'b, 'a>) -> MmzItem<'a> {
        st.mem.mmz_items.get_index(self.0 as usize).copied().unwrap()
    }
}

impl<'b, 'a: 'b> MmzList<'a> {
    pub fn alloc(self, st: &mut MmzState<'b, 'a>) -> MmzListPtr<'a> {
        let (idx, _) = st.mem.mmz_lists.insert_full(self);
        Ptr(u32::try_from(idx).unwrap(), PhantomData)
    }
}

impl<'b, 'a: 'b> MmzListPtr<'a> {
    pub fn read(self, st: &MmzState<'b, 'a>) -> MmzList<'a> {
        st.mem.mmz_lists.get_index(self.0 as usize).copied().unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MmzHyp<'a> {
    pub ident: Option<Str<'a>>,
    pub pos: Option<usize>,
    pub expr: MmzItem<'a>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MmzVar<'a> {
    pub ident: Option<Str<'a>>,
    pub pos: usize,
    pub ty: Type,
    pub is_dummy: bool,
}

impl<'a> MmzVar<'a> {
    pub fn to_parse_var(self) -> MmzItem<'a> {
        MmzItem::Var {
            pos: self.pos,
            ty: self.ty,
            is_dummy: self.is_dummy
        }
    }
    
    pub fn is_bound(self) -> bool {
        self.ty.is_bound()
    }

    pub fn sort(self) -> u8 {
        self.ty.sort()
    }
}

#[derive(Debug)]
pub struct DeclaredNotation<'a> {
    pub has_coe: bool,
    pub consts: Vec<(Str<'a>, Option<Fix>)>
}

impl<'a> std::default::Default for DeclaredNotation<'a> {
    fn default() -> Self {
        DeclaredNotation {
            has_coe: false,
            consts: Vec::new()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DelimKind {
    Left,
    Right,
    Both,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Prec {
    Num(u32),
    Max,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NotationInfo<'a> {
    pub term_num: u32,
    pub term_ident: Str<'a>,
    pub rassoc: bool,
    pub lits: Arc<[NotationLit<'a>]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fix {
    Infixl,
    Infixr,
    Prefix,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NotationLit<'a> {
    Var { pos: usize, prec: Prec },
    Const(Str<'a>),
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Coe {
    // term_id
    Single {
        term_num: u32,
    },
    // transitive
    // `Trans(c1, m, c2)` asserts that `c1: s1 -> m` and `c2: m -> s2` (so we get a transitive
    // coercion from `s1` to `s2`).
    // middle is a sort_id
    Trans {
        c1: Arc<Coe>,
        sort_num: u8,
        c2: Arc<Coe>
    },
}

pub struct MmzMem<'a> {
    pub outline: &'a Outline<'a>,

    pub mmz: &'a [u8],
    pub mmz_files: &'a [String],
    pub mmz_file_num: usize,
    pub mmz_pos: usize,
    pub strs: FxIndexSet<Str<'a>>,
    pub math_strs: FxIndexSet<MathStr<'a>>,
    pub mmz_items: FxIndexSet<MmzItem<'a>>,
    pub mmz_lists: FxIndexSet<MmzList<'a>>,
    pub delims: Vec<(u8, DelimKind)>,

    pub consts: FxMap<Str<'a>, Prec>,
    pub prefixes: FxMap<Str<'a>, NotationInfo<'a>>,
    pub infixes: FxMap<Str<'a>, NotationInfo<'a>>,    

    // unneeded
    //pub declared_notations: FxIndexMap<Str<'a>, DeclaredNotation<'a>>,
    pub nonlocal_termdefs: FxMap<TermIdent<'a>, TermNum>,
    pub nonlocal_asserts: FxMap<AssertIdent<'a>, AssertNum>,
    sorts: Vec<SortIdent<'a>>,
    pub provs: FxMap<SortNum, bool>,
    // sort_id, |-> [sort_id, coe]
    // A map of sort pairs `s1,s2` to the coercion `c: s1 -> s2`.
    pub coes: FxMap<SortNum, FxMap<SortNum, Coe>>,
    /// A map of sorts `s` to some sort `t` such that `t` is provable and `c: s -> t` is in `coes`,
    /// if one exists.
    pub coe_prov: FxMap<SortNum, SortNum>,
    num_sorts: u8,
    num_termdefs: u32,
    num_asserts: u32,
    bmaps: Vec<Bmap<usize, MmzItem<'a>>>,
    vecs: Vec<Vec<MmzItem<'a>>>,
}


impl<'a> MmzMem<'a> {
    //fn new_for_test() -> Res<Self> {
    //}

    /// The main constructor for `State`.
    pub fn new_from(outline: &'a Outline<'a>) -> Res<Self> {
        let mut math_strs = FxIndexSet::with_hasher(Default::default());
        let mut mmz_lists = FxIndexSet::with_hasher(Default::default());
        math_strs.insert(Empty);
        mmz_lists.insert(MmzList::Nil);

        Ok(MmzMem {
            outline,
            mmz: none_err!(outline.file_data.mmz_files.first())?.as_bytes(),
            mmz_files: outline.file_data.mmz_files.as_slice(),
            mmz_pos: 0usize,
            mmz_file_num: 0usize,
        
            strs: FxIndexSet::with_hasher(Default::default()),
            math_strs,
            mmz_items: FxIndexSet::with_hasher(Default::default()),
            mmz_lists,
            delims: Vec::new(),

            consts: FxMap::with_hasher(Default::default()),
            prefixes: FxMap::with_hasher(Default::default()),
            infixes: FxMap::with_hasher(Default::default()),
            //declared_notations: FxIndexMap::with_hasher(Default::default()),

            nonlocal_termdefs: FxMap::with_hasher(Default::default()),
            nonlocal_asserts: FxMap::with_hasher(Default::default()),
            sorts: Vec::new(),
            provs: FxMap::with_hasher(Default::default()),
            coes: FxMap::with_hasher(Default::default()),
            coe_prov: FxMap::with_hasher(Default::default()),
            num_sorts: 0,
            num_termdefs: 0,
            num_asserts: 0,
            bmaps: Vec::new(),
            vecs: Vec::new(),
        })
    }        

    pub fn verify1(&mut self, bump: &mut Bump, stmt: StmtCmd) -> Res<()> {
        if !stmt.is_local() {
            let item = match stmt {
                StmtCmd::Sort {..} => None,
                StmtCmd::TermDef {..} => {
                    let term = self.outline.get_term_by_num(self.num_termdefs_done())?;
                    Some(L(term))
                }
                StmtCmd::Axiom {..} | StmtCmd::Thm {..} => {
                    let assert = self.outline.get_assert_by_num(self.num_asserts_done())?;
                    Some(R(assert))
                }
            };
            self.parse_until(bump, stmt, item)?;
        }
        Ok(self.add_declar(stmt))
    }

    pub fn next_mmz_file(&mut self) -> Res<()> {
        self.mmz_file_num += 1;
        self.mmz_pos = 0;
        Ok(self.mmz = none_err!(self.mmz_files.get(self.mmz_file_num))?.as_bytes())
    }


    pub fn coe_prov_or_else(&self, from: SortNum) -> SortNum {
        self.coe_prov.get(&from).copied().unwrap_or(from)
    }


    pub fn add_termdef(&mut self, ident: Str<'a>) -> u32 {
        let idx = self.num_termdefs;
        assert!(self.nonlocal_termdefs.insert(ident, idx).is_none());
        idx
    }

    pub fn add_assert(&mut self, ident: Str<'a>) -> u32 {
        let idx = self.num_asserts;
        assert!(self.nonlocal_asserts.insert(ident, idx).is_none());

        idx
    }

    pub fn get_sort_num(&self, ident: Str<'a>) -> Res<u8> {
        let idx = none_err!(self.sorts.iter().position(|s| *s == ident))?;
        conv_err!(u8::try_from(idx))
    }

    pub fn add_sort(&mut self, ident: Str<'a>) -> u8 {
        let idx = self.sorts.len();
        assert!(!self.sorts.iter().any(|x| *x == ident));
        self.sorts.push(ident);
        let sort_num = u8::try_from(idx).unwrap();
        let mods = self.outline.get_sort_mods(idx).unwrap();
        assert!(self.provs.insert(sort_num, mods.is_provable()).is_none());
        sort_num
    }

    pub fn num_sorts_done(&self) -> u8{
        self.num_sorts
    }
    pub fn num_termdefs_done(&self) -> u32 {
        self.num_termdefs
    }
    pub fn num_asserts_done(&self) -> u32 {
        self.num_asserts
    }

    pub fn add_declar(&mut self, stmt_cmd: StmtCmd) {
        match stmt_cmd {
            StmtCmd::Sort {..} => self.num_sorts += 1,
            StmtCmd::TermDef {..} => self.num_termdefs += 1,
            StmtCmd::Axiom {..} | StmtCmd::Thm {..} => self.num_asserts += 1,
        }
    }

    pub fn get_term_by_ident(&self, ident: &Str<'a>) -> Res<Term<'a>> {
        let term_num = none_err!(self.nonlocal_termdefs.get(ident).copied())?;
        self.outline.get_term_by_num(term_num)
    }        
  
}

//#[derive(Debug)]
pub struct MmzState<'b, 'a: 'b> {
    pub mem: &'b mut MmzMem<'a>,
    vars_todo: BumpVec<'b, (Str<'a>, bool)>,
    vars_done: BumpVec<'b, MmzVar<'a>>,
    hyps: BumpVec<'b, MmzHyp<'a>>,
    ustack: BumpVec<'b, MmzItem<'a>>,
    uheap: BumpVec<'b, MmzItem<'a>>,
    pub next_bv: u64    

}

impl<'b, 'a: 'b> MmzState<'b, 'a> {
    pub fn new_from(mem: &'b mut MmzMem<'a>, bump: &'b mut Bump) -> MmzState<'b, 'a> {
        bump.reset();
        MmzState {
            mem,
            vars_todo: BumpVec::new_in(bump),
            vars_done: BumpVec::new_in(bump),
            hyps: BumpVec::new_in(bump),
            ustack: BumpVec::new_in(bump),
            uheap: BumpVec::new_in(bump),
            next_bv: 1u64            
        }
    }
}

impl<'b, 'a: 'b> MmzState<'b, 'a> {

    pub fn take_next_bv(&mut self) -> u64 {
        let outgoing = self.next_bv;
        // Assert we're under the limit of 55 bound variables.
        assert!(outgoing >> 56 == 0);
        self.next_bv *= 2;
        outgoing
    }    

    /// Produce the list of variables that have been parsed which are not dummy variables
    /// (But may be either bound or regular)
    pub fn non_dummy_vars(&self) -> impl Iterator<Item = MmzVar> {
        self.vars_done.iter().filter(|v| !v.is_dummy).copied()
    }

    /// Produce the list of potential dependencies (bound variables that are not dummies)
    pub fn potential_deps(&self) -> impl Iterator<Item = MmzVar> {
        self.non_dummy_vars().filter(|v| v.is_bound())
    }

    /// Produce an iterator with the same elements as what an Mmb `Args` should have ()
    pub fn args_iter(&self) -> impl Iterator<Item = MmzVar> {
        self.vars_done.iter().copied().filter(|v| !v.is_dummy)
    }


    pub fn new_vec(&mut self) -> Vec<MmzItem<'a>> {
        self.mem.vecs.pop().unwrap_or_else(|| Vec::new())
    }

    /// Used for vecs of args in the math parser. When you're done with it, 
    /// turn the args into a hash-consed list and return the empty vector to 
    /// the pool of vecs.
    pub fn cash_in_vec(&mut self, mut v: Vec<MmzItem<'a>>) -> MmzList<'a> {
        let mut args = MmzList::Nil;
        while let Some(elem) = v.pop() {
            args = MmzList::Cons(elem.alloc(self), args.alloc(self));
        }
        self.mem.vecs.push(v);
        args
    }

    pub fn new_bmap(&mut self) -> Bmap<usize, MmzItem<'a>> {
        self.mem.bmaps.pop().unwrap_or_else(|| Bmap::new())
    }

    /// Used for the recursive parsing of arguments in the math parser. We use a bmap
    /// instead of a list since we need to end up with a packed vec, but we may not
    /// get the arguments sequentially, since they may be rearranged by notation.
    ///
    /// The convenient ways of doing this (drain/pop/etc) are for some reason
    /// nightly-only for BTreeMap.
    pub fn cash_in_bmap(&mut self, mut bmap: Bmap<usize, MmzItem<'a>>) -> Res<MmzList<'a>> {
        let mut counter = bmap.len();
        let mut args = MmzList::Nil;
        while counter != 0 {
            counter -= 1;
            let hd = none_err!(bmap.get(&counter).copied())?;
            let hd = hd.alloc(self);
            let tl = args.alloc(self);
            args = MmzList::Cons(hd, tl)
        }
        
        bmap.clear();
        self.mem.bmaps.push(bmap);
        Ok(args)
    }    


    pub fn is_empty(&self) -> bool {
        self.mem.mmz_pos == self.mem.mmz.len()
    }

    pub fn cur(&self) -> Option<u8> {
        self.mem.mmz.get(self.mem.mmz_pos).copied()
    }

    pub fn cur_slice(&self) -> &'a [u8] {
        self.mem.mmz.get(self.mem.mmz_pos..).unwrap_or_else(|| &[])
    }

    pub fn advance(&mut self, n: usize) {
        self.mem.mmz_pos += n;
    }    
}


