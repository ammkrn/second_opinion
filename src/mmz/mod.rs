pub mod parse;
pub mod math_parser;

use std::convert::TryFrom;
use std::collections::HashMap;
use std::sync::Arc;

use bumpalo::Bump;
use bumpalo::collections::Vec as BumpVec;

use crate::none_err;
use crate::conv_err;
use crate::Outline;
use crate::util::{ 
    Either::*,
    Str,
    SortNum,
    TermNum,
    AssertNum,
    SortIdent,
    TermIdent,
    AssertIdent,
    VerifErr,
    Res,
    Type,
    Term
};
use crate::mmb::stmt::StmtCmd;

pub type MathStr<'b, 'a> = BumpVec<'b, Str<'a>>;

// Stack item
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmzExpr<'b> {
    Var(MmzVar<'b>),
    App {
        term_num: u32,
        num_args: u16,
        args: &'b [MmzExpr<'b>],
        sort: SortNum,
    },
}

impl<'b> MmzExpr<'b> {
    fn sort(self) -> SortNum {
        match self {
            MmzExpr::Var(v) => v.sort(),
            MmzExpr::App { sort, .. } => sort
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MmzHyp<'a> {
    pub ident: Option<Str<'a>>,
    pub pos: Option<usize>,
    pub expr: MmzExpr<'a>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MmzVar<'a> {
    pub ident: Option<Str<'a>>,
    pub pos: usize,
    pub ty: Type,
    pub is_dummy: bool,
}

impl<'a> MmzVar<'a> {
    pub fn is_bound(self) -> bool {
        self.ty.is_bound()
    }

    pub fn sort(self) -> u8 {
        self.ty.sort()
    }
}

//#[derive(Debug)]
//pub struct DeclaredNotation<'a> {
//    pub has_coe: bool,
//    pub consts: Vec<(Str<'a>, Option<Fix>)>
//}

//impl<'a> std::default::Default for DeclaredNotation<'a> {
//    fn default() -> Self {
//        DeclaredNotation {
//            has_coe: false,
//            consts: Vec::new()
//        }
//    }
//}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DelimKind {
    Left,
    Right,
    Both,
}

/// Operator precedence for user-declared notation. 
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Prec {
    Num(u32),
    Max,
}

/// The corresponding term number, its ident (name), whether it's right-associative, and any
/// literal items/symbols used in the declaration. For general notation declarations that 
/// start with a non-variable, that gets left out of `lits`, and instead becomes
/// one of the keys in `prefixes`. When the math parser finds the initial token, it
/// looksup the term using the `prefixes` mapping, and then uses the remaining consts
/// as checks to make sure the item is syntactically correct, but it will have already
/// parsed and gone past the initial const token.
///
/// Examples of lits:
///```text
/// NotationInfo { 
///     term_num: 2, 
///     term_ident: an, 
///     rassoc: false, 
///     lits: [Var { pos: 0, prec: Num(34) }, Const(/\), Var { pos: 1, prec: Num(35) }] 
/// }
///
/// NotationInfo { 
///    term_num: 1, 
///    term_ident: not, 
///    rassoc: true, 
///    lits: [Var { pos: 0, prec: Num(41) }] 
///}
///
/// // notice the missing `Const([)` at the front; it's a key in the `prefixes` map.
/// NotationInfo { 
///     term_num: 14, 
///     term_ident: sb, 
///     rassoc: true, 
///     lits: [Var { pos: 0, prec: Num(1) }, Const(/), Var { pos: 1, prec: Num(1) }, Const(]), Var { pos: 2, prec: Num(42) }] 
/// }
///```
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right
}

/// Inside of a general notation declaration, you can either have variables (`Var`) or notation symbols.
/// For example, in the notation for `peano.mm0/sb` which represents variable substitution,
///```text
/// notation sb (a: nat) {x: nat} (p: wff x): wff =
/// ($[$:41) a ($/$:0) x ($]$:0) p;
///```
/// You have three variables [ a, x, p ]
///
/// and three `Const` items, [ $[$, $/$, $]$ ]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NotationLit<'a> {
    Var { pos: usize, prec: Prec },
    Const(Str<'a>),
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Coe {
    // term_id
    Single {
        term_num: TermNum,
    },
    // transitive
    // `Trans(c1, m, c2)` asserts that `c1: s1 -> m` and `c2: m -> s2` (so we get a transitive
    // coercion from `s1` to `s2`).
    Trans {
        // (sA -> sB)
        c1: Arc<Coe>,
        // sB
        middleman_sort: SortNum,
        // (sB -> sC)
        c2: Arc<Coe>
    },
}

/// The persistent (remains between the checking of each mm0 declaration) mm0 state.
/// 
/// The most complex part of this is the notation system. Users can declare 4 kinds of notation,
/// prefix, infixl, infixr, and general. The verifier tracks these in only two maps, putting 
/// prefix and general notations in the `prefixes` map, and infixl/infixr declarations in the `infixes` map.
/// The reason for this grouping is because the math parser looks for these two things separately, and the places
/// where a prefix item might be used are also the places where a general notation can be, and the same is true
/// for both flavors of infix.
///
/// There are four maps holding notation information. 
/// 1. `consts`: map of the item's name to its associated precedence.
/// 2. `occupied_precs`: Prevents parser ambiguities; see the doc comment above the field for more info about this.
/// 3. `prefixes`: Associates the items' name to its `NotationInfo { term_num, term_ident, rassoc, lits }`
/// 3. `infixes`: Associates the items' name to its `NotationInfo { term_num, term_ident, rassoc, lits }`
pub struct MmzMem<'a> {
    pub outline: &'a Outline<'a>,

    pub mmz: &'a [u8],
    pub mmz_files: &'a [String],
    pub mmz_file_num: usize,
    pub mmz_pos: usize,
    pub delims: Vec<(u8, DelimKind)>,

    /// Maps the string representing a user-declared notation to its associated precedence value. For example:
    ///```text 
    /// peano.mm0/and 
    ///
    /// /\ |-> `Prec::Num(34)`
    ///```
    pub consts: HashMap<Str<'a>, Prec>,
    /// A map containing both prefix and general notation declarations. 
    ///
    /// `Ident |-> NotationInfo { term_num, term_ident, rassoc, lits }`
    pub prefixes: HashMap<Str<'a>, NotationInfo<'a>>,
    pub infixes: HashMap<Str<'a>, NotationInfo<'a>>,    
    /// A mapping of precedence levels to (prefix \/ infixl \/ infixr).
    /// This is necessary to prevent ambiguities in the math parser; while the math parser 
    /// won't completely break without this, "You will get _a_ parse, but part of the idea here 
    /// is that you will also get _the_ parse", where _the_ parse is the one that conforms to
    /// the context-free grammar laid out [here](https://github.com/digama0/mm0/blob/master/mm0.md#secondary-parsing).
    ///
    /// If the environment permits both an infixl and infixr at the same precednce level, for example:
    ///
    ///```text
    /// infixr im: $->$ prec 25;
    /// infixl an: $/\$ prec 25;
    ///```
    ///
    /// Then beginning from state `Start`, and using rules 0, 1, and 2 taken from the mm0 expression grammar, we can derive 
    /// both `(a -> (b /\ c))` and `((a -> b) /\ c)` as parses of `$ a -> b /\ c $`:
    ///```text
    /// Start := $ expr(0) $;
    /// rule0 := expression(p1) -> expression(p2)                   (if p1 < p2)
    /// rule1 := expression(p) -> expression(p) OP expression(p+1)  (if OP is infixl prec p)
    /// rule2 := expression(p) -> expression(p+1) OP expression(p)  (if OP is infixr prec p)
    ///
    /// with both:
    /// infixr im: $->$ prec 25;
    /// infixl an: $/\$ prec 25;
    ///
    /// To get ((a -> b) /\ c):
    /// ($ a -> b /\ c $, 0)   ~rule0~> ($ a -> b /\ c $, 25) 
    /// ($ a -> b /\ c $, 25)  ~rule1~> ($ a -> b $, 25) /\ ($ c $, 26)
    /// ($ a -> b $, 25)       ~rule2~> ($ a $, 26) -> ($ b $, 25)
    ///
    /// To get (a -> (b /\ c)):
    /// ($ a -> b /\ c $, 0)  ~rule0~> ($ a -> b /\ c $, 25) by rule0
    /// ($ a -> b /\ c $, 25) ~rule2~> ($ a $, 26) -> ($ b /\ c $, 25) by rule2
    /// ($ b /\ c $, 25)      ~rule1~> ($ b $, 25) /\ ($ c $, 26) by rule1
    ///```
    ///
    /// By disallowing both `-> infixr` and `/\ infixl` to inhabit the same precedence, this ambiguity
    /// can be avoided.
    ///
    /// `peano.mm1` and the mm1 files based on it adopt a convention of using even precedence numbers for 
    /// left-associative infix operators, and odd precedence numbers for right-associative infix operators
    /// as a simple way to avoid this kind of collision.
    /// infixl is L
    /// infixr is R
    /// (prefix w/ arity > 0) /\ general ending with a variable are Rassoc
    /// 0ary prefix /\ general ending with a const don't affect the map.
    pub occupied_precs: HashMap<Prec, Assoc>,    
    // unneeded
    //pub declared_notations: FxIndexMap<Str<'a>, DeclaredNotation<'a>>,
    pub nonlocal_termdefs: HashMap<TermIdent<'a>, TermNum>,
    pub nonlocal_asserts: HashMap<AssertIdent<'a>, AssertNum>,
    sorts: Vec<SortIdent<'a>>,
    pub provs: HashMap<SortNum, bool>,
    /// `sort_id |-> [sort_id |-> coe]`
    ///
    /// A map of sort pairs `s1/from, s2/to` to the coercion `c: s1 -> s2`.
    pub coes: HashMap<SortNum, HashMap<SortNum, Coe>>,
    /// A map of sorts `s` to some sort `t` such that `t` is provable and `c: s -> t` is in `coes`,
    /// if one exists.
    pub coe_prov: HashMap<SortNum, SortNum>,

    num_sorts: u8,
    num_termdefs: u32,
    num_asserts: u32,
}

impl<'a> MmzMem<'a> {
    //fn new_for_test() -> Res<Self> {
    //}

    /// The main constructor for `State`.
    pub fn new_from(outline: &'a Outline<'a>) -> Res<Self> {
        Ok(MmzMem {
            outline,
            mmz: none_err!(outline.file_data.mmz_files.first())?.as_bytes(),
            mmz_files: outline.file_data.mmz_files.as_slice(),
            mmz_pos: 0usize,
            mmz_file_num: 0usize,
        
            delims: Vec::new(),

            consts: HashMap::new(),
            prefixes: HashMap::new(),
            infixes: HashMap::new(),
            occupied_precs: HashMap::new(),
            //declared_notations: FxIndexMap::with_hasher(Default::default()),
            nonlocal_termdefs: HashMap::new(),
            nonlocal_asserts: HashMap::new(),
            sorts: Vec::new(),
            provs: HashMap::new(),
            coes: HashMap::new(),
            coe_prov: HashMap::new(),
            num_sorts: 0,
            num_termdefs: 0,
            num_asserts: 0,
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


    pub fn add_termdef(&mut self, ident: Str<'a>) -> TermNum {
        let idx = self.num_termdefs;
        assert!(self.nonlocal_termdefs.insert(ident, idx).is_none());
        idx
    }

    pub fn add_assert(&mut self, ident: Str<'a>) -> AssertNum {
        let idx = self.num_asserts;
        assert!(self.nonlocal_asserts.insert(ident, idx).is_none());

        idx
    }

    pub fn get_sort_num(&self, ident: Str<'a>) -> Res<u8> {
        let idx = none_err!(self.sorts.iter().position(|s| *s == ident))?;
        conv_err!(u8::try_from(idx))
    }

    pub fn add_sort(&mut self, ident: Str<'a>) -> SortNum {
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

    pub fn occupy_prec(&mut self, term_ident: Str<'a>, prec: Prec, assoc: Assoc) -> Res<()> {
        if let Some(already) = self.occupied_precs.insert(prec, assoc) {
            if already != assoc {
                return Err(VerifErr::Msg(format!("{:?}; Cannot re-occupy prec {:?} with different associativity", term_ident, prec)))
            }
        }
        Ok(())
    }
}

//#[derive(Debug)]
pub struct MmzState<'b, 'a: 'b> {
    pub mem: &'b mut MmzMem<'a>,
    bump: &'b Bump,
    vars_todo: BumpVec<'b, (Str<'a>, bool)>,
    vars_done: BumpVec<'b, MmzVar<'b>>,
    hyps: BumpVec<'b, MmzHyp<'b>>,
    ustack: BumpVec<'b, MmzExpr<'b>>,
    uheap: BumpVec<'b, MmzExpr<'b>>,
    pub next_bv: u64    

}

impl<'b, 'a: 'b> MmzState<'b, 'a> {
    pub fn new_from(mem: &'b mut MmzMem<'a>, bump: &'b mut Bump) -> MmzState<'b, 'a> {
        bump.reset();
        MmzState {
            mem,
            bump,
            vars_todo: BumpVec::new_in(bump),
            vars_done: BumpVec::new_in(bump),
            hyps: BumpVec::new_in(bump),
            ustack: BumpVec::new_in(bump),
            uheap: BumpVec::new_in(bump),
            next_bv: 1u64            
        }
    }

    pub fn alloc<A>(&self, item: A) -> &'b A {
        &*self.bump.alloc(item)
    }        

    pub fn take_next_bv(&mut self) -> u64 {
        let outgoing = self.next_bv;
        // Assert we're under the limit of 55 bound variables.
        assert!(outgoing >> 55 == 0);
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
