use std::convert::TryFrom;
use crate::make_sure;
use crate::Outline;
use crate::util::{ Res, VerifErr };
use crate::mmb::proof::{ ProofIter };
use crate::util::{ 
    Type,
    Term,
    Assert,
    Args,
    Ptr,
    FxIndexSet,
    parse_u8,
    parse_u16,
    parse_u32,
    parse_u64,
};
use crate::mmb::stmt::StmtCmd;
use crate::conv_err;
use crate::none_err;

pub mod proof;
pub mod unify;
pub mod index;
pub mod stmt;


use MmbList::*;

const MM0B_MAGIC: u32 = 0x42304D4D;

// Each sort has one byte associated to it, which
// contains flags for the sort modifiers.
// The high four bits are unused.
pub const SORT_PURE     : u8 = 1;
pub const SORT_STRICT   : u8 = 2;
pub const SORT_PROVABLE : u8 = 4;
pub const SORT_FREE     : u8 = 8;

/// bound mask: 10000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
pub const TYPE_BOUND_MASK: u64 = 1 << 63;


/// deps mask: 00000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
pub const TYPE_DEPS_MASK: u64 = (1 << 56) - 1;


// Returns true if a value with type 'from' can be cast to a value of type 'to'.
// This requires that the sorts be the same, and additionally if 'to' is a
// name then so is 'from'.
pub fn sorts_compatible(from: Type, to: Type) -> bool {
  let (from, to) = (from.inner, to.inner);
  let diff = from ^ to;
  let c1 = || (diff & !TYPE_DEPS_MASK) == 0;
  let c2 = || (diff & !TYPE_BOUND_MASK & !TYPE_DEPS_MASK) == 0;
  let c3 = || ((from & TYPE_BOUND_MASK) != 0);
  c1() || (c2() && c3())
}

pub type MmbListPtr<'a> = Ptr<'a, MmbList<'a>>;
pub type MmbPtr<'a> = Ptr<'a, MmbItem<'a>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmbList<'a> {
    Nil,
    Cons(MmbPtr<'a>, MmbListPtr<'a>)
}

// Stack item
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MmbItem<'a> {
    Var {
        idx: usize,
        ty: Type
    },
    App {
        term_num: u32,
        args: MmbList<'a>,
        ty: Type,
    },
    Proof(MmbPtr<'a>),
    Conv(MmbPtr<'a>, MmbPtr<'a>),
    CoConv(MmbPtr<'a>, MmbPtr<'a>)
}


impl<'b, 'a: 'b> MmbItem<'a> {
    pub fn alloc(self, st: &mut MmbState<'b, 'a>) -> MmbPtr<'a> {
        let (idx, _) = st.mem.mmb_items.insert_full(self);
        Ptr(u32::try_from(idx).unwrap(), std::marker::PhantomData)
    }

    //fn read(self, _: &St<'_>) -> StoreItem { self }

    pub fn get_ty(self) -> Res<Type> {
        match self {
            | MmbItem::Var { ty, .. }
            | MmbItem::App { ty, ..} => Ok(ty),
            _ => Err(VerifErr::Msg(format!("No type!")))
        }
    }

    pub fn get_deps(self) -> Res<Type> {
        self.get_ty()
        .and_then(|ty| ty.deps())
        .map(|deps| Type { inner: deps })
    }

    pub fn get_bound_digit(self) -> Res<Type> {
        self.get_ty()
        .and_then(|ty| ty.bound_digit())
        .map(|bound_idx| Type { inner: bound_idx })
    }

    pub fn low_bits(self) -> Type {
        self.get_deps().or(self.get_bound_digit()).unwrap()
    }
}

impl<'b, 'a: 'b> MmbPtr<'a>  {
    pub fn read(self, st: &MmbState<'b, 'a>) -> MmbItem<'a> {
        st.mem.mmb_items.get_index(self.0 as usize).copied().unwrap()
    }

    //pub fn alloc(self, _: &mut St<'_>) -> StorePtr { self }
}

impl<'b, 'a: 'b> MmbList<'a> {
    pub fn alloc(self, st: &mut MmbState<'b, 'a>) -> MmbListPtr<'a> {
        let (idx, _) = st.mem.mmb_lists.insert_full(self);
        Ptr(u32::try_from(idx).unwrap(), std::marker::PhantomData)
    }

    //pub fn read(self, _: &St<'_>) -> StoreItems { self }
}

impl<'b, 'a: 'b> MmbListPtr<'a>  {
    pub fn read(self, st: &MmbState<'b, 'a>) -> MmbList<'a> {
        st.mem.mmb_lists.get_index(self.0 as usize).copied().unwrap()
    }

    //pub fn alloc(self, _: &mut St<'_>) -> StorePtrs { self }
}

#[derive(Debug, Clone, Copy)]
pub struct Header {
    /// "= MM0B_VERSION"
    pub magic: u32,
    pub version: u8,
    /// Number of declared sorts
    pub num_sorts: u8,
    pub reserved: u16,
    /// Number of terms and defs
    pub num_terms: u32,
    /// Number of axioms and theorems
    pub num_thms: u32,

    /// Pointer to start of term table
    pub terms_start: u32,
    /// Pointer to start of theorem table
    pub thms_start: u32,
    /// Pointer to start of proof section
    pub proof_stream_start: u32,
    pub reserved2: u32,
    /// Pointer to start of index, or 0
    pub index_start: u64,
    // The list of all sorts. The number of sorts is
    // limited to 128 because of the data layout.
    // So don't monomorphize too much.
    pub sort_data_start: u32,
}

impl std::default::Default for Header {
    fn default() -> Header {
        Header {
            magic: 0,
            version: 0,
            num_sorts: 0,
            reserved: 0,
            num_terms: 0,
            num_thms: 0,
            terms_start: 0,
            thms_start: 0,
            proof_stream_start: 0,
            reserved2: 0,
            index_start: 0,
            sort_data_start: 0
        }
    }
}

pub fn parse_header(mmb: &[u8]) -> Res<Header> {
    let (magic, source) = parse_u32(mmb)?;
    assert_eq!(magic, MM0B_MAGIC);
    let (version, source) = parse_u8(source)?;
    let (num_sorts, source) = parse_u8(source)?;
    let (reserved, source) = parse_u16(source)?;
    let (num_terms, source) = parse_u32(source)?;
    let (num_thms, source) = parse_u32(source)?;
    let (terms_start, source) = parse_u32(source)?;
    let (thms_start, source) = parse_u32(source)?;
    let (proof_stream_start, source) = parse_u32(source)?;
    let (reserved2, source) = parse_u32(source)?;
    let (index_start, source) = parse_u64(source)?;
    let sort_data_start = conv_err!(u32::try_from(mmb.len() - source.len()))?;
    Ok(Header {
        magic,
        version,
        num_sorts,
        reserved,
        num_terms,
        num_thms,
        terms_start,
        thms_start,
        proof_stream_start,
        reserved2,
        index_start,
        sort_data_start
    })
}

pub struct MmbMem<'a> {
    pub outline: &'a Outline<'a>,
    pub mmb_items: FxIndexSet<MmbItem<'a>>,
    pub mmb_lists: FxIndexSet<MmbList<'a>>,

    // Cleared between each declaration as the borrowing struct gets dropped
    pub stack: Vec<MmbItem<'a>>,
    pub heap: Vec<MmbItem<'a>>,
    pub ustack: Vec<MmbItem<'a>>,
    pub uheap: Vec<MmbItem<'a>>,
    pub hstack: Vec<MmbItem<'a>>,     
}

impl<'a> MmbMem<'a> {
    pub fn new_from(outline: &'a Outline<'a>) -> Res<Self> {
        let mut mmb_lists = FxIndexSet::with_hasher(Default::default());
        mmb_lists.insert(Nil);

        Ok(MmbMem {
            outline,
            mmb_items: FxIndexSet::with_hasher(Default::default()),
            mmb_lists,
       
            stack: Vec::new(),
            heap: Vec::new(),
            uheap: Vec::new(),
            ustack: Vec::new(),
            hstack: Vec::new(),
        })
    }    

    pub fn verify1(&mut self, stmt: StmtCmd, proof: ProofIter<'a>) -> Res<()> {
        match stmt {
            StmtCmd::Sort {..} => { 
                if !proof.is_null() {
                    return Err(VerifErr::Msg(format!("mmb sorts must have null proof iterators")));
                }
            },
            StmtCmd::TermDef { num, .. } => {
                let term = self.outline.get_term_by_num(num.unwrap())?;
                if !term.is_def() && !proof.is_null() {
                    return Err(VerifErr::Msg(format!("mmb terms must have null proof iterators")));
                }
                MmbState::from(&mut *self).verify_termdef(stmt, term, proof)?;
            }
            StmtCmd::Axiom { num } | StmtCmd::Thm { num, .. } => {
                let assert = self.outline.get_assert_by_num(num.unwrap())?;
                MmbState::from(&mut *self).verify_assert(stmt, assert, proof)?;
            }            
        }
        Ok(self.outline.add_declar(stmt))
    }
}

//#[derive(Debug)]
pub struct MmbState<'b, 'a: 'b> {
    pub mem: &'b mut MmbMem<'a>,
    pub next_bv: u64    
}

impl<'b, 'a: 'b> std::ops::Drop for MmbState<'b, 'a> {
    fn drop(&mut self) {
        self.mem.stack.clear();
        self.mem.heap.clear();
        self.mem.ustack.clear();
        self.mem.uheap.clear();
        self.mem.hstack.clear();        
    }
}

impl<'b, 'a: 'b> From<&'b mut MmbMem<'a>> for MmbState<'b, 'a> {
    fn from(mem: &'b mut MmbMem<'a>) -> MmbState<'b, 'a> {
        MmbState {
            mem,
            next_bv: 1u64            
        }
    }
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    pub fn take_next_bv(&mut self) -> u64 {
        let outgoing = self.next_bv;
        // Assert we're under the limit of 55 bound variables.
        assert!(outgoing >> 56 == 0);
        self.next_bv *= 2;
        outgoing
    }    
}

impl<'b, 'a: 'b> MmbState<'b, 'a> {
    fn load_args(&mut self, args: Args<'a>, stmt: StmtCmd) -> Res<()> {
        make_sure!(self.mem.heap.len() == 0);
        make_sure!(self.next_bv == 1);

        for (idx, arg) in args.enumerate() {
            if arg.is_bound() {
                // b/c we have a bound var, assert the arg's sort is not strict
                make_sure!(self.mem.outline.get_sort_mods(arg.sort() as usize).unwrap().inner & SORT_STRICT == 0);
                // increment the bv counter/checker
                let this_bv = self.take_next_bv();
                // assert that the mmb file has the right/sequential bv idx for this bound var
                make_sure!(arg.bound_digit()? == this_bv);
            } else {
                // assert that this doesn't have any dependencies with a bit pos/idx greater
                // than the number of bvs that have been declared/seen.
                make_sure!(0 == (arg.deps().unwrap() & !(self.next_bv - 1)));
            }

            self.mem.heap.push(MmbItem::Var { idx, ty: arg });
        }
        // For termdefs, pop the last item (which is the return) off the stack.
        if let StmtCmd::TermDef {..} = stmt {
            self.mem.heap.pop();
        }
        Ok(())
    }       

    pub fn verify_termdef(
        &mut self, 
        stmt: StmtCmd,
        term: Term<'a>,
        proof: ProofIter,
    ) -> Res<()> {
        self.load_args(term.args(), stmt)?;
        if term.is_def() {
            self.run_proof(crate::mmb::proof::Mode::Def, proof)?;
            let final_val = none_err!(self.mem.stack.pop())?;
            let ty = final_val.get_ty()?;
            make_sure!(self.mem.stack.is_empty());
            make_sure!(sorts_compatible(ty, term.ret()));
            make_sure!(self.mem.uheap.is_empty());
            for arg in self.mem.heap.iter().take(term.num_args_no_ret() as usize) {
                self.mem.uheap.push(*arg);
            }

            self.run_unify(crate::mmb::unify::UMode::UDef, term.unify(), final_val)?;
        }
        Ok(())
    }

    pub fn verify_assert(
        &mut self, 
        stmt: StmtCmd,
        assert: Assert<'a>,
        proof: ProofIter,
    ) -> Res<()> {
        self.load_args(assert.args(), stmt)?;
        self.run_proof(crate::mmb::proof::Mode::Thm, proof)?;

        let final_val = match (none_err!(self.mem.stack.pop())?, stmt) {
            (MmbItem::Proof(p), StmtCmd::Thm {..}) => p.read(self),
            (owise, StmtCmd::Axiom {..}) => owise,
            owise => return Err(VerifErr::Msg(format!("Expected a proof; got {:?}", owise)))
        };

        make_sure!(self.mem.stack.is_empty());
        make_sure!(self.mem.uheap.is_empty());
        for arg in self.mem.heap.iter().take(assert.args().len()) {
            self.mem.uheap.push(*arg);
        }

        self.run_unify(crate::mmb::unify::UMode::UThmEnd, assert.unify(), final_val)
    }
}


