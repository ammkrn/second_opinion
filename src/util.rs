use std::convert::{ TryFrom, TryInto };
use std::marker::PhantomData;
use std::fmt::{ Debug, Formatter, Result as FmtResult };
use std::sync::atomic::{ AtomicU8, AtomicU32, Ordering::Relaxed };

use crate::mmb::unify::UnifyIter;
use crate::mmb::proof::ProofIter;
use crate::mmb::stmt::StmtCmd;


/// 10000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
const TYPE_SORT_MASK: u64 = (1 << 63) | ((1 << 56) - 1);


#[macro_export]
macro_rules! localize {
    ( $e:expr ) => {
        $e.map_err(|e| VerifErr::Local(file!(), line!(), Box::new(e)))
    }
}

#[macro_export]
macro_rules! io_err {
    ( $e:expr ) => {
        $e.map_err(|e| VerifErr::IoErr(file!(), line!(), Box::new(e)))
    }
}

#[macro_export]
macro_rules! none_err {
    ( $e:expr ) => {
        $e.ok_or(VerifErr::NoneErr(file!(), line!()))
    }
}

#[macro_export]
macro_rules! conv_err {
    ( $e:expr ) => {
        $e.map_err(|_| VerifErr::ConvErr(file!(), line!()))
    }
}

#[macro_export]
macro_rules! make_sure {
    ( $e:expr ) => {
        if !($e) {
            return Err(VerifErr::MakeSure(file!(), line!()))
        }
    }
}

macro_rules! bin_parser {
    ( $(($name: ident, $t:ident))* ) => {
        $(
            pub fn $name(source: &[u8]) -> Res<($t, &[u8])> {
                let int_bytes =
                    source
                    .get(0..std::mem::size_of::<$t>())
                    .ok_or_else(|| {
                        VerifErr::Msg(format!("binary parser ran out of input @ {}: {}", file!(), line!()))
                    })?;

                let new_pos = std::mem::size_of::<$t>();
                Ok(
                    ($t::from_le_bytes(int_bytes.try_into().unwrap()), &source[new_pos..])
                )
            }
        )*
    };
}

bin_parser! {
    (parse_u8,  u8)
    (parse_u16, u16)
    (parse_u32, u32)
    (parse_u64, u64)
}

macro_rules! bitwise_inner {
    ( $($t:ident),* ) => {
        $(
            impl std::ops::BitAnd<$t> for $t {
                type Output = Self;
                fn bitand(self, rhs: Self) -> Self::Output {
                    $t { inner: self.inner & rhs.inner }
                }
            }

            impl std::ops::BitAndAssign<$t> for $t {
                fn bitand_assign(&mut self, other: Self) {
                    self.inner &= other.inner
                }
            }

            impl std::ops::BitOr<$t> for $t {
                type Output = Self;
                fn bitor(self, rhs: Self) -> Self::Output {
                    $t { inner: self.inner | rhs.inner }
                }
            }

            impl std::ops::BitOrAssign<$t> for $t {
                fn bitor_assign(&mut self, other: Self) {
                    self.inner |= other.inner
                }
            }

            impl std::ops::Not for $t {
                type Output = $t;
                fn not(self) -> Self::Output {
                    $t { inner: !self.inner }
                }
            }
        )*
    }
}

bitwise_inner!(Type, Mods);


// These are just so that the reader can see they have their
// respective meaning at the call-site.
pub type SortNum = u8;
pub type TermNum = u32;
pub type AssertNum = u32;
pub type SortIdent<'a> = Str<'a>;
pub type TermIdent<'a> = Str<'a>;
pub type AssertIdent<'a> = Str<'a>;


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ptr<'a, A>(pub u32, pub PhantomData<&'a A>);


#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Str<'a>(pub &'a [u8]);

impl<'b, 'a: 'b> Str<'a> {
    pub fn as_bytes(&self) -> &'a [u8] {
        self.0
    }
}

impl<'a> Debug for Str<'a> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        for byte in self.0.iter() {
            write!(f, "{}", *byte as char)?;
        }
        Ok(())
    }
}



#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Either<A, B> {
    L(A),
    R(B),
}

pub type Arg = Type;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type {
    pub inner: u64
}

impl std::default::Default for Type {
    fn default() -> Self {
        Type { inner: 0 }
    }
}

impl Type {
    pub fn high_bit(self) -> Self {
        Type { inner: self.inner & (!crate::mmb::TYPE_DEPS_MASK) }
    }

    pub fn disjoint(self, other: Self) -> bool {
        (self.inner & other.inner) == 0
    }

    pub fn new_bound() -> Self {
        Type { inner: 1 << 63 }
    }
    
    pub fn new(bound: bool) -> Self {
        if bound {
            Type { inner: 1 << 63 }
        } else {
            Type { inner: 0 }
        }
    }

    pub fn new_with_sort(sort_num: u8) -> Self {
        Type { inner: (sort_num as u64) << 56 }
    }

    #[inline]
    pub fn is_bound(self) -> bool {
        self.inner & (1 << 63) != 0
    }
    
    pub fn add_sort(&mut self, sort_id: u8) {
        // clear existing sort if any;
        self.inner &= TYPE_SORT_MASK;
        // Add new sort
        self.inner |= ((sort_id as u64) << 56);
    }


    /// Add a dependency on bv_idx
    pub fn add_dep(&mut self, bv_idx: u64) {
        self.inner |= 1 << bv_idx.checked_sub(1).expect("No 0th bv to depend on")
    }

    pub fn sort(self) -> u8 {
        u8::try_from((self.inner >> 56) & 0x7F).unwrap()
    }

    pub fn depends_on_(self, j: u64) -> bool {
        self.inner & (1u64 << j.checked_sub(1).expect("No 0th to depend on")) != 0
    }

    /// If this is the type of a bound variable, return a u64 
    /// whose only activated bit is the bit indicating which bv
    /// it is.
    pub fn bound_digit(self) -> Res<u64> {
        if self.is_bound() {
            Ok(self.inner & !(0xFF << 56))
        } else {
            Err(VerifErr::Msg(format!("Not bound")))
        }
    }

    /// The POSITION (1 - 55) of this bound variable, NOT the literal u64.
    pub fn bound_pos(self) -> Res<u64> {
        if self.is_bound() {
            for i in 0..56 {
                if ((1 << i) & self.inner) != 0 {
                    return Ok(i + 1)
                }
            }
            Err(VerifErr::Msg(format!("should be unreachable")))
        } else {
            Err(VerifErr::Msg(format!("Not bound")))
        }
    }

    pub fn has_deps(self) -> bool {
        if self.is_bound() {
            false
        } else {
            (self.inner & crate::mmb::TYPE_DEPS_MASK) > 0
        }
    }

    /// If this is a regular/not-bound variable, return a u64
    /// whose only activated bits are the ones marking the bvs
    /// on which it depends.
    pub fn deps(self) -> Res<u64> {
        if !self.is_bound() {
            Ok(self.inner & !(0xFF << 56))
        } else {
            Err(VerifErr::Msg(format!("No deps")))
        }
    }
}

#[test]
fn bound1() {
    let mut t1 = Type::new_bound();
    t1 |= Type { inner: (1 << 15) };
    assert_eq!(t1.bound_pos().unwrap(), 16);
}

#[test]
fn bound2() {
    let mut t1 = Type::new_bound();
    t1 |= Type { inner: (1 << 0) };
    assert_eq!(t1.bound_pos().unwrap(), 1);
}

#[test]
fn bound3() {
    let mut t1 = Type::new_bound();
    t1 |= Type { inner: (1 << 55) };
    assert_eq!(t1.bound_pos().unwrap(), 56);
}

#[test]
fn bound_err1() {
    let t1 = Type::new_bound();
    assert!(t1.bound_pos().is_err())
}

#[test]
fn bound_err2() {
    let t1 = Type::new(false);
    assert!(t1.bound_pos().is_err())
}

#[test]
fn deps1() {
    let t0 = Type { inner: 0 };
    let mut t1_v = Type { inner: 0 };
    let mut t1 = Type { inner: 0 };
    let t2 = Type { inner: 1 };
    let t3 = Type::new_bound();

    assert!(!t0.has_deps());
    assert!(!t1.has_deps());
    assert!(t2.has_deps());
    assert!(!t3.has_deps());

    assert_eq!(t2.deps().unwrap(), 1);
    t1.add_dep(1);
    t1.add_dep(2);
    t1.add_dep(4);
    assert!(t1.has_deps());
    assert_eq!(t1.deps().unwrap(), 11);

    t1_v.add_dep(4);
    t1_v.add_dep(1);
    t1_v.add_dep(2);
    assert!(t1_v.has_deps());
    assert_eq!(t1_v.deps().unwrap(), 11);
    println!("t3: {:?}", t3);
    let bound_1 = Type { inner: Type::new_bound().inner | (1 << 8) };
    println!("bound idx: {:?}", bound_1.bound_digit());
    assert!(bound_1.is_bound());
}


pub type Res<A> = Result<A, VerifErr>;

//#[derive(Clone)]
pub enum VerifErr {
    MakeSure(&'static str, u32),
    NoneErr(&'static str, u32),
    ConvErr(&'static str, u32),
    Msg(String),
    // Crate a rough backtrace; use the `localize!` macro to make this.
    Local(&'static str, u32, Box<VerifErr>),
    Unreachable(&'static str, u32),
    IoErr(&'static str, u32, std::io::Error)
}

impl Debug for VerifErr {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            VerifErr::Msg(s) => {
                let mut d = f.debug_struct("VerifErr::Msg");
                d.field("Msg", &format_args!("{}", s));
                d.finish()
            },
            VerifErr::Local(fi, l, e) => {
                let mut d = f.debug_struct("VerifErr::Local");
                d.field("file", &fi);
                d.field("line", &l);
                d.field("Msg", &e);
                d.finish()
            },
            VerifErr::MakeSure(fi, l) => {
                let mut d = f.debug_struct("VerifErr::MakeSure");
                d.field("file", &fi);
                d.field("line", &l);
                d.finish()
            },
            VerifErr::ConvErr(fi, l) => {
                let mut d = f.debug_struct("VerifErr::ConvErr");
                d.field("file", &fi);
                d.field("line", &l);
                d.finish()
            },
            VerifErr::Unreachable(fi, l) => {
                let mut d = f.debug_struct("VerifErr::Unreachable");
                d.field("file", &fi);
                d.field("line", &l);
                d.finish()
            },
            VerifErr::IoErr(fi, l, e) => {
                let mut d = f.debug_struct("VerifErr::IoErr");
                d.field("file", &fi);
                d.field("line", &l);
                d.field("err", &format_args!("{}", e));
                d.finish()
            },
            VerifErr::NoneErr(fi, l) => {
                let mut d = f.debug_struct("VerifErr::NoneErr");
                d.field("file", &fi);
                d.field("line", &l);
                d.finish()
            },
        }
    }
}

 /// A reference to an entry in the term table.
#[derive(Debug, Clone, Copy)]
pub struct Term<'a> {
    /// The sort of the term.
    pub term_num: u32,
    pub sort: u8,
    /// Number of args NOT including `ret`
    pub args_start: &'a [u8],
    // The pointer to the start of the unify stream.
    pub unify: UnifyIter<'a>,
}

/// An iterator over the arguments of a term/assertion that doesn't require allocation
/// of a vector, instead reading them from the source file each time.
#[derive(Debug, Clone, Copy)]
pub struct Args<'a> {
    source: &'a [u8],
}

impl<'a> DoubleEndedIterator for Args<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.source.is_empty() {
            None
        } else {
            let split = self.source.len().checked_sub(8)?;
            let (lhs, rhs) = self.source.split_at(split);
            self.source = lhs;
            match parse_u64(rhs) {
                Err(_) => unreachable!("Should have been guaranteed by check in `prefix_args`"),
                Ok((parsed, rest)) => {
                    assert!(rest.is_empty());
                    Some(Type { inner: parsed })
                }
            }
        }
    }
}


impl<'a> ExactSizeIterator for Args<'a> {
    fn len(&self) -> usize {
        self.source.len() / std::mem::size_of::<u64>()
    }
}

impl<'a> Iterator for Args<'a> {
    type Item = Arg;
    fn next(&mut self) -> Option<Self::Item> {
        if self.source.is_empty() {
            return None
        }
        match parse_u64(self.source) {
            Err(_) => unreachable!("Should have been guaranteed by check in `prefix_args`"),
            Ok((parsed, rest)) => {
                self.source = rest;
                Some(Type { inner: parsed })
            }
        }
    }

    // Needed for `len` to work correctly.
    fn size_hint(&self) -> (usize, Option<usize>) {
        (
            self.source.len() / std::mem::size_of::<u64>(),
            Some(self.source.len() / std::mem::size_of::<u64>())
        )
    }
}


#[test]
fn args_back1() {
    let s1 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32, 33
    ];
    let s2 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25,
    ];
    let s3 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
    ];
    let tgt1 = [26, 27, 28, 29, 30, 31, 32, 33];
    let tgt2 = [18, 19, 20, 21, 22, 23, 24, 25];
    let tgt3 = [10, 11, 12, 13, 14, 15, 16, 17];

    let mut args = Args { source: s1 };
    let back = args.next_back().unwrap();
    assert_eq!(back.inner, u64::from_le_bytes(tgt1));
    assert_eq!(args.source, s2);
    let back = args.next_back().unwrap();
    assert_eq!(back.inner, u64::from_le_bytes(tgt2));
    assert_eq!(args.source, s3);
    let back = args.next_back().unwrap();
    assert_eq!(back.inner, u64::from_le_bytes(tgt3));
    assert!(args.source.is_empty());
}


#[test]
fn args_back_err1() {
    let s1 = &[10, 11, 12, 13, 14, 15, 16];
    let mut args = Args { source: s1 };
    let back = args.next_back();
    assert!(back.is_none());
}

#[test]
fn args_no_ret1() {
    let fake_unify = UnifyIter { buf: &[], pos: 0 };
    let s1 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32, 33
    ];
    let t = Term { term_num: 0, sort: 0, args_start: s1, unify: fake_unify };
    let s2 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25,
    ];

    let args_no_ret = t.args_no_ret();
    assert_eq!(args_no_ret.source, s2);
}

#[test]
fn args_no_ret2() {
    let fake_unify = UnifyIter { buf: &[], pos: 0 };
    let s1 = &[
        10, 11, 12, 13, 14, 15, 16, 17,
    ];
    let t = Term { term_num: 0, sort: 0, args_start: s1, unify: fake_unify };

    let args_no_ret = t.args_no_ret();
    assert_eq!(args_no_ret.source, &[]);
}

impl<'a> Term<'a> {

    /// Returns true if this is a `def`, false for a `term`.
    #[inline]
    pub fn is_def(&self) -> bool {
        self.sort & 0x80 != 0
    }
    /// The return sort of this term/def.
    #[inline]
    pub fn sort(&self) -> SortNum {
        self.sort & 0x7F
    }

    /// args; including the `ret` element at the end.
    #[inline]
    pub fn args(&self) -> Args<'a> {
        Args {
            source: self.args_start,
        }
    }

    /// args without the `ret` element at the end.
    /// This will panic if there are less than 8 bytes in `source`,
    /// which seems fine for now, since that would mean we had an invalid `Args` 
    /// to start with.
    #[inline]
    pub fn args_no_ret(&self) -> Args<'a> {
        Args {
            source: &self.args_start[..(self.args_start.len() - std::mem::size_of::<u64>())],
        }
    }    

    pub fn num_args_no_ret(&self) -> u16 {
        u16::try_from(self.args().len().checked_sub(1).unwrap()).unwrap()
    }

    /// The return sort and dependencies.
    pub fn ret(&self) -> Type {
        self.args().last().unwrap()
    }

    /// The beginning of the unify stream for the term.
    #[inline]
    pub fn unify(&self) -> UnifyIter<'_> {
        self.unify.clone()
    }
}

/// A reference to an entry in the theorem table.
#[derive(Debug, Clone, Copy)]
pub struct Assert<'a> {
    /// The array of arguments.
    // `Arg` is a u64
    pub assert_num: u32,
    pub args_start: &'a [u8],
    /// The pointer to the start of the unify stream.
    pub unify: UnifyIter<'a>,
}

impl<'a> Assert<'a> {
    /// The list of arguments of this axiom/theorem.
    #[inline]
    pub fn args(&self) -> Args<'a> {
        Args {
            source: self.args_start,
        }
    }

    /// The beginning of the unify stream.
    #[inline]
    pub fn unify(&self) -> UnifyIter<'a> {
        self.unify.clone()
    }

    pub fn num_args(&self) -> u16 {
        u16::try_from(self.args().len()).unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Mods {
    pub inner: u8,
}

#[test]
fn test_mods1() {
    let m = Mods { inner: 1 };
    assert!(!m.is_provable());
    let m = Mods { inner: 2 };
    assert!(!m.is_provable());
    let m = Mods { inner: 4 };
    assert!(m.is_provable());
    let m = Mods { inner: 8 };
    assert!(!m.is_provable());
    let m = Mods { inner: 3 };
    assert!(!m.is_provable());
    let m = Mods { inner: 12 };
    assert!(m.is_provable());
    let m = Mods { inner: 7 };
    assert!(m.is_provable());
}

impl Mods {
    pub fn new() -> Self {
        Mods { inner: 0u8 }
    }

    pub fn is_provable(self) -> bool {
        (self.inner & Mods::provable().inner) != 0
    }

    pub fn pure() -> Self {
        Mods { inner: 1 }
    }
    
    pub fn strict() -> Self {
        Mods { inner: 2 }
    }

    pub fn provable() -> Self {
        Mods { inner: 4 }
    }

    pub fn free() -> Self {
        Mods { inner: 8 }
    }
}

/// An iterator over the declaration stream. This is the main provider of 
/// verification obligations for mmb items, giving you both the target (for example,
/// `public term, number 13`) as well as the proof stream. The unification stream
/// Is later looked up using the item number when it's needed.
#[derive(Debug, Clone)]
pub struct DeclIter<'a> {
    /// The full source file.
    pub mmb: &'a [u8],
    /// The index of the current declaration in the file.
    /// Starts at `proof_stream_start` from the header file.
    pub pos: usize,
    pub next_sort_num: u8,
    pub next_termdef_num: u32,
    pub next_assert_num: u32,
}

/// We pair the item number (sortnum, termnum, assertnum) with the statement
/// So that during parallel checking of mmb declarations, we know which item is
/// which, since they may be checked out of order.
impl<'a> Iterator for DeclIter<'a> {
    type Item = Result<(StmtCmd, ProofIter<'a>), VerifErr>;
    fn next(&mut self) -> Option<Self::Item> {
        match try_next_decl(self.mmb, self.pos)? {
            Err(e) => Some(Err(e)),
            Ok((stmt, pr, rest)) => {
                let stmt = match stmt {
                    StmtCmd::Sort {..} => {
                        let num = self.next_sort_num;
                        self.next_sort_num += 1;
                        StmtCmd::Sort { num: Some(num) }
                    }
                    StmtCmd::TermDef {local, ..} => {
                        let num = self.next_termdef_num;
                        self.next_termdef_num += 1;
                        StmtCmd::TermDef { num: Some(num), local }
                    }
                    StmtCmd::Axiom {..} => {
                        let num = self.next_assert_num;
                        self.next_assert_num += 1;
                        StmtCmd::Axiom { num: Some(num) }
                    }
                    StmtCmd::Thm {local, ..} => {
                        let num = self.next_assert_num;
                        self.next_assert_num += 1;
                        StmtCmd::Thm { num: Some(num), local }
                    }
                };
                self.pos = rest;
                Some(Ok((stmt, pr)))
            }
        }
    }
}

/// is only used for `DeclIter::next`.
/// This always gets the full mmb file
fn try_next_decl(mmb: &[u8], pos: usize) -> Option<Res<(StmtCmd, ProofIter<'_>, usize)>> {
    let (cmd, data, rest) = match try_next_cmd(mmb, pos) {
        // Means cmd == 0, but here is unreachable
        Ok(None) => return None,
        // Means there was an error slicing in `try_next_cmd`
        Err(e) => return Some(Err(e)),
        Ok(Some(((cmd, data), rest))) => (cmd, data, rest)
    };

    let next2 = pos + data as usize;


    let pr = ProofIter {
        buf: mmb,
        pos: rest,
        ends_at: pos + (data as usize)
    };
    Some(Ok((
        StmtCmd::try_from(cmd).ok()?,
        pr, 
        next2
    )))
}

// used by proof and unify
// This now always gets the full mmb file.
pub fn try_next_cmd<T>(mmb: &[u8], pos: usize) -> Res<Option<(T, usize)>> 
where T: TryFrom<(u8, u32)> {
    let (cmd, data, new_pos) = parse_cmd(mmb, pos)?;
    if cmd == 0 {
        return Ok(None);
    }

    Ok(Some((
        T::try_from((cmd, data)).map_err(|_| VerifErr::Msg(format!("try_next_cmd failed @ pos {}", pos)))?,
        new_pos
    )))
}




/// Constants used in the MMB specification.
pub mod cmd {
    /// `DATA_8 = 0x40`, used as a command mask for an 8 bit data field
    pub const DATA_8: u8 = 0x40;
    /// `DATA_16 = 0x80`, used as a command mask for a 16 bit data field
    pub const DATA_16: u8 = 0x80;
    /// `DATA_32 = 0xC0`, used as a command mask for a 32 bit data field
    pub const DATA_32: u8 = 0xC0;
    /// `DATA_MASK = 0xC0`, selects one of `DATA_8`, `DATA_16`, or `DATA_32` for data size
    pub const DATA_MASK: u8 = 0xC0;
}

fn parse_cmd(mmb: &[u8], start_at: usize) -> Res<(u8, u32, usize)> {
    match mmb.get(start_at..) {
        None | Some([]) => Err(VerifErr::Msg("Parse cmd exhausted".to_string())),
        Some([n, tl @ ..]) => {
            let cmd_kind = n & !cmd::DATA_MASK;
            let cmd_size = n & cmd::DATA_MASK;
            match cmd_size {
                0 => Ok((cmd_kind, 0, mmb.len() - tl.len())),
                cmd::DATA_8 => {
                    let (data, rest) = parse_u8(tl)?;
                    Ok((cmd_kind, data as u32, mmb.len() - rest.len()))
                }
                cmd::DATA_16 => {
                    let (data, rest) = parse_u16(tl)?;
                    Ok((cmd_kind, data as u32, mmb.len() - rest.len()))
                }
                cmd::DATA_32 => {
                    let (data, rest) = parse_u32(tl)?;
                    Ok((cmd_kind, data, mmb.len() - rest.len()))
                }
                _ => Err(VerifErr::Msg("Parse cmd got unknown size".to_string())),
            }
        }
    }
}


/// There's a better name for this, it just hasn't come to me yet.
pub struct Outline<'a> {
    pub file_data: &'a crate::fs::FileData,
    pub header: crate::mmb::Header,
    pub index: crate::mmb::index::Index<'a>,

    /// Get the proof stream for the file.
    /// Has the whole mmb file, and the position at which the proof stream starts (taken from the header)
    pub declarations: Vec<(StmtCmd, ProofIter<'a>)>,
    mmb_num_sorts_done: AtomicU8,
    mmb_num_termdefs_done: AtomicU32,
    mmb_num_asserts_done: AtomicU32,
}

impl<'a> Outline<'a> {
    pub fn new_from(file_data: &'a crate::fs::FileData) -> Res<Self> {
        let header = crate::mmb::parse_header(file_data.mmb_file.as_slice())?;
        let index  = crate::mmb::index::parse_index(file_data.mmb_file.as_slice(), header)?;
        let declars = DeclIter {
            mmb: file_data.mmb_file.as_slice(),
            pos: header.proof_stream_start as usize,
            next_sort_num: 0,
            next_termdef_num: 0,
            next_assert_num: 0,
        };
        
        let declarations: Vec<(StmtCmd, ProofIter)> = declars.collect::<Result<Vec<(StmtCmd, ProofIter)>, VerifErr>>()?;
        Ok(Outline {
            file_data,
            header,
            index,
            declarations,
            mmb_num_sorts_done: AtomicU8::new(0),
            mmb_num_termdefs_done: AtomicU32::new(0),
            mmb_num_asserts_done: AtomicU32::new(0),
        })
    }    

    pub fn add_declar(&self, stmt: StmtCmd) {
        match stmt {
            StmtCmd::Sort {..} => { self.next_sort(); },
            StmtCmd::TermDef {..} => { self.next_termdef(); },
            StmtCmd::Axiom {..} | StmtCmd::Thm {..} => { self.next_assert(); },
        }        
    }

    pub fn assert_mmz_done(&self, mmz: &crate::mmz::MmzMem<'a>, errs: &mut Vec<VerifErr>) {
        if mmz.num_sorts_done() != self.header.num_sorts {
            errs.push(VerifErr::Msg(format!(
                "mmz verified fewer sorts than specified in the header. Verified {}, header specified {}", 
                mmz.num_sorts_done(), 
                self.header.num_sorts
            )))
        }

        if mmz.num_termdefs_done() != self.header.num_terms {
            errs.push(VerifErr::Msg(format!(
                "mmz verified fewer terms than specified in the header. Verified {}, header specified {}", 
                mmz.num_termdefs_done(), 
                self.header.num_terms
            )))
        }

        if mmz.num_asserts_done() != self.header.num_thms {
            errs.push(VerifErr::Msg(format!(
                "mmz verified fewer assertions than specified in the header. Verified {}, header specified {}", 
                mmz.num_asserts_done(), 
                self.header.num_thms
            )))
        }        
    }

    pub fn assert_mmb_done(&self, errs: &mut Vec<VerifErr>) {
        if self.mmb_num_sorts_done() != self.header.num_sorts {
            errs.push(VerifErr::Msg(format!(
                "mmb verified fewer sorts than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_sorts_done(), 
                self.header.num_sorts
            )))
        }

        if self.mmb_num_termdefs_done() != self.header.num_terms {
            errs.push(VerifErr::Msg(format!(
                "mmb verified fewer terms than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_termdefs_done(), 
                self.header.num_terms
            )))
        }

        if self.mmb_num_asserts_done() != self.header.num_thms {
            errs.push(VerifErr::Msg(format!(
                "mmb verified fewer assertions than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_asserts_done(), 
                self.header.num_thms
            )))
        }         
    }
}

impl<'a> Outline<'a> {
    pub fn mmb(&self) -> &'a [u8] {
        self.file_data.mmb_file.as_slice()
    }

    pub fn mmb_num_sorts_done(&self) -> u8 {
        self.mmb_num_sorts_done.load(Relaxed)
    }

    pub fn mmb_num_termdefs_done(&self) -> u32 {
        self.mmb_num_termdefs_done.load(Relaxed)
    }

    pub fn mmb_num_asserts_done(&self) -> u32 {
        self.mmb_num_asserts_done.load(Relaxed)
    }

    fn next_sort(&self) -> u8 {
        self.mmb_num_sorts_done.fetch_add(1, Relaxed)
    }
    
    fn next_termdef(&self) -> u32 {
        self.mmb_num_termdefs_done.fetch_add(1, Relaxed)
    }

    fn next_assert(&self) -> u32 {
        self.mmb_num_asserts_done.fetch_add(1, Relaxed)
    }

    pub fn get_sort_mods(&self, n: usize) -> Res<Mods> {
        none_err! {
            self
            .mmb()
            .get(self.header.sort_data_start as usize + n)
            .map(|byte| Mods { inner: *byte })
        }
    }    

    /// Get a term (by number) from the mmb file
    pub fn get_term_by_num(&self, term_num: u32) -> Res<Term<'a>> {
        let start_point = (self.header.terms_start as usize) + ((term_num as usize) * 8);
        let source = none_err!(self.mmb().get(start_point..))?;
        let (num_args, source) = parse_u16(source)?;
        let (sort, source) = parse_u8(source)?;
        let (_reserved, source) = parse_u8(source)?;
        let (term_args_start, _) = parse_u32(source)?;

        let args_start = none_err!(self.mmb().get(term_args_start as usize..))?;
        let split_point = none_err!{ std::mem::size_of::<u64>().checked_mul((num_args + 1) as usize) }?;
        let (args_start, unify_start) = args_start.split_at(split_point);

        let unify = UnifyIter {
            buf: self.mmb(),
            pos: self.mmb().len() - unify_start.len(),
        };

        Ok(Term { term_num, sort, args_start, unify })
    }

    /// Get an assertion (by number) from the mmb file
    pub fn get_assert_by_num(&self, assert_num: u32) -> Res<Assert<'a>> {
        let thm_start = (self.header.thms_start + (assert_num * 8)) as usize;
        let source = self.mmb().get(thm_start..).ok_or(VerifErr::Msg(format!("Bad index")))?;
        let (num_args, source) = parse_u16(source)?;
        let (_reserved, source) = parse_u16(source)?;
        let (args_start, _) = parse_u32(source)?;

        let args_slice = none_err!(self.mmb().get(args_start as usize..))?;

        let split_point = none_err! { std::mem::size_of::<u64>().checked_mul(num_args as usize) }?;
        let (args_start, unify_start) = args_slice.split_at(split_point);

        let unify = UnifyIter {
            buf: self.mmb(),
            pos: self.mmb().len() - unify_start.len(),
        };

        Ok(Assert { assert_num, args_start, unify })        
    }      
}

/// These are helper functions for rendering unsigned integers
/// as a sequence of bits. For example, `view64(TYPE_SORT_MASK)` renders as:
///
/// 10000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
/// 
/// They're not efficient, but they're for debugging and I'm too lazy to write efficient
/// ones right now.
pub fn view64(n: u64) -> String {
    let s = format!("{:#066b}", n);  
    let mut acc = String::new();
    for (idx, c) in s.chars().skip(2).enumerate() {
        if idx % 8 == 0 && idx != 0 {
            acc.push('_');
        }
        acc.push(c);
    }
    acc
}

pub fn view32(n: u32) -> String {
    let s = format!("{:#034b}", n);  
    let mut acc = String::new();
    for (idx, c) in s.chars().skip(2).enumerate() {
        if idx % 8 == 0 && idx != 0 {
            acc.push('_');
        }
        acc.push(c);
    }
    acc
}

pub fn view16(n: u16) -> String {
    let s = format!("{:#018b}", n);  
    let mut acc = String::new();
    for (idx, c) in s.chars().skip(2).enumerate() {
        if idx % 8 == 0 && idx != 0 {
            acc.push('_');
        }
        acc.push(c);
    }
    acc
}

pub fn view8(n: u8) -> String {
    let s = format!("{:#010b}", n);  
    let mut acc = String::new();
    for (idx, c) in s.chars().skip(2).enumerate() {
        if idx % 8 == 0 && idx != 0 {
            acc.push('_');
        }
        acc.push(c);
    }
    acc
}

impl Debug for Type {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", view64(self.inner))
    }
}
