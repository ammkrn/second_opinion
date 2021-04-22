use std::fmt::{ Debug, Formatter, Result as FmtResult };
use std::sync::atomic::{ AtomicU8, AtomicU32, Ordering::Relaxed };

use mm0b_parser::NumdStmtCmd;
use mm0b_parser::ProofIter;
use mm0b_parser::ParseError;

#[macro_export]
macro_rules! localize {
    ( $e:expr ) => {
        $e.map_err(|e| VerifErr::Local(file!(), line!(), Box::new(e)))
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
macro_rules! io_err {
    ( $r:expr ) => {
        $r.map_err(|e| VerifErr::IoErr(file!(), line!(), e))
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

// These are just so that the reader can see they have their
// respective meaning at the call-site.
pub type SortIdent<'a> = Str<'a>;
pub type TermIdent<'a> = Str<'a>;
pub type AssertIdent<'a> = Str<'a>;

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

pub type Res<A> = Result<A, VerifErr>;

//#[derive(Clone)]
pub enum VerifErr {
    MakeSure(&'static str, u32),
    NoneErr(&'static str, u32),
    ConvErr(&'static str, u32),
    Msg(String),
    // Create a rough backtrace; use the `localize!` macro to make this.
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

/// There's a better name for this, it just hasn't come to me yet.
pub struct Outline<'a> {
    pub file_view: &'a crate::fs::FileView<'a>,
    /// Get the proof stream for the file.
    /// Has the whole mmb file, and the position at which the proof stream starts (taken from the header)
    pub declarations: Vec<(NumdStmtCmd, ProofIter<'a>)>,
    mmb_num_sorts_done: AtomicU8,
    mmb_num_termdefs_done: AtomicU32,
    mmb_num_asserts_done: AtomicU32,
}

impl<'a> Outline<'a> {
    pub fn mmb_num_sorts_done(&self) -> u8 {
        self.mmb_num_sorts_done.load(Relaxed)
    }

    pub fn mmb_num_termdefs_done(&self) -> u32 {
        self.mmb_num_termdefs_done.load(Relaxed)
    }

    pub fn mmb_num_asserts_done(&self) -> u32 {
        self.mmb_num_asserts_done.load(Relaxed)
    }

    pub fn new_from(file_data: &'a crate::fs::FileView<'a>) -> Res<Self> {
        let declars : Result<Vec<(NumdStmtCmd, ProofIter)>, ParseError> = file_data.mmb.proof().collect();
        
        Ok(Outline {
            file_view: file_data,
            declarations: declars.map_err(|e| VerifErr::Msg(format!("{}", e)))?,
            mmb_num_sorts_done: AtomicU8::new(0),
            mmb_num_termdefs_done: AtomicU32::new(0),
            mmb_num_asserts_done: AtomicU32::new(0),
        })
    }    

    pub fn add_declar(&self, stmt: NumdStmtCmd) {
        match stmt {
            NumdStmtCmd::Sort {..} => { self.mmb_num_sorts_done.fetch_add(1, Relaxed); },
            NumdStmtCmd::TermDef {..} => { self.mmb_num_termdefs_done.fetch_add(1, Relaxed); },
            NumdStmtCmd::Axiom {..} | NumdStmtCmd::Thm {..} => { self.mmb_num_asserts_done.fetch_add(1, Relaxed); },
        }        
    }

    pub fn assert_mmz_done(&self, mmz: &crate::mmz::MmzMem<'a>) -> Res<()> {
        if mmz.num_sorts_done().into_inner() != self.file_view.mmb.header.num_sorts {
            return Err(VerifErr::Msg(format!(
                "mmz verified fewer sorts than specified in the header. Verified {}, header specified {}", 
                mmz.num_sorts_done().into_inner(), 
                self.file_view.mmb.header.num_sorts
            )))
        }

        if mmz.num_termdefs_done() != self.file_view.mmb.header.num_terms.get() {
            return Err(VerifErr::Msg(format!(
                "mmz verified fewer terms than specified in the header. Verified {}, header specified {}", 
                mmz.num_termdefs_done(), 
                self.file_view.mmb.header.num_terms.get()
            )))
        }

        if mmz.num_asserts_done() != self.file_view.mmb.header.num_thms.get() {
            return Err(VerifErr::Msg(format!(
                "mmz verified fewer assertions than specified in the header. Verified {}, header specified {}", 
                mmz.num_asserts_done(), 
                self.file_view.mmb.header.num_thms.get()
            )))
        }        
        Ok(())
    }

    pub fn assert_mmb_done(&self) -> Res<()> {
        if self.mmb_num_sorts_done() != self.file_view.mmb.header.num_sorts {
            return Err(VerifErr::Msg(format!(
                "mmb verified fewer sorts than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_sorts_done(), 
                self.file_view.mmb.header.num_sorts
            )))
        } 

        if self.mmb_num_termdefs_done() != self.file_view.mmb.header.num_terms.get() {
            return Err(VerifErr::Msg(format!(
                "mmb verified fewer terms than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_termdefs_done(), 
                self.file_view.mmb.header.num_terms.get()
            )))
        }

        if self.mmb_num_asserts_done() != self.file_view.mmb.header.num_thms.get() {
            return Err(VerifErr::Msg(format!(
                "mmb verified fewer assertions than specified in the header. Verified {}, header specified {}", 
                self.mmb_num_asserts_done(), 
                self.file_view.mmb.header.num_thms.get()
            )))
        }         
        Ok(())
    }
}

///// These are helper functions for rendering unsigned integers
///// as a sequence of bits. For example, `view64(TYPE_SORT_MASK)` renders as:
/////
///// 10000000_11111111_11111111_11111111_11111111_11111111_11111111_11111111
///// 
///// They're not efficient, but they're for debugging and I'm too lazy to write efficient
///// ones right now.
//pub fn view64(n: u64) -> String {
//    let s = format!("{:#066b}", n);  
//    let mut acc = String::new();
//    for (idx, c) in s.chars().skip(2).enumerate() {
//        if idx % 8 == 0 && idx != 0 {
//            acc.push('_');
//        }
//        acc.push(c);
//    }
//    acc
//}

//pub fn view32(n: u32) -> String {
//    let s = format!("{:#034b}", n);  
//    let mut acc = String::new();
//    for (idx, c) in s.chars().skip(2).enumerate() {
//        if idx % 8 == 0 && idx != 0 {
//            acc.push('_');
//        }
//        acc.push(c);
//    }
//    acc
//}

//pub fn view16(n: u16) -> String {
//    let s = format!("{:#018b}", n);  
//    let mut acc = String::new();
//    for (idx, c) in s.chars().skip(2).enumerate() {
//        if idx % 8 == 0 && idx != 0 {
//            acc.push('_');
//        }
//        acc.push(c);
//    }
//    acc
//}

//pub fn view8(n: u8) -> String {
//    let s = format!("{:#010b}", n);  
//    let mut acc = String::new();
//    for (idx, c) in s.chars().skip(2).enumerate() {
//        if idx % 8 == 0 && idx != 0 {
//            acc.push('_');
//        }
//        acc.push(c);
//    }
//    acc
//}
