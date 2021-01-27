//! Because we're using indirected data structures and rust doesn't support formatters with extra arguments, we need to make a new
//! temporary struct and implement formatting methods on that. 

use std::fmt::{ Debug, Formatter, Result as FmtResult };
use crate::util::Type;
use crate::mmz::{ MmzState, MathStr, MathStrPtr, MmzPtr, MmzList, MmzListPtr, MathStr::*, MmzItem };


pub struct Fmtr<S, A> {
    elem: A,
    state: S,
}

pub fn fmtr<S, A>(elem: A, state: S) -> Fmtr<S, A> {
    Fmtr {
        elem,
        state,
    }
}

impl<'b, 'a: 'b, S: Copy, A> Fmtr<S, A> {
    fn with<B>(&self, elem: B) -> Fmtr<S, B> {
        Fmtr {
            elem,
            state: self.state,
        }
    }
}

impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MathStrPtr<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.with(self.elem.read(self.state)).fmt(f)
    }
}

/// The debug implementation for Fmtr<MathStr> produces a comma-separated list
/// of the tokenized output given the current set of delimiters known to `State`.
impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MathStr<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self.elem {
            Empty => write!(f, ""),
            Cont(prefix, suffix) => {
                self.with(prefix).fmt(f)?;
                write!(f, "{:?}", suffix)
            }
        }
    }
}

impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MmzPtr<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.with(self.elem.read(self.state)).fmt(f)
    }
}

impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MmzItem<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self.elem {
            MmzItem::Var { pos, ty, is_dummy } => {
                let mut d = f.debug_struct("Var");
                d.field("pos", &pos);
                d.field("ty", &ty);
                d.field("is_dummy", &is_dummy);
                d.finish()
            },
            MmzItem::App { term_num, num_args, args } => {
                let mut d = f.debug_struct("App");
                d.field("term_num", &term_num);
                d.field("num_args", &num_args);
                d.field("args", &self.with(args));
                d.finish()
            }
        }
    }
}

impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MmzListPtr<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.with(self.elem.read(self.state)).fmt(f)
    }
}

impl<'b, 'a: 'b> Debug for Fmtr<&MmzState<'b, 'a>, MmzList<'a>> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let mut cursor = self.elem;
        let mut d = f.debug_list();
        while let MmzList::Cons(hd, tl) = cursor {
            d.entry(&self.with(hd.read(self.state)));
            cursor = tl.read(self.state);
        }
        d.finish()        
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
