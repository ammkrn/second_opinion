use std::fmt::{ Debug, Formatter, Result as FmtResult };
use crate::mmb::Header;
use crate::util::{
    parse_u8,
    parse_u32,
    parse_u64,
    Res,
    VerifErr
};
use crate::none_err;

/// A parsed `MMB` file index.
pub struct Index<'a> {
    /// The full file
    pub mmb: &'a [u8],
    /// A pointer to the root of the binary search tree, for searching based on name.
    pub root: u64,
    /// Pointers to the index entries for the sorts
    pub sorts: Vec<u64>,
    /// Pointers to the index entries for the terms
    // The u64 you get back is to an `indexentry`.
    pub terms: Vec<u64>,
    /// Pointers to the index entries for the theorems
    pub thms: Vec<u64>,
}

impl<'a> Debug for Index<'a> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        let mut d = f.debug_struct("Index");
        d.field("root", &self.root);
        d.field("sorts", &self.sorts);
        d.field("terms", &self.terms);
        d.field("thms", &self.thms);
        d.finish()
    }
}

impl<'a> std::default::Default for Index<'a> {
    fn default() -> Index<'a> {
        Index {
            mmb: b"",
            root: 0,
            sorts: Vec::new(),
            terms: Vec::new(),
            thms: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IndexEntry<'a> {
    // pointer to left subchild (for binary searching by strings)
    pub left: u64,
    // pointer to right subchild
    pub right: u64,
    // For locating in the source file
    pub row: u32,
    // For locating in the source file
    pub col: u32,
    // pointer to the command that declares this item
    pub proof: u64,
    // Index of the object in the relevant table
    pub ix: u32,
    // sort, term, thm, var
    pub kind: u8,
    // zero-terminated char* buffer
    pub charbuff: &'a [u8],
}

use crate::Outline;
impl<'a> Outline<'a> {
    #[inline]
    pub fn term_index_entry(&self, term_num: u32) -> Option<IndexEntry<'a>> {
        let entry = *&self.index.terms[term_num as usize];
        self.index_entry(entry as usize)
    }

    #[inline]
    pub fn assert_index_entry(&self, assert_num: u32) -> Option<IndexEntry<'a>> {
        let entry = *&self.index.thms[assert_num as usize];
        self.index_entry(entry as usize)
    }

    #[inline]
    pub fn index_entry(&self, start_at: usize) -> Option<IndexEntry<'a>> {
        let (left, rest) = parse_u64(&self.mmb()[start_at..]).unwrap();
        let (right, rest) = parse_u64(rest).unwrap();
        let (row, rest) = parse_u32(rest).unwrap();
        let (col, rest) = parse_u32(rest).unwrap();
        let (proof, rest) = parse_u64(rest).unwrap();
        let (ix, rest) = parse_u32(rest).unwrap();
        let (kind, rest) = parse_u8(rest).unwrap();
        let charbuff = parse_cstr(rest)?;
        Some(IndexEntry {
            left,
            right,
            row,
            col,
            proof,
            ix,
            kind,
            charbuff,
        })
    }
}

fn parse_cstr<'a>(source: &'a [u8]) -> Option<&'a [u8]> {
    let null = source.iter().position(|c| *c == 0)?;
    let (s, _) = source.split_at(null);
    Some(s)
}

pub fn parse_index<'a>(mmb: &'a [u8], header: Header) -> Res<Index<'a>> {
    let (root, rest) = parse_u64(&mmb[header.index_start as usize..])
        .expect("Failed to get u64 for index root");
    let (sorts, rest) = prefix_u64(rest, header.num_sorts as usize)
        .expect("Failed to get sorts in index");
    let (terms, rest) = prefix_u64(rest, header.num_terms as usize)
        .expect("Failed to get num terms");
    let (thms, _) = prefix_u64(rest, header.num_thms as usize)
        .expect("Failed to get num thms in index");
    Ok(Index {
        mmb,
        root,
        sorts,
        terms,
        thms,
    })
}

#[inline]
pub fn prefix_u64(mut bytes: &[u8], num_elems: usize) -> Res<(Vec<u64>, &[u8])> {
    let split_point = none_err!{ std::mem::size_of::<u64>().checked_mul(num_elems) }?;

    if split_point <= bytes.len() {
        let mut v = Vec::with_capacity(num_elems);
        for _ in 0..num_elems {
            let (inner, rest_) = parse_u64(bytes)?;
            bytes = rest_;
            v.push(inner);
        }
        Ok((v, bytes))
    } else {
        Err(VerifErr::Msg(format!("Bad prefix arg")))
    }
}

