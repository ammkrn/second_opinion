
/// `STMT_AXIOM = 0x02`, starts an `axiom` declaration
pub const STMT_AXIOM: u8 = 0x02;
/// `STMT_SORT = 0x04`, starts a `sort` declaration
pub const STMT_SORT: u8 = 0x04;
// `STMT_TERM = 0x05`, starts a `term` declaration
//pub const STMT_TERM: u8 = 0x05;
/// `STMT_DEF = 0x05`, starts a `def` declaration. (This is the same as
/// `STMT_TERM` because the actual indication of whether this is a
/// def is in the term header)
pub const STMT_DEF: u8 = 0x05;
/// `STMT_THM = 0x06`, starts a `theorem` declaration
pub const STMT_THM: u8 = 0x06;
/// `STMT_LOCAL = 0x08`, starts a `local` declaration
/// (a bit mask to be combined with `STMT_THM` or `STMT_DEF`)
pub const STMT_LOCAL: u8 = 0x08;
/// `STMT_LOCAL_DEF = 0x0D`
pub const STMT_LOCAL_DEF: u8 = STMT_LOCAL | STMT_DEF;
/// `STMT_LOCAL_THM = 0x0E`
pub const STMT_LOCAL_THM: u8 = STMT_LOCAL | STMT_THM;


/// The main part of the proof consists of a sequence of declarations,
/// and these commands denote the different kind of declaration that can
/// be introduced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StmtCmd {
    /// A new sort. Equivalent to `sort foo;`. This is followed by no data,
    /// as the sort data is stored in the header.
    Sort { num: Option<u8> },
    /// A new axiom. Equivalent to `axiom foo ...`. This is followed by a proof
    /// sequence, that should unify with the unify sequence in the header.
    Axiom { num: Option<u32> },
    /// A new term or def. Equivalent to `term/def foo ...`.
    /// If `local` is true, then this is `local def foo`. This is followed by
    /// no data, as the header contains the unify sequence and can be checked on its own.
    TermDef { num: Option<u32>, local: bool },
    /// A new theorem. Equivalent to `(pub) theorem foo ...`, where `local` means
    /// that the theorem is not `pub`. This is followed by a proof sequence,
    /// that will construct the statement and proof, and should unify
    /// with the unify sequence in the header.
    Thm { num: Option<u32>, local: bool },
}

impl StmtCmd {
    pub fn is_local(self) -> bool {
        match self {
            | StmtCmd::TermDef { local: true, .. } 
            | StmtCmd::Thm { local: true, .. } => true,
            _ => false
        }
    }
}

impl std::convert::TryFrom<u8> for StmtCmd {
    type Error = ();
    fn try_from(cmd: u8) -> Result<Self, ()> {
        Ok(match cmd {
            STMT_SORT => StmtCmd::Sort { num: None },
            STMT_AXIOM => StmtCmd::Axiom { num: None },
            STMT_DEF => StmtCmd::TermDef { num: None, local: false },
            STMT_LOCAL_DEF => StmtCmd::TermDef { num: None, local: true },
            STMT_THM => StmtCmd::Thm { num: None, local: false },
            STMT_LOCAL_THM => StmtCmd::Thm { num: None, local: true },
            _ => return Err(()),
        })
    }
}

