use std::convert::TryFrom;
use std::sync::Arc;
use std::collections::HashMap;
use bumpalo::collections::Vec as BumpVec;
use mm0b_parser::NumdStmtCmd;
use crate::mmz::{
    MmzState,
    MmzMem,
    DelimKind, 
    MmzExpr,
    Prec, 
    Fix, 
    NotationInfo, 
    NotationLit, 
    Coe,
    MmzVar,
    MmzHyp,
    Assoc
};
use crate::util::{ 
    Str, 
    Res, 
    VerifErr, 
    Either, 
    Either::*, 
};
use crate::make_sure;
use crate::localize;
use crate::none_err;
use mm0b_parser::{ UnifyCmd, Arg, Type, UnifyIter, TermRef, ThmRef };
use mm0_util::{ SortId, Modifiers };
use crate::mmb::unify::{ UMode };

/// Demand a Prec::Num (err owise);
/// 
/// If true, return (Prec + 1) else Prec
fn bump<'a>(yes: bool, _: Str<'a>, p: Prec) -> Prec {
    if !yes {
        p
    } else if let Prec::Num(num) = p {
        if let Some(i) = num.checked_add(1) {
            Prec::Num(i)
        } else {
            panic!("bump prec out of range")
        }
    } else {
        panic!("infix constants cannot have prec max")
    }
}

pub fn wc(c: u8) -> bool {
    c == b' ' || c == b'\n'
}

/// return true iff a given character is an acceptable ident starter.
pub fn ident_start(c: u8) -> bool {
    (b'a'..=b'z').contains(&c) || (b'A'..=b'Z').contains(&c) || c == b'_'
}

/// return true iff a given character is an acceptable ident character.
pub fn ident_rest(c: u8) -> bool {
    ident_start(c) || (b'0'..=b'9').contains(&c)
}


/// Remove the leading and trailing whitespace from a byte slice.
pub fn trim(mut bytes: &[u8]) -> &[u8] {
    while let [hd, tl @ ..] = bytes {
        if wc(*hd) {
            bytes = tl;
        } else {
            break
        }
    }

    while let [lhs @ .., last] = bytes {
        if wc(*last) {
            bytes = lhs
        } else {
            break
        }
    }
    bytes
}   


impl<'b, 'a: 'b> MmzMem<'a> {
    pub fn cur_slice(&self) -> &'a [u8] {
        self.mmz.get(self.mmz_pos..).unwrap_or_else(|| &[])
    }

    pub fn parse_until(
        &mut self,
        bump: &mut bumpalo::Bump,
        stmt_cmd: NumdStmtCmd, 
        item: Option<Either<TermRef<'a>, ThmRef<'a>>>
    ) -> Res<()> {
        'outer: loop {
            'inner: loop {
                let mut mmz_st = MmzState::new_from(self, bump);
                if mmz_st.cur().is_none() {
                    break 'inner
                }
            
                match { mmz_st.skip_ws(); mmz_st.peek_word() } {
                    b"provable" | b"strict" | b"free" | b"pure" | b"sort" => return mmz_st.parse_sort(),
                    b"term" | b"def" => {
                        if let Some(L(t)) = item {
                            return mmz_st.parse_termdef(t)
                        } else {
                            return Err(VerifErr::Unreachable(file!(), line!()));
                        }
                    }
                    b"axiom" | b"theorem" => {
                        make_sure!(matches!(stmt_cmd, NumdStmtCmd::Axiom {..}) || matches!(stmt_cmd, NumdStmtCmd::Thm {..}));
                        if let Some(R(assert)) = item {
                            return mmz_st.parse_assert(assert)
                        } else {
                            return Err(VerifErr::Unreachable(file!(), line!()));
                        }
                     },
                     b"delimiter" => mmz_st.delims()?,
                     b"prefix" | b"infixl" | b"infixr" => mmz_st.simple_notation()?,
                     b"notation" => mmz_st.gen_notation()?,
                     b"coercion" => mmz_st.coercion()?,
                     b"import" => mmz_st.parse_import()?,
                     b"input" => return Err(VerifErr::Msg(format!("`input` statements are not currently suppprted"))),
                     b"output" => return Err(VerifErr::Msg(format!("`output` statements are not currently supported"))),
                     _ => break 'inner,
                }                
            }

            if let Ok(()) = self.next_mmz_file() {
                continue 'outer
            } else {
                return Err(VerifErr::Msg(
                    format!("`parse_until` ran out of input with remaining verification obligations. Remaining: {:?}", String::from_utf8_lossy(self.cur_slice()))
                ))
            }
        }
    }    
}

impl<'b, 'a: 'b> MmzState<'b, 'a> {
    pub fn skip_ws(&mut self) {
        while !self.is_empty() {
            match self.cur_slice() {
                [b'-', b'-', ..] => {
                    self.advance(2);
                    // skip the rest of the line;
                    while self.cur().map(|c| c != b'\n').unwrap_or(false) {
                        self.advance(1)
                    }
                },
                [hd, ..] if wc(*hd) => self.advance(1),
                _ => break
            }
        }
    }

    pub fn guard(&mut self, c: u8) -> Res<u8> {
        self.skip_ws();
        if self.cur() == Some(c) {
            self.advance(1);
            Ok(c)
        } else {
            Err(VerifErr::Msg(
                format!("guard failed: expected `{}`, got {:?} @ {}", c as char, self.cur(), self.mem.mmz_pos)
            ))
        }
    }

    /// Given an expression `(e: x)` and a target sort `z`, try to coerce an expression `(e: z)`
    pub fn coerce(&mut self, e_x: MmzExpr<'b>, z: SortId) -> Res<MmzExpr<'b>> {
        // If the task is coercion of `(e: z)` to `(e: z)`, just return `e`.
        if e_x.sort() == z { 
            return Ok(e_x)
        }

        // If the coercion `x > z` exists, but `z` is provable, return `(e: x)`
        if let Some(tgt_id) = self.mem.coe_prov.get(&e_x.sort()) {
            if z == *tgt_id {
                return Ok(e_x)
            }
        }

        // Find the existing coercion `x > z`
        let coe = none_err!(self.mem.coes.get(&e_x.sort()).and_then(|m| m.get(&z)).cloned())?;

        match coe {
            // If `my_coe: x > z` is a straight-shot, just return `(my_coe (e: x)) : z`
            Coe::Single { term_num } => {
                Ok(MmzExpr::App { 
                    term_num,
                    num_args: 1,
                    args: self.alloc(bumpalo::vec![in self.bump; e_x]),
                    sort: z
                })
            },

            // If this is a transitive coercion `x > y > z`, return `(y_to_z (x_to_y (e: x)))`k
            Coe::Trans { middleman_sort: y, .. } => {
                self.coerce(e_x, y)
                .and_then(|y_expr| self.coerce(y_expr, z))
            },
        }
    }    

    fn kw(&mut self, k: &[u8]) -> Option<&'a [u8]> {
        let rollback = self.mem.mmz_pos;
        self.skip_ws();
        if self.cur_slice().starts_with(k) {
            let taken_kw = &self.cur_slice()[0..k.len()];
            self.advance(k.len());
            Some(taken_kw)
        } else {
            self.mem.mmz_pos = rollback;
            None
        }
    }

    // Kind of a lot of effort to avoid allocation.
    fn delim_kind(&mut self) -> Res<DelimKind> {
        let rollback = self.mem.mmz_pos;
        self.skip_ws();
        let out = match self.skip_formula() {
            Err(_) => Err(VerifErr::Msg(format!("Bad delim stmt"))),
            Ok(_) => match self.skip_formula() {
                Err(_) => Ok(DelimKind::Both),
                Ok(_) => match self.skip_formula() {
                    Err(_) => Ok(DelimKind::Left),
                    Ok(_) => Err(VerifErr::Msg(format!("too many formulas in delim stmt (3+)"))),
                }
            }
        };
        self.mem.mmz_pos = rollback;
        out
    }

    // Parse, then insert the actual delimiter tokens.
    fn delim_aux(&mut self, kind: DelimKind) -> Res<()> {
        localize!(self.guard(b'$'))?;
        while let Some([c]) = self.math_tok().map(|s| s.as_bytes()) {
            if self.mem.delims.iter().any(|(k, _)| k == c) {
                return Err(VerifErr::Msg(format!("Cannot redeclare delimiter: {}", *c as char)))
            } else {
                self.mem.delims.push((*c, kind))
            }
        }
        if kind == DelimKind::Both|| kind == DelimKind::Right {
            localize!(self.guard(b';'))?;
        }
        Ok(())
    }

    // 1. Find the `delimiter` keyword
    // 2. Determine whether we have a Both or Left/Right kind of delimiter statement
    // 3. Use delim_aux two parse and insert the actual delimiter tokens.
    pub fn delims(&mut self) -> Res<()> {
        self.skip_ws();
        if !self.kw(b"delimiter ").is_some() {
            let _x = String::from_utf8_lossy(self.peek_word());
            return Err(VerifErr::Msg(
                format!("Bad delim stmt; keyword `delimiter` failed. Word is: {}", _x)
            ))
        }

        let kind = self.delim_kind()?;
        self.delim_aux(kind)?;
        if kind == DelimKind::Left {
            self.delim_aux(DelimKind::Right)?;
        }
        Ok(())
    }

    /// Returns the nex
    /// Doesn't advance past the word.
    fn peek_word(&mut self) -> &'a [u8] {
        let rollback = self.mem.mmz_pos;
        self.skip_ws();
        let start = self.mem.mmz_pos;
        loop {
            match self.cur() {
                None => break,
                Some(c) if wc(c) => break,
                Some(_) => self.advance(1),
            }
        }

        let out = &self.mem.mmz[start..self.mem.mmz_pos];
        self.mem.mmz_pos = rollback;
        out
    }

    /// EITHER a dummy `.` OR an `ident_`
    fn dummy_ident(&mut self) -> Res<Str<'a>> {
        let rollback = self.mem.mmz_pos;
        self.skip_ws();
        let start = self.mem.mmz_pos;
        if let Some(b'.') = self.cur() {
            self.advance(1);
        }
        match self.cur() {
            Some(c) if ident_start(c) => self.advance(1),
            _ => {
                self.mem.mmz_pos = rollback;
                return Err(VerifErr::Msg(
                    format!("ident_ failed; word: {}", String::from_utf8_lossy(self.peek_word()))
                ))
            }
        }
        while let Some(c) = self.cur() {
            if ident_rest(c) {
                self.advance(1)
            } else {
                break
            }
        }
        Ok(Str(&self.mem.mmz[start..self.mem.mmz_pos]))
    }

    fn ident(&mut self) -> Res<Str<'a>> {
        let rollback = self.mem.mmz_pos;
        let ident = self.ident_()?;
        if let [b'_', ..] = ident.as_bytes() {
            self.mem.mmz_pos = rollback;
            return Err(VerifErr::Msg(format!("ident got underscore")))
        }
        Ok(ident)
    }

    fn ident_(&mut self) -> Res<Str<'a>> {
        let rollback = self.mem.mmz_pos;
        self.skip_ws();
        let start = self.mem.mmz_pos;
        match self.cur() {
            Some(c) if ident_start(c) => self.advance(1),
            _ => {
                self.mem.mmz_pos = rollback;
                return Err(VerifErr::Msg(
                    format!("ident_ failed; word: {}", String::from_utf8_lossy(self.peek_word()))
                ))
            }
        }
        while let Some(c) = self.cur() {
            if ident_rest(c) {
                self.advance(1)
            } else {
                break
            }
        }
        Ok(Str(&self.mem.mmz[start..self.mem.mmz_pos]))
    }    

    pub fn parse_u32(&mut self) -> Option<u32> {
        self.skip_ws();
        let mut acc = None;
        while let Some(c) = self.cur() {
            if c.is_ascii_digit() {
                self.advance(1);
                acc = Some((acc.unwrap_or(0) * 10) + ((c as u32) - 48))
            } else {
                break
            }
        }
        acc
    }    
}

fn add_nota_info<'a>(
    m: &mut HashMap<Str<'a>, NotationInfo<'a>>,
    tok: Str<'a>,
    n: NotationInfo<'a>,
) -> Res<()> {
    if let Some(e) = m.insert(tok, n.clone()) {
        if e != n {
            return Err(VerifErr::Msg(format!("Incompatible error in add_nota_info")))
        }
    }
    
    Ok(())
}



impl<'b, 'a: 'b> MmzState<'b, 'a> {
    pub fn prec_lvl(&mut self) -> Option<Prec> {
        if self.kw(b"max").is_some() {
            Some(Prec::Max)
        } else {
            self.parse_u32().map(|n| Prec::Num(n))
        }
    }

    fn gen_notation(&mut self) -> Res<()> {
        none_err!(self.kw(b"notation "))?;
        let ident = self.ident()?;
        let term = self.mem.get_term_by_ident(&ident)?;
        let _binders = self.binders(term.args_and_ret(), "notation")?;
        localize!(self.guard(b'='))?;
        let prec_const = self.prec_const()?;
        let mut lits = vec![L(prec_const)];
        loop {
            self.skip_ws();
            let rollback = self.mem.mmz_pos;
            match self.prec_const() {
                Ok((s, p)) => {
                    lits.push(L((s, p)));
                },
                Err(_) => {
                    self.mem.mmz_pos = rollback;
                    match self.ident() {
                        Ok(y) => {
                            lits.push(R(y));
                        },
                        Err(_) => break,
                    }
                }
            } 
        }
        // notation_literal
        self.elab_gen_nota(
            term.tid.into_inner(),
            ident,
            u16::try_from(term.args().len()).unwrap(),
            lits
        )?;
        localize!(self.guard(b';'))?;
        Ok(())
    }

    /// Add the association of `tok: Str |-> prec: Prec` to the map `MmzMem::consts`
    fn add_const(&mut self, tk: Str<'a>, prec: Prec) -> Res<()> {
        if tk.as_bytes() == b"(" || tk.as_bytes() == b")" {
            return Err(VerifErr::Msg(format!("Parens not allowed as notation consts; they're reserved by mm0")));
        }

        match self.mem.consts.insert(tk, prec) {
            Some(already) if already != prec => {
                Err(VerifErr::Msg(format!("Cannot redeclare const {:?} with new prec. It was already declared with {:?}", tk, already)))
            },
            _ => Ok(())
        }
    }    

    fn elab_gen_nota(
        &mut self,
        term_num: u32,
        term_ident: Str<'a>,
        term_num_args: u16,
        lits: Vec<Either<(Str<'a>, Prec), Str<'a>>>,
    ) -> Res<()> {

        let num_args_nota = self.vars_done.len();
        assert_eq!(num_args_nota, term_num_args as usize);

        let mut vars_used = BumpVec::new_in(self.bump);
        let mut it = lits.iter().peekable();

        let (mut lits2, mut right_associative, tok, first_prec) = match it.next() {
            None => panic!("Notation requires at least one literal"),
            Some(L((tok, prec))) => (Vec::<NotationLit>::new(), true, tok, prec),
            Some(R(_)) => panic!("generalized infix not allowed in mm0")
        };

        self.add_const(*tok, first_prec.clone())?;
        if it.peek().is_none() {
            right_associative = false;
        }

        while let Some(lit) = it.next() {
            match *lit {
                L((tok, prec)) => {
                    lits2.push(NotationLit::Const(tok));
                    self.add_const(tok, prec)?
                }
                R(var_ident) => {
                    // In assigning the variable its precedence...
                    // If there's no const/symbol after it, 
                    let prec = match it.peek() {
                        None => bump(right_associative, *tok, *first_prec),
                        // If you have [.., var, symbol, .. ] then try to bump
                        // the prec of the variable by one.
                        Some(L((tok2, prec2))) => bump(true, *tok2, *prec2),
                        // If the next token is another var, give Prec::Max
                        Some(R(_)) => Prec::Max,
                    };
                    vars_used.push(var_ident);
                    let pos = self.vars_done.iter().position(|v| v.ident == Some(var_ident)).unwrap();
                    lits2.push(NotationLit::Var { pos, prec })
                }
            }
        }        

        for sig_var in self.vars_done.iter() {
            if let Some(ident) = sig_var.ident {
                // Dummy variables not allowed in `notation` declarations.
                make_sure!(!sig_var.is_dummy);
                // Each ident mentioned on the LHS of the colon must be used in the notation.
                make_sure!(vars_used.iter().any(|used_ident| *used_ident == ident));

            } else {
                return Err(VerifErr::Msg(format!("anonymous vars not allowed in general notation declarations!")))
            }
        }

        // If the notation declartion ends with a variable, it's considered 
        // right-associative for the precedence disambiguation.
        if let NotationLit::Var {..} = none_err!(lits2.last())? {
            self.mem.occupy_prec(term_ident, *first_prec, Assoc::Right)?;
        }

        let info = NotationInfo {
            term_num,
            term_ident,
            rassoc: right_associative,
            lits: Arc::from(lits2),
        };

        //self
        //.declared_notations
        //.entry(term_ident)
        //.or_default()
        //.consts
        //.push((*tok, None));        

        add_nota_info(&mut self.mem.prefixes, *tok, info)
    }

    fn prec_const(&mut self) -> Res<(Str<'a>, Prec)> {
        localize!(self.guard(b'('))?;
        let constant = self.constant()?;
        localize!(self.guard(b':'))?;
        let prec = none_err!(self.prec_lvl())?;
        localize!(self.guard(b')'))?;
        Ok((constant, prec))
    }

    // for all coercions from `x` to `ys`, if `y e. ys` is provable
    // insert `x |-> y` into `provs`.
    // If a pair `x |-> y` already existed, throw an error.
    // For example, if there are two
    // x |-> nat
    // x |-> nat
    // You have a diamond.
    fn update_provs(&mut self) -> Res<()> {
        let mut provs = HashMap::with_hasher(Default::default());
        for (&s1, m) in self.mem.coes.iter() {
            for s2 in m.keys().copied() {
                if self.mem.outline.file_view.mmb_sort_mods(s2)?.contains(Modifiers::PROVABLE) {
                    if let Some(_s2) = provs.insert(s1, s2) {
                        return Err(VerifErr::Msg(format!("Coercion diamond to provable detected. from: {:?}, to: {:?}", s1, s2)))
                    }
                }
            }
        }
        Ok(self.mem.coe_prov = provs)
    }    

    fn add_coe(
        &mut self,
        term: TermRef,
        _term_ident: Str<'a>,
        from: SortId,
        to: SortId,
    ) -> Res<()> {
        self.add_coe_raw(term, from, to)?;
        self.update_provs()?;
        //self
        //.declared_notations
        //.entry(term_ident)
        //.or_default()
        //.has_coe = true;

        Ok(())
    }

    /// Suppose we wanted to add some coercion coercion my_coe: x > y;`
    /// 
    /// In doing so, we need to consider the transitive coercions "on either side. c
    /// That is, coercions from a sort `w` to `x`, and coercions from `y` to a sort `z`.
    /// In doing so, we need to:
    /// 1. Account for new transitive coercions that will result from the addition
    /// 2. Make sure we didn't create any cycles
    /// 3. Make sure we didn't create any diamonds.
    fn add_coe_raw(
        &mut self,
        term: TermRef,
        x: SortId,
        y: SortId,
    ) -> Res<()> {
        // If the coercion `x > y` already exists, do nothing, otherwise continue
        // knowing that `x > y` is unique.
        match self.mem.coes.get(&x).and_then(|m| m.get(&y)) {
            Some(&Coe::Single { term_num }) if term_num == term.tid => return Ok(()),
            _ => {}
        }

        // Make the new coercion `x > y` with whatever term_num corresponds to `my_coe`.
        let coe_x_y = Arc::new(Coe::Single { term_num: term.tid });

        // Holds:
        // 1. The original coercion `x > y`
        // 2. All transitive coercions `w > y`
        // 3. All transitive coercions `x > z`
        let mut todo = BumpVec::new_in(self.bump);

        // For any coercions already declared that go (either directly or transitively)
        // from `w > x`, place (w, y, (Trans { w > x, x, w > y })) in `todo`
        for (w, coes_w_xs) in self.mem.coes.iter() {
            if let Some(coe_w_x) = coes_w_xs.get(&x) {
                todo.push((
                    *w,
                    y,
                    Arc::new(Coe::Trans {
                        c1: Arc::new(coe_w_x.clone()), 
                        middleman_sort: x, 
                        c2: coe_x_y.clone()
                    }),
                ))
            }
        }

        todo.push((x, y, coe_x_y.clone()));

        // For any existing coercion `y > z`, push 
        // (x, z, Trans { x > y, y, y > z })
        // onto `todos`
        if let Some(m) = self.mem.coes.get(&y) {
            for (z, y_to_z) in m {
                todo.push((
                    x,
                    *z,
                    Arc::new(Coe::Trans{
                        c1: coe_x_y.clone(), 
                        middleman_sort: y, 
                        c2: Arc::new(y_to_z.clone())
                    }),
                ))
            }
        }

        // If the addition of `x > y` would create a transitive coercion
        // such what `w > x > y > w`, we've created a cycle.
        for (w, z, coe) in todo {
            if w == z {
                return Err(VerifErr::Msg(format!("Coercion cycle detected!")));
            }
            // If, when inserting the transitive coercion `w > z`, we find an existing 
            // coercion `w > z`, we know there's a diamond being created since the first 
            // thing we did was confirm that there was no existing coercion `x > y`.
            // Therefore, there's some alternate path between `w` and `z`.
            if let Some(_) =self.mem.coes.entry(w).or_default().insert(z, coe.as_ref().clone()) {
                return Err(VerifErr::Msg(format!("Coercion diamond detected!")));
            }
        }
        Ok(())
    }      

    fn elab_coe(
        &mut self,
        term: TermRef,
        term_ident: Str<'a>,
        from: SortId,
        to: SortId,
    ) -> Res<()> {
        assert_eq!(term.args().len(), 1);
        self.add_coe(term, term_ident, from, to)
    }    

    fn coercion(&mut self) -> Res<()> {
        none_err!(self.kw(b"coercion "))?;
        let ident = self.ident()?;
        localize!(self.guard(b':'))?;
        let from = self.ident()?;
        localize!(self.guard(b'>'))?;
        let to = self.ident()?;
        localize!(self.guard(b';'))?;

        let term = self.mem.get_term_by_ident(&ident)?;
        let from_num = self.mem.get_sort_id(from)?;
        let to_num = self.mem.get_sort_id(to)?;
        self.elab_coe(term, ident, from_num, to_num)
    }

    fn simple_notation(&mut self) -> Res<()> {
        let fix = if self.kw(b"prefix ").is_some() {
            Fix::Prefix
        } else if self.kw(b"infixl ").is_some() {
            Fix::Infixl
        } else if self.kw(b"infixr ").is_some() {
            Fix::Infixr
        } else {
            return Err(VerifErr::Msg(format!("Expected fix")))
        };

        let ident = self.ident()?;
        let term = self.mem.get_term_by_ident(&ident)?;
        localize!(self.guard(b':'))?;
        let constant = self.constant()?;
        if !self.kw(b"prec").is_some() {
            return localize!(Err(VerifErr::Msg(format!("Missing prec keyword"))))
        }

        let prec = none_err!(self.prec_lvl())?;
        localize!(self.guard(b';'))?;
        match fix {
            Fix::Prefix => self.elab_simple_prefix(ident, term, constant, prec),
            Fix::Infixl => self.elab_simple_infix(ident, term, constant, prec, false),
            Fix::Infixr => self.elab_simple_infix(ident, term, constant, prec, true),
        }
    }

    fn elab_simple_prefix(
        &mut self,
        term_ident: Str<'a>,
        term: TermRef<'a>,
        constant: Str<'a>,
        prec: Prec,         
    ) -> Res<()> {
        let mut lits = Vec::new();

        // This is now all_args - 2
        if let Some(n) = term.args().len().checked_sub(1) {
            for i in 0..n {
                lits.push(NotationLit::Var {
                    pos: i as usize,
                    prec: Prec::Max,
                })
            }
            lits.push(NotationLit::Var { pos: n as usize, prec });
        }

        self.add_const(constant, prec)?;

        let info = NotationInfo {
            term_num: term.tid.into_inner(),
            term_ident,
            rassoc: true,
            lits: Arc::from(lits),
        };
        //self
        //.declared_notations
        //.entry(term_ident)
        //.or_default()
        //.consts
        //.push((constant, Some(Fix::Prefix)));        

        // 0-ary prefixes don't affect the occupied map.
        if term.args().len() > 0 {
            self.mem.occupy_prec(term_ident, prec, Assoc::Right)?;
        }

        add_nota_info(
            &mut self.mem.prefixes,
            constant,
            info
        )
    }

    fn elab_simple_infix(
        &mut self,
        term_ident: Str<'a>,
        term: TermRef<'a>,
        constant: Str<'a>,
        prec: Prec,         
        is_infixr: bool,
    ) -> Res<()> {
        match prec {
            Prec::Max => return Err(VerifErr::Msg(format!("Max not allowed for simple infix notations"))),
            Prec::Num(n) => {
                let i2 = none_err!(n.checked_add(1))?;
                if term.args().len() != 2 {
                    return localize!(Err(VerifErr::Msg(
                        format!("infix notations must be for terms with 2 arguments. {:?} had {}", term_ident, term.args().len())
                    )))
                }
                let lits = if is_infixr {
                    vec![
                        NotationLit::Var { pos: 0, prec: Prec::Num(i2) },
                        NotationLit::Const(constant),
                        NotationLit::Var { pos: 1, prec },
                    ]
                } else {
                    vec![
                        NotationLit::Var { pos: 0, prec },
                        NotationLit::Const(constant),
                        NotationLit::Var { pos: 1, prec: Prec::Num(i2) }
                    ]
                };

                self.add_const(constant, prec)?;

                let info = NotationInfo {
                    term_num: term.tid.into_inner(),
                    term_ident,
                    rassoc: is_infixr,
                    lits: Arc::from(lits),
                };                

                //self
                //.declared_notations
                //.entry(term_ident)
                //.or_default()
                //.consts
                //.push((constant, Some(if is_infixr { Fix::Infixr } else { Fix::Infixl })));

                if is_infixr {
                    self.mem.occupy_prec(term_ident, prec, Assoc::Right)?
                } else {
                    self.mem.occupy_prec(term_ident, prec, Assoc::Left)?
                }

                add_nota_info(&mut self.mem.infixes, constant, info)
            }
        }
    }

    fn sort(&mut self) -> Res<(Str<'a>, Modifiers)> {
        let mut mods = Modifiers::empty();
        while let Some(_) = self.cur() {
            if self.kw(b"provable ").is_some() {
                mods.insert(Modifiers::PROVABLE);
            } else if self.kw(b"strict ").is_some() {
                mods.insert(Modifiers::STRICT);
            } else if self.kw(b"pure ").is_some() {
                mods.insert(Modifiers::PURE);
            } else if self.kw(b"free ").is_some() {
                mods.insert(Modifiers::FREE);
            } else if self.kw(b"sort ").is_some() {
                break;
            } else {
                return Err(VerifErr::Msg(format!("Bad sort parse")))
            }
        }
        let ident = self.ident()?;
        localize!(self.guard(b';'))?;
        Ok((ident, mods))
    }


    pub fn parse_sort(&mut self) -> Res<()> {
        let (ident, mods) = self.sort()?;
        let mmb_mods = self.mem.outline.file_view.mmb_sort_mods(self.mem.num_sorts_done())?;
        make_sure!(mods == mmb_mods);
        self.mem.add_sort(ident)?;
        Ok(())
    }

    pub fn parse_termdef(
        &mut self, 
        term: TermRef<'a>,
    ) -> Res<()> {
        make_sure!(self.kw(b"term ").or(self.kw(b"def ")).is_some());
        let ident = self.ident()?;
        let mode = if term.def() { "def" } else { "term" };
        self.binders(term.args_and_ret(), mode)?;

        if term.def() && self.peek_word() == b"=" {
            localize!(self.guard(b'='))?;
            let rhs_e = self.expr_()?;
            let rhs_e = self.coerce(rhs_e, self.mem.coe_prov_or_else(rhs_e.sort()))?;
            self.check_expr(term.unify(), rhs_e, UMode::UDef)?;
        }

        localize!(self.guard(b';'))?;
        self.mem.add_termdef(ident);
        Ok(())
    }

    /// Parse an `axiom` or a `theorem` from a .mm0 file
    pub fn parse_assert(
        &mut self, 
        assert: ThmRef<'a>,
    ) -> Res<()> {
        make_sure!(self.kw(b"axiom ").or(self.kw(b"theorem ")).is_some());
        let ident = self.ident().unwrap();
        let _binders = self.binders(assert.args(), "assert")?;
        let tgt = self.hyps.pop().unwrap().expr;
        self.check_expr(
            assert.unify(),
            tgt,
            UMode::UThm
        )?;
        localize!(self.guard(b';'))?;
        self.mem.add_assert(ident);
        Ok(())
    }

    /// Parse an import statement. At this point, all of the imports have
    /// previously been parsed and resolved since they have to be handled
    /// before the main mmz parse, so this just identifies and skips the statement.
    pub fn parse_import(&mut self) -> Res<()> {
        make_sure!(self.kw(b"import ").is_some());
        localize!(self.guard(b'"'))?;
        while let Some(d) = self.cur() {
            if d == b'"' {
                self.advance(1);
                localize!(self.guard(b';'))?;
                self.skip_ws();
                break
            } else {
                self.advance(1);
            }
        }
        Ok(())
    }

    fn binders(
        &mut self, 
        args: &[Arg],
        mode: &str,
    ) -> Res<()> {
        // This rolling back of the binders on failure is just to make eventual error-reporting
        // nicer. If part of the binder group fails, we want to be able to fail the whole group.
        let (mut todo_len, mut done_len) = (0, 0);
        // Loop over 'getting a binder group, like
        // iter1.. {x: nat}
        // iter_n.. (ph ps: wff x)
        while let Some(_) = self.cur() {
            // The portion of the declaration's arguments that we haven't yet parsed.
            let args_todo = args.iter().copied().skip(self.non_dummy_vars().count());
            match self.binder_group(args_todo, mode) {
                Ok(_) => {
                    todo_len = self.vars_todo.len();
                    done_len = self.vars_done.len();
                    continue
                }
                Err(_) => {
                    self.vars_todo.truncate(todo_len);
                    self.vars_done.truncate(done_len);
                    break
                }
            }
        }

        localize!(self.guard(b':'))?;
        let args_todo = args.iter().copied().skip(self.non_dummy_vars().count());
        self.return_ty(args_todo, mode)
    }

    // Parse the variable names on the left hand side of the colon.
    // The (x y) in `(x y : A)`, or the `a` and `b` in {a .b: T}
    fn binder_idents(&mut self, mode: &str) -> Res<()> {
        while let Ok(var_ident) = if mode == "def" { self.dummy_ident() } else { self.ident_() } {
            match var_ident.as_bytes() {
                [b'.', tl @ ..] => {
                    make_sure!(mode == "def");
                    self.vars_todo.push((Str(tl), true))
                },
                _ => self.vars_todo.push((var_ident, false))
            }
        }
        Ok(())
    }

    fn binder_group<I>(&mut self, args_todo: I, mode: &str) -> Res<()> 
    where I: Iterator<Item = Arg> + ExactSizeIterator {
        let opener = localize!(self.guard(b'(').or(self.guard(b'{')))?;
        let num_non_dummy_before = self.non_dummy_vars().count();
        // Get the variable idents/names, put them in `vars_todo` until we know their type
        self.binder_idents(mode)?;
        // Find and skip past the type separator `:`
        localize!(self.guard(b':'))?;

        // Try to parse a formula or dep_type as appropriate.
        // Both of these functions then transfer the new vars added to `vars_todo`
        // into `vars_done`, adding the appropriate type info.
        self.skip_ws();
        if let Some(b'$') = self.cur() {
            self.binder_fml(opener == b'{', mode)?;
        } else {
            self.binder_dep_ty(opener == b'{')?;
        }

        // Type-check the new variables we parsed. For dummy variables, make sure they have the high byte (bindedness and sort)
        // matches what the mmb file's args have (since the low 7 bytes are just the bound var index, which may be different).
        //
        // For regular variables, assert that the entire type is equal.
        make_sure!(args_todo.len() >= self.non_dummy_vars().skip(num_non_dummy_before).count());
        for (l, r) in self.non_dummy_vars().skip(num_non_dummy_before).zip(args_todo) {
            if opener == b'(' {
                make_sure!(l.ty == r)
            } else {
                make_sure!(l.ty.high_bit() == r.high_bit())
            }
        }

        match opener {
            b'(' => { localize!(self.guard(b')'))?; }
            b'{' => { localize!(self.guard(b'}'))?; }
            _ => return Err(VerifErr::Msg(format!("Binder group has mismatched braces")))
        }

        Ok(())
    }    

    /// This is only used in one spot, so expects the parser to already be at the leading `$`
    fn binder_fml(&mut self, bound: bool, mode: &str) -> Res<()> {
        make_sure!(mode == "assert");
        // No bound hyps
        make_sure!(!bound);
        // Has to be either an axiom or a theorem to have hyps
        let math_expr = self.expr_()?;
        let math_expr = self.coerce(math_expr, self.mem.coe_prov_or_else(math_expr.sort()))?;
        for (ident, dummy) in self.vars_todo.iter().skip(self.vars_done.len()) {
            make_sure!(!dummy);
            let pos = self.vars_done.len();
            self.hyps.push(MmzHyp { 
                ident: Some(*ident),
                pos: Some(pos), 
                expr: math_expr
            })
        }        
        Ok(())
    }

    /// Parse the `wff x y` from `(ph: wff x y)`
    /// where `x` and `y` are previously declared dependencies.
    fn binder_dep_ty(&mut self, bound: bool) -> Res<()> {
        let sort_ident = self.ident()?;
        let sort_id = self.mem.get_sort_id(sort_ident)?;
        // Needs to make a new bound type
        let mut ty_accum = Type::new(bound);
        ty_accum.add_sort(sort_id);
        if bound {
            ty_accum |= Type::from(self.take_next_bv());
        } else {
            while let Ok(dep_ident) = self.ident() {
                make_sure!(!bound);
                let dep_pos = none_err!(self.potential_deps().position(|v| v.ident == Some(dep_ident)))?;
                ty_accum.add_dep(dep_pos as u64);
            }
        }

        for (ident, dummy) in self.vars_todo.iter().skip(self.vars_done.len()) {
            let pos = self.vars_done.len();
            self.vars_done.push(MmzVar { 
                ident: Some(*ident),
                pos, 
                ty: ty_accum,
                is_dummy: *dummy
            })
        }        
        Ok(())
    }

    fn return_ty<I>(&mut self, mut arrow_args: I, mode: &str) -> Res<()> 
    where I: Iterator<Item = Arg> + ExactSizeIterator + Clone {
        while let Some(_) = self.cur() {
            // If it's a hypothesis
            if let Some(b'$') = { self.skip_ws(); self.cur() } {
                make_sure!(mode == "assert"); 
                let math_expr = self.expr_()?;
                let math_expr = self.coerce(math_expr, self.mem.coe_prov_or_else(math_expr.sort()))?;
                self.hyps.push(MmzHyp { ident: None, pos: None, expr: math_expr });
            } else {
                // If it's an arrow type.
                let sort_ident = self.ident()?;
                let sort_id = self.mem.get_sort_id(sort_ident)?;
                let mut ty_accum = Type::new_of_sort(sort_id.into_inner());

                while let Ok(dep_ident) = self.ident() {
                    let dep_pos = none_err!(self.potential_deps().position(|v| v.ident == Some(dep_ident)))?;
                    ty_accum.add_dep(dep_pos as u64);
                }
                // Type-check the return type.
                make_sure!(ty_accum == none_err!(arrow_args.next())?);
            }

            if let Some(b'>') = { self.skip_ws(); self.cur() } {
                self.advance(1);
            } else {
                break
            }
        }
        Ok(())
    }    

    pub fn check_expr(
        &mut self,
        u: UnifyIter,
        tgt: MmzExpr<'b>,
        mode: UMode,
    ) -> Res<()> {
        self.ustack.push(tgt);

        for v in self.vars_done.iter().filter(|v| !v.is_dummy) {
            self.uheap.push(MmzExpr::Var(*v))
        }

        for maybe_cmd in u {
            match maybe_cmd.map_err(|e| VerifErr::Msg(format!("{}", e)))? {
                UnifyCmd::Ref(i) => {
                    let heap_elem = *&self.uheap[i as usize];
                    let stack_elem = none_err!(self.ustack.pop())?;
                    if heap_elem != stack_elem {
                        return Err(VerifErr::Msg(format!("check_expr Ref eq test went bad")))
                    }
                }
                UnifyCmd::Term { tid, save } => {
                    let p = none_err!(self.ustack.pop())?;
                    if let MmzExpr::App { term_num:n2, args, .. } = p {
                        make_sure!(tid == n2);
                        self.ustack.extend(args.into_iter().rev());
                        if save {
                            self.uheap.push(p);
                        }
                    } else {
                        return Err(VerifErr::Msg(format!("UnifyCmd expected term")))
                    }
                },
                UnifyCmd::Dummy(sort_id) => {
                    make_sure!(mode == UMode::UDef);
                    let p = none_err!(self.ustack.pop())?;
                    if let MmzExpr::Var(MmzVar { ty, is_dummy, .. }) = p {
                        make_sure!(sort_id == ty.sort());
                        make_sure!(is_dummy);
                        self.uheap.push(p)
                    } else {
                        return localize!(Err(VerifErr::Msg(format!("check_expr failed at dummy"))))
                    }
                }
                UnifyCmd::Hyp => self.ustack.push(none_err!(self.hyps.pop())?.expr),
            }
        }
        Ok(self.uheap.clear())
    }
}

