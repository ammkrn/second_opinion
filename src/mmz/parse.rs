use crate::mmb::stmt::StmtCmd;

use crate::mmz::{
    MmzState,
    MmzMem,
    DelimKind, 
    MmzItem,
    MmzList,
    MmzList::*,
    Prec, 
    Fix, 
    NotationInfo, 
    NotationLit, 
    Coe,
    MmzVar,
    MmzHyp,
};
use crate::util::{ 
    Mods, 
    Str, 
    Res, 
    VerifErr, 
    SortNum,
    FxIndexMap,
    FxMap,
    Type,
    Either, 
    Term, 
    Assert, 
    Either::*, 
    Args,
};
use crate::make_sure;
use crate::localize;
use crate::none_err;
use std::sync::Arc;
use crate::mmb::unify::{ UnifyCmd, UnifyIter, UMode };

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

    pub fn is_empty(&self) -> bool {
        self.mmz_pos == self.mmz.len()
    }

    pub fn cur(&self) -> Option<u8> {
        self.mmz.get(self.mmz_pos).copied()
    }

    pub fn cur_slice(&self) -> &'a [u8] {
        self.mmz.get(self.mmz_pos..).unwrap_or_else(|| &[])
    }

    pub fn advance(&mut self, n: usize) {
        self.mmz_pos += n;
    }       

    pub fn parse_until(
        &mut self,
        stmt_cmd: StmtCmd, 
        item: Option<Either<Term<'a>, Assert<'a>>>
    ) -> Res<()> {
        'outer: loop {
            'inner: loop {

                let mut mmz_st = MmzState::from(&mut *self);
                if mmz_st.cur().is_none() {
                    break 'inner
                }
            
                match { mmz_st.skip_ws(); mmz_st.peek_word() } {
                    b"provable" | b"strict" | b"free" | b"pure" | b"sort" => return mmz_st.parse_sort(),
                    b"term" | b"def" => {
                        if let Some(L(t)) = item {
                            return mmz_st.parse_termdef(t)

                        } else {
                            unreachable!()
                        }
                    }
                    b"axiom" | b"theorem" => {
                        make_sure!(matches!(stmt_cmd, StmtCmd::Axiom {..}) || matches!(stmt_cmd, StmtCmd::Thm {..}));
                        if let Some(R(assert)) = item {
                            return mmz_st.parse_assert(assert)
                        } else {
                            unreachable!()
                        }
                     },
                     b"delimiter" => mmz_st.delims()?,
                     b"prefix" | b"infixl" | b"infixr" => mmz_st.simple_notation()?,
                     b"notation" => mmz_st.gen_notation()?,
                     b"coercion" => mmz_st.coercion()?,
                     b"import" => mmz_st.parse_import()?,
                     b"input" => return Err(VerifErr::Msg(format!("`input` statements are not currently suppprted"))),
                     b"output" => return Err(VerifErr::Msg(format!("Output statements are not currently supported"))),
                     _ => break 'inner,
                }                
            }

            if let Ok(()) = self.next_mmz_file() {
                continue 'outer
            } else {
                return Err(VerifErr::Msg(
                    format!("`parse_until` ran out of input with remaining verification obligations.")
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

    pub fn coerce(
        &mut self,
        expr: MmzItem<'a>,
        sort: SortNum,
        tgt: SortNum,
    ) -> Res<MmzItem<'a>> {
        if sort == tgt { 
            return Ok(expr)
        }

        if let Some(tgt_id) = self.mem.coe_prov.get(&sort) {
            if tgt == *tgt_id {
                return Ok(expr)
            }
        }
        let coe = none_err!(self.mem.coes.get(&sort).and_then(|m| m.get(&tgt)).cloned())?;
        match coe {
            Coe::Single { term_num } => {
                let args = Cons(expr.alloc(self), Nil.alloc(self));
                Ok(MmzItem::App { 
                    term_num,
                    num_args: 1,
                    args
                })
            },

            Coe::Trans { sort_num, .. } => {
                self.coerce(expr, sort, sort_num)
                .and_then(|inner| self.coerce(inner, sort_num, tgt))
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
        Ok(Str::dedup(&self.mem.mmz[start..self.mem.mmz_pos], self))
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
        Ok(Str::dedup(&self.mem.mmz[start..self.mem.mmz_pos], self))
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
    m: &mut FxIndexMap<Str<'a>, NotationInfo<'a>>,
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
        let _binders = self.binders(term.args(), "notation")?;
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
            term.term_num,
            ident,
            term.num_args_no_ret(),
            lits
        )?;
        localize!(self.guard(b';'))?;
        Ok(())
    }

    fn add_const(&mut self, tk: Str<'a>, prec: Prec) {
        if tk.as_bytes() == b"(" || tk.as_bytes() == b")" {
            panic!("Parens not allowed as notation consts");
        }

        if let Some(x) = self.mem.consts.insert(tk, prec) {
            if x != prec {
                println!("Cannot redeclare const {:?}", tk);
                println!("prec1: {:?}\n", prec);
                println!("prec2: {:?}\n", x);
                panic!()
            }
        }
    }    

    fn elab_gen_nota(
        &mut self,
        term_num: u32,
        term_ident: Str<'a>,
        term_num_args: u16,
        lits: Vec<Either<(Str<'a>, Prec), Str<'a>>>,
    ) -> Res<()> {
        let num_args_nota = self.mem.vars_done.len();
        assert_eq!(num_args_nota, term_num_args as usize);

        let mut vars_used = Vec::new();
        let mut it = lits.iter().peekable();

        let (mut lits2, mut right_associative, tok, prec) = match it.next() {
            None => panic!("Notation requires at least one literal"),
            Some(L((tok, prec))) => (Vec::<NotationLit>::new(), true, tok, prec),
            Some(R(_)) => panic!("generalized infix not allowed in mm0")
        };

        self.add_const(*tok, prec.clone());
        if it.peek().is_none() {
            right_associative = false;
        }

        while let Some(lit) = it.next() {
            match *lit {
                L((tok, prec)) => {
                    lits2.push(NotationLit::Const(tok));
                    self.add_const(tok, prec)
                }
                R(var_ident) => {
                    let prec = match it.peek() {
                        None => bump(right_associative, *tok, *prec),
                        Some(L((tok2, prec2))) => bump(true, *tok2, *prec2),
                        Some(R(_)) => Prec::Max,
                    };
                    vars_used.push(var_ident);
                    let pos = self.mem.vars_done.iter().position(|v| v.ident == Some(var_ident)).unwrap();
                    lits2.push(NotationLit::Var { pos, prec })
                }
            }
        }        

        for sig_var in self.mem.vars_done.iter() {
            if let Some(ident) = sig_var.ident {
                // Dummy variables not allowed in `notation` declarations.
                make_sure!(!sig_var.is_dummy);
                // Each ident mentioned on the LHS of the colon must be used in the notation.
                make_sure!(vars_used.iter().any(|used_ident| *used_ident == ident));

            } else {
                return Err(VerifErr::Msg(format!("anonymous vars not allowed in general notation declarations!")))
            }
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

    fn update_provs(&mut self) -> Res<()> {
        let mut provs = FxMap::with_hasher(Default::default());
        for (s1, m) in self.mem.coes.iter() {
            for s2 in m.keys() {
                if self.mem.outline.get_sort_mods(*s2 as usize)?.is_provable() {
                    if let Some(_s2) = provs.insert(*s1, *s2) {
                        println!("Coercion diamond to provable detected");
                        panic!();
                    }
                }
            }
        }
        Ok(self.mem.coe_prov = provs)
    }    

    fn add_coe(
        &mut self,
        term: Term,
        _term_ident: Str<'a>,
        from: u8,
        to: u8,
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

    fn add_coe_raw(
        &mut self,
        term: Term,
        from: u8,
        to: u8,
    ) -> Res<()> {
        match self.mem.coes.get(&from).and_then(|m| m.get(&to)) {
            Some(&Coe::Single { term_num }) if term_num == term.term_num => return Ok(()),
            _ => {}
        }

        let c1 = Arc::new(Coe::Single { term_num: term.term_num });

        let mut todo = Vec::new();

        for (sl, m) in self.mem.coes.iter() {
            if let Some(c) = m.get(&from) {
                todo.push((
                    *sl,
                    to,
                    Arc::new(Coe::Trans{
                        c1: Arc::new(c.clone()), 
                        sort_num: from, 
                        c2: c1.clone()
                    }),
                ))
            }
        }

        todo.push((from, to, c1.clone()));

        if let Some(m) =self.mem.coes.get(&to) {
            for (sr, c) in m {
                todo.push((
                    from,
                    *sr,
                    Arc::new(Coe::Trans{
                        c1: c1.clone(), 
                        sort_num: from, 
                        c2: Arc::new(c.clone())
                    }),
                ))
            }
        }

        for (sl, sr, c) in todo {
            if sl == sr {
                println!("Coercion cycle detected!");
                panic!();
            }
            if let Some(_) =self.mem.coes.entry(sl).or_default().insert(sr, c.as_ref().clone()) {
                println!("Coercion diamond detected!");
                panic!()
            }
        }
        Ok(())
    }    

    fn elab_coe(
        &mut self,
        term: Term,
        term_ident: Str<'a>,
        from: u8,
        to: u8,
    ) -> Res<()> {
        assert_eq!(term.num_args_no_ret(), 1);
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
        let from_num = self.mem.get_sort_num(from)?;
        let to_num = self.mem.get_sort_num(to)?;
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
        term: Term<'a>,
        constant: Str<'a>,
        prec: Prec,         
    ) -> Res<()> {
        let mut lits = Vec::new();

        // This is now all_args - 2
        if let Some(n) = term.num_args_no_ret().checked_sub(1) {
            for i in 0..n {
                lits.push(NotationLit::Var {
                    pos: i as usize,
                    prec: Prec::Max,
                })
            }
            lits.push(NotationLit::Var { pos: n as usize, prec });
        }

        self.mem.consts.insert(constant, prec);

        let info = NotationInfo {
            term_num: term.term_num,
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

        add_nota_info(
            &mut self.mem.prefixes,
            constant,
            info
        )
    }

    fn elab_simple_infix(
        &mut self,
        term_ident: Str<'a>,
        term: Term<'a>,
        constant: Str<'a>,
        prec: Prec,         
        is_infixr: bool,
    ) -> Res<()> {
        match prec {
            Prec::Max => return Err(VerifErr::Msg(format!("Max not allowed for simple infix notations"))),
            Prec::Num(n) => {
                let i2 = none_err!(n.checked_add(1))?;
                if term.num_args_no_ret() != 2 {
                    return localize!(Err(VerifErr::Msg(
                        format!("infix notations must be for terms with 2 arguments. {:?} had {}", term_ident, term.num_args_no_ret())
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
                self.mem.consts.insert(constant, prec);

                let info = NotationInfo {
                    term_num: term.term_num,
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

                add_nota_info(&mut self.mem.infixes, constant, info)
            }
        }
    }

    fn sort(&mut self) -> Res<(Str<'a>, Mods)> {
        let mut mods = Mods::new();
        while let Some(_) = self.cur() {
            if self.kw(b"provable ").is_some() {
                mods |= Mods::provable();
            } else if self.kw(b"strict ").is_some() {
                mods |= Mods::strict();
            } else if self.kw(b"pure ").is_some() {
                mods |= Mods::pure();
            } else if self.kw(b"free ").is_some() {
                mods |= Mods::free();
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
        let mmb_mods = self.mem.outline.get_sort_mods(self.mem.num_sorts_done() as usize)?;
        make_sure!(mods == mmb_mods);
        self.mem.add_sort(ident);
        Ok(())
    }

    pub fn parse_termdef(
        &mut self, 
        term: Term<'a>,
    ) -> Res<()> {
        make_sure!(self.kw(b"term ").or(self.kw(b"def ")).is_some());
        let ident = self.ident()?;

        let mode = if term.is_def() { "def" } else { "term" };
        self.binders(term.args(), mode)?;

        if term.is_def() && self.peek_word() == b"=" {
            localize!(self.guard(b'='))?;
            let (rhs_e, rhs_s) = self.expr_(Prec::Num(0))?;
            let rhs_e = self.coerce(rhs_e, rhs_s, self.mem.coe_prov_or_else(rhs_s))?;
            self.check_expr(term.unify(), rhs_e, UMode::UDef)?;
        }

        localize!(self.guard(b';'))?;
        self.mem.add_termdef(ident);
        Ok(())
    }

    pub fn parse_assert(
        &mut self, 
        assert: Assert<'a>,
    ) -> Res<()> {
        make_sure!(self.kw(b"axiom ").or(self.kw(b"theorem ")).is_some());
        let ident = self.ident().unwrap();
        let _binders = self.binders(assert.args(), "assert")?;
        let tgt = self.mem.hyps.pop().unwrap().expr;
        self.check_expr(
            assert.unify(),
            tgt,
            UMode::UThm
        )?;
        localize!(self.guard(b';'))?;
        self.mem.add_assert(ident);
        Ok(())
    }

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
        args: Args<'a>,
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
            let args_todo = args.skip(self.non_dummy_vars().count());
            match self.binder_group(args_todo, mode) {
                Ok(_) => {
                    todo_len = self.mem.vars_todo.len();
                    done_len = self.mem.vars_done.len();
                    continue
                }
                Err(_) => {
                    self.mem.vars_todo.truncate(todo_len);
                    self.mem.vars_done.truncate(done_len);
                    break
                }
            }
        }

        localize!(self.guard(b':'))?;
        let args_todo = args.skip(self.non_dummy_vars().count());
        self.return_ty(args_todo, mode)
    }

    // Parse the variable names on the left hand side of the colon.
    // The (x y) in `(x y : A)`, or the `a` and `b` in {a .b: T}
    fn binder_idents(&mut self, mode: &str) -> Res<()> {
        while let Ok(var_ident) = if mode == "def" { self.dummy_ident() } else { self.ident_() } {
            match var_ident.as_bytes() {
                [b'.', tl @ ..] => {
                    make_sure!(mode == "def");
                    let new_ident = Str::dedup(tl, self);
                    self.mem.vars_todo.push((new_ident, true))
                },
                _ => self.mem.vars_todo.push((var_ident, false))
            }
        }
        Ok(())
    }

    fn binder_group(&mut self, args_todo: std::iter::Skip<Args<'a>>, mode: &str) -> Res<()> {
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
        self.guard(b'$')?;
        // No bound hyps
        make_sure!(!bound);
        // Has to be either an axiom or a theorem to have hyps
        make_sure!(mode == "assert");
        let (math_expr, math_sort) = self.expr(Prec::Num(0))?;
        let math_expr = self.coerce(math_expr, math_sort,self.mem.coe_prov_or_else(math_sort))?;
        for (ident, dummy) in self.mem.vars_todo.iter().skip(self.mem.vars_done.len()) {
            make_sure!(!dummy);
            let pos = self.mem.vars_done.len();
            self.mem.hyps.push(MmzHyp { 
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
        let sort_num = self.mem.get_sort_num(sort_ident)?;
        let mut ty_accum = Type::new(bound);
        ty_accum.add_sort(sort_num);
        if bound {
            ty_accum.inner |= self.take_next_bv();
        } else {
            while let Ok(dep_ident) = self.ident() {
                make_sure!(!bound);
                let dep_pos = 1 + none_err!(self.potential_deps().position(|v| v.ident == Some(dep_ident)))?;
                ty_accum.add_dep(dep_pos as u64);
            }
        }

        for (ident, dummy) in self.mem.vars_todo.iter().skip(self.mem.vars_done.len()) {
            let pos = self.mem.vars_done.len();
            self.mem.vars_done.push(MmzVar { 
                ident: Some(*ident),
                pos, 
                ty: ty_accum,
                is_dummy: *dummy
            })
        }        
        Ok(())
    }

    fn return_ty(&mut self, mut arrow_args: std::iter::Skip<Args<'a>>, mode: &str) -> Res<()> {
        while let Some(_) = self.cur() {
            // If it's a hypothesis
            if let Some(b'$') = { self.skip_ws(); self.cur() } {
                make_sure!(mode == "assert"); 
                let (math_expr, math_sort) = self.expr_(Prec::Num(0))?;
                let math_expr = self.coerce(math_expr, math_sort,self.mem.coe_prov_or_else(math_sort))?;
                self.mem.hyps.push(MmzHyp { ident: None, pos: None, expr: math_expr });
            } else {
                // If it's an arrow type.
                let sort_ident = self.ident()?;
                let sort_num = self.mem.get_sort_num(sort_ident)?;
                let mut ty_accum = Type::new_with_sort(sort_num);

                while let Ok(dep_ident) = self.ident() {
                    let dep_pos = 1 + none_err!(self.potential_deps().position(|v| v.ident == Some(dep_ident)))?;
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

    pub fn push_ustack_rev_mmz(&mut self, items: MmzList<'a>) {
        if let Cons(hd, tl) = items {
            self.push_ustack_rev_mmz(tl.read(self));
            let hd_ = hd.read(self);
            self.mem.ustack.push(hd_);
        }
    }

    pub fn check_expr(
        &mut self,
        u: UnifyIter,
        tgt: MmzItem<'a>,
        mode: UMode,
    ) -> Res<()> {
        self.mem.ustack.push(tgt);

        for v in self.mem.vars_done.iter().filter(|v| !v.is_dummy) {
            self.mem.uheap.push(v.to_parse_var());
        }

        for maybe_cmd in u {
            match maybe_cmd? {
                UnifyCmd::Ref(i) => {
                    let heap_elem = *&self.mem.uheap[i as usize];
                    let stack_elem = none_err!(self.mem.ustack.pop())?;
                    if heap_elem != stack_elem {
                        return Err(VerifErr::Msg(format!("check_expr Ref eq test went bad")))
                    }
                }
                UnifyCmd::Term { term_num, save } => {
                    let p = none_err!(self.mem.ustack.pop())?;
                    if let MmzItem::App { term_num:n2, args, .. } = p {
                        make_sure!(term_num == n2);
                        self.push_ustack_rev_mmz(args);
                        if save {
                            self.mem.uheap.push(p);
                        }
                    } else {
                        return Err(VerifErr::Msg(format!("UnifyCmd expected term")))
                    }
                },
                UnifyCmd::Dummy { sort_id } => {
                    make_sure!(mode == UMode::UDef);
                    let p = none_err!(self.mem.ustack.pop())?;
                    if let MmzItem::Var { ty, is_dummy, .. } = p {
                        make_sure!(sort_id == ty.sort());
                        make_sure!(is_dummy);
                        self.mem.uheap.push(p)
                    } else {
                        return localize!(Err(VerifErr::Msg(format!("check_expr failed at dummy"))))
                    }
                }
                UnifyCmd::Hyp => self.mem.ustack.push(none_err!(self.mem.hyps.pop())?.expr),
            }
        }
        Ok(self.mem.uheap.clear())
    }
}

