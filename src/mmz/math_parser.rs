use bumpalo::collections::Vec as BumpVec;
use crate::mmz::parse::{ wc, trim };
use crate::none_err;
use crate::localize;
use crate::make_sure;
use crate::mmz::{
    MmzState,
    NotationLit,
    MathStr,
    MmzItem,
    Prec,
    DelimKind,
};
use crate::util::{ 
    Res,
    VerifErr,
    Str,
    SortNum,
    Term,
};

const APP_PREC: u32 = 1024;

impl<'b, 'a: 'b> MmzState<'b, 'a> {
    /// move past non-comment whitespace
    fn skip_math_ws(&mut self) {
        while self.cur().map(|c| wc(c)).unwrap_or(false) {
            self.advance(1);
        } 
    }

    /// Parse a sequence of math tokens delimited by `$` characters.
    fn math_string(&mut self) -> Res<MathStr<'b, 'a>> {
        localize!(self.guard(b'$'))?;

        let mut acc = BumpVec::new_in(self.bump);
        while let Some(tok) = self.math_tok() {
            acc.push(tok);
        }
        Ok(acc)
    }    

    /// Try to parse a certain character, but when you skip whitespace, don't look for comments
    /// since we're working in a math string
    fn guard_math(&mut self, c: u8) -> Res<u8> {
        self.skip_math_ws();
        if self.cur() == Some(c) {
            self.advance(1);
            Ok(c)
        } else {
            localize!(Err(VerifErr::Msg(format!("guard_math failed: expected {}", c as char))))
        }
    }    

    // Math-strings are tokenized by
    // FIRST: splitting on wc
    // THEN: splitting AFTER `Left` delimiters,
    // THEN: splitting BEFORE `Right` delimiters
    // THEN: splitting BEFORE AND AFTER `Both` delimiters
    //
    // This is slightly more involved that it would seem.
    pub fn math_tok(&mut self) -> Option<Str<'a>> {
        self.skip_math_ws();

        if self.cur() == Some(b'$') {
            self.advance(1);
            return None
        }
        
        let start = self.mem.mmz_pos;
        while let Some(c) = self.cur() {
            match self.mem.delims.iter().find(|(d, _)| *d == c).map(|(_, kind)| kind) {
                // If this is the first character, we want to return it even though
                // we're breaking before and after `Both` delims
                Some(DelimKind::Both) if start == self.mem.mmz_pos => {
                    self.advance(1);
                    break
                },
                // If this is NOT the first characrter, don't return it; it has to be 
                // a standalone token.
                Some(DelimKind::Both) => break,
                // If this is the first character, keep going
                Some(DelimKind::Right) if start == self.mem.mmz_pos => self.advance(1),
                Some(DelimKind::Right) => break,
                Some(DelimKind::Left) => {
                    self.advance(1);
                    break
                }
                None if c == b'$' => break,
                None if wc(c) => break,
                None => self.advance(1)
            }
        }

        let out = &self.mem.mmz[start..self.mem.mmz_pos];
        if out.is_empty() { 
            None
        } else if let [lhs @ .., b'$'] = out {
            Some(Str(trim(lhs)))
        } else {
            Some(Str(trim(out)))
        }        
    }

    fn peek_math_tok(&mut self) -> Option<Str<'a>> {
        let rollback = self.mem.mmz_pos;
        let next = self.math_tok();
        self.mem.mmz_pos = rollback;
        next
    }    

    
    pub fn skip_formula(&mut self) -> Res<()> {
        localize!(self.guard(b'$'))?;
        while let Some(c) = self.cur() {
            self.advance(1);
            if c == b'$' {
                return Ok(())
            }
        }
        Err(VerifErr::Msg(format!("unclosed formula in `skip_formula`")))
    }    

    /// Parse a math-string that you can assert is only comprised
    /// of a single token.
    pub fn constant(&mut self) -> Res<Str<'a>> {
        let s = self.math_string()?;
        if let [tk] = s.as_slice() {
            Ok(*tk)
        } else {
            Err(VerifErr::Msg(format!("constant can only be used for math strings comprised of 1 token")))
        }
    }    
 



    /// For initial calls to `expr`; expects the parser to have something 
    /// surrounded by `$` delimiters.
    pub fn expr_(&mut self) -> Res<(MmzItem<'b>, SortNum)> {
        localize!(self.guard(b'$'))?;
        let (out_l, out_r) = self.expr(Prec::Num(0))?;
        self.skip_math_ws();
        if let Some(b'$') = self.cur() {
            self.advance(1)
        }
        
        Ok((out_l, out_r))
    }    

    /// For recursive calls to `expr`; doesn't demand a leading `$` token
    fn expr(&mut self, p: Prec) -> Res<(MmzItem<'b>, SortNum)> {
        let (mut lhs, mut s) = self.prefix(p)?;
        self.lhs(p, &mut lhs, &mut s)?;
        Ok((lhs, s))
    }    

    fn term_app(&mut self, this_prec: Prec, tok: &Str<'a>) -> Res<(MmzItem<'b>, SortNum)> {
        let term = self.mem.get_term_by_ident(&tok)?;
        if term.num_args_no_ret() == 0 {
            Ok((MmzItem::App { 
                term_num: term.term_num, 
                num_args: 0, 
                args: self.alloc(BumpVec::new_in(self.bump)) 
            }, 
            term.sort()))
        } else {
            make_sure!(this_prec <= Prec::Num(APP_PREC));
            let mut sig_args = BumpVec::new_in(self.bump);
            let mut restore = self.mem.mmz_pos;

            for arg in term.args() {
                if let Ok((e_, s_)) = self.expr(Prec::Max) {
                    sig_args.push(self.coerce(e_, s_, arg.sort())?);
                    restore = self.mem.mmz_pos;
                } else {
                    self.mem.mmz_pos = restore;
                    break
                }
            }

            Ok((
                MmzItem::App {
                    term_num: term.term_num,
                    num_args: term.num_args_no_ret(),
                    args: self.alloc(sig_args).as_slice()
                },
                term.sort()
            ))
        }
    }

    fn prefix(&mut self, this_prec: Prec) -> Res<(MmzItem<'b>, SortNum)> {
        self.skip_math_ws();
        if let Some(b'(') = self.cur() {
            self.advance(1);
            let (e, s) = self.expr(Prec::Num(0))?;
            self.guard_math(b')')?;
            return Ok((e, s))
        } 

        let tok = none_err!(self.math_tok())?;
        if let Some(q) = self.mem.consts.get(&tok).copied() {
            self.prefix_const(this_prec, &tok, q)
        } else if let Some(mmz_var) = self.vars_done.iter().find(|v| v.ident == Some(tok)) {
            Ok((mmz_var.to_parse_var(), mmz_var.ty.sort()))
        } else {
            self.term_app(this_prec, &tok)
        }
    }

    fn prefix_const(&mut self, last_prec: Prec, tok: &Str<'a>, next_prec: Prec) -> Res<(MmzItem<'b>, SortNum)> {
        if next_prec >= last_prec {
            if let Some(pfx_info) = self.mem.prefixes.get(tok).cloned() {
                let term_num = pfx_info.term_num;
                let term = self.mem.outline.get_term_by_num(term_num)?;
                let args = self.literals(pfx_info.lits.as_ref(), term)?;
                let ret = MmzItem::App {
                    term_num,
                    num_args: term.num_args_no_ret(),
                    args: self.alloc(args)
                };
                return Ok((ret, term.sort()))
            }
        } 
        Err(VerifErr::Msg(format!("bad prefix const")))
    }    

    fn literals(
        &mut self, 
        lits: &[NotationLit<'a>], 
        term: Term<'a>, 
    ) -> Res<BumpVec<'b, MmzItem<'b>>> {
        let mut math_args = BumpVec::new_in(self.bump);
        for lit in lits {
            if let NotationLit::Var {..} = lit {
                math_args.push(None)
            }
        }

        for lit in lits {
            match lit {
                NotationLit::Const(fml) => {
                    let tk = none_err!(self.math_tok())?;
                    make_sure!(tk == *fml);
                }
                NotationLit::Var { pos, prec } => {
                    let (e, s) = self.expr(*prec)?;
                    let nth_arg = none_err!(term.args().nth(*pos))?;
                    let tgt_sort = nth_arg.sort();
                    let coerced = self.coerce(e, s, tgt_sort)?;
                    match math_args.get_mut(*pos) {
                        Some(x @ None) => *x = Some(coerced),
                        _ => return Err(VerifErr::Msg(format!("misplaced variable in math_parser::literals")))
                    }
                }
            }
        }

        let mut out = BumpVec::new_in(self.bump);
        for arg in math_args {
            match arg {
                Some(x) => out.push(x),
                None => return Err(VerifErr::Msg(format!("incomplete sequence of args in math_parser::literals")))
            }
        }

        Ok(out)
    }    

    fn lhs_test(&mut self, current_prec: Prec) -> Option<Res<(Term<'a>, Prec)>> {
        let peeked = self.peek_math_tok()?;
        let next_prec = self.mem.consts.get(&peeked).copied()?;

        if next_prec >= current_prec {
            self.mem.infixes.get(&peeked).cloned().map(|infix| {
                // advance past peeked token.
                make_sure!(peeked == self.math_tok().unwrap());
                if infix.rassoc {
                    self
                    .mem
                    .outline
                    .get_term_by_num(infix.term_num)
                    .map(|t| (t, next_prec))
                } else if let Prec::Num(n) = next_prec {
                    self
                    .mem
                    .outline
                    .get_term_by_num(infix.term_num)
                    .map(|t| (t, Prec::Num(n + 1)))
                } else {
                    Err(VerifErr::Msg(format!("lhs_test failed")))
                }
            })
        } else {
            None
        }
    }

    fn lhs(
        &mut self,
        p: Prec,
        lhs_e: &mut MmzItem<'b>,
        lhs_s: &mut SortNum
    ) -> Res<()> {
        while let Some((ge_infix_term, ge_infix_prec)) = self.lhs_test(p).transpose()? {
            let (mut rhs_e, mut rhs_s)= self.prefix(ge_infix_prec)?;
            self.lhs2((lhs_e, lhs_s), (ge_infix_term, ge_infix_prec), (&mut rhs_e, &mut rhs_s))?
        }
        Ok(())
    }

    fn check_next_prec(
        &mut self,
        rhs_e: &mut MmzItem<'b>,
        rhs_s: &mut SortNum,
        current_prec: Prec,
    ) -> Option<Res<()>> {
        let peeked = self.peek_math_tok()?;
        let next_prec = self.mem.consts.get(&peeked).copied()?;
        // just confirm that peeked is an infix.
        let _ = self.mem.infixes.get(&peeked)?;
        
        if next_prec >= current_prec {
            assert!(current_prec <= next_prec);
            Some(self.lhs(next_prec, rhs_e, rhs_s))
        } else {
            None
        }
    }

    fn lhs2(
        &mut self,
        (lhs_e, lhs_s): (&mut MmzItem<'b>, &mut SortNum),
        (infix_term, infix_prec): (Term<'a>, Prec),
        (rhs_e, rhs_s): (&mut MmzItem<'b>, &mut SortNum),
    ) -> Res<()> {
        while self.check_next_prec(rhs_e, rhs_s, infix_prec).transpose()?.is_some() {
            continue
        }

        let mut args = infix_term.args();
        // Odd but convenient way to assert that this thing has two args + a return
        // while getting the first two args.
        if let (Some(fst), Some(snd), Some(_), None) = (args.next(), args.next(), args.next(), args.next()) {
            let end_args = bumpalo::vec![
                in self.bump;
                self.coerce(*lhs_e, *lhs_s, fst.sort())?,
                self.coerce(*rhs_e, *rhs_s, snd.sort())?
            ];

            *lhs_e = MmzItem::App {
                term_num: infix_term.term_num,
                num_args: infix_term.num_args_no_ret(),
                args: self.alloc(end_args)
            };
            Ok(*lhs_s = infix_term.sort())
        } else {
            panic!()
        }
    }
}

