//! This module implements an operator precedence parser which aims to turn `$`-delimited math strings 
//! (sometimes also called "formulas") into mm0 expressions while allowing for the use of user-defined notation.

use bumpalo::collections::Vec as BumpVec;
use crate::mmz::parse::{ wc, trim };
use crate::none_err;
use crate::localize;
use crate::make_sure;
use crate::mmz::{
    MmzState,
    NotationLit,
    NotationInfo,
    MathStr,
    MmzExpr,
    Prec,
    DelimKind,
};
use crate::util::{ 
    Res,
    VerifErr,
    Str,
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
 
    /// The main entry point to the math parser. When the mmz parser wants
    /// to parse an expression from a new math string (`$ .. $`), it calls this.
    pub fn expr_(&mut self) -> Res<MmzExpr<'b>> {
        localize!(self.guard(b'$'))?;
        let out_e = self.expr(Prec::Num(0), None)?;
        self.skip_math_ws();
        if let Some(b'$') = self.cur() {
            self.advance(1)
        }
        Ok(out_e)
    }    

    /// Gets a pair (prec, expr), and tries to continue parsing the rest
    /// of some math string held onto by `self`, which holds the mmz file,
    /// and by extension the math string we're working on.
    fn expr(&mut self, initial_prec: Prec, accum: Option<MmzExpr<'b>>) -> Res<MmzExpr<'b>> {
        match accum {
            // This was an initial call to `expr`; there's no accumulating expression yet.
            None => {
                let prefix = self.prefix(initial_prec)?;
                self.expr(initial_prec, Some(prefix))
            },
            // This is a continuation call, adding to some accumulating expression.
            // These calls can only come from calls to `expr` made from within
            // the module.
            Some(a) => match self.take_ge_infix(initial_prec).transpose()? {
                // We've reached the end of the current expression, either
                // because the math-string is over, or because initial_prec > next_prec
                None => Ok(a),
                // Continue adding to this accumulator.
                // we have: (prec_low, a) .. $ `op2:prec_high` b .. $
                Some((op_term, op_prec)) => {
                    let b = self.prefix(op_prec)?;
                    let a_until_lt = self.lhs(a, (op_term, op_prec), b)?;
                    self.expr(initial_prec, Some(a_until_lt))
                }
            }
        }
    }

    /// `prefix` determined we have a raw term application, so just parse the arguments
    /// and return `App { t, args* }`
    fn term_app(&mut self, this_prec: Prec, tok: &Str<'a>) -> Res<MmzExpr<'b>> {
        let term = self.mem.get_term_by_ident(&tok)?;
        // If this is a 0-ary term.
        if term.num_args_no_ret() == 0 {
            Ok(MmzExpr::App { 
                term_num: term.term_num, 
                num_args: 0, 
                args: self.alloc(BumpVec::new_in(self.bump)),
                sort: term.sort()
            })
        } else {
            make_sure!(this_prec <= Prec::Num(APP_PREC));
            let mut sig_args = BumpVec::new_in(self.bump);
            let mut restore = self.mem.mmz_pos;

            for arg in term.args() {
                if let Ok(e_) = self.expr(Prec::Max, None) {
                    sig_args.push(self.coerce(e_, arg.sort())?);
                    restore = self.mem.mmz_pos;
                } else {
                    self.mem.mmz_pos = restore;
                    break
                }
            }

            Ok(MmzExpr::App {
                term_num: term.term_num,
                num_args: term.num_args_no_ret(),
                args: self.alloc(sig_args).as_slice(),
                sort: term.sort()
            })
        }
    }

    /// Parse one of the following:
    ///
    /// 1. An expression surrounded by parentheses
    /// 2. An expression using either a prefix notation or a general notation
    /// 3. An occurrence of a declared variable
    /// 4. A raw term application (like `not ph`)
    fn prefix(&mut self, this_prec: Prec) -> Res<MmzExpr<'b>> {
        self.skip_math_ws();
        if let Some(b'(') = self.cur() {
            self.advance(1);
            let e = self.expr(Prec::Num(0), None)?;
            self.guard_math(b')')?;
            return Ok(e)
        } 

        let tok = none_err!(self.math_tok())?;
        if let Some(q) = self.mem.consts.get(&tok).copied() {
            self.prefix_const(this_prec, &tok, q)
        } else if let Some(mmz_var) = self.vars_done.iter().find(|v| v.ident == Some(tok)) {
            Ok(MmzExpr::Var(*mmz_var))
        } else {
            self.term_app(this_prec, &tok)
        }
    }

    /// If `prefix` determines we have either a prefix notation or a general notation,
    /// use this to try and aprse the correct arguments, applying them to whatever
    /// term corresponds to the notation symbol being used.
    fn prefix_const(&mut self, last_prec: Prec, tok: &Str<'a>, next_prec: Prec) -> Res<MmzExpr<'b>> {
        if next_prec >= last_prec {
            if let Some(pfx_info) = self.mem.prefixes.get(tok).cloned() {
                let term_num = pfx_info.term_num;
                let term = self.mem.outline.get_term_by_num(term_num)?;
                return self.apply_notation(pfx_info.lits.as_ref(), term)
            }
        } 
        Err(VerifErr::Msg(format!("bad prefix const")))
    }    

    /// Having previously parsed a prefix or general notation and determined its
    /// corresponding `term`, parse and check the arguments demanded by that `term`
    /// and then apply them, returning the `App t e*` expression.
    fn apply_notation(
        &mut self, 
        declar_lits: &[NotationLit<'a>], 
        term: Term<'a>, 
    ) -> Res<MmzExpr<'b>> {
        // A vec of `[None, .., None]` for as many `NotationLit::Var {..}`  are demanded by the term's signature.
        // The option stuff is a safe workaround for the fact that they may occur out of order relative to the
        // underlying term's signature.
        let mut math_args = BumpVec::new_in(self.bump);
        for declar_lit in declar_lits {
            if let NotationLit::Var {..} = declar_lit {
                math_args.push(None)
            }
        }

        // For each item (var or symbol) in the original notation declaration,
        // If it's a Const/symbol, make sure the one in the math string is right
        for lit in declar_lits {
            match lit {
                // Make sure the notation characters present in the math-string
                // match those specified in the original notation declaration.
                NotationLit::Const(fml) => {
                    let tk = none_err!(self.math_tok())?;
                    make_sure!(tk == *fml);
                }
                // Make sure the variable in the math string has the sort called
                // for by the variable in the notation declaration.
                NotationLit::Var { pos, prec } => {
                    let sig_e = none_err!(term.args().nth(*pos))?;
                    let e = self.expr(*prec, None)?;
                    let coerced = self.coerce(e, sig_e.sort())?;
                    match math_args.get_mut(*pos) {
                        Some(x @ None) => *x = Some(coerced),
                        _ => return Err(VerifErr::Msg(format!("misplaced variable in math_parser::literals")))
                    }
                }
            }
        }

        // Collect the actual arguments that were present in the math-string
        // now that they've been checked, removing the `Option`.
        let mut out = BumpVec::new_in(self.bump);
        for arg in math_args {
            match arg {
                Some(x) => out.push(x),
                None => return Err(VerifErr::Msg(format!("incomplete sequence of args in math_parser::literals")))
            }
        }

        Ok(MmzExpr::App {
            term_num: term.term_num,
            num_args: term.num_args_no_ret(),
            args: self.alloc(out),
            sort: term.sort(),
        })        

    }      

    /// If the next peeked token is an *infix* operator with a precedence that is greater than or
    /// equal to the last precedence, return (token, Prec, notation info)
    fn peek_ge_infix(&mut self, last_prec: Prec) -> Option<(Str<'a>, Prec, NotationInfo<'a>)> {
        let peeked = self.peek_math_tok()?;
        let next_prec = self.mem.consts.get(&peeked).copied()?;
        if (next_prec >= last_prec) {
            if let Some(notation_info) = self.mem.infixes.get(&peeked).cloned() {
                Some((peeked, next_prec, notation_info))
            } else {
                None
            }
        } else {
            None
        }
    }      

    /// If the next token is an infix operator with precedence >= the last
    /// precedence, return the term it represents, and its precedence, bumping the precedence
    /// by 1 if it's left-associative so that the `>=` test will fail if the next operator
    /// is the same.
    /// 
    /// DOES advance the parser.
    fn take_ge_infix(&mut self, last_prec: Prec) -> Option<Res<(Term<'a>, Prec)>> {
        let (_, next_prec, notation_info) = self.peek_ge_infix(last_prec)?;
        let infix_term = self.mem.outline.get_term_by_num(notation_info.term_num);
        self.math_tok().unwrap();
        Some(
            if notation_info.rassoc {
                infix_term.map(|t| (t, next_prec))
            } else if let Prec::Num(n) = next_prec {
                infix_term.map(|t| (t, Prec::Num(n + 1)))
            } else {
                Err(VerifErr::Msg(format!("bad lhs")))
            }
        )
    }    

    // From `(a, op1, b)`, either continue adding to the right-hand side if there's a stronger operator next
    // or finish and return `App { op1 a b }`
    fn lhs(
        &mut self,
        a: MmzExpr<'b>,
        (op0_term, op0_prec): (Term<'a>, Prec),
        b: MmzExpr<'b>,
    ) -> Res<MmzExpr<'b>> {
        // If the next token in the math-string is an infix, such that op0_prec <= op1_prec,
        // recurse with lhs(a, op0, (b op1 c*..))
        if let Some((op1_term, op1_prec)) = self.take_ge_infix(op0_prec).transpose()? {
            let c = self.prefix(op1_prec)?;
            let b_op_cprime = self.lhs(b, (op1_term, op1_prec), c)?;
            self.lhs(a, (op0_term, op0_prec), b_op_cprime)
        } else {
            // Next item is None or a weaker infix, so return `App { op1 a b }`
            let mut plus_args = op0_term.args();
            if let (Some(fst), Some(snd), Some(_), None) = (plus_args.next(), plus_args.next(), plus_args.next(), plus_args.next()) {
                let a_coerced = self.coerce(a, fst.sort())?;
                let b_coerced = self.coerce(b, snd.sort())?;

                Ok(MmzExpr::App {
                    term_num: op0_term.term_num,
                    num_args: op0_term.num_args_no_ret(),
                    args: self.alloc(bumpalo::vec![in self.bump; a_coerced, b_coerced]),
                    sort: op0_term.sort()
                })
            } else {
                Err(VerifErr::Msg(format!("math_parser::lhs2 got a list of infix args that had some number of elems not equal to (2 + 1)")))
            }
        }
    }     

}

