// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Alethe proof parser for clean's SMT proof DAG.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::{BTreeMap, HashMap};

use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Token {
    LParen,
    RParen,
    Keyword(String),
    Symbol(String),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SpannedToken {
    token: Token,
    offset: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct Tokenizer<'a> {
    input: &'a str,
    offset: usize,
}

impl<'a> Tokenizer<'a> {
    pub(crate) fn new(input: &'a str) -> Self {
        Self { input, offset: 0 }
    }

    fn tokenize(mut self) -> Result<Vec<SpannedToken>, AletheParseError> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next_token()? {
            tokens.push(token);
        }
        Ok(tokens)
    }

    fn next_token(&mut self) -> Result<Option<SpannedToken>, AletheParseError> {
        self.skip_ws_and_comments();
        let Some(ch) = self.peek_char() else {
            return Ok(None);
        };
        let offset = self.offset;
        let token = match ch {
            '(' => {
                self.bump_char();
                Token::LParen
            }
            ')' => {
                self.bump_char();
                Token::RParen
            }
            '"' => Token::String(self.read_string_literal()?),
            '|' => Token::Symbol(self.read_quoted_symbol()?),
            ':' => Token::Keyword(self.read_symbol_like()),
            _ => Token::Symbol(self.read_symbol_like()),
        };
        Ok(Some(SpannedToken { token, offset }))
    }

    fn skip_ws_and_comments(&mut self) {
        loop {
            while matches!(self.peek_char(), Some(ch) if ch.is_whitespace()) {
                self.bump_char();
            }
            if self.peek_char() == Some(';') {
                while let Some(ch) = self.bump_char() {
                    if ch == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn read_string_literal(&mut self) -> Result<String, AletheParseError> {
        let start = self.offset;
        let mut result = String::new();
        let _ = self.bump_char();
        loop {
            match self.bump_char() {
                Some('"') => {
                    if self.peek_char() == Some('"') {
                        let _ = self.bump_char();
                        result.push('"');
                    } else {
                        return Ok(result);
                    }
                }
                Some(ch) => result.push(ch),
                None => {
                    return Err(AletheParseError::InvalidTerm {
                        reason: format!("unterminated string literal starting at offset {start}"),
                    });
                }
            }
        }
    }

    fn read_quoted_symbol(&mut self) -> Result<String, AletheParseError> {
        let start = self.offset;
        let mut result = String::new();
        let _ = self.bump_char();
        loop {
            match self.bump_char() {
                Some('|') => return Ok(result),
                Some(ch) => result.push(ch),
                None => {
                    return Err(AletheParseError::InvalidTerm {
                        reason: format!("unterminated quoted symbol starting at offset {start}"),
                    });
                }
            }
        }
    }

    fn read_symbol_like(&mut self) -> String {
        let mut result = String::new();
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() || matches!(ch, '(' | ')' | ';') {
                break;
            }
            result.push(ch);
            let _ = self.bump_char();
        }
        result
    }

    fn peek_char(&self) -> Option<char> {
        self.input[self.offset..].chars().next()
    }

    fn bump_char(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.offset += ch.len_utf8();
        Some(ch)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum AletheRuleKind {
    True,
    False,
    NotTrue,
    NotFalse,
    AndType,
    AndPos,
    AndNeg,
    NotAnd,
    Or,
    OrPos,
    OrNeg,
    NotOr,
    Implies,
    ImpliesPos,
    ImpliesNeg1,
    ImpliesNeg2,
    NotImplies1,
    NotImplies2,
    Equiv,
    EquivPos1,
    EquivPos2,
    EquivNeg1,
    EquivNeg2,
    NotEquiv1,
    NotEquiv2,
    Ite,
    ItePos1,
    ItePos2,
    IteNeg1,
    IteNeg2,
    NotIte1,
    NotIte2,
    XorPos1,
    XorPos2,
    XorNeg1,
    XorNeg2,
    Resolution,
    ThResolution,
    Contraction,
    Refl,
    Symm,
    Trans,
    Cong,
    EqReflexive,
    EqTransitive,
    EqCongruent,
    EqCongruentPred,
    LaTautology,
    LaGeneric,
    LaDisequality,
    LaTotality,
    LaMultPos,
    LaMultNeg,
    LiaGeneric,
    ForallInst,
    Skolem,
    Subproof,
    Bind,
    AllSimplify,
    BoolSimplify,
    ArithSimplify,
    BvBitblast,
    ReadOverWritePos,
    ReadOverWriteNeg,
    Extensionality,
    FpToBv,
    StringLength,
    StringDecompose,
    StringCodeInj,
    Hole,
    Drup,
    Trust,
    #[allow(dead_code)]
    // 2026-07-31: no caller in EITHER build (the module-level not(test) allow covers only the lib build).
    Custom(String),
}

impl AletheRuleKind {
    pub(crate) fn from_name(name: &str) -> Result<Self, AletheParseError> {
        let rule = match name {
            "true" => Self::True,
            "false" => Self::False,
            "not_true" => Self::NotTrue,
            "not_false" => Self::NotFalse,
            "and" => Self::AndType,
            "and_pos" => Self::AndPos,
            "and_neg" => Self::AndNeg,
            "not_and" => Self::NotAnd,
            "or" => Self::Or,
            "or_pos" => Self::OrPos,
            "or_neg" => Self::OrNeg,
            "not_or" => Self::NotOr,
            "implies" => Self::Implies,
            "implies_pos" => Self::ImpliesPos,
            "implies_neg1" => Self::ImpliesNeg1,
            "implies_neg2" => Self::ImpliesNeg2,
            "not_implies1" => Self::NotImplies1,
            "not_implies2" => Self::NotImplies2,
            "equiv" => Self::Equiv,
            "equiv_pos1" => Self::EquivPos1,
            "equiv_pos2" => Self::EquivPos2,
            "equiv_neg1" => Self::EquivNeg1,
            "equiv_neg2" => Self::EquivNeg2,
            "not_equiv1" => Self::NotEquiv1,
            "not_equiv2" => Self::NotEquiv2,
            "ite" => Self::Ite,
            "ite_pos1" => Self::ItePos1,
            "ite_pos2" => Self::ItePos2,
            "ite_neg1" => Self::IteNeg1,
            "ite_neg2" => Self::IteNeg2,
            "not_ite1" => Self::NotIte1,
            "not_ite2" => Self::NotIte2,
            "xor_pos1" => Self::XorPos1,
            "xor_pos2" => Self::XorPos2,
            "xor_neg1" => Self::XorNeg1,
            "xor_neg2" => Self::XorNeg2,
            "resolution" => Self::Resolution,
            "th_resolution" => Self::ThResolution,
            "contraction" => Self::Contraction,
            "refl" => Self::Refl,
            "symm" => Self::Symm,
            "trans" => Self::Trans,
            "cong" => Self::Cong,
            "eq_reflexive" => Self::EqReflexive,
            "eq_transitive" => Self::EqTransitive,
            "eq_congruent" => Self::EqCongruent,
            "eq_congruent_pred" => Self::EqCongruentPred,
            "la_tautology" => Self::LaTautology,
            "la_generic" => Self::LaGeneric,
            "la_disequality" => Self::LaDisequality,
            "la_totality" => Self::LaTotality,
            "la_mult_pos" => Self::LaMultPos,
            "la_mult_neg" => Self::LaMultNeg,
            "lia_generic" => Self::LiaGeneric,
            "forall_inst" => Self::ForallInst,
            "sko_forall" => Self::Skolem,
            "subproof" => Self::Subproof,
            "bind" => Self::Bind,
            "all_simplify" => Self::AllSimplify,
            "bool_simplify" => Self::BoolSimplify,
            "arith_simplify" => Self::ArithSimplify,
            "bv_bitblast" => Self::BvBitblast,
            "read_over_write_pos" => Self::ReadOverWritePos,
            "read_over_write_neg" => Self::ReadOverWriteNeg,
            "extensionality" => Self::Extensionality,
            "fp_to_bv" => Self::FpToBv,
            "string_length" => Self::StringLength,
            "string_decompose" => Self::StringDecompose,
            "string_code_inj" => Self::StringCodeInj,
            "hole" => Self::Hole,
            "drup" => Self::Drup,
            "trust" => Self::Trust,
            _ => {
                return Err(AletheParseError::UnknownRule {
                    name: name.to_string(),
                });
            }
        };
        Ok(rule)
    }

    pub(crate) fn name(&self) -> &str {
        match self {
            Self::True => "true",
            Self::False => "false",
            Self::NotTrue => "not_true",
            Self::NotFalse => "not_false",
            Self::AndType => "and",
            Self::AndPos => "and_pos",
            Self::AndNeg => "and_neg",
            Self::NotAnd => "not_and",
            Self::Or => "or",
            Self::OrPos => "or_pos",
            Self::OrNeg => "or_neg",
            Self::NotOr => "not_or",
            Self::Implies => "implies",
            Self::ImpliesPos => "implies_pos",
            Self::ImpliesNeg1 => "implies_neg1",
            Self::ImpliesNeg2 => "implies_neg2",
            Self::NotImplies1 => "not_implies1",
            Self::NotImplies2 => "not_implies2",
            Self::Equiv => "equiv",
            Self::EquivPos1 => "equiv_pos1",
            Self::EquivPos2 => "equiv_pos2",
            Self::EquivNeg1 => "equiv_neg1",
            Self::EquivNeg2 => "equiv_neg2",
            Self::NotEquiv1 => "not_equiv1",
            Self::NotEquiv2 => "not_equiv2",
            Self::Ite => "ite",
            Self::ItePos1 => "ite_pos1",
            Self::ItePos2 => "ite_pos2",
            Self::IteNeg1 => "ite_neg1",
            Self::IteNeg2 => "ite_neg2",
            Self::NotIte1 => "not_ite1",
            Self::NotIte2 => "not_ite2",
            Self::XorPos1 => "xor_pos1",
            Self::XorPos2 => "xor_pos2",
            Self::XorNeg1 => "xor_neg1",
            Self::XorNeg2 => "xor_neg2",
            Self::Resolution => "resolution",
            Self::ThResolution => "th_resolution",
            Self::Contraction => "contraction",
            Self::Refl => "refl",
            Self::Symm => "symm",
            Self::Trans => "trans",
            Self::Cong => "cong",
            Self::EqReflexive => "eq_reflexive",
            Self::EqTransitive => "eq_transitive",
            Self::EqCongruent => "eq_congruent",
            Self::EqCongruentPred => "eq_congruent_pred",
            Self::LaTautology => "la_tautology",
            Self::LaGeneric => "la_generic",
            Self::LaDisequality => "la_disequality",
            Self::LaTotality => "la_totality",
            Self::LaMultPos => "la_mult_pos",
            Self::LaMultNeg => "la_mult_neg",
            Self::LiaGeneric => "lia_generic",
            Self::ForallInst => "forall_inst",
            Self::Skolem => "sko_forall",
            Self::Subproof => "subproof",
            Self::Bind => "bind",
            Self::AllSimplify => "all_simplify",
            Self::BoolSimplify => "bool_simplify",
            Self::ArithSimplify => "arith_simplify",
            Self::BvBitblast => "bv_bitblast",
            Self::ReadOverWritePos => "read_over_write_pos",
            Self::ReadOverWriteNeg => "read_over_write_neg",
            Self::Extensionality => "extensionality",
            Self::FpToBv => "fp_to_bv",
            Self::StringLength => "string_length",
            Self::StringDecompose => "string_decompose",
            Self::StringCodeInj => "string_code_inj",
            Self::Hole => "hole",
            Self::Drup => "drup",
            Self::Trust => "trust",
            Self::Custom(name) => name,
        }
    }
}

impl std::fmt::Display for AletheRuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SmtTerm {
    Var(String, SmtSort),
    Bool(bool),
    Int(i64),
    Rational(i64, i64),
    BitVec(u64, u32),
    Str(String),
    App(SmtSymbol, Vec<SmtTermId>),
    Not(SmtTermId),
    Ite(SmtTermId, SmtTermId, SmtTermId),
    Let(Vec<(String, SmtTermId)>, SmtTermId),
    Forall(Vec<(String, SmtSort)>, SmtTermId),
    Exists(Vec<(String, SmtSort)>, SmtTermId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SmtTermId(pub(crate) u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SmtSort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    Array(Box<SmtSort>, Box<SmtSort>),
    String,
    Named(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum SmtSymbol {
    Named(String),
    Indexed(String, Vec<u32>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SmtProofStep {
    Assume(SmtTermId),
    Resolution {
        clause: Vec<SmtTermId>,
        premises: Vec<SmtStepId>,
        pivot: Option<SmtTermId>,
    },
    TheoryLemma {
        theory: SmtTheory,
        kind: TheoryLemmaDetail,
        clause: Vec<SmtTermId>,
    },
    Step {
        rule: AletheRuleKind,
        clause: Vec<SmtTermId>,
        premises: Vec<SmtStepId>,
        args: Vec<SmtTermId>,
    },
    Anchor {
        end_step: SmtStepId,
        variables: Vec<(String, SmtSort)>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SmtStepId(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum SmtTheory {
    Core,
    Euf,
    Lra,
    Lia,
    Bv,
    Arrays,
    Fp,
    Strings,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TheoryLemmaDetail {
    EufTransitive,
    EufCongruent,
    EufCongruentPred,
    LraFarkas {
        coefficients: Vec<(i64, i64)>,
    },
    LiaGeneric {
        annotation: LiaDetail,
    },
    BvBitBlast {
        gate_type: Option<String>,
        width: Option<u32>,
    },
    ArraySelectStore {
        index_eq: bool,
    },
    ArrayExtensionality,
    FpToBv {
        operation: String,
    },
    StringLength,
    StringContent,
    StringNormalForm,
    Generic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LiaDetail {
    BoundsGap,
    Divisibility,
    CuttingPlane { divisor: i64 },
    FarkasOnly,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SmtProofDag {
    pub(crate) terms: Vec<SmtTerm>,
    pub(crate) steps: Vec<SmtProofStep>,
    pub(crate) declarations: BTreeMap<String, SmtSort>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum AletheParseError {
    #[error("unexpected token at offset {offset}: expected {expected}, found {found}")]
    UnexpectedToken {
        offset: usize,
        expected: String,
        found: String,
    },
    #[error("unknown rule `{name}`")]
    UnknownRule { name: String },
    #[error("undeclared symbol `{name}`")]
    UndeclaredSymbol { name: String },
    #[error("undefined step id `{name}`")]
    UndefinedStepId { name: String },
    #[error("invalid term: {reason}")]
    InvalidTerm { reason: String },
    #[error("unexpected end of input")]
    Eof,
}

#[derive(Debug, Clone)]
struct FunctionDecl {
    arg_sorts: Vec<SmtSort>,
    return_sort: SmtSort,
}

#[derive(Debug)]
struct PendingAnchor {
    anchor_step: SmtStepId,
    end_step_name: String,
}

#[derive(Debug)]
pub(crate) struct Parser {
    tokens: Vec<SpannedToken>,
    index: usize,
    terms: Vec<SmtTerm>,
    term_sorts: Vec<Option<SmtSort>>,
    steps: Vec<SmtProofStep>,
    declarations: BTreeMap<String, SmtSort>,
    declared_sorts: HashMap<String, u32>,
    functions: HashMap<String, FunctionDecl>,
    step_ids: HashMap<String, SmtStepId>,
    pending_anchors: Vec<PendingAnchor>,
    scopes: Vec<HashMap<String, SmtSort>>,
}

impl Parser {
    fn new(tokens: Vec<SpannedToken>) -> Self {
        Self {
            tokens,
            index: 0,
            terms: Vec::new(),
            term_sorts: Vec::new(),
            steps: Vec::new(),
            declarations: BTreeMap::new(),
            declared_sorts: HashMap::new(),
            functions: HashMap::new(),
            step_ids: HashMap::new(),
            pending_anchors: Vec::new(),
            scopes: Vec::new(),
        }
    }

    fn parse(mut self) -> Result<SmtProofDag, AletheParseError> {
        while self.peek_token().is_some() {
            self.expect_lparen()?;
            let head = self.expect_symbol()?;
            match head.as_str() {
                "declare-fun" => self.parse_declare_fun()?,
                "declare-const" => self.parse_declare_const()?,
                "declare-sort" => self.parse_declare_sort()?,
                "assume" => self.parse_assume()?,
                "step" => self.parse_step()?,
                "anchor" => self.parse_anchor()?,
                _ => {
                    return Err(
                        self.unexpected_here("top-level command", format!("symbol `{head}`"))
                    );
                }
            }
            self.expect_rparen()?;
        }
        self.resolve_pending_anchors()?;
        Ok(SmtProofDag {
            terms: self.terms,
            steps: self.steps,
            declarations: self.declarations,
        })
    }

    fn parse_declare_fun(&mut self) -> Result<(), AletheParseError> {
        let name = self.expect_symbol()?;
        self.expect_lparen()?;
        let mut arg_sorts = Vec::new();
        while !self.next_is_rparen() {
            arg_sorts.push(self.parse_sort()?);
        }
        self.expect_rparen()?;
        let return_sort = self.parse_sort()?;
        self.insert_function(name, arg_sorts, return_sort)
    }

    fn parse_declare_const(&mut self) -> Result<(), AletheParseError> {
        let name = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.insert_function(name, Vec::new(), sort)
    }

    fn parse_declare_sort(&mut self) -> Result<(), AletheParseError> {
        let name = self.expect_symbol()?;
        let arity = self.expect_u32("sort arity")?;
        if self.declared_sorts.insert(name.clone(), arity).is_some() {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("duplicate sort declaration `{name}`"),
            });
        }
        Ok(())
    }

    fn insert_function(
        &mut self,
        name: String,
        arg_sorts: Vec<SmtSort>,
        return_sort: SmtSort,
    ) -> Result<(), AletheParseError> {
        if self.functions.contains_key(&name) {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("duplicate declaration `{name}`"),
            });
        }
        self.declarations.insert(name.clone(), return_sort.clone());
        self.functions.insert(
            name,
            FunctionDecl {
                arg_sorts,
                return_sort,
            },
        );
        Ok(())
    }

    fn parse_assume(&mut self) -> Result<(), AletheParseError> {
        let step_name = self.expect_symbol()?;
        let term = self.parse_term()?;
        let step_id = self.push_step(SmtProofStep::Assume(term));
        self.record_step_id(step_name, step_id)
    }

    fn parse_step(&mut self) -> Result<(), AletheParseError> {
        let step_name = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        let mut rule: Option<AletheRuleKind> = None;
        let mut premises = Vec::new();
        let mut args = Vec::new();
        let mut seen_rule = false;
        let mut seen_premises = false;
        let mut seen_args = false;

        while !self.next_is_rparen() {
            let keyword = self.expect_keyword()?;
            match keyword.as_str() {
                ":rule" => {
                    if seen_rule {
                        return Err(AletheParseError::InvalidTerm {
                            reason: format!("duplicate :rule on step `{step_name}`"),
                        });
                    }
                    seen_rule = true;
                    let rule_name = self.expect_symbol()?;
                    rule = Some(AletheRuleKind::from_name(&rule_name)?);
                }
                ":premises" => {
                    if seen_premises {
                        return Err(AletheParseError::InvalidTerm {
                            reason: format!("duplicate :premises on step `{step_name}`"),
                        });
                    }
                    seen_premises = true;
                    premises = self.parse_premises()?;
                }
                ":args" => {
                    if seen_args {
                        return Err(AletheParseError::InvalidTerm {
                            reason: format!("duplicate :args on step `{step_name}`"),
                        });
                    }
                    seen_args = true;
                    args = self.parse_term_list()?;
                }
                _ => {
                    return Err(self.unexpected_here(
                        ":rule, :premises, or :args",
                        format!("keyword `{keyword}`"),
                    ));
                }
            }
        }

        let rule = rule.ok_or_else(|| AletheParseError::InvalidTerm {
            reason: format!("missing :rule on step `{step_name}`"),
        })?;

        let step = self.build_step(rule, clause, premises, args)?;
        let step_id = self.push_step(step);
        self.record_step_id(step_name, step_id)
    }

    fn parse_anchor(&mut self) -> Result<(), AletheParseError> {
        let keyword = self.expect_keyword()?;
        if keyword != ":step" {
            return Err(self.unexpected_here(":step", format!("keyword `{keyword}`")));
        }
        let end_step_name = self.expect_symbol()?;
        let mut variables = Vec::new();
        let mut seen_args = false;
        while !self.next_is_rparen() {
            let keyword = self.expect_keyword()?;
            match keyword.as_str() {
                ":args" => {
                    if seen_args {
                        return Err(AletheParseError::InvalidTerm {
                            reason: format!("duplicate :args on anchor for `{end_step_name}`"),
                        });
                    }
                    seen_args = true;
                    variables = self.parse_anchor_args()?;
                }
                _ => {
                    return Err(self.unexpected_here(":args", format!("keyword `{keyword}`")));
                }
            }
        }
        let anchor_step = self.push_step(SmtProofStep::Anchor {
            end_step: SmtStepId(u32::MAX),
            variables,
        });
        self.pending_anchors.push(PendingAnchor {
            anchor_step,
            end_step_name,
        });
        Ok(())
    }

    fn build_step(
        &mut self,
        rule: AletheRuleKind,
        clause: Vec<SmtTermId>,
        premises: Vec<SmtStepId>,
        args: Vec<SmtTermId>,
    ) -> Result<SmtProofStep, AletheParseError> {
        if matches!(rule, AletheRuleKind::Resolution) {
            let pivot = args.first().copied();
            return Ok(SmtProofStep::Resolution {
                clause,
                premises,
                pivot,
            });
        }

        if premises.is_empty() {
            match rule {
                AletheRuleKind::EqTransitive => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Euf,
                        kind: TheoryLemmaDetail::EufTransitive,
                        clause,
                    });
                }
                AletheRuleKind::EqCongruent => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Euf,
                        kind: TheoryLemmaDetail::EufCongruent,
                        clause,
                    });
                }
                AletheRuleKind::EqCongruentPred => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Euf,
                        kind: TheoryLemmaDetail::EufCongruentPred,
                        clause,
                    });
                }
                AletheRuleKind::LaGeneric => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Lra,
                        kind: TheoryLemmaDetail::LraFarkas {
                            coefficients: self.parse_coefficients(&args)?,
                        },
                        clause,
                    });
                }
                AletheRuleKind::LiaGeneric => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Lia,
                        kind: TheoryLemmaDetail::LiaGeneric {
                            annotation: self.parse_lia_detail(&args)?,
                        },
                        clause,
                    });
                }
                AletheRuleKind::BvBitblast => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Bv,
                        kind: TheoryLemmaDetail::BvBitBlast {
                            gate_type: None,
                            width: None,
                        },
                        clause,
                    });
                }
                AletheRuleKind::ReadOverWritePos => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Arrays,
                        kind: TheoryLemmaDetail::ArraySelectStore { index_eq: true },
                        clause,
                    });
                }
                AletheRuleKind::ReadOverWriteNeg => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Arrays,
                        kind: TheoryLemmaDetail::ArraySelectStore { index_eq: false },
                        clause,
                    });
                }
                AletheRuleKind::Extensionality => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Arrays,
                        kind: TheoryLemmaDetail::ArrayExtensionality,
                        clause,
                    });
                }
                AletheRuleKind::FpToBv => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Fp,
                        kind: TheoryLemmaDetail::FpToBv {
                            operation: self.parse_fp_operation(&args),
                        },
                        clause,
                    });
                }
                AletheRuleKind::StringLength => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Strings,
                        kind: TheoryLemmaDetail::StringLength,
                        clause,
                    });
                }
                AletheRuleKind::StringDecompose => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Strings,
                        kind: TheoryLemmaDetail::StringContent,
                        clause,
                    });
                }
                AletheRuleKind::StringCodeInj => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: SmtTheory::Strings,
                        kind: TheoryLemmaDetail::StringNormalForm,
                        clause,
                    });
                }
                AletheRuleKind::Trust => {
                    return Ok(SmtProofStep::TheoryLemma {
                        theory: self.infer_theory_from_clause(&clause),
                        kind: TheoryLemmaDetail::Generic,
                        clause,
                    });
                }
                _ => {}
            }
        }

        Ok(SmtProofStep::Step {
            rule,
            clause,
            premises,
            args,
        })
    }

    fn parse_coefficients(&self, args: &[SmtTermId]) -> Result<Vec<(i64, i64)>, AletheParseError> {
        args.iter()
            .map(|arg| {
                self.term_as_rational(*arg)
                    .ok_or_else(|| AletheParseError::InvalidTerm {
                        reason: format!(
                            "expected rational coefficient, found {:?}",
                            self.term(*arg)
                        ),
                    })
            })
            .collect()
    }

    fn parse_lia_detail(&self, args: &[SmtTermId]) -> Result<LiaDetail, AletheParseError> {
        let Some(last) = args.last() else {
            return Ok(LiaDetail::FarkasOnly);
        };
        let Some(symbol) = self.term_as_symbol_name(*last) else {
            return Ok(LiaDetail::FarkasOnly);
        };
        match symbol {
            "bounds_gap" | "BoundsGap" => Ok(LiaDetail::BoundsGap),
            "divisibility" | "Divisibility" => Ok(LiaDetail::Divisibility),
            "cutting_plane" | "CuttingPlane" => {
                if args.len() < 2 {
                    return Err(AletheParseError::InvalidTerm {
                        reason: "cutting_plane annotation requires a divisor".to_string(),
                    });
                }
                let divisor_term = args[args.len() - 2];
                let divisor = self.term_as_i64(divisor_term).ok_or_else(|| {
                    AletheParseError::InvalidTerm {
                        reason: "cutting_plane divisor must be an integer".to_string(),
                    }
                })?;
                Ok(LiaDetail::CuttingPlane { divisor })
            }
            _ => Ok(LiaDetail::FarkasOnly),
        }
    }

    fn parse_fp_operation(&self, args: &[SmtTermId]) -> String {
        args.first()
            .and_then(|arg| self.term_as_symbol_name(*arg))
            .map_or_else(|| "unknown".to_string(), ToString::to_string)
    }

    fn infer_theory_from_clause(&self, clause: &[SmtTermId]) -> SmtTheory {
        let mut has_euf = false;
        let mut has_lra = false;
        let mut has_lia = false;
        for term in clause {
            match self.classify_term_theory(*term) {
                Some(SmtTheory::Strings) => return SmtTheory::Strings,
                Some(SmtTheory::Fp) => return SmtTheory::Fp,
                Some(SmtTheory::Arrays) => return SmtTheory::Arrays,
                Some(SmtTheory::Bv) => return SmtTheory::Bv,
                Some(SmtTheory::Lra) => has_lra = true,
                Some(SmtTheory::Lia) => has_lia = true,
                Some(SmtTheory::Euf) => has_euf = true,
                Some(SmtTheory::Core) | None => {}
            }
        }
        if has_lra {
            SmtTheory::Lra
        } else if has_lia {
            SmtTheory::Lia
        } else if has_euf {
            SmtTheory::Euf
        } else {
            SmtTheory::Core
        }
    }

    fn classify_term_theory(&self, term_id: SmtTermId) -> Option<SmtTheory> {
        match self.term(term_id) {
            SmtTerm::BitVec(_, _) => Some(SmtTheory::Bv),
            SmtTerm::Str(_) => Some(SmtTheory::Strings),
            SmtTerm::Rational(_, _) => Some(SmtTheory::Lra),
            SmtTerm::Int(_) | SmtTerm::Bool(_) => None,
            SmtTerm::Var(_, sort) => self.classify_sort_theory(sort),
            SmtTerm::Not(inner) => self.classify_term_theory(*inner),
            SmtTerm::Ite(c, t, e) => self
                .classify_term_theory(*c)
                .or_else(|| self.classify_term_theory(*t))
                .or_else(|| self.classify_term_theory(*e)),
            SmtTerm::Let(bindings, body) => bindings
                .iter()
                .find_map(|(_, value)| self.classify_term_theory(*value))
                .or_else(|| self.classify_term_theory(*body)),
            SmtTerm::Forall(vars, body) | SmtTerm::Exists(vars, body) => vars
                .iter()
                .find_map(|(_, sort)| self.classify_sort_theory(sort))
                .or_else(|| self.classify_term_theory(*body)),
            SmtTerm::App(symbol, args) => {
                let name = match symbol {
                    SmtSymbol::Named(name) => name.as_str(),
                    SmtSymbol::Indexed(name, _) => name.as_str(),
                };
                if name.starts_with("str.") {
                    return Some(SmtTheory::Strings);
                }
                if name == "select" || name == "store" {
                    return Some(SmtTheory::Arrays);
                }
                if name.starts_with("fp.") || name == "fp" {
                    return Some(SmtTheory::Fp);
                }
                if name.starts_with("bv") || name == "concat" {
                    return Some(SmtTheory::Bv);
                }
                if matches!(name, "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/") {
                    if args.iter().any(|arg| {
                        matches!(self.term_sort(*arg), Some(SmtSort::Real))
                            || matches!(self.term(*arg), SmtTerm::Rational(_, _))
                    }) {
                        return Some(SmtTheory::Lra);
                    }
                    return Some(SmtTheory::Lia);
                }
                args.iter()
                    .find_map(|arg| self.classify_term_theory(*arg))
                    .or(Some(SmtTheory::Euf))
            }
        }
    }

    fn classify_sort_theory(&self, sort: &SmtSort) -> Option<SmtTheory> {
        match sort {
            SmtSort::BitVec(_) => Some(SmtTheory::Bv),
            SmtSort::Array(_, _) => Some(SmtTheory::Arrays),
            SmtSort::String => Some(SmtTheory::Strings),
            SmtSort::Real => Some(SmtTheory::Lra),
            SmtSort::Int => Some(SmtTheory::Lia),
            SmtSort::Bool | SmtSort::Named(_) => None,
        }
    }

    fn parse_premises(&mut self) -> Result<Vec<SmtStepId>, AletheParseError> {
        self.expect_lparen()?;
        let mut premises = Vec::new();
        while !self.next_is_rparen() {
            let name = self.expect_symbol()?;
            let step_id = self
                .step_ids
                .get(&name)
                .copied()
                .ok_or(AletheParseError::UndefinedStepId { name })?;
            premises.push(step_id);
        }
        self.expect_rparen()?;
        Ok(premises)
    }

    fn parse_term_list(&mut self) -> Result<Vec<SmtTermId>, AletheParseError> {
        self.expect_lparen()?;
        let mut terms = Vec::new();
        while !self.next_is_rparen() {
            terms.push(self.parse_term()?);
        }
        self.expect_rparen()?;
        Ok(terms)
    }

    fn parse_anchor_args(&mut self) -> Result<Vec<(String, SmtSort)>, AletheParseError> {
        self.expect_lparen()?;
        let mut variables = Vec::new();
        while !self.next_is_rparen() {
            self.expect_lparen()?;
            let first = self.expect_symbol()?;
            if first == ":=" {
                return Err(AletheParseError::InvalidTerm {
                    reason: "anchor assignments are not supported in this parser".to_string(),
                });
            }
            let sort = self.parse_sort()?;
            self.expect_rparen()?;
            variables.push((first, sort));
        }
        self.expect_rparen()?;
        Ok(variables)
    }

    fn parse_clause(&mut self) -> Result<Vec<SmtTermId>, AletheParseError> {
        self.expect_lparen()?;
        let head = self.expect_symbol()?;
        if head != "cl" {
            return Err(self.unexpected_here("clause `(cl ...)`", format!("symbol `{head}`")));
        }
        let mut clause = Vec::new();
        while !self.next_is_rparen() {
            clause.push(self.parse_term()?);
        }
        self.expect_rparen()?;
        Ok(clause)
    }

    fn parse_sort(&mut self) -> Result<SmtSort, AletheParseError> {
        match self.peek_token() {
            Some(SpannedToken {
                token: Token::Symbol(symbol),
                ..
            }) => {
                let symbol = symbol.clone();
                let _ = self.bump_token();
                match symbol.as_str() {
                    "Bool" => Ok(SmtSort::Bool),
                    "Int" => Ok(SmtSort::Int),
                    "Real" => Ok(SmtSort::Real),
                    "String" => Ok(SmtSort::String),
                    _ => {
                        if self.declared_sorts.contains_key(&symbol) {
                            Ok(SmtSort::Named(symbol))
                        } else {
                            Err(AletheParseError::InvalidTerm {
                                reason: format!("unknown sort `{symbol}`"),
                            })
                        }
                    }
                }
            }
            Some(SpannedToken {
                token: Token::LParen,
                ..
            }) => {
                self.expect_lparen()?;
                let head = self.expect_symbol()?;
                let sort = match head.as_str() {
                    "BitVec" => {
                        let width = self.expect_u32("bitvector width")?;
                        SmtSort::BitVec(width)
                    }
                    "Array" => {
                        let index = self.parse_sort()?;
                        let value = self.parse_sort()?;
                        SmtSort::Array(Box::new(index), Box::new(value))
                    }
                    "_" => {
                        let head = self.expect_symbol()?;
                        if head != "BitVec" {
                            return Err(AletheParseError::InvalidTerm {
                                reason: format!("unsupported indexed sort `(_ {head} ...)`"),
                            });
                        }
                        let width = self.expect_u32("bitvector width")?;
                        SmtSort::BitVec(width)
                    }
                    _ => {
                        return Err(AletheParseError::InvalidTerm {
                            reason: format!("unsupported sort constructor `{head}`"),
                        });
                    }
                };
                self.expect_rparen()?;
                Ok(sort)
            }
            Some(token) => Err(self.unexpected("sort", token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn parse_term(&mut self) -> Result<SmtTermId, AletheParseError> {
        match self.peek_token() {
            Some(SpannedToken {
                token: Token::LParen,
                ..
            }) => {
                self.expect_lparen()?;
                self.parse_paren_term()
            }
            Some(SpannedToken {
                token: Token::String(value),
                ..
            }) => {
                let value = value.clone();
                let _ = self.bump_token();
                Ok(self.push_term(SmtTerm::Str(value), Some(SmtSort::String)))
            }
            Some(SpannedToken {
                token: Token::Symbol(atom),
                ..
            }) => {
                let atom = atom.clone();
                let _ = self.bump_token();
                self.parse_atom_term(&atom)
            }
            Some(token) => Err(self.unexpected("term", token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn parse_paren_term(&mut self) -> Result<SmtTermId, AletheParseError> {
        let Some(token) = self.peek_token().cloned() else {
            return Err(AletheParseError::Eof);
        };
        match token.token {
            Token::Symbol(ref name) if name == "not" => {
                let _ = self.bump_token();
                let inner = self.parse_term()?;
                self.expect_rparen()?;
                Ok(self.push_term(SmtTerm::Not(inner), Some(SmtSort::Bool)))
            }
            Token::Symbol(ref name) if name == "ite" => {
                let _ = self.bump_token();
                let cond = self.parse_term()?;
                let then_branch = self.parse_term()?;
                let else_branch = self.parse_term()?;
                self.expect_rparen()?;
                let sort = match (
                    self.term_sort(cond),
                    self.term_sort(then_branch),
                    self.term_sort(else_branch),
                ) {
                    (Some(SmtSort::Bool), Some(t), Some(e)) if t == e => Some(t.clone()),
                    _ => self.term_sort(then_branch).cloned(),
                };
                Ok(self.push_term(SmtTerm::Ite(cond, then_branch, else_branch), sort))
            }
            Token::Symbol(ref name) if name == "let" => {
                let _ = self.bump_token();
                let bindings = self.parse_let_bindings()?;
                let binding_scope = bindings
                    .iter()
                    .map(|(name, value)| {
                        let sort = self.term_sort(*value).cloned().ok_or_else(|| {
                            AletheParseError::InvalidTerm {
                                reason: format!("unable to infer sort for let binding `{name}`"),
                            }
                        })?;
                        Ok((name.clone(), sort))
                    })
                    .collect::<Result<HashMap<_, _>, AletheParseError>>()?;
                self.scopes.push(binding_scope);
                let body = self.parse_term()?;
                let _ = self.scopes.pop();
                self.expect_rparen()?;
                let sort = self.term_sort(body).cloned();
                Ok(self.push_term(SmtTerm::Let(bindings, body), sort))
            }
            Token::Symbol(ref name) if name == "forall" || name == "exists" => {
                let quantifier = name.clone();
                let _ = self.bump_token();
                let vars = self.parse_sorted_vars()?;
                let scope = vars.iter().cloned().collect::<HashMap<_, _>>();
                self.scopes.push(scope);
                let body = self.parse_term()?;
                let _ = self.scopes.pop();
                self.expect_rparen()?;
                let term = if quantifier == "forall" {
                    SmtTerm::Forall(vars, body)
                } else {
                    SmtTerm::Exists(vars, body)
                };
                Ok(self.push_term(term, Some(SmtSort::Bool)))
            }
            Token::Symbol(ref name) if name == "-" => {
                let _ = self.bump_token();
                let args = self.parse_application_args_until_rparen()?;
                self.make_minus_term(args)
            }
            Token::Symbol(ref name) if name == "/" => {
                let _ = self.bump_token();
                let args = self.parse_application_args_until_rparen()?;
                self.make_division_term(args)
            }
            Token::Symbol(ref name) if name == "_" => {
                let _ = self.bump_token();
                let term = self.parse_underscore_term()?;
                self.expect_rparen()?;
                Ok(term)
            }
            Token::LParen => {
                let head = self.parse_indexed_symbol()?;
                let args = self.parse_application_args_until_rparen()?;
                let sort = self.infer_app_sort(&head, &args)?;
                Ok(self.push_term(SmtTerm::App(head, args), sort))
            }
            Token::Symbol(_) => {
                let head_name = self.expect_symbol()?;
                let head = SmtSymbol::Named(head_name);
                let args = self.parse_application_args_until_rparen()?;
                self.validate_declared_arity(&head, args.len())?;
                let sort = self.infer_app_sort(&head, &args)?;
                Ok(self.push_term(SmtTerm::App(head, args), sort))
            }
            _ => Err(self.unexpected("compound term head", &token)),
        }
    }

    fn parse_let_bindings(&mut self) -> Result<Vec<(String, SmtTermId)>, AletheParseError> {
        self.expect_lparen()?;
        let mut bindings = Vec::new();
        while !self.next_is_rparen() {
            self.expect_lparen()?;
            let name = self.expect_symbol()?;
            let value = self.parse_term()?;
            self.expect_rparen()?;
            bindings.push((name, value));
        }
        self.expect_rparen()?;
        Ok(bindings)
    }

    fn parse_sorted_vars(&mut self) -> Result<Vec<(String, SmtSort)>, AletheParseError> {
        self.expect_lparen()?;
        let mut vars = Vec::new();
        while !self.next_is_rparen() {
            self.expect_lparen()?;
            let name = self.expect_symbol()?;
            let sort = self.parse_sort()?;
            self.expect_rparen()?;
            vars.push((name, sort));
        }
        self.expect_rparen()?;
        Ok(vars)
    }

    fn parse_underscore_term(&mut self) -> Result<SmtTermId, AletheParseError> {
        let name = self.expect_symbol()?;
        let mut indices = Vec::new();
        while !self.next_is_rparen() {
            indices.push(self.expect_u32("index")?);
        }
        if let Some(rest) = name.strip_prefix("bv") {
            if !rest.is_empty() && indices.len() == 1 {
                let value = parse_u64(rest, "bitvector value")?;
                let width = indices[0];
                return Ok(
                    self.push_term(SmtTerm::BitVec(value, width), Some(SmtSort::BitVec(width)))
                );
            }
        }
        let symbol = SmtSymbol::Indexed(name, indices);
        let sort = self.infer_app_sort(&symbol, &[])?;
        Ok(self.push_term(SmtTerm::App(symbol, Vec::new()), sort))
    }

    fn parse_indexed_symbol(&mut self) -> Result<SmtSymbol, AletheParseError> {
        self.expect_lparen()?;
        let underscore = self.expect_symbol()?;
        if underscore != "_" {
            return Err(self.unexpected_here(
                "indexed symbol `(_ name idx...)`",
                format!("symbol `{underscore}`"),
            ));
        }
        let name = self.expect_symbol()?;
        let mut indices = Vec::new();
        while !self.next_is_rparen() {
            indices.push(self.expect_u32("index")?);
        }
        self.expect_rparen()?;
        Ok(SmtSymbol::Indexed(name, indices))
    }

    fn parse_application_args_until_rparen(&mut self) -> Result<Vec<SmtTermId>, AletheParseError> {
        let mut args = Vec::new();
        while !self.next_is_rparen() {
            args.push(self.parse_term()?);
        }
        self.expect_rparen()?;
        Ok(args)
    }

    fn make_minus_term(&mut self, args: Vec<SmtTermId>) -> Result<SmtTermId, AletheParseError> {
        if args.len() == 1 {
            if let Some(value) = self.term_as_i64(args[0]) {
                let negated = value
                    .checked_neg()
                    .ok_or_else(|| AletheParseError::InvalidTerm {
                        reason: "integer literal overflow".to_string(),
                    })?;
                return Ok(self.push_term(SmtTerm::Int(negated), Some(SmtSort::Int)));
            }
            if let Some((numer, denom)) = self.term_as_rational(args[0]) {
                let negated = numer
                    .checked_neg()
                    .ok_or_else(|| AletheParseError::InvalidTerm {
                        reason: "rational literal overflow".to_string(),
                    })?;
                return Ok(self.push_term(SmtTerm::Rational(negated, denom), Some(SmtSort::Real)));
            }
        }
        let head = SmtSymbol::Named("-".to_string());
        let sort = self.infer_app_sort(&head, &args)?;
        Ok(self.push_term(SmtTerm::App(head, args), sort))
    }

    fn make_division_term(&mut self, args: Vec<SmtTermId>) -> Result<SmtTermId, AletheParseError> {
        if args.len() == 2 {
            let lhs = self.term_as_rational(args[0]);
            let rhs = self.term_as_rational(args[1]);
            if let (Some((lhs_num, lhs_den)), Some((rhs_num, rhs_den))) = (lhs, rhs) {
                if rhs_num == 0 {
                    return Err(AletheParseError::InvalidTerm {
                        reason: "division by zero in rational literal".to_string(),
                    });
                }
                let num =
                    lhs_num
                        .checked_mul(rhs_den)
                        .ok_or_else(|| AletheParseError::InvalidTerm {
                            reason: "rational literal overflow".to_string(),
                        })?;
                let den =
                    lhs_den
                        .checked_mul(rhs_num)
                        .ok_or_else(|| AletheParseError::InvalidTerm {
                            reason: "rational literal overflow".to_string(),
                        })?;
                let (num, den) = normalize_rational(num, den)?;
                return Ok(self.push_term(SmtTerm::Rational(num, den), Some(SmtSort::Real)));
            }
        }
        let head = SmtSymbol::Named("/".to_string());
        let sort = self.infer_app_sort(&head, &args)?;
        Ok(self.push_term(SmtTerm::App(head, args), sort))
    }

    fn parse_atom_term(&mut self, atom: &str) -> Result<SmtTermId, AletheParseError> {
        if atom == "true" {
            return Ok(self.push_term(SmtTerm::Bool(true), Some(SmtSort::Bool)));
        }
        if atom == "false" {
            return Ok(self.push_term(SmtTerm::Bool(false), Some(SmtSort::Bool)));
        }
        if let Some((value, width)) = parse_bitvec_atom(atom)? {
            return Ok(self.push_term(SmtTerm::BitVec(value, width), Some(SmtSort::BitVec(width))));
        }
        if let Some(value) = parse_i64_atom(atom)? {
            return Ok(self.push_term(SmtTerm::Int(value), Some(SmtSort::Int)));
        }
        if let Some((numer, denom)) = parse_decimal_atom(atom)? {
            return Ok(self.push_term(SmtTerm::Rational(numer, denom), Some(SmtSort::Real)));
        }

        if let Some(sort) = self.lookup_symbol_sort(atom) {
            return Ok(self.push_term(SmtTerm::Var(atom.to_string(), sort.clone()), Some(sort)));
        }

        Err(AletheParseError::UndeclaredSymbol {
            name: atom.to_string(),
        })
    }

    fn lookup_symbol_sort(&self, name: &str) -> Option<SmtSort> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
            .or_else(|| {
                self.functions.get(name).and_then(|decl| {
                    if decl.arg_sorts.is_empty() {
                        Some(decl.return_sort.clone())
                    } else {
                        None
                    }
                })
            })
    }

    fn validate_declared_arity(
        &self,
        symbol: &SmtSymbol,
        arity: usize,
    ) -> Result<(), AletheParseError> {
        if let SmtSymbol::Named(name) = symbol {
            if let Some(decl) = self.functions.get(name) {
                if decl.arg_sorts.len() != arity {
                    return Err(AletheParseError::InvalidTerm {
                        reason: format!(
                            "symbol `{name}` expects {} arguments, found {arity}",
                            decl.arg_sorts.len()
                        ),
                    });
                }
            }
        }
        Ok(())
    }

    fn infer_app_sort(
        &self,
        symbol: &SmtSymbol,
        args: &[SmtTermId],
    ) -> Result<Option<SmtSort>, AletheParseError> {
        if let SmtSymbol::Named(name) = symbol {
            if let Some(decl) = self.functions.get(name) {
                return Ok(Some(decl.return_sort.clone()));
            }
            match name.as_str() {
                "=" | "distinct" | "<" | "<=" | ">" | ">=" | "and" | "or" | "xor" | "=>"
                | "implies" => return Ok(Some(SmtSort::Bool)),
                "+" | "-" | "*" | "div" | "mod" => {
                    return Ok(self.numeric_result_sort(args));
                }
                "/" => {
                    if args
                        .iter()
                        .any(|arg| matches!(self.term_sort(*arg), Some(SmtSort::Real)))
                        || args
                            .iter()
                            .any(|arg| matches!(self.term(*arg), SmtTerm::Rational(_, _)))
                    {
                        return Ok(Some(SmtSort::Real));
                    }
                    return Ok(Some(SmtSort::Int));
                }
                "select" => {
                    if let Some(SmtSort::Array(_, value)) =
                        args.first().and_then(|arg| self.term_sort(*arg))
                    {
                        return Ok(Some((**value).clone()));
                    }
                }
                "store" => {
                    if let Some(sort) = args.first().and_then(|arg| self.term_sort(*arg)) {
                        return Ok(Some(sort.clone()));
                    }
                }
                "str.++" => return Ok(Some(SmtSort::String)),
                "str.len" | "str.to_code" => return Ok(Some(SmtSort::Int)),
                "str.contains" | "str.prefixof" | "str.suffixof" => {
                    return Ok(Some(SmtSort::Bool));
                }
                "cl" => return Ok(None),
                _ => {}
            }
        }
        if let SmtSymbol::Indexed(name, indices) = symbol {
            if name == "extract" && indices.len() == 2 {
                let high = indices[0];
                let low = indices[1];
                if high < low {
                    return Err(AletheParseError::InvalidTerm {
                        reason: format!("invalid extract indices {high} < {low}"),
                    });
                }
                // Width is `high - low + 1`. `high >= low` guarantees the
                // subtraction cannot underflow, but the `+ 1` overflows when
                // `high - low == u32::MAX` (e.g. `high = u32::MAX, low = 0`),
                // which would abort under `overflow-checks`/`panic=abort` on
                // untrusted proof text. Reject such an out-of-range width
                // gracefully instead of overflowing.
                let width = high
                    .checked_sub(low)
                    .and_then(|span| span.checked_add(1))
                    .ok_or_else(|| AletheParseError::InvalidTerm {
                        reason: format!("extract width out of range for indices {high} {low}"),
                    })?;
                return Ok(Some(SmtSort::BitVec(width)));
            }
        }
        Ok(None)
    }

    fn numeric_result_sort(&self, args: &[SmtTermId]) -> Option<SmtSort> {
        if args
            .iter()
            .any(|arg| matches!(self.term_sort(*arg), Some(SmtSort::Real)))
            || args
                .iter()
                .any(|arg| matches!(self.term(*arg), SmtTerm::Rational(_, _)))
        {
            Some(SmtSort::Real)
        } else if args
            .iter()
            .all(|arg| matches!(self.term_sort(*arg), Some(SmtSort::Int)))
        {
            Some(SmtSort::Int)
        } else {
            None
        }
    }

    fn resolve_pending_anchors(&mut self) -> Result<(), AletheParseError> {
        for pending in &self.pending_anchors {
            let end_step = self
                .step_ids
                .get(&pending.end_step_name)
                .copied()
                .ok_or_else(|| AletheParseError::UndefinedStepId {
                    name: pending.end_step_name.clone(),
                })?;
            let step = self
                .steps
                .get_mut(pending.anchor_step.0 as usize)
                .ok_or_else(|| AletheParseError::InvalidTerm {
                    reason: format!(
                        "internal error: missing anchor step {}",
                        pending.anchor_step.0
                    ),
                })?;
            match step {
                SmtProofStep::Anchor { end_step: slot, .. } => *slot = end_step,
                _ => {
                    return Err(AletheParseError::InvalidTerm {
                        reason: "internal error: anchor fixup pointed to non-anchor step"
                            .to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    fn record_step_id(&mut self, name: String, step_id: SmtStepId) -> Result<(), AletheParseError> {
        if self.step_ids.insert(name.clone(), step_id).is_some() {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("duplicate step id `{name}`"),
            });
        }
        Ok(())
    }

    fn push_term(&mut self, term: SmtTerm, sort: Option<SmtSort>) -> SmtTermId {
        let term_id = SmtTermId(self.terms.len() as u32);
        self.terms.push(term);
        self.term_sorts.push(sort);
        term_id
    }

    fn push_step(&mut self, step: SmtProofStep) -> SmtStepId {
        let step_id = SmtStepId(self.steps.len() as u32);
        self.steps.push(step);
        step_id
    }

    fn term(&self, term_id: SmtTermId) -> &SmtTerm {
        &self.terms[term_id.0 as usize]
    }

    fn term_sort(&self, term_id: SmtTermId) -> Option<&SmtSort> {
        self.term_sorts
            .get(term_id.0 as usize)
            .and_then(Option::as_ref)
    }

    fn term_as_i64(&self, term_id: SmtTermId) -> Option<i64> {
        match self.term(term_id) {
            SmtTerm::Int(value) => Some(*value),
            _ => None,
        }
    }

    fn term_as_rational(&self, term_id: SmtTermId) -> Option<(i64, i64)> {
        match self.term(term_id) {
            SmtTerm::Int(value) => Some((*value, 1)),
            SmtTerm::Rational(numer, denom) => Some((*numer, *denom)),
            _ => None,
        }
    }

    fn term_as_symbol_name(&self, term_id: SmtTermId) -> Option<&str> {
        match self.term(term_id) {
            SmtTerm::Var(name, _) => Some(name.as_str()),
            SmtTerm::App(SmtSymbol::Named(name), args) if args.is_empty() => Some(name.as_str()),
            _ => None,
        }
    }

    fn next_is_rparen(&self) -> bool {
        matches!(
            self.peek_token(),
            Some(SpannedToken {
                token: Token::RParen,
                ..
            })
        )
    }

    fn peek_token(&self) -> Option<&SpannedToken> {
        self.tokens.get(self.index)
    }

    fn bump_token(&mut self) -> Option<SpannedToken> {
        let token = self.tokens.get(self.index).cloned()?;
        self.index += 1;
        Some(token)
    }

    fn expect_lparen(&mut self) -> Result<(), AletheParseError> {
        match self.bump_token() {
            Some(SpannedToken {
                token: Token::LParen,
                ..
            }) => Ok(()),
            Some(token) => Err(self.unexpected("`(`", &token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn expect_rparen(&mut self) -> Result<(), AletheParseError> {
        match self.bump_token() {
            Some(SpannedToken {
                token: Token::RParen,
                ..
            }) => Ok(()),
            Some(token) => Err(self.unexpected("`)`", &token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn expect_symbol(&mut self) -> Result<String, AletheParseError> {
        match self.bump_token() {
            Some(SpannedToken {
                token: Token::Symbol(symbol),
                ..
            }) => Ok(symbol),
            Some(token) => Err(self.unexpected("symbol", &token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn expect_keyword(&mut self) -> Result<String, AletheParseError> {
        match self.bump_token() {
            Some(SpannedToken {
                token: Token::Keyword(keyword),
                ..
            }) => Ok(keyword),
            Some(token) => Err(self.unexpected("keyword", &token)),
            None => Err(AletheParseError::Eof),
        }
    }

    fn expect_u32(&mut self, what: &str) -> Result<u32, AletheParseError> {
        let token = self.expect_symbol()?;
        parse_u32(&token, what)
    }

    fn unexpected(&self, expected: &str, found: &SpannedToken) -> AletheParseError {
        AletheParseError::UnexpectedToken {
            offset: found.offset,
            expected: expected.to_string(),
            found: describe_token(&found.token),
        }
    }

    fn unexpected_here(&self, expected: &str, found: String) -> AletheParseError {
        let offset = self
            .peek_token()
            .map_or(self.current_offset(), |token| token.offset);
        AletheParseError::UnexpectedToken {
            offset,
            expected: expected.to_string(),
            found,
        }
    }

    fn current_offset(&self) -> usize {
        self.tokens.last().map_or(0, |token| token.offset + 1)
    }
}

pub(crate) fn parse_alethe(input: &str) -> Result<SmtProofDag, AletheParseError> {
    let tokens = Tokenizer::new(input).tokenize()?;
    Parser::new(tokens).parse()
}

fn describe_token(token: &Token) -> String {
    match token {
        Token::LParen => "`(`".to_string(),
        Token::RParen => "`)`".to_string(),
        Token::Keyword(keyword) => format!("keyword `{keyword}`"),
        Token::Symbol(symbol) => format!("symbol `{symbol}`"),
        Token::String(string) => format!("string literal \"{string}\""),
    }
}

fn parse_u32(value: &str, what: &str) -> Result<u32, AletheParseError> {
    value
        .parse::<u32>()
        .map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid {what} `{value}`"),
        })
}

fn parse_u64(value: &str, what: &str) -> Result<u64, AletheParseError> {
    value
        .parse::<u64>()
        .map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid {what} `{value}`"),
        })
}

fn parse_i64_atom(atom: &str) -> Result<Option<i64>, AletheParseError> {
    if atom.is_empty() || atom.contains('.') {
        return Ok(None);
    }
    if atom == "+" || atom == "-" {
        return Ok(None);
    }
    if atom
        .chars()
        .enumerate()
        .all(|(index, ch)| ch.is_ascii_digit() || ((ch == '+' || ch == '-') && index == 0))
    {
        let value = atom
            .parse::<i64>()
            .map_err(|_| AletheParseError::InvalidTerm {
                reason: format!("invalid integer literal `{atom}`"),
            })?;
        Ok(Some(value))
    } else {
        Ok(None)
    }
}

fn parse_decimal_atom(atom: &str) -> Result<Option<(i64, i64)>, AletheParseError> {
    if !atom.contains('.') {
        return Ok(None);
    }
    let (sign, digits) = if let Some(rest) = atom.strip_prefix('-') {
        (-1_i64, rest)
    } else if let Some(rest) = atom.strip_prefix('+') {
        (1_i64, rest)
    } else {
        (1_i64, atom)
    };
    let Some((whole, frac)) = digits.split_once('.') else {
        return Ok(None);
    };
    if whole.is_empty() || frac.is_empty() {
        return Ok(None);
    }
    if !(whole.chars().all(|ch| ch.is_ascii_digit()) && frac.chars().all(|ch| ch.is_ascii_digit()))
    {
        return Ok(None);
    }
    let whole_value = whole
        .parse::<i64>()
        .map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid decimal literal `{atom}`"),
        })?;
    let frac_value = frac
        .parse::<i64>()
        .map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid decimal literal `{atom}`"),
        })?;
    let denom =
        10_i64
            .checked_pow(frac.len() as u32)
            .ok_or_else(|| AletheParseError::InvalidTerm {
                reason: format!("decimal literal `{atom}` is too precise"),
            })?;
    let numer = whole_value
        .checked_mul(denom)
        .and_then(|lhs| lhs.checked_add(frac_value))
        .ok_or_else(|| AletheParseError::InvalidTerm {
            reason: format!("decimal literal `{atom}` overflowed i64"),
        })?;
    let numer = numer
        .checked_mul(sign)
        .ok_or_else(|| AletheParseError::InvalidTerm {
            reason: format!("decimal literal `{atom}` overflowed i64"),
        })?;
    Ok(Some(normalize_rational(numer, denom)?))
}

fn parse_bitvec_atom(atom: &str) -> Result<Option<(u64, u32)>, AletheParseError> {
    if let Some(bits) = atom.strip_prefix("#b") {
        if bits.is_empty() || !bits.chars().all(|ch| ch == '0' || ch == '1') {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("invalid bitvector literal `{atom}`"),
            });
        }
        if bits.len() > 64 {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("bitvector literal `{atom}` exceeds 64 bits"),
            });
        }
        let value = u64::from_str_radix(bits, 2).map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid bitvector literal `{atom}`"),
        })?;
        return Ok(Some((value, bits.len() as u32)));
    }
    if let Some(hex) = atom.strip_prefix("#x") {
        if hex.is_empty() || !hex.chars().all(|ch| ch.is_ascii_hexdigit()) {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("invalid bitvector literal `{atom}`"),
            });
        }
        if hex.len() > 16 {
            return Err(AletheParseError::InvalidTerm {
                reason: format!("bitvector literal `{atom}` exceeds 64 bits"),
            });
        }
        let value = u64::from_str_radix(hex, 16).map_err(|_| AletheParseError::InvalidTerm {
            reason: format!("invalid bitvector literal `{atom}`"),
        })?;
        return Ok(Some((value, (hex.len() as u32) * 4)));
    }
    Ok(None)
}

fn normalize_rational(numer: i64, denom: i64) -> Result<(i64, i64), AletheParseError> {
    if denom == 0 {
        return Err(AletheParseError::InvalidTerm {
            reason: "rational literal has zero denominator".to_string(),
        });
    }
    let (mut numer, mut denom) = (numer, denom);
    if denom < 0 {
        numer = numer
            .checked_neg()
            .ok_or_else(|| AletheParseError::InvalidTerm {
                reason: "rational literal overflow".to_string(),
            })?;
        denom = denom
            .checked_neg()
            .ok_or_else(|| AletheParseError::InvalidTerm {
                reason: "rational literal overflow".to_string(),
            })?;
    }
    let gcd = gcd_i64(numer, denom);
    Ok((numer / gcd, denom / gcd))
}

fn gcd_i64(lhs: i64, rhs: i64) -> i64 {
    let mut lhs = i128::from(lhs).abs();
    let mut rhs = i128::from(rhs).abs();
    if lhs == 0 && rhs == 0 {
        return 1;
    }
    while rhs != 0 {
        let tmp = lhs % rhs;
        lhs = rhs;
        rhs = tmp;
    }
    lhs as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(dag: &SmtProofDag, id: SmtTermId) -> &SmtTerm {
        &dag.terms[id.0 as usize]
    }

    #[test]
    fn parses_basic_declarations_and_resolution() {
        let input = r#"
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-const a U)
            (declare-const p Bool)
            (assume h1 p)
            (step t1 (cl (not p)) :rule trust)
            (step t2 (cl) :rule resolution :premises (h1 t1))
        "#;

        let dag = parse_alethe(input).expect("basic proof should parse");
        assert_eq!(
            dag.declarations.get("a"),
            Some(&SmtSort::Named("U".to_string()))
        );
        assert_eq!(
            dag.declarations.get("f"),
            Some(&SmtSort::Named("U".to_string()))
        );
        assert_eq!(dag.declarations.get("p"), Some(&SmtSort::Bool));
        assert_eq!(dag.steps.len(), 3);

        match &dag.steps[0] {
            SmtProofStep::Assume(term_id) => {
                assert_eq!(
                    term(&dag, *term_id),
                    &SmtTerm::Var("p".to_string(), SmtSort::Bool)
                );
            }
            other => panic!("expected assume, found {other:?}"),
        }

        match &dag.steps[2] {
            SmtProofStep::Resolution {
                clause,
                premises,
                pivot,
            } => {
                assert!(clause.is_empty());
                assert_eq!(premises, &vec![SmtStepId(0), SmtStepId(1)]);
                assert_eq!(*pivot, None);
            }
            other => panic!("expected resolution, found {other:?}"),
        }
    }

    #[test]
    fn parses_eq_transitive_as_theory_lemma() {
        let input = r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-const c U)
            (step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
        "#;

        let dag = parse_alethe(input).expect("eq_transitive proof should parse");
        assert_eq!(dag.steps.len(), 1);
        match &dag.steps[0] {
            SmtProofStep::TheoryLemma {
                theory,
                kind,
                clause,
            } => {
                assert_eq!(*theory, SmtTheory::Euf);
                assert_eq!(*kind, TheoryLemmaDetail::EufTransitive);
                assert_eq!(clause.len(), 3);
            }
            other => panic!("expected EUF theory lemma, found {other:?}"),
        }
    }

    #[test]
    fn parses_lra_and_lia_theory_steps() {
        let input = r#"
            (declare-const x Real)
            (declare-const y Int)
            (step lra1 (cl (> x 0.0) (<= x 0.0)) :rule la_generic :args (1.0 1.0))
            (step lia1 (cl (>= y 10) (<= y 5)) :rule lia_generic :args (1 1))
        "#;

        let dag = parse_alethe(input).expect("arithmetic proof should parse");
        assert_eq!(dag.steps.len(), 2);

        match &dag.steps[0] {
            SmtProofStep::TheoryLemma {
                theory,
                kind: TheoryLemmaDetail::LraFarkas { coefficients },
                clause,
            } => {
                assert_eq!(*theory, SmtTheory::Lra);
                assert_eq!(coefficients, &vec![(1, 1), (1, 1)]);
                assert_eq!(clause.len(), 2);
            }
            other => panic!("expected LRA lemma, found {other:?}"),
        }

        match &dag.steps[1] {
            SmtProofStep::TheoryLemma {
                theory,
                kind: TheoryLemmaDetail::LiaGeneric { annotation },
                clause,
            } => {
                assert_eq!(*theory, SmtTheory::Lia);
                assert_eq!(*annotation, LiaDetail::FarkasOnly);
                assert_eq!(clause.len(), 2);
            }
            other => panic!("expected LIA lemma, found {other:?}"),
        }
    }

    #[test]
    fn parses_complex_terms_and_sorts() {
        let input = r#"
            (declare-sort U 0)
            (declare-const flag Bool)
            (declare-const bv8 (_ BitVec 8))
            (declare-const s String)
            (declare-fun p (Int) Bool)
            (declare-fun q (U) Bool)
            (assume h1 (let ((z 5) (w (- (/ 3.0 2.0))))
                         (ite flag (p z) (not (p (- 3))))))
            (assume h2 (forall ((u U) (n Int))
                         (exists ((m Int)) (q u))))
            (assume h3 (= bv8 #b10101010))
            (assume h4 (= s "hi ""there"""))
        "#;

        let dag = parse_alethe(input).expect("rich term proof should parse");
        assert_eq!(dag.steps.len(), 4);
        assert_eq!(dag.declarations.get("bv8"), Some(&SmtSort::BitVec(8)));
        assert_eq!(dag.declarations.get("s"), Some(&SmtSort::String));

        match &dag.steps[0] {
            SmtProofStep::Assume(term_id) => match term(&dag, *term_id) {
                SmtTerm::Let(bindings, body) => {
                    assert_eq!(bindings.len(), 2);
                    match term(&dag, *body) {
                        SmtTerm::Ite(cond, then_branch, else_branch) => {
                            assert_eq!(
                                term(&dag, *cond),
                                &SmtTerm::Var("flag".to_string(), SmtSort::Bool)
                            );
                            assert!(matches!(term(&dag, *then_branch), SmtTerm::App(_, _)));
                            assert!(matches!(term(&dag, *else_branch), SmtTerm::Not(_)));
                        }
                        other => panic!("expected ite body, found {other:?}"),
                    }
                }
                other => panic!("expected let term, found {other:?}"),
            },
            other => panic!("expected assume, found {other:?}"),
        }

        match &dag.steps[1] {
            SmtProofStep::Assume(term_id) => match term(&dag, *term_id) {
                SmtTerm::Forall(vars, body) => {
                    assert_eq!(vars.len(), 2);
                    assert!(matches!(term(&dag, *body), SmtTerm::Exists(_, _)));
                }
                other => panic!("expected forall term, found {other:?}"),
            },
            other => panic!("expected assume, found {other:?}"),
        }

        match &dag.steps[2] {
            SmtProofStep::Assume(term_id) => match term(&dag, *term_id) {
                SmtTerm::App(SmtSymbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    assert_eq!(args.len(), 2);
                    assert_eq!(term(&dag, args[1]), &SmtTerm::BitVec(0b1010_1010, 8));
                }
                other => panic!("expected equality term, found {other:?}"),
            },
            other => panic!("expected assume, found {other:?}"),
        }

        match &dag.steps[3] {
            SmtProofStep::Assume(term_id) => match term(&dag, *term_id) {
                SmtTerm::App(SmtSymbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    assert_eq!(
                        term(&dag, args[1]),
                        &SmtTerm::Str("hi \"there\"".to_string())
                    );
                }
                other => panic!("expected equality term, found {other:?}"),
            },
            other => panic!("expected assume, found {other:?}"),
        }
    }

    #[test]
    fn parses_anchor_with_future_end_step() {
        let input = r#"
            (declare-const p Bool)
            (anchor :step t3 :args ((x Int) (flag Bool)))
            (step t3.t1 (cl p) :rule trust)
            (step t3.t2 (cl (not p) p) :rule or)
            (step t3 (cl p) :rule subproof :premises (t3.t1 t3.t2))
        "#;

        let dag = parse_alethe(input).expect("subproof should parse");
        assert_eq!(dag.steps.len(), 4);

        match &dag.steps[0] {
            SmtProofStep::Anchor {
                end_step,
                variables,
            } => {
                assert_eq!(*end_step, SmtStepId(3));
                assert_eq!(
                    variables,
                    &vec![
                        ("x".to_string(), SmtSort::Int),
                        ("flag".to_string(), SmtSort::Bool),
                    ]
                );
            }
            other => panic!("expected anchor, found {other:?}"),
        }

        match &dag.steps[3] {
            SmtProofStep::Step { premises, .. } => {
                assert_eq!(premises, &vec![SmtStepId(1), SmtStepId(2)]);
            }
            other => panic!("expected subproof step, found {other:?}"),
        }
    }

    #[test]
    fn rejects_unknown_rule_and_missing_premise() {
        let unknown_rule = r#"
            (step t1 (cl) :rule made_up_rule)
        "#;
        assert!(matches!(
            parse_alethe(unknown_rule),
            Err(AletheParseError::UnknownRule { name }) if name == "made_up_rule"
        ));

        let missing_premise = r#"
            (declare-const p Bool)
            (step t1 (cl p) :rule or :premises (h1))
        "#;
        assert!(matches!(
            parse_alethe(missing_premise),
            Err(AletheParseError::UndefinedStepId { name }) if name == "h1"
        ));
    }

    #[test]
    fn rejects_extract_width_overflow_without_panicking() {
        // Regression: `(_ extract <hi> <lo>)` computed `hi - lo + 1` on `u32`
        // without an overflow guard. With `hi = u32::MAX` and `lo = 0` the
        // `hi < lo` check passes and `hi - lo + 1` overflows, aborting under
        // `overflow-checks`/`panic=abort` on untrusted Alethe proof text.
        let input = "(declare-const x (_ BitVec 8))\n(assume h1 ((_ extract 4294967295 0) x))\n";
        // Must return a graceful parse error, not panic.
        let result = parse_alethe(input);
        assert!(
            matches!(result, Err(AletheParseError::InvalidTerm { .. })),
            "expected graceful InvalidTerm error, got {result:?}"
        );
    }

    #[test]
    fn extract_normal_indices_parse_successfully() {
        // Correct-path behavior must be unchanged: an in-range extract such as
        // `(_ extract 7 0)` (width 7 - 0 + 1 = 8) still parses without error.
        // The width `high - low + 1` is computed inside `infer_app_sort` during
        // this parse, so a successful parse exercises the fixed arithmetic on
        // the correct path.
        let input = "(declare-const x (_ BitVec 8))\n(assume h1 (= ((_ extract 7 0) x) x))\n";
        let dag = parse_alethe(input).expect("normal extract should parse");
        assert!(matches!(&dag.steps[0], SmtProofStep::Assume(_)));
    }

    #[test]
    fn extract_max_span_width_is_rejected_not_panicking() {
        // Boundary: `high - low == u32::MAX` (e.g. high = u32::MAX, low = 0)
        // is the exact input where `+ 1` overflows. It must be rejected
        // gracefully rather than aborting.
        let input = "(declare-const x (_ BitVec 8))\n(assume h1 ((_ extract 4294967295 0) x))\n";
        assert!(matches!(
            parse_alethe(input),
            Err(AletheParseError::InvalidTerm { .. })
        ));
    }
}
