// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! The executable's verdict text, rendered from what a re-admitted case theorem
//! states. `KCheckLabelledMain.lean` prints each case's verdict with
//! `outcomeText`, `probeText`, `boolText`, `framesText`, `decodeBoolText` or
//! `runText`, and a refusal or decode error by its derived `Repr` with every
//! `KCheck.` removed. `VerdictText::verdict` renders the value `v` of a theorem
//! `run_<case> = v` the same way, so the test compares each line of
//! `expected_output.txt` in full with the verdict its theorem states, not only its
//! `accepted`/`refused` head. Every value is read in weak head normal form by
//! Clean's kernel over the re-admitted environment, and any shape those printers
//! do not cover (a name Lean would escape, a family with no printer) is refused by
//! name rather than guessed.

use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Literal, TypeChecker};

type Rendered = Result<String, String>;

pub(super) struct VerdictText<'env> {
    env: &'env Environment,
    checker: TypeChecker<'env>,
}

/// A name component `Name.toString` prints as it is.
fn plain_identifier(component: &str) -> bool {
    let mut chars = component.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

impl<'env> VerdictText<'env> {
    pub(super) fn new(env: &'env Environment) -> Self {
        Self {
            env,
            checker: TypeChecker::new(env),
        }
    }

    /// The head constant of `e`'s weak head normal form and its arguments.
    fn head(&self, e: &Expr) -> Result<(String, Vec<Expr>), String> {
        let whnf = self.checker.whnf(e);
        let ExprKind::Const(head, _) = whnf.get_app_fn().kind() else {
            return Err(format!("not headed by a constant: {whnf}"));
        };
        let args = whnf.get_app_args();
        Ok((
            head.to_string(),
            args.iter().map(|arg| (**arg).clone()).collect(),
        ))
    }

    /// `e` in weak head normal form as a constructor application: the
    /// constructor's name and its fields (the arguments after the parameters).
    pub(super) fn constructor(&self, e: &Expr) -> Result<(String, Vec<Expr>), String> {
        let (head, mut args) = self.head(e)?;
        let info = self
            .env
            .get_constructor(&clean_kernel::Name::from_string(&head))
            .ok_or_else(|| format!("{head} is not a constructor"))?;
        let params = info.num_params as usize;
        if args.len() != params + info.num_fields as usize {
            return Err(format!("{head} applied to {} arguments", args.len()));
        }
        Ok((head, args.split_off(params)))
    }

    fn nat(&self, e: &Expr) -> Rendered {
        let whnf = self.checker.whnf(e);
        if let ExprKind::Lit(Literal::Nat(n)) = whnf.kind() {
            return Ok(n.to_string());
        }
        match self.constructor(&whnf)? {
            (ctor, fields) if ctor == "Nat.zero" && fields.is_empty() => Ok("0".to_owned()),
            (ctor, _) => Err(format!("not a numeral: {ctor}")),
        }
    }

    pub(super) fn string(&self, e: &Expr) -> Rendered {
        let whnf = self.checker.whnf(e);
        match whnf.kind() {
            ExprKind::Lit(Literal::String(s)) => Ok(s.to_string()),
            _ => Err(format!("not a string literal: {whnf}")),
        }
    }

    fn boolean(&self, e: &Expr) -> Rendered {
        match self.constructor(e)? {
            (ctor, fields) if ctor == "Bool.true" && fields.is_empty() => Ok("true".to_owned()),
            (ctor, fields) if ctor == "Bool.false" && fields.is_empty() => Ok("false".to_owned()),
            (ctor, _) => Err(format!("not a Bool: {ctor}")),
        }
    }

    /// `Name.toString` of a name of string components, each printed unescaped.
    fn name(&self, e: &Expr) -> Rendered {
        let mut components = Vec::new();
        let mut cursor = e.clone();
        loop {
            let (ctor, fields) = self.constructor(&cursor)?;
            match (ctor.as_str(), fields.as_slice()) {
                ("Lean.Name.anonymous", []) => break,
                ("Lean.Name.str", [prefix, component]) => {
                    components.push(self.string(component)?);
                    cursor = prefix.clone();
                }
                _ => return Err(format!("not a name of string components: {ctor}")),
            }
        }
        if components.is_empty() {
            return Err("the anonymous name".to_owned());
        }
        components.reverse();
        if let Some(escaped) = components.iter().find(|c| !plain_identifier(c)) {
            return Err(format!(
                "Name.toString would escape the component {escaped:?}"
            ));
        }
        Ok(components.join("."))
    }

    pub(super) fn pair(&self, e: &Expr) -> Result<(Expr, Expr), String> {
        match self.constructor(e)? {
            (ctor, fields) if ctor == "Prod.mk" => {
                let [first, second] = <[Expr; 2]>::try_from(fields)
                    .map_err(|_| "Prod.mk has two fields".to_owned())?;
                Ok((first, second))
            }
            (ctor, _) => Err(format!("not a pair: {ctor}")),
        }
    }

    pub(super) fn list(&self, e: &Expr) -> Result<Vec<Expr>, String> {
        let mut items = Vec::new();
        let mut cursor = e.clone();
        loop {
            let (ctor, fields) = self.constructor(&cursor)?;
            match (ctor.as_str(), fields.as_slice()) {
                ("List.nil", []) => return Ok(items),
                ("List.cons", [item, tail]) => {
                    items.push(item.clone());
                    cursor = tail.clone();
                }
                _ => return Err(format!("not a list: {ctor}")),
            }
        }
    }

    /// `reportText`: the base, then the offsets as `ToString (List (Nat × Nat))`.
    fn report(&self, e: &Expr) -> Rendered {
        let (ctor, fields) = self.constructor(e)?;
        let ("KCheckSpec.Report.mk", [base, offsets]) = (ctor.as_str(), fields.as_slice()) else {
            return Err(format!("not a report: {ctor}"));
        };
        let offsets = self
            .list(offsets)?
            .iter()
            .map(|entry| {
                let (parameter, offset) = self.pair(entry)?;
                Ok(format!(
                    "({}, {})",
                    self.nat(&parameter)?,
                    self.nat(&offset)?
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        Ok(format!("{} [{}]", self.nat(base)?, offsets.join(", ")))
    }

    /// A receipt's summary as `outcomeText` and `runText` print it.
    fn receipt(&self, e: &Expr) -> Rendered {
        let (name, bound) = self.pair(e)?;
        Ok(format!(
            "{} bound {}",
            self.name(&name)?,
            self.report(&bound)?
        ))
    }

    /// The derived `Repr` of a refusal or a decode error, at the top
    /// (precedence 0) or as a constructor's argument (`max_prec`, where every
    /// constructor, nullary or not, is parenthesised).
    fn repr(&self, e: &Expr, argument: bool) -> Rendered {
        let whnf = self.checker.whnf(e);
        if let ExprKind::Lit(Literal::Nat(n)) = whnf.kind() {
            return Ok(n.to_string());
        }
        let (head, _) = self.head(&whnf)?;
        let family = self
            .env
            .get_constructor(&clean_kernel::Name::from_string(&head))
            .ok_or_else(|| format!("{head} is not a constructor"))?
            .inductive_name
            .to_string();
        match family.as_str() {
            "Nat" => return self.nat(&whnf),
            "Lean.Name" => return Ok(format!("`{}", self.name(&whnf)?)),
            "KCheck.Refusal" | "KCheck.DecodeError" | "KCheck.Site" | "KCheck.Token" => {}
            other => return Err(format!("no Repr printer for a value of {other}")),
        }
        let (ctor, fields) = self.constructor(&whnf)?;
        let mut text = ctor;
        for field in &fields {
            text.push(' ');
            text.push_str(&self.repr(field, true)?);
        }
        Ok(if argument { format!("({text})") } else { text })
    }

    /// The text after `accepted ` for a verdict `Except.ok value` of type `ty`.
    fn accepted(&self, ty: &Expr, value: &Expr) -> Rendered {
        let (family, args) = self.head(ty)?;
        match (family.as_str(), args.as_slice()) {
            ("Prod", [_, _]) => self.receipt(value),
            ("KCheckSpec.Report", []) => Ok(format!("report {}", self.report(value)?)),
            ("Bool", []) => self.boolean(value),
            ("List", [element]) => {
                let items = self.list(value)?;
                match self.head(element)?.0.as_str() {
                    "Nat" => Ok(format!(
                        "frames [{}]",
                        items
                            .iter()
                            .map(|item| self.nat(item))
                            .collect::<Result<Vec<_>, String>>()?
                            .join(", ")
                    )),
                    "Prod" => Ok(format!(
                        "receipts {}",
                        items
                            .iter()
                            .map(|item| self.receipt(item))
                            .collect::<Result<Vec<_>, String>>()?
                            .join(", ")
                    )),
                    other => Err(format!("no printer for an accepted list of {other}")),
                }
            }
            (other, _) => Err(format!("no printer for an accepted {other}")),
        }
    }

    /// The verdict text the executable prints for a run whose value is `value`.
    pub(super) fn verdict(&self, value: &Expr) -> Rendered {
        let (head, args) = self.head(value)?;
        match (head.as_str(), args.as_slice()) {
            ("Except.ok", [_, ty, ok]) => Ok(format!("accepted {}", self.accepted(ty, ok)?)),
            ("Except.error", [_, _, error]) => Ok(format!(
                "refused {}",
                self.repr(error, false)?.replace("KCheck.", "")
            )),
            _ => Err(format!(
                "not an Except verdict: {head} applied to {} arguments",
                args.len()
            )),
        }
    }
}
