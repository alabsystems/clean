// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Crystal E4: String literal expansion in the typed target
//! (`KernelAcceptsTcIn.lit_string_expand` / `TypingTcIn.lit_string_expand`).
//!
//! The deployed `string_lit_to_constructor` (`clean-kernel/src/tc/reduction/nat.rs`)
//! rewrites `Literal::String(s)` to
//! `String.ofList (List.cons.{0} Char (Char.ofNat c1) (... (List.nil.{0} Char)))`,
//! one `Char.ofNat` of a raw `Nat` literal per Unicode scalar value of `s`, in
//! order. Three branches call it, each only when `string_literal_admitted()`
//! holds (`tc/fold_admission.rs`: `Nat` is canonical and so are `String.ofList`
//! and `Char.ofNat`, by δ-closure digest against the kernel's pin table):
//! `try_string_lit_expansion_core` (a literal against a constant-headed
//! application: `is_def_eq(whnf(expansion), s)`), `try_iota_reduction` (a
//! literal major, expanded and whnf'd before rule lookup) and
//! `reduce_proj_with_mode` (a literal projection subject, expanded and whnf'd).
//!
//! The model states the expansion itself as ONE rule of both families, keyed on
//! the literal's decoded payload (`literal_string_codec`: the payload IS the
//! character list, through a bijection proved both ways) and on the admission
//! fact `StringLitAdmitIn R`: `R` holds the canonical `String.ofList` and
//! `Char.ofNat` records and the canonical `String.mk` constructor entry,
//! reflected at registration from the deployed default prelude
//! (`Environment::with_prelude`), where the kernel's pin table admits them
//! (checked at registration: a prelude whose heads the table refuses refuses
//! this stage). The three deployed branches are then DERIVED: the expansion is
//! the rule, whnf is a conversion of the same family, and the recursor spine /
//! projection carries it by `app_cong` / `proj_cong`.
//!
//! WORLD, stated. The admission constructor pins the clean-prelude world's
//! bodies (`String.ofList := fun d => String.mk d` over the `List Char`
//! structure, `Char.ofNat` by `dite` on `Nat.isValidChar`). The kernel's pin
//! table also admits Lean 4.30's `Init` (`String.ofList` building
//! `String.ofByteArray`), whose bodies differ: an environment in that world
//! expands deployed and is NOT covered by this constructor; it needs its own.
//! The specification's own world pins `String.ofList` but not `Char.ofNat`, so
//! the deployed kernel never expands a string literal there. Lean 4.8.0's
//! kernel expands through the constructor `String.mk` (no `String.ofList`
//! exists there), so the deployed kernel, keyed on `String.ofList`, never
//! expands in a Lean 4.8 environment: a completeness gap in the safe direction.
//! Not extracted Rust execution.

use crate::spec::error::SpecError;
use crate::spec::Specification;
use clean_kernel::{Environment, Name};

/// The reflected names the String-literal rules key on, read from the validated
/// interning table at registration (reserved native rule keys of the generator).
pub const ACCEPTS_TC_STRING_NAME_ALIASES: &[(&str, &str)] = &[
    ("accepts_tc_string_of_list_name", "String.ofList"),
    ("accepts_tc_string_mk_name", "String.mk"),
    ("accepts_tc_string_rec_name", "String.rec"),
    ("accepts_tc_list_name", "List"),
    ("accepts_tc_list_nil_name", "List.nil"),
    ("accepts_tc_list_cons_name", "List.cons"),
    ("accepts_tc_char_name", "Char"),
    ("accepts_tc_char_of_nat_name", "Char.ofNat"),
];

/// The canonical DEFINITIONS the admission fact pins, `(record alias, real
/// name)`: each record is `KDefSig.mk <signature> <body>`, reflected from the
/// deployed default prelude at registration.
const STRING_ADMIT_DEFINITIONS: &[(&str, &str)] = &[
    ("accepts_tc_string_of_list_def", "String.ofList"),
    ("accepts_tc_char_of_nat_def", "Char.ofNat"),
];

/// The canonical CONSTRUCTOR entries the admission fact pins.
const STRING_ADMIT_CONSTRUCTORS: &[(&str, &str)] = &[("accepts_tc_string_mk_meta", "String.mk")];

/// The model's image of `string_lit_to_constructor`: the scalar-value range a
/// Rust `str` guarantees, the character list, and the `String.ofList`
/// application over it.
const EXPANSION: &[(&str, &str)] = &[
    (
        r"def string_lit_char_valid (c : Nat) : Bool := @Bool.rec (fun (_ : Bool) => Bool) (@Bool.rec (fun (_ : Bool) => Bool) Bool.false (nat_leb (Nat.succ c) 1114112) (nat_leb 57344 c)) Bool.true (nat_leb (Nat.succ c) 55296)",
        "A Unicode scalar value: c < 0xD800, or 0xDFFF < c < 0x110000 (Nat.isValidChar). Every character of a Rust str satisfies it.",
    ),
    (
        r"def string_lit_chars_valid (cs : ListType Nat) : Bool := @ListType.rec Nat (fun (_ : ListType Nat) => Bool) Bool.true (fun (c : Nat) (_ : ListType Nat) (ih : Bool) => @Bool.rec (fun (_ : Bool) => Bool) Bool.false ih (string_lit_char_valid c)) cs",
        "Every character of the list is a Unicode scalar value (the range a Rust str guarantees).",
    ),
    (
        r"def string_lit_char_list (cs : ListType Nat) : KExpr := @ListType.rec Nat (fun (_ : ListType Nat) => KExpr) (KExpr.app (KExpr.const accepts_tc_list_nil_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.const accepts_tc_char_name (@ListType.nil Level))) (fun (c : Nat) (_ : ListType Nat) (ih : KExpr) => KExpr.app (KExpr.app (KExpr.app (KExpr.const accepts_tc_list_cons_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.const accepts_tc_char_name (@ListType.nil Level))) (KExpr.app (KExpr.const accepts_tc_char_of_nat_name (@ListType.nil Level)) (literal_nat c))) ih) cs",
        "The deployed string_lit_to_constructor's character list: List.cons.{0} Char (Char.ofNat (literal c)) ... (List.nil.{0} Char), one Char.ofNat of a raw Nat literal per scalar value, in order.",
    ),
    (
        r"def string_lit_expansion (cs : ListType Nat) : KExpr := KExpr.app (KExpr.const accepts_tc_string_of_list_name (@ListType.nil Level)) (string_lit_char_list cs)",
        "The deployed string_lit_to_constructor's result: String.ofList applied to the character list.",
    ),
];

/// `List.{0} Char`, the domain of the canonical `String.ofList`'s lambda (the
/// witnesses' beta step names it; the kernel checks it against the reflected body).
const STRING_OF_LIST_DOM: &str = r"def accepts_tc_string_of_list_dom : KExpr := KExpr.app (KExpr.const accepts_tc_list_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.const accepts_tc_char_name (@ListType.nil Level))";

/// The registered alias of a real name the stage keys on.
fn name_alias(real: &str) -> Result<&'static str, SpecError> {
    ACCEPTS_TC_STRING_NAME_ALIASES
        .iter()
        .find(|(_, r)| *r == real)
        .map(|(alias, _)| *alias)
        .ok_or_else(|| SpecError::TypeError(format!("no String-literal name alias for {real}")))
}

/// Whether the deployed kernel expands string literals in `env`: exactly
/// `TypeChecker::string_literal_admitted` (`tc/fold_admission.rs`).
fn deployed_string_literal_admitted(env: &Environment) -> bool {
    env.nat_literal_extension_canonical()
        && env.native_fold_authorized(&Name::from_string("String.ofList"))
        && env.native_fold_authorized(&Name::from_string("Char.ofNat"))
}

impl Specification {
    /// Register the names, the expansion, the reflected canonical records and
    /// the admission predicate: everything the two typed families' new rule
    /// mentions. Runs before the typed relations are declared.
    pub(super) fn add_accepts_tc_string_prelude(&mut self) -> Result<(), SpecError> {
        for (alias, real) in ACCEPTS_TC_STRING_NAME_ALIASES {
            let tag = self.reflected_name_tag(real)?;
            self.add_recursive_def(
                &format!("def {alias} : Name := kcre_name_{tag}"),
                "The reflected name a String-literal rule of KernelAcceptsTcIn / TypingTcIn keys on, read from the validated interning table at registration (a reserved native rule key).",
            )?;
        }
        for (source, description) in EXPANSION {
            self.add_recursive_def(source, description)?;
        }
        let prelude = Environment::with_prelude();
        if !deployed_string_literal_admitted(&prelude) {
            return Err(SpecError::EnvError(
                "the deployed default prelude no longer admits string literal expansion \
                 (String.ofList / Char.ofNat / Nat not canonical there): the canonical records \
                 this stage pins would name a world the kernel refuses"
                    .to_string(),
            ));
        }
        let mut premises = Vec::new();
        for (alias, real) in STRING_ADMIT_DEFINITIONS {
            let tag_of = |n: &str| self.reflected_name_tag(n);
            let sig = crate::red_env_reflect::reflect_const_sig_text(&prelude, real, tag_of)
                .map_err(|e| SpecError::TypeError(format!("canonical {real} signature: {e}")))?;
            let tag_of = |n: &str| self.reflected_name_tag(n);
            let body =
                crate::red_env_reflect::reflect_definition_value_text_at(&prelude, real, 0, tag_of)
                    .map_err(|e| SpecError::TypeError(format!("canonical {real} body: {e}")))?;
            let body_alias = alias.replace("_def", "_body");
            self.add_recursive_def(
                &format!("def {body_alias} : KExpr := {body}"),
                "The deployed default prelude's canonical definition body, reflected at registration where the kernel's pin table admits it; never typed in.",
            )?;
            self.add_recursive_def(
                &format!("def {alias} : KDefSig := KDefSig.mk {sig} {body_alias}"),
                "The deployed default prelude's canonical definition record (signature and body), reflected at registration where the kernel's pin table admits it; never typed in.",
            )?;
            let name = name_alias(real)?;
            premises.push(format!(
                "@Eq (OptionType KDefSig) (kdef_for (red_def R) {name}) (@OptionType.some KDefSig {alias})"
            ));
        }
        for (alias, real) in STRING_ADMIT_CONSTRUCTORS {
            let tag_of = |n: &str| self.reflected_name_tag(n);
            let meta = crate::red_env_reflect::reflect_ctor_meta_text(&prelude, real, tag_of)
                .map_err(|e| SpecError::TypeError(format!("canonical {real} metadata: {e}")))?;
            self.add_recursive_def(
                &format!("def {alias} : KCtorMeta := {meta}"),
                "The deployed default prelude's canonical constructor metadata, reflected at registration; never typed in.",
            )?;
            let name = name_alias(real)?;
            premises.push(format!(
                "@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) {name}) (@OptionType.some KCtorMeta {alias})"
            ));
        }
        self.add_inductive(
            &format!(
                "inductive StringLitAdmitIn (R : RedEnv) : Type\n| mk : {} -> StringLitAdmitIn R",
                premises.join(" -> ")
            ),
            "The admission fact string literal expansion keys on: R holds the deployed default prelude's canonical String.ofList and Char.ofNat records and String.mk constructor entry (the model's image of string_literal_admitted's pin-table verdict, for the clean-prelude world). A syntactic predicate over R's tables, not a typing claim.",
        )?;
        Ok(())
    }
}

/// The witness string: `"ab"`, the scalar values 97 and 98.
const AB: &str = "(@ListType.cons Nat 97 (@ListType.cons Nat 98 (@ListType.nil Nat)))";

/// `(name, type, value)` of the derived rules: each deployed branch that
/// expands a String literal, over any `R` carrying the admission fact.
fn derived_rules() -> Vec<(String, String, String)> {
    let hyps = "(hadm : StringLitAdmitIn R) (hv : @Eq Bool (string_lit_chars_valid cs) Bool.true)";
    let lit = "(literal_string (string_lit_code cs))";
    let exp = "(string_lit_expansion cs)";
    let arm = "(@KernelAcceptsTcIn.lit_string_expand R tenv G cs hadm hv)";
    let head = "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn)";
    let bind = "fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn)";
    vec![
        (
            "accepts_tc_lit_string_every_payload".to_string(),
            format!("{head} (n : Nat), StringLitAdmitIn R -> @Eq Bool (string_lit_chars_valid (string_lit_chars n)) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G (literal_string n) (string_lit_expansion (string_lit_chars n))"),
            format!("{bind} (n : Nat) (hadm : StringLitAdmitIn R) (hv : @Eq Bool (string_lit_chars_valid (string_lit_chars n)) Bool.true) =>
Eq.substType Nat (fun (k : Nat) => KernelAcceptsTcIn R tenv Bool.false G (literal_string k) (string_lit_expansion (string_lit_chars n)))
  (string_lit_code (string_lit_chars n)) n (string_lit_code_chars n)
  (@KernelAcceptsTcIn.lit_string_expand R tenv G (string_lit_chars n) hadm hv)"),
        ),
        (
            "accepts_tc_string_lit_expansion".to_string(),
            format!("{head} (cs : ListType Nat) (W : KExpr) (s : KExpr), StringLitAdmitIn R -> @Eq Bool (string_lit_chars_valid cs) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G {exp} W -> KernelAcceptsTcIn R tenv Bool.false G W s -> KernelAcceptsTcIn R tenv Bool.false G {lit} s"),
            format!("{bind} (cs : ListType Nat) (W : KExpr) (s : KExpr) {hyps} (hw : KernelAcceptsTcIn R tenv Bool.false G {exp} W) (hs : KernelAcceptsTcIn R tenv Bool.false G W s) =>
@KernelAcceptsTcIn.trans R tenv G {lit} W s (@KernelAcceptsTcIn.trans R tenv G {lit} {exp} W {arm} hw) hs"),
        ),
        (
            "accepts_tc_iota_major_string_literal".to_string(),
            format!("{head} (f : KExpr) (cs : ListType Nat) (rhs : KExpr), StringLitAdmitIn R -> @Eq Bool (string_lit_chars_valid cs) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.app f {exp}) rhs -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.app f {lit}) rhs"),
            format!("{bind} (f : KExpr) (cs : ListType Nat) (rhs : KExpr) {hyps} (h : KernelAcceptsTcIn R tenv Bool.false G (KExpr.app f {exp}) rhs) =>
@KernelAcceptsTcIn.trans R tenv G (KExpr.app f {lit}) (KExpr.app f {exp}) rhs
  (@KernelAcceptsTcIn.app_cong R tenv G f f {lit} {exp} (@KernelAcceptsTcIn.cdp R tenv G f f (@DefEqCDPIn.refl R f)) {arm})
  h"),
        ),
        (
            "accepts_tc_proj_string_literal".to_string(),
            format!("{head} (S : Name) (i : Nat) (cs : ListType Nat) (rhs : KExpr), StringLitAdmitIn R -> @Eq Bool (string_lit_chars_valid cs) Bool.true -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj S i {exp}) rhs -> KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj S i {lit}) rhs"),
            format!("{bind} (S : Name) (i : Nat) (cs : ListType Nat) (rhs : KExpr) {hyps} (h : KernelAcceptsTcIn R tenv Bool.false G (KExpr.proj S i {exp}) rhs) =>
@KernelAcceptsTcIn.trans R tenv G (KExpr.proj S i {lit}) (KExpr.proj S i {exp}) rhs
  (@KernelAcceptsTcIn.proj_cong R tenv G S i {lit} {exp} {arm})
  h"),
        ),
    ]
}

/// `(name, type, value)` of the witnesses at the fixture `accepts_tc_string_env`
/// (the reflected seed's tables extended with the canonical String closure):
/// the admission fact, the rule itself, each derived branch reaching a concrete
/// result, the empty-payload instance of the every-payload lemma, and each
/// one's TypingTcIn corollary.
fn witnesses() -> Vec<(String, String, String)> {
    let env = "accepts_tc_string_env";
    let g = "(tenv : KDeclEnv) (G : ListType CtxEntryIn)";
    let lit = format!("(literal_string (string_lit_code {AB}))");
    let exp = format!("(string_lit_expansion {AB})");
    let list = format!("(string_lit_char_list {AB})");
    let mk = "(KExpr.const accepts_tc_string_mk_name (@ListType.nil Level))";
    let built = format!("(KExpr.app {mk} {list})");
    let valid = "(@Eq.refl Bool Bool.true)";
    // delta then beta: String.ofList L == String.mk L at the fixture.
    let ofl = "(KExpr.const accepts_tc_string_of_list_name (@ListType.nil Level))";
    let body = "accepts_tc_string_of_list_body";
    let delta = format!(
        "(accepts_tc_delta {env} tenv G {exp} accepts_tc_string_of_list_name {body} (@Eq.refl (OptionType Name) (@OptionType.some Name accepts_tc_string_of_list_name)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {body})))"
    );
    let beta = format!(
        "(accepts_tc_beta {env} tenv G accepts_tc_string_of_list_dom (KExpr.app {mk} (KExpr.bvar Nat.zero)) {list})"
    );
    let to_ctor = format!(
        "(@KernelAcceptsTcIn.trans {env} tenv G {exp} (KExpr.app {body} {list}) {built} {delta} {beta})"
    );
    let _ = ofl;
    let s_name = "literal_builtin_string_name";
    let proj_lit = format!("(KExpr.proj {s_name} Nat.zero {lit})");
    let proj_exp = format!("(KExpr.proj {s_name} Nat.zero {exp})");
    let proj_built = format!("(KExpr.proj {s_name} Nat.zero {built})");
    let proj_beta = format!(
        "(@KernelAcceptsTcIn.cdp {env} tenv G {proj_built} {list} (@DefEqCDPIn.raw {env} {proj_built} {list} (@par_reduces_cdp.projection_beta {env} {s_name} Nat.zero {built} {list} (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {list})))))"
    );
    let motive = "(KExpr.lam (KExpr.const literal_builtin_string_name (@ListType.nil Level)) (KExpr.app (KExpr.const accepts_tc_list_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.const accepts_tc_char_name (@ListType.nil Level))))";
    let minor = "(KExpr.lam accepts_tc_string_of_list_dom (KExpr.bvar Nat.zero))";
    let us = "(@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))";
    let rec_f = format!(
        "(KExpr.app (KExpr.app (KExpr.const accepts_tc_string_rec_name {us}) {motive}) {minor})"
    );
    let rhs_inst = format!(
        "(recursor_rhs_instance (recmeta_signature accepts_tc_string_rec_meta) (recrule_rhs accepts_tc_string_rec_mk_rule) {us})"
    );
    let contractum =
        format!("(KExpr.app (KExpr.app (KExpr.app {rhs_inst} {motive}) {minor}) {list})");
    let at_ctor = format!("(KExpr.app {rec_f} {built})");
    let iota = format!(
        "(accepts_tc_iota {env} tenv G {at_ctor} accepts_tc_string_rec_name accepts_tc_string_rec_meta {built} accepts_tc_string_mk_name accepts_tc_string_rec_mk_rule {contractum} (@Eq.refl (OptionType Name) (@OptionType.some Name accepts_tc_string_rec_name)) (@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta accepts_tc_string_rec_meta)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {built})) (@Eq.refl (OptionType Name) (@OptionType.some Name accepts_tc_string_mk_name)) (@Eq.refl (OptionType RecRule) (@OptionType.some RecRule accepts_tc_string_rec_mk_rule)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr {contractum})))"
    );
    let mut out = vec![
        (
            "accepts_tc_string_admit".to_string(),
            format!("StringLitAdmitIn {env}"),
            format!("@StringLitAdmitIn.mk {env} (@Eq.refl (OptionType KDefSig) (@OptionType.some KDefSig accepts_tc_string_of_list_def)) (@Eq.refl (OptionType KDefSig) (@OptionType.some KDefSig accepts_tc_char_of_nat_def)) (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta accepts_tc_string_mk_meta))"),
        ),
        (
            "kernel_accepts_tc_in_lit_string_expand".to_string(),
            format!("forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G {lit} {exp}"),
            format!("fun {g} => @KernelAcceptsTcIn.lit_string_expand {env} tenv G {AB} accepts_tc_string_admit {valid}"),
        ),
        (
            "kernel_accepts_tc_in_string_lit_constructor".to_string(),
            format!("forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G {lit} {built}"),
            format!("fun {g} => accepts_tc_string_lit_expansion {env} tenv G {AB} {built} {built} accepts_tc_string_admit {valid} {to_ctor} (@KernelAcceptsTcIn.cdp {env} tenv G {built} {built} (@DefEqCDPIn.refl {env} {built}))"),
        ),
        (
            "kernel_accepts_tc_in_string_lit_proj".to_string(),
            format!("forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G {proj_lit} {list}"),
            format!("fun {g} => accepts_tc_proj_string_literal {env} tenv G {s_name} Nat.zero {AB} {list} accepts_tc_string_admit {valid} (@KernelAcceptsTcIn.trans {env} tenv G {proj_exp} {proj_built} {list} (@KernelAcceptsTcIn.proj_cong {env} tenv G {s_name} Nat.zero {exp} {built} {to_ctor}) {proj_beta})"),
        ),
        (
            "kernel_accepts_tc_in_string_lit_iota".to_string(),
            format!("forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G (KExpr.app {rec_f} {lit}) {contractum}"),
            format!("fun {g} => accepts_tc_iota_major_string_literal {env} tenv G {rec_f} {AB} {contractum} accepts_tc_string_admit {valid} (@KernelAcceptsTcIn.trans {env} tenv G (KExpr.app {rec_f} {exp}) {at_ctor} {contractum} (@KernelAcceptsTcIn.app_cong {env} tenv G {rec_f} {rec_f} {exp} {built} (@KernelAcceptsTcIn.cdp {env} tenv G {rec_f} {rec_f} (@DefEqCDPIn.refl {env} {rec_f})) {to_ctor}) {iota})"),
        ),
        (
            "kernel_accepts_tc_in_lit_string_empty".to_string(),
            format!("forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G (literal_string Nat.zero) (string_lit_expansion (@ListType.nil Nat))"),
            format!("fun {g} => accepts_tc_lit_string_every_payload {env} tenv G Nat.zero accepts_tc_string_admit {valid}"),
        ),
    ];
    let mut sound = Vec::new();
    for (name, ty, _) in out.iter().skip(1) {
        let Some(rest) = ty.strip_prefix(&format!(
            "forall {g}, KernelAcceptsTcIn {env} tenv Bool.false G "
        )) else {
            continue;
        };
        let stem = name.trim_start_matches("kernel_accepts_tc_in_");
        sound.push((
            format!("accepts_tc_{stem}_sound"),
            format!("forall {g}, TypingTcIn {env} tenv Bool.false G {rest}"),
            format!("fun {g} => kernel_accepts_tc_in_sound {env} tenv Bool.false G {rest} (@{name} tenv G)"),
        ));
    }
    out.extend(sound);
    out
}

/// Every PROOF this stage registers, in registration order (the census list).
pub const STRING_LITERAL_PROOF_NAMES: &[&str] = &[
    "accepts_tc_lit_string_every_payload",
    "accepts_tc_string_lit_expansion",
    "accepts_tc_iota_major_string_literal",
    "accepts_tc_proj_string_literal",
    "accepts_tc_string_admit",
    "kernel_accepts_tc_in_lit_string_expand",
    "kernel_accepts_tc_in_string_lit_constructor",
    "kernel_accepts_tc_in_string_lit_proj",
    "kernel_accepts_tc_in_string_lit_iota",
    "kernel_accepts_tc_in_lit_string_empty",
    "accepts_tc_lit_string_expand_sound",
    "accepts_tc_string_lit_constructor_sound",
    "accepts_tc_string_lit_proj_sound",
    "accepts_tc_string_lit_iota_sound",
    "accepts_tc_lit_string_empty_sound",
];

impl Specification {
    /// Register the derived branches and the witnesses (after the typed
    /// relations and the native-fold helper lemmas `accepts_tc_delta` /
    /// `accepts_tc_beta` / `accepts_tc_iota` they compose).
    pub(super) fn add_accepts_tc_string_witnesses(&mut self) -> Result<(), SpecError> {
        let theorem = |spec: &mut Specification, name: &str, ty: &str, value: &str| {
            super::super::acceptance_in::theorem(
                spec,
                name,
                ty,
                value,
                "Checked String-literal expansion: the deployed string_lit_to_constructor as the lit_string_expand rule of KernelAcceptsTcIn, a branch that expands (def-eq, recursor major, projection subject) derived from it, or a witness at the canonical-closure fixture; no assumed reduction, typing or source-execution claim.",
            )
        };
        for (name, ty, value) in derived_rules() {
            theorem(self, &name, &ty, &value)?;
        }
        // The fixture: the reflected seed's tables extended with the canonical
        // String closure the admission fact names, and String.rec's rule for the
        // iota witness, all reflected from the deployed default prelude.
        let prelude = Environment::with_prelude();
        let (meta, rules) =
            crate::red_env_reflect::reflect_recursor_text(&prelude, "String.rec", |n| {
                self.reflected_name_tag(n)
            })
            .map_err(|e| SpecError::TypeError(format!("canonical String.rec: {e}")))?;
        let mk_atom = format!("kcre_name_{}", self.reflected_name_tag("String.mk")?);
        let (_, fields, rhs) = rules
            .iter()
            .find(|(ctor, _, _)| *ctor == mk_atom)
            .ok_or_else(|| SpecError::TypeError("String.rec has no rule for String.mk".into()))?;
        self.add_recursive_def(
            &format!("def accepts_tc_string_rec_meta : RecMeta := {meta}"),
            "The deployed default prelude's String.rec metadata, reflected at registration (never typed in).",
        )?;
        self.add_recursive_def(
            &format!(
                "def accepts_tc_string_rec_mk_rule : RecRule := RecRule.mk {mk_atom} {} {rhs}",
                crate::red_env_reflect::render_nat(u64::from(*fields))
            ),
            "The deployed default prelude's String.rec rule for String.mk, reflected at registration (never typed in).",
        )?;
        self.add_recursive_def(
            STRING_OF_LIST_DOM,
            "List.{0} Char, the domain the canonical String.ofList abstracts over.",
        )?;
        self.add_recursive_def(
            r"def accepts_tc_string_env : RedEnv := RedEnv.mk (RecEnv.addRec (red_rec kernel_core_red_env) accepts_tc_string_rec_name accepts_tc_string_rec_meta (RecRules.cons accepts_tc_string_rec_mk_rule RecRules.nil)) (DefEnv.addDef (DefEnv.addDef (red_def kernel_core_red_env) accepts_tc_string_of_list_name accepts_tc_string_of_list_def) accepts_tc_char_of_nat_name accepts_tc_char_of_nat_def) (IndCtorEnv.addCtor (red_ind_ctor kernel_core_red_env) accepts_tc_string_mk_name accepts_tc_string_mk_meta)",
            "Witness environment: the reflected seed's tables extended with the deployed default prelude's canonical String.ofList / Char.ofNat records, the String.mk constructor entry and String.rec's rule. Data, not an admission claim.",
        )?;
        for (name, ty, value) in witnesses() {
            theorem(self, &name, &ty, &value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_literal_records_parse_and_names_match() {
        for (source, _) in EXPANSION {
            clean_parser::parse_decl(source).expect("expansion parses");
        }
        clean_parser::parse_decl(STRING_OF_LIST_DOM).expect("domain parses");
        let mut names = Vec::new();
        for (name, ty, value) in derived_rules().into_iter().chain(witnesses()) {
            clean_parser::parse_decl(&format!("def {name} : {ty} := {value}"))
                .unwrap_or_else(|e| panic!("{name} parses: {e:?}"));
            names.push(name);
        }
        assert_eq!(names, STRING_LITERAL_PROOF_NAMES);
    }
}
