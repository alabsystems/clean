// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Crystal E4d: the deployed native Nat and Int folds as DERIVED conversions
//! of `KernelAcceptsTcIn`.
//!
//! The deployed `reduce_nat` (`clean-kernel/src/tc/reduction/nat.rs`) folds a
//! Nat head applied to literals in one step, `reduce_int` does the same for
//! `Int.add` / `Int.sub` / `Int.mul` once each operand whnfs to a
//! constructor-applied literal (the closure member `Int.neg` gets its own lemma;
//! a whnf-to-literal step before the fold is an ordinary derivation composed by
//! congruence), and `reduce_int_pred_fold` collapses a `Nat.rec` predecessor
//! loop over an `Int` accumulator. Since clean main `df9163459` each fold fires only
//! when the head's delta-closure digest is one the kernel pins as canonical
//! (`env/native_fold_canon.tsv`). A fold is justified exactly when the head's
//! own unfolding computes what the fold computes, so the model needs no new
//! rule: for each fold key this stage PROVES, over any reduction environment
//! `R` that holds the canonical definitions of the key's closure (and the
//! canonical `Nat.rec` / `Int.rec` / `Bool.rec` rules and the `Prod.mk`
//! constructor entry where the closure reaches them), that `op (literal a)
//! (literal b)` converts to `literal (op a b)` by `delta` / `beta` / `iota` /
//! projection-beta and the literal / constructor rules `lit_zero` / `lit_succ`
//! alone. Each lemma is one induction mirroring the definition's own
//! recursion; the meta-level `op a b` on the right is the same definition, so
//! no arithmetic fact is assumed. A symbolic `Int` / `Bool` argument is split
//! into its constructors BEFORE any beta, because a stuck literal reader under
//! a binder is not a closed term the kernel can compare.
//!
//! "Canonical" is the body the specification's own environment holds for the
//! head, whose closure digest the pin table admits (measured per head through
//! `Environment::native_fold_verdict`): the bodies and the `Int.rec` rules are
//! reflected at registration from the LIVE environment by the generator's own
//! reflector, never typed in, and a body that disagrees with the one the proofs
//! were generated against refuses registration. The bitwise folds
//! (`Nat.land` / `lor` / `xor` / `shiftRight`) register LATE: their closure
//! reaches `Nat.shiftRight`, which the build defines only at its end.
//!
//! The proof terms are MINTED by `scripts/gen_accepts_tc_native_nat.py` into
//! `generated/accepts_tc_native_nat.json`; that script is outside the trusted
//! base (the kernel re-checks every term here), and its output is the artifact
//! this stage registers. Names are placeholders `kcre_name_@@<real name>@@`,
//! resolved through the validated interning table at registration.
//!
//! Scope, stated: the canonical closures of the specification world. The pin
//! table also admits other worlds (Lean's `Init`, where `Nat.gcd` is the only
//! further key) whose bodies differ; each needs its own agreement lemma over
//! its own body, and none is claimed here. Not extracted Rust execution.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The minted declarations (see the module docs).
const SCRIPT: &str = include_str!("../generated/accepts_tc_native_nat.json");

/// Every PROOF this module registers, in registration order. A unit test
/// derives the same list from the minted artifact and compares.
pub const NATIVE_NAT_PROOF_NAMES: &[&str] = &[
    "accepts_tc_iota_reduct_of_lookup",
    "accepts_tc_beta",
    "accepts_tc_app_l",
    "accepts_tc_app_r",
    "accepts_tc_delta",
    "accepts_tc_iota",
    "accepts_tc_nat_rec_meta_reflected",
    "accepts_tc_nat_rec_zero_rule_reflected",
    "accepts_tc_nat_rec_succ_rule_reflected",
    "kernel_accepts_tc_in_nat_succ_fold",
    "kernel_accepts_tc_in_nat_pred_fold",
    "kernel_accepts_tc_in_nat_add_fold",
    "kernel_accepts_tc_in_nat_sub_fold",
    "kernel_accepts_tc_in_nat_mul_fold",
    "kernel_accepts_tc_in_nat_pow_fold",
    "kernel_accepts_tc_in_nat_shiftleft_fold",
    "kernel_accepts_tc_in_nat_beq_fold",
    "kernel_accepts_tc_in_nat_ble_fold",
    "kernel_accepts_tc_in_nat_blt_fold",
    "accepts_tc_nat_rec_select_zero",
    "accepts_tc_nat_rec_select_lit",
    "kernel_accepts_tc_in_nat_divcore_fold",
    "kernel_accepts_tc_in_nat_modcore_fold",
    "kernel_accepts_tc_in_nat_div_fold",
    "kernel_accepts_tc_in_nat_mod_fold",
    "accepts_tc_nat_pred_body_reflected",
    "accepts_tc_nat_add_body_reflected",
    "accepts_tc_nat_sub_body_reflected",
    "accepts_tc_nat_add_instance",
    "accepts_tc_nat_add_instance_sound",
    "accepts_tc_nat_sub_instance",
    "accepts_tc_nat_sub_instance_sound",
    "accepts_tc_nat_mul_instance",
    "accepts_tc_nat_mul_instance_sound",
    "accepts_tc_nat_pow_instance",
    "accepts_tc_nat_pow_instance_sound",
    "accepts_tc_nat_shiftleft_instance",
    "accepts_tc_nat_shiftleft_instance_sound",
    "accepts_tc_nat_beq_instance",
    "accepts_tc_nat_beq_instance_sound",
    "accepts_tc_nat_ble_instance",
    "accepts_tc_nat_ble_instance_sound",
    "accepts_tc_nat_div_instance",
    "accepts_tc_nat_div_instance_sound",
    "accepts_tc_nat_mod_instance",
    "accepts_tc_nat_mod_instance_sound",
    "accepts_tc_nat_pred_instance",
    "accepts_tc_nat_pred_instance_sound",
    "kernel_accepts_tc_in_int_negofnat_fold",
    "kernel_accepts_tc_in_int_neg_fold",
    "accepts_tc_int_pred_step_select",
    "kernel_accepts_tc_in_int_subnatnat_fold",
    "kernel_accepts_tc_in_int_add_fold",
    "kernel_accepts_tc_in_int_mul_fold",
    "kernel_accepts_tc_in_int_sub_fold",
    "kernel_accepts_tc_in_int_tonat_fold",
    "kernel_accepts_tc_in_int_pred_fold",
    "accepts_tc_int_add_instance",
    "accepts_tc_int_add_instance_sound",
    "accepts_tc_int_sub_instance",
    "accepts_tc_int_sub_instance_sound",
    "accepts_tc_int_mul_instance",
    "accepts_tc_int_mul_instance_sound",
    "accepts_tc_int_neg_instance",
    "accepts_tc_int_neg_instance_sound",
    "accepts_tc_int_pred_fold_instance",
    "accepts_tc_bool_rec_false_rule_reflected",
    "accepts_tc_bool_rec_true_rule_reflected",
    "accepts_tc_prod_proj_0",
    "accepts_tc_prod_proj_1",
    "kernel_accepts_tc_in_bool_not_fold",
    "kernel_accepts_tc_in_bool_and_fold",
    "kernel_accepts_tc_in_bool_or_fold",
    "kernel_accepts_tc_in_bool_xor_fold",
    "kernel_accepts_tc_in_nat_ofbool_fold",
    "kernel_accepts_tc_in_nat_toboolpar_fold",
    "kernel_accepts_tc_in_prod_fst_fold",
    "kernel_accepts_tc_in_prod_snd_fold",
    "kernel_accepts_tc_in_nat_div2pair_fold",
    "kernel_accepts_tc_in_nat_div2_fold",
    "kernel_accepts_tc_in_nat_div2par_fold",
    "kernel_accepts_tc_in_nat_iterdiv2_fold",
    "kernel_accepts_tc_in_nat_shiftright_fold",
    "kernel_accepts_tc_in_nat_testbit_fold",
    "kernel_accepts_tc_in_nat_bitwiseaux_and_fold",
    "kernel_accepts_tc_in_nat_bitwise_and_fold",
    "kernel_accepts_tc_in_nat_land_fold",
    "kernel_accepts_tc_in_nat_bitwiseaux_or_fold",
    "kernel_accepts_tc_in_nat_bitwise_or_fold",
    "kernel_accepts_tc_in_nat_lor_fold",
    "kernel_accepts_tc_in_nat_bitwiseaux_xor_fold",
    "kernel_accepts_tc_in_nat_bitwise_xor_fold",
    "kernel_accepts_tc_in_nat_xor_fold",
    "accepts_tc_bool_and_body_reflected",
    "accepts_tc_nat_land_instance",
    "accepts_tc_nat_land_instance_sound",
    "accepts_tc_nat_lor_instance",
    "accepts_tc_nat_lor_instance_sound",
    "accepts_tc_nat_xor_instance",
    "accepts_tc_nat_xor_instance_sound",
    "accepts_tc_nat_shiftright_instance",
    "accepts_tc_nat_shiftright_instance_sound",
];

/// One minted declaration.
pub(super) enum NativeItem {
    /// A transparent definition (`def ...`).
    Def(String),
    /// A proof: name, type, value.
    Theorem(String, String, String),
    /// A definition whose value is the LIVE environment's definition of `of`,
    /// reflected by the generator's reflector: `def <name> : KExpr := <value>`.
    ReflectBody {
        name: String,
        of: String,
        zero_levels: usize,
    },
    /// The LIVE environment's recursor `of`, reflected: `def <meta> : RecMeta`
    /// and one `def <rule> : RecRule` per `(constructor, rule constant)`.
    ReflectRec {
        of: String,
        meta: String,
        rules: Vec<(String, String)>,
    },
}

fn resolve(spec: &Specification, text: &str) -> Result<String, SpecError> {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("@@") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 2..];
        let end = after.find("@@").ok_or_else(|| {
            SpecError::TypeError(format!(
                "native Nat fold artifact: unterminated name placeholder near {:?}",
                &rest[start..rest.len().min(start + 40)]
            ))
        })?;
        let tag = spec.reflected_name_tag(&after[..end])?;
        out.push_str(&tag.to_string());
        rest = &after[end + 2..];
    }
    out.push_str(rest);
    Ok(out)
}

/// Whether the artifact item is registered by the LATE pass (after
/// `Specification::build_stages` defines `Nat.shiftRight` and the bitwise
/// closure it reaches).
fn is_late(v: &serde_json::Value) -> bool {
    v["late"].as_bool().unwrap_or(false)
}

fn items_where(keep: impl Fn(&serde_json::Value) -> bool) -> Result<Vec<NativeItem>, SpecError> {
    let parsed: Vec<serde_json::Value> = serde_json::from_str(SCRIPT)
        .map_err(|e| SpecError::TypeError(format!("native Nat fold artifact is not JSON: {e}")))?;
    let field = |v: &serde_json::Value, key: &str| -> Result<String, SpecError> {
        v[key].as_str().map(str::to_string).ok_or_else(|| {
            SpecError::TypeError(format!("native Nat fold artifact item lacks `{key}`: {v}"))
        })
    };
    parsed
        .iter()
        .filter(|v| keep(v))
        .map(|v| match v["kind"].as_str() {
            Some("def") => Ok(NativeItem::Def(field(v, "source")?)),
            Some("theorem") => Ok(NativeItem::Theorem(
                field(v, "name")?,
                field(v, "ty")?,
                field(v, "body")?,
            )),
            Some("reflect_body") => Ok(NativeItem::ReflectBody {
                name: field(v, "name")?,
                of: field(v, "of")?,
                zero_levels: usize::try_from(v["zero_levels"].as_u64().unwrap_or(0)).map_err(
                    |_| {
                        SpecError::TypeError(format!(
                            "native fold artifact: zero_levels overflows: {v}"
                        ))
                    },
                )?,
            }),
            Some("reflect_rec") => Ok(NativeItem::ReflectRec {
                of: field(v, "of")?,
                meta: field(v, "meta")?,
                rules: v["rules"]
                    .as_object()
                    .map(|m| {
                        m.iter()
                            .filter_map(|(ctor, c)| Some((ctor.clone(), c.as_str()?.to_string())))
                            .collect()
                    })
                    .unwrap_or_default(),
            }),
            other => Err(SpecError::TypeError(format!(
                "native Nat fold artifact: unknown item kind {other:?}"
            ))),
        })
        .collect()
}

impl Specification {
    /// Register the minted native-Nat fold declarations (after the typed
    /// relations and their helper lemmas).
    pub(super) fn add_accepts_tc_native_nat(&mut self) -> Result<(), SpecError> {
        self.register_native_items(items_where(|v| !is_late(v))?)
    }

    /// The LATE pass: the bitwise folds, whose closures the build defines only
    /// at its end (`Specification::build_stages`).
    pub(crate) fn add_accepts_tc_native_nat_late(&mut self) -> Result<(), SpecError> {
        self.register_native_items(items_where(is_late)?)
    }

    fn register_native_items(&mut self, items: Vec<NativeItem>) -> Result<(), SpecError> {
        for item in items {
            match item {
                NativeItem::Def(source) => {
                    let source = resolve(self, &source)?;
                    self.add_recursive_def(
                        &source,
                        "Transparent data of the native-Nat fold lemmas (a canonical rule, a named sub-term of a canonical body, or the Bool literal reader); not an admission or typing claim.",
                    )?;
                }
                NativeItem::Theorem(name, ty, body) => {
                    let ty = resolve(self, &ty)?;
                    let body = resolve(self, &body)?;
                    super::super::acceptance_in::theorem(
                        self,
                        &name,
                        &ty,
                        &body,
                        "Checked native-Nat fold: the deployed reduce_nat fold of a canonical head on literals is a derived KernelAcceptsTcIn conversion (delta, beta, iota, literal rules), or a helper of one; no assumed reduction, typing or source-execution claim.",
                    )?;
                }
                NativeItem::ReflectRec { of, meta, rules } => {
                    let (meta_text, reflected) =
                        crate::red_env_reflect::reflect_recursor_text(self.env(), &of, |real| {
                            self.reflected_name_tag(real)
                        })
                        .map_err(|e| {
                            SpecError::TypeError(format!("native fold canonical recursor: {e}"))
                        })?;
                    self.add_recursive_def(
                        &format!("def {meta} : RecMeta := {meta_text}"),
                        "The live specification environment's recursor metadata, reflected by the generator's reflector at registration (never typed in).",
                    )?;
                    for (ctor, constant) in rules {
                        let atom = format!("kcre_name_{}", self.reflected_name_tag(&ctor)?);
                        let (_, fields, rhs) = reflected
                            .iter()
                            .find(|(c, _, _)| *c == atom)
                            .ok_or_else(|| {
                                SpecError::TypeError(format!("{of} has no rule for {ctor}"))
                            })?;
                        self.add_recursive_def(
                            &format!(
                                "def {constant} : RecRule := RecRule.mk {atom} {} {rhs}",
                                crate::red_env_reflect::render_nat(u64::from(*fields))
                            ),
                            "The live specification environment's recursor rule, reflected by the generator's reflector at registration (never typed in).",
                        )?;
                    }
                }
                NativeItem::ReflectBody {
                    name,
                    of,
                    zero_levels,
                } => {
                    let value = crate::red_env_reflect::reflect_definition_value_text_at(
                        self.env(),
                        &of,
                        zero_levels,
                        |real| self.reflected_name_tag(real),
                    )
                    .map_err(|e| {
                        SpecError::TypeError(format!("native Nat fold canonical body: {e}"))
                    })?;
                    self.add_recursive_def(
                        &format!("def {name} : KExpr := {value}"),
                        "The live specification environment's definition of a native-fold key, reflected by the generator's reflector at registration (never typed in).",
                    )?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_nat_proof_names_match_the_artifact() {
        let theorem_names = |late: bool| {
            items_where(|v| is_late(v) == late)
                .expect("the minted artifact parses")
                .into_iter()
                .filter_map(|item| match item {
                    NativeItem::Theorem(name, _, _) => Some(name),
                    NativeItem::Def(_)
                    | NativeItem::ReflectBody { .. }
                    | NativeItem::ReflectRec { .. } => None,
                })
                .collect::<Vec<String>>()
        };
        let mut from_artifact = theorem_names(false);
        from_artifact.extend(theorem_names(true));
        assert_eq!(from_artifact, NATIVE_NAT_PROOF_NAMES);
    }
}
