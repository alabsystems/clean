// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A lossless tagged payload for the existing `KExpr.lit : Nat -> KExpr` leaf.
//!
//! Even payloads represent natural literals; odd payloads represent interned
//! string identities. `literal_decode_encode` proves the round trip, so the
//! representation neither identifies literal kinds nor loses their values.
//! The string interner must itself preserve identity at the Rust boundary.
//!
//! `KExpr.lit` now contains an ENCODED literal, not a raw natural literal.
//! Existing reduction, substitution and comparison lemmas quantify over every
//! payload and remain valid. Raw values must enter through `literal_nat` or
//! `literal_string`; no arithmetic reducer may operate on the encoded payload
//! as if it were the natural value. The reduction-environment reflector still
//! declines production literal nodes, so it has no untagged ingress to migrate.
//!
//! The two type names are read from the validated reflection interning table,
//! including the generator's fresh-table override during regeneration. The
//! implementation-shaped model uses these same early aliases. This establishes
//! name agreement, not the typing or semantic coherence of the real prelude.
//! Syntactic distinctness below is not a claim of inequivalence under an
//! arbitrary definition environment.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

pub(super) fn theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
    dependencies: &[&str],
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            dependencies
                .iter()
                .map(|name| (*name).to_string())
                .collect(),
        ),
        axiom_deps: HashSet::new(),
    })
}

impl Specification {
    pub(super) fn add_literal_model(&mut self) -> Result<(), SpecError> {
        let nat_tag = self.reflected_name_tag("Nat")?;
        let string_tag = self.reflected_name_tag("String")?;
        if nat_tag == string_tag {
            return Err(SpecError::EnvError(
                "literal builtin names have the same reflection tag".to_string(),
            ));
        }
        // Early short aliases avoid both the late kcre_name registration stage
        // and a deeply nested unary source term for a less-frequent builtin.
        // The kernel checks each successor equation and the distinction proof
        // below; no reflected tag is installed as an axiom.
        for tag in 0..=nat_tag.max(string_tag) {
            let value = if tag == 0 {
                "Nat.zero".to_string()
            } else {
                format!("Nat.succ literal_builtin_tag_{}", tag - 1)
            };
            self.add_recursive_def(
                &format!("def literal_builtin_tag_{tag} : Nat := {value}"),
                "An early, checked numeral alias for the validated semantic-name interning table.",
            )?;
        }
        for (kind, tag) in [("nat", nat_tag), ("string", string_tag)] {
            self.add_recursive_def(
                &format!("def literal_builtin_{kind}_tag : Nat := literal_builtin_tag_{tag}"),
                "The exact builtin tag from the validated reflection interning table, not a separately chosen model name.",
            )?;
            self.add_recursive_def(
                &format!("def literal_builtin_{kind}_name : Name := Name.str Name.anonymous literal_builtin_{kind}_tag"),
                "Canonical early builtin-name alias shared with the implementation-shaped literal model.",
            )?;
        }

        self.add_inductive(
            "inductive LiteralCodeValue : Type\n\
             | natVal : Nat -> LiteralCodeValue\n\
             | strVal : Nat -> LiteralCodeValue",
            "Decoded literal values. Natural values and interned string identities are distinct constructors.",
        )?;
        for (source, description) in [
            (
                "def literal_nat_code (n : Nat) : Nat := @Nat.rec (fun (_ : Nat) => Nat) Nat.zero (fun (_ : Nat) (r : Nat) => Nat.succ (Nat.succ r)) n",
                "Encode a natural literal as its doubled value. Structural recursion avoids a dependency on arithmetic normalization.",
            ),
            (
                "def literal_string_code (n : Nat) : Nat := Nat.succ (literal_nat_code n)",
                "Encode an interned string identity as the odd tag following its doubled identity.",
            ),
            (
                "def literal_next (v : LiteralCodeValue) : LiteralCodeValue := match v with\n\
                 | LiteralCodeValue.natVal n => LiteralCodeValue.strVal n\n\
                 | LiteralCodeValue.strVal n => LiteralCodeValue.natVal (Nat.succ n)",
                "Successor on the tagged enumeration of literal values.",
            ),
            (
                "def literal_decode (n : Nat) : LiteralCodeValue := @Nat.rec (fun (_ : Nat) => LiteralCodeValue) (LiteralCodeValue.natVal Nat.zero) (fun (_ : Nat) (v : LiteralCodeValue) => literal_next v) n",
                "Decode every tagged payload into its literal kind and original value or string identity.",
            ),
            (
                "def literal_encode (v : LiteralCodeValue) : Nat := match v with\n\
                 | LiteralCodeValue.natVal n => literal_nat_code n\n\
                 | LiteralCodeValue.strVal n => literal_string_code n",
                "Encode either literal kind without identifying the two constructors.",
            ),
            (
                "def literal_value_payload (v : LiteralCodeValue) : Nat := match v with\n\
                 | LiteralCodeValue.natVal n => n\n\
                 | LiteralCodeValue.strVal n => n",
                "Project the decoded payload; used only after the literal kind has been retained separately.",
            ),
            (
                "def literal_nat (n : Nat) : KExpr := KExpr.lit (literal_nat_code n)",
                "The only raw-natural ingress into the reflected tagged literal leaf.",
            ),
            (
                "def literal_string (n : Nat) : KExpr := KExpr.lit (literal_string_code n)",
                "Reflect an interned string identity into its distinct tagged literal leaf.",
            ),
            (
                "def literal_nat_type : KExpr := KExpr.const literal_builtin_nat_name (@ListType.nil Level)",
                "The Nat type under the validated shared reflection name encoding. Prelude semantic coherence remains an explicit obligation.",
            ),
            (
                "def literal_string_type : KExpr := KExpr.const literal_builtin_string_name (@ListType.nil Level)",
                "The String type under the same validated reflection table used for the Nat builtin and implementation-shaped syntax.",
            ),
            (
                "def literal_value_type (v : LiteralCodeValue) : KExpr := match v with\n\
                 | LiteralCodeValue.natVal n => literal_nat_type\n\
                 | LiteralCodeValue.strVal n => literal_string_type",
                "Exact type returned for each decoded literal kind.",
            ),
            (
                "def literal_type_of_code (n : Nat) : KExpr := literal_value_type (literal_decode n)",
                "Recover the exact built-in literal type from the lossless tagged payload.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }

        theorem(
            self,
            "literal_nat_decode",
            "forall (n : Nat), @Eq LiteralCodeValue (literal_decode (literal_nat_code n)) (LiteralCodeValue.natVal n)",
            "fun (n : Nat) => @Nat.rec (fun (k : Nat) => @Eq LiteralCodeValue (literal_decode (literal_nat_code k)) (LiteralCodeValue.natVal k)) (@Eq.refl LiteralCodeValue (LiteralCodeValue.natVal Nat.zero)) (fun (k : Nat) (ih : @Eq LiteralCodeValue (literal_decode (literal_nat_code k)) (LiteralCodeValue.natVal k)) => @Eq.cong LiteralCodeValue LiteralCodeValue (fun (v : LiteralCodeValue) => literal_next (literal_next v)) (literal_decode (literal_nat_code k)) (LiteralCodeValue.natVal k) ih) n",
            "Decoding an encoded natural returns that exact natural, by induction on the value.",
            &["literal_decode", "literal_nat_code", "literal_next", "Eq.cong"],
        )?;
        theorem(
            self,
            "literal_string_decode",
            "forall (n : Nat), @Eq LiteralCodeValue (literal_decode (literal_string_code n)) (LiteralCodeValue.strVal n)",
            "fun (n : Nat) => @Eq.cong LiteralCodeValue LiteralCodeValue literal_next (literal_decode (literal_nat_code n)) (LiteralCodeValue.natVal n) (literal_nat_decode n)",
            "Decoding an encoded string returns that exact interned string identity.",
            &["literal_nat_decode", "literal_string_code", "literal_next", "Eq.cong"],
        )?;
        theorem(
            self,
            "literal_decode_encode",
            "forall (v : LiteralCodeValue), @Eq LiteralCodeValue (literal_decode (literal_encode v)) v",
            "fun (v : LiteralCodeValue) => @LiteralCodeValue.rec (fun (w : LiteralCodeValue) => @Eq LiteralCodeValue (literal_decode (literal_encode w)) w) literal_nat_decode literal_string_decode v",
            "The codec round trip preserves BOTH the literal kind and its payload for every value.",
            &["literal_nat_decode", "literal_string_decode", "literal_encode"],
        )?;
        theorem(
            self,
            "literal_encode_next",
            "forall (v : LiteralCodeValue), @Eq Nat (literal_encode (literal_next v)) (Nat.succ (literal_encode v))",
            "fun (v : LiteralCodeValue) => @LiteralCodeValue.rec (fun (w : LiteralCodeValue) => @Eq Nat (literal_encode (literal_next w)) (Nat.succ (literal_encode w))) (fun (n : Nat) => @Eq.refl Nat (Nat.succ (literal_nat_code n))) (fun (n : Nat) => @Eq.refl Nat (Nat.succ (Nat.succ (literal_nat_code n)))) v",
            "The decoded-value successor agrees with successor of the encoded payload.",
            &["literal_encode", "literal_next", "literal_nat_code"],
        )?;
        theorem(
            self,
            "literal_encode_decode",
            "forall (n : Nat), @Eq Nat (literal_encode (literal_decode n)) n",
            "fun (n : Nat) => @Nat.rec (fun (k : Nat) => @Eq Nat (literal_encode (literal_decode k)) k) (@Eq.refl Nat Nat.zero) (fun (k : Nat) (ih : @Eq Nat (literal_encode (literal_decode k)) k) => @Eq.trans Nat (literal_encode (literal_next (literal_decode k))) (Nat.succ (literal_encode (literal_decode k))) (Nat.succ k) (literal_encode_next (literal_decode k)) (@Eq.cong Nat Nat Nat.succ (literal_encode (literal_decode k)) k ih)) n",
            "The reverse round trip shows every raw payload decodes to a supported literal value. There are no uninhabited or reserved payloads.",
            &["literal_encode_next", "literal_decode", "Eq.trans", "Eq.cong"],
        )?;
        for (kind, value_ctor, code, result_type, decode) in [
            (
                "nat",
                "natVal",
                "literal_nat_code",
                "literal_nat_type",
                "literal_nat_decode",
            ),
            (
                "string",
                "strVal",
                "literal_string_code",
                "literal_string_type",
                "literal_string_decode",
            ),
        ] {
            theorem(
                self,
                &format!("literal_{kind}_code_type"),
                &format!("forall (n : Nat), @Eq KExpr (literal_type_of_code ({code} n)) {result_type}"),
                &format!("fun (n : Nat) => @Eq.cong LiteralCodeValue KExpr literal_value_type (literal_decode ({code} n)) (LiteralCodeValue.{value_ctor} n) ({decode} n)"),
                "Decode the literal tag and obtain the exact corresponding built-in type.",
                &[decode, "literal_value_type", "Eq.cong"],
            )?;
        }
        theorem(
            self,
            "literal_encode_injective",
            "forall (a : LiteralCodeValue) (b : LiteralCodeValue), @Eq Nat (literal_encode a) (literal_encode b) -> @Eq LiteralCodeValue a b",
            "fun (a : LiteralCodeValue) (b : LiteralCodeValue) (h : @Eq Nat (literal_encode a) (literal_encode b)) => @Eq.trans LiteralCodeValue a (literal_decode (literal_encode a)) b (@Eq.symm LiteralCodeValue (literal_decode (literal_encode a)) a (literal_decode_encode a)) (@Eq.trans LiteralCodeValue (literal_decode (literal_encode a)) (literal_decode (literal_encode b)) b (@Eq.cong Nat LiteralCodeValue literal_decode (literal_encode a) (literal_encode b) h) (literal_decode_encode b))",
            "Equal encoded payloads imply equal decoded literal values, including their kind tags.",
            &["literal_decode_encode", "Eq.cong", "Eq.symm", "Eq.trans"],
        )?;
        theorem(
            self,
            "literal_nat_code_injective",
            "forall (a : Nat) (b : Nat), @Eq Nat (literal_nat_code a) (literal_nat_code b) -> @Eq Nat a b",
            "fun (a : Nat) (b : Nat) (h : @Eq Nat (literal_nat_code a) (literal_nat_code b)) => @Eq.cong LiteralCodeValue Nat literal_value_payload (LiteralCodeValue.natVal a) (LiteralCodeValue.natVal b) (literal_encode_injective (LiteralCodeValue.natVal a) (LiteralCodeValue.natVal b) h)",
            "The natural-value encoding is injective for arbitrary natural values.",
            &["literal_encode_injective", "literal_value_payload", "Eq.cong"],
        )?;
        theorem(
            self,
            "literal_string_code_injective",
            "forall (a : Nat) (b : Nat), @Eq Nat (literal_string_code a) (literal_string_code b) -> @Eq Nat a b",
            "fun (a : Nat) (b : Nat) (h : @Eq Nat (literal_string_code a) (literal_string_code b)) => @Eq.cong LiteralCodeValue Nat literal_value_payload (LiteralCodeValue.strVal a) (LiteralCodeValue.strVal b) (literal_encode_injective (LiteralCodeValue.strVal a) (LiteralCodeValue.strVal b) h)",
            "The string-identity encoding is injective for arbitrary interned identities.",
            &["literal_encode_injective", "literal_value_payload", "Eq.cong"],
        )?;
        theorem(
            self,
            "literal_codes_disjoint",
            "forall (a : Nat) (b : Nat), @Eq Nat (literal_nat_code a) (literal_string_code b) -> Empty",
            "fun (a : Nat) (b : Nat) (h : @Eq Nat (literal_nat_code a) (literal_string_code b)) => @Eq.substType LiteralCodeValue (fun (v : LiteralCodeValue) => @LiteralCodeValue.rec (fun (_ : LiteralCodeValue) => Type) (fun (_ : Nat) => Nat) (fun (_ : Nat) => Empty) v) (LiteralCodeValue.natVal a) (LiteralCodeValue.strVal b) (literal_encode_injective (LiteralCodeValue.natVal a) (LiteralCodeValue.strVal b) h) Nat.zero",
            "No natural literal and string literal share an encoded payload, even when their untagged payloads coincide.",
            &["literal_encode_injective", "Eq.substType", "LiteralCodeValue.rec"],
        )?;

        self.add_recursive_def(
            "def literal_leaf_payload (e : KExpr) : Nat := match e with\n\
             | KExpr.sort u => Nat.zero\n\
             | KExpr.bvar i => Nat.zero\n\
             | KExpr.app f a => Nat.zero\n\
             | KExpr.lam A b => Nat.zero\n\
             | KExpr.pi A B => Nat.zero\n\
             | KExpr.const n us => Nat.zero\n\
             | KExpr.let_ A v b => Nat.zero\n\
             | KExpr.proj s i e => Nat.zero\n\
             | KExpr.lit n => n",
            "Project a literal leaf's encoded payload. Non-literal cases are unused defaults, not a representation of those terms.",
        )?;
        theorem(
            self,
            "literal_kinds_distinct",
            "forall (a : Nat) (b : Nat), @Eq KExpr (literal_nat a) (literal_string b) -> Empty",
            "fun (a : Nat) (b : Nat) (h : @Eq KExpr (literal_nat a) (literal_string b)) => literal_codes_disjoint a b (@Eq.cong KExpr Nat literal_leaf_payload (literal_nat a) (literal_string b) h)",
            "The reflected expression representation distinguishes Nat and String literals for all payloads.",
            &["literal_codes_disjoint", "literal_leaf_payload", "Eq.cong"],
        )?;
        for (name, constructor, code_injective) in [
            (
                "literal_nat_injective",
                "literal_nat",
                "literal_nat_code_injective",
            ),
            (
                "literal_string_injective",
                "literal_string",
                "literal_string_code_injective",
            ),
        ] {
            theorem(
                self,
                name,
                &format!("forall (a : Nat) (b : Nat), @Eq KExpr ({constructor} a) ({constructor} b) -> @Eq Nat a b"),
                &format!("fun (a : Nat) (b : Nat) (h : @Eq KExpr ({constructor} a) ({constructor} b)) => {code_injective} a b (@Eq.cong KExpr Nat literal_leaf_payload ({constructor} a) ({constructor} b) h)"),
                "Expression-level literal representation preserves the exact payload within this literal kind.",
                &[code_injective, "literal_leaf_payload", "Eq.cong"],
            )?;
        }
        self.add_recursive_def(
            "def literal_type_name_code (e : KExpr) : Nat := match e with\n\
             | KExpr.sort u => Nat.zero\n\
             | KExpr.bvar i => Nat.zero\n\
             | KExpr.app f a => Nat.zero\n\
             | KExpr.lam A b => Nat.zero\n\
             | KExpr.pi A B => Nat.zero\n\
             | KExpr.const n us => @Name.rec (fun (_ : Name) => Nat) Nat.zero (fun (_ : Name) (k : Nat) (_ : Nat) => k) n\n\
             | KExpr.let_ A v b => Nat.zero\n\
             | KExpr.proj s i e => Nat.zero\n\
             | KExpr.lit n => Nat.zero",
            "A syntactic discriminator for the two built-in type names, not a definitional-equality decision procedure.",
        )?;
        let smallest_tag = nat_tag.min(string_tag);
        let (zero_case, positive_case) = if nat_tag < string_tag {
            ("Nat", "Empty")
        } else {
            ("Empty", "Nat")
        };
        theorem(
            self,
            "literal_types_distinct",
            "@Eq KExpr literal_nat_type literal_string_type -> Empty",
            &format!("fun (h : @Eq KExpr literal_nat_type literal_string_type) => @Eq.substType Nat (fun (n : Nat) => @Nat.rec (fun (_ : Nat) => Type) {zero_case} (fun (_ : Nat) (_ : Type) => {positive_case}) (Nat.sub n literal_builtin_tag_{smallest_tag})) literal_builtin_nat_tag literal_builtin_string_tag (@Eq.cong KExpr Nat literal_type_name_code literal_nat_type literal_string_type h) Nat.zero"),
            "The exact Nat and String return expressions differ, proved by reducing the validated table's concrete distinct tags. This does not assert non-convertibility in an arbitrary environment.",
            &["literal_type_name_code", "literal_builtin_nat_tag", "literal_builtin_string_tag", "Eq.cong", "Eq.substType", "Nat.rec", "Nat.sub"],
        )?;
        self.add_inductive(
            "inductive LiteralReturn (n : Nat) (T : KExpr) : Type\n\
             | intro : @Eq KExpr T (literal_type_of_code n) -> LiteralReturn n T",
            "Type-valued wrapper for a literal's exact returned type. Its fixed payload and type are explicit uniform parameters, not varying recursor indices.",
        )?;
        self.add_recursive_def(
            "def literal_infer_result (e : KExpr) (T : KExpr) : Type := match e with\n\
             | KExpr.sort u => Nat\n\
             | KExpr.bvar i => Nat\n\
             | KExpr.app f a => Nat\n\
             | KExpr.lam A b => Nat\n\
             | KExpr.pi A B => Nat\n\
             | KExpr.const n us => Nat\n\
             | KExpr.let_ A v b => Nat\n\
             | KExpr.proj s i e => Nat\n\
             | KExpr.lit n => LiteralReturn n T",
            "Inversion motive: an exact return-type equation at literals; no assertion about other expression heads.",
        )?;
        theorem(
            self,
            "literal_return_eq",
            "forall (n : Nat) (T : KExpr), LiteralReturn n T -> @Eq KExpr T (literal_type_of_code n)",
            "fun (n : Nat) (T : KExpr) (h : LiteralReturn n T) => @LiteralReturn.rec n T (fun (_h : LiteralReturn n T) => @Eq KExpr T (literal_type_of_code n)) (fun (heq : @Eq KExpr T (literal_type_of_code n)) => heq) h",
            "Extract the proved equation from a literal return witness, using the recursor's explicit uniform parameters.",
            &["LiteralReturn.rec"],
        )?;
        // The string payload's decoding (`literal_string_codec`): the payload
        // IS the literal's character list, through a bijection proved both ways.
        self.add_literal_string_codec()
    }
}

#[cfg(test)]
mod tests {
    use super::theorem;
    use crate::spec::Specification;
    use crate::test_utils::run_with_stack;
    use clean_kernel::Environment;
    use std::collections::HashMap;

    fn literal_spec(red_env_interning_override: Option<String>) -> Specification {
        let mut spec = Specification {
            env: Environment::new(),
            definitions: HashMap::new(),
            red_env_script_override: None,
            red_env_interning_override,
            model_unit_source: crate::spec::ModelUnitSource::default(),
        };
        spec.add_foundation_types().expect("foundation types");
        spec.add_foundation_arith_lemmas()
            .expect("arithmetic lemmas");
        spec.add_foundation_arith_witnesses()
            .expect("arithmetic witnesses");
        spec.add_foundation_arith_positivity()
            .expect("arithmetic positivity");
        spec.add_foundation_arith_transport()
            .expect("arithmetic transport");
        spec.add_expr_model().expect("expression model");
        spec.add_literal_model().expect("literal codec and proofs");
        spec
    }

    #[test]
    fn literal_codec_roundtrip_and_kind_separation_are_kernel_checked() {
        run_with_stack(|| {
            // This early proof test must not depend on publishing a new whole-
            // environment snapshot. Production/default name fidelity is checked
            // by the reflector and full-spec gates against the committed table.
            let mut spec = literal_spec(Some("0\tKExpr\n1\tNat\n2\tString\n".to_string()));

            for (kind, real_name) in [("nat", "Nat"), ("string", "String")] {
                let tag = spec
                    .reflected_name_tag(real_name)
                    .expect("shared builtin tag");
                theorem(
                    &mut spec,
                    &format!("literal_builtin_{kind}_table_fidelity"),
                    &format!("@Eq Name literal_builtin_{kind}_name (Name.str Name.anonymous literal_builtin_tag_{tag})"),
                    &format!("@Eq.refl Name literal_builtin_{kind}_name"),
                    "Kernel-checked regression: the early builtin alias is exactly the validated active table entry.",
                    &[],
                )
                .expect("builtin alias matches the shared table");

                theorem(
                    &mut spec,
                    &format!("literal_return_{kind}_extraction_regression"),
                    &format!("@Eq KExpr literal_{kind}_type (literal_type_of_code (literal_{kind}_code Nat.zero))"),
                    &format!("literal_return_eq (literal_{kind}_code Nat.zero) literal_{kind}_type (@LiteralReturn.intro (literal_{kind}_code Nat.zero) literal_{kind}_type (@Eq.symm KExpr (literal_type_of_code (literal_{kind}_code Nat.zero)) literal_{kind}_type (literal_{kind}_code_type Nat.zero)))"),
                    "Early-stage regression: construct a literal return wrapper and extract its checked equation before full context-refinement registration.",
                    &[],
                )
                .expect("literal return wrapper and extraction kernel-check");
            }

            for name in [
                "literal_decode_encode",
                "literal_encode_decode",
                "literal_encode_injective",
                "literal_nat_injective",
                "literal_string_injective",
                "literal_kinds_distinct",
                "literal_types_distinct",
                "literal_builtin_nat_table_fidelity",
                "literal_builtin_string_table_fidelity",
                "literal_return_eq",
                "literal_return_nat_extraction_regression",
                "literal_return_string_extraction_regression",
            ] {
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have no hidden axiom dependencies"
                );
            }

            for (name, lhs, rhs) in [
                (
                    "literal_kind_collision_must_fail",
                    "literal_nat Nat.zero",
                    "literal_string Nat.zero",
                ),
                (
                    "literal_value_collision_must_fail",
                    "literal_nat Nat.zero",
                    "literal_nat (Nat.succ Nat.zero)",
                ),
                (
                    "literal_type_collision_must_fail",
                    "literal_nat_type",
                    "literal_string_type",
                ),
            ] {
                let result = theorem(
                    &mut spec,
                    name,
                    &format!("@Eq KExpr ({lhs}) ({rhs})"),
                    &format!("@Eq.refl KExpr ({lhs})"),
                    "Negative control: the kernel must reject this false identification.",
                    &[],
                );
                assert!(result.is_err(), "kernel accepted {name}");
            }
        });
    }

    #[test]
    fn literal_builtin_distinctness_handles_the_other_valid_tag_order() {
        run_with_stack(|| {
            let spec = literal_spec(Some("0\tString\n1\tNat\n".to_string()));
            assert_eq!(spec.reflected_name_tag("Nat").expect("Nat tag"), 1);
            assert_eq!(spec.reflected_name_tag("String").expect("String tag"), 0);
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, "literal_types_distinct")
                    .is_empty(),
                "changing the table order must preserve a checked, axiom-free distinction proof"
            );
        });
    }
}
