// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The DECODING of a string literal's payload: `literal_string n` is the
//! literal whose characters are `string_lit_chars n`.
//!
//! `literal_string n` carries one `Nat`, the payload of the tagged `KExpr.lit`
//! leaf (`literal_model`). Until this stage that payload was an opaque interned
//! identity, so no rule could state what the deployed
//! `string_lit_to_constructor` does with a literal (expand it to
//! `String.ofList [Char.ofNat c, ...]`). Here the payload IS the character list,
//! through a bijection `ListType Nat <-> Nat` proved in both directions:
//!
//! - `string_lit_code` encodes: `[] -> 0`, `c :: cs -> 2^c * (2 * code cs + 1)`,
//!   built from the literal codec's own doubling (`literal_nat_code`) and odd
//!   successor (`literal_string_code`), so no arithmetic lemma is assumed;
//! - `string_lit_chars` decodes: it iterates `string_lit_next` (the binary
//!   successor read on that representation, structural on the list) `n` times
//!   from the empty list;
//! - `string_lit_code_chars` proves every payload is the code of its decoding
//!   (the encoding is onto), and `string_lit_code_injective` that distinct
//!   character lists never share a payload; `string_lit_chars_code` is the
//!   round trip the other way. So no payload is junk, and the decoding is a
//!   function of the payload alone: no interning table, no premise.
//!
//! The representation obligation this discharges: a deployed
//! `Literal::String(s)` is `literal_string (string_lit_code cs)` for `cs` the
//! Unicode scalar values of `s` in order (what `s.chars()` yields, the list
//! `string_lit_to_constructor` walks). The scalar-value range a Rust `str`
//! guarantees (`string_lit_chars_valid`) is stated where the expansion rule
//! uses it (`acceptance_cdp_in/string_literal.rs`), after `nat_leb` exists.
//!
//! Evaluation cost, stated: the code of a character `c` doubles `c` times
//! through a unary recursion, so the kernel must never be asked to evaluate a
//! code of a real character; every proof here and every witness keeps codes
//! symbolic (the same syntactic payload on both sides).

use super::literal_model::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// The codec definitions, in registration order.
const DEFINITIONS: &[(&str, &str)] = &[
    (
        r"def string_lit_step (c : Nat) (x : Nat) : Nat := @Nat.rec (fun (_ : Nat) => Nat) (literal_string_code x) (fun (_ : Nat) (r : Nat) => literal_nat_code r) c",
        "One character of the string payload code: 2^c * (2x + 1), through the literal codec's doubling and odd successor.",
    ),
    (
        r"def string_lit_code (cs : ListType Nat) : Nat := @ListType.rec Nat (fun (_ : ListType Nat) => Nat) Nat.zero (fun (c : Nat) (_ : ListType Nat) (ih : Nat) => string_lit_step c ih) cs",
        "Encode a string literal's character list (Unicode scalar values, in order) as its literal payload: [] -> 0, c :: cs -> 2^c * (2 * code cs + 1).",
    ),
    (
        r"def string_lit_bump (cs : ListType Nat) : ListType Nat := @ListType.rec Nat (fun (_ : ListType Nat) => ListType Nat) (@ListType.nil Nat) (fun (c : Nat) (rest : ListType Nat) (_ : ListType Nat) => @ListType.cons Nat (Nat.succ c) rest) cs",
        "Increment the first character code (doubles the payload code; the empty list is fixed).",
    ),
    (
        r"def string_lit_next (cs : ListType Nat) : ListType Nat := @ListType.rec Nat (fun (_ : ListType Nat) => ListType Nat) (@ListType.cons Nat Nat.zero (@ListType.nil Nat)) (fun (c : Nat) (rest : ListType Nat) (ih : ListType Nat) => @Nat.rec (fun (_ : Nat) => ListType Nat) (string_lit_bump ih) (fun (k : Nat) (_ : ListType Nat) => @ListType.cons Nat Nat.zero (@ListType.cons Nat k rest)) c) cs",
        "The character list whose payload code is one more (binary successor on the run-length representation; structural on the list).",
    ),
    (
        r"def string_lit_chars (n : Nat) : ListType Nat := @Nat.rec (fun (_ : Nat) => ListType Nat) (@ListType.nil Nat) (fun (_ : Nat) (cs : ListType Nat) => string_lit_next cs) n",
        "Decode a string literal payload to its character list: string_lit_next iterated n times from the empty list.",
    ),
];

/// `(name, type, value, description, dependencies)`, in registration order.
const PROOFS: &[(&str, &str, &str, &str, &[&str])] = &[
    (
        "string_lit_code_bump",
        r"forall (cs : ListType Nat), @Eq Nat (string_lit_code (string_lit_bump cs)) (literal_nat_code (string_lit_code cs))",
        r"fun (cs : ListType Nat) => @ListType.rec Nat (fun (m : ListType Nat) => @Eq Nat (string_lit_code (string_lit_bump m)) (literal_nat_code (string_lit_code m))) (@Eq.refl Nat Nat.zero) (fun (c : Nat) (rest : ListType Nat) (_ : @Eq Nat (string_lit_code (string_lit_bump rest)) (literal_nat_code (string_lit_code rest))) => @Eq.refl Nat (literal_nat_code (string_lit_step c (string_lit_code rest)))) cs",
        "Incrementing the first character doubles the payload code.",
        &["string_lit_code", "string_lit_bump", "literal_nat_code"],
    ),
    (
        "string_lit_code_next",
        r"forall (cs : ListType Nat), @Eq Nat (string_lit_code (string_lit_next cs)) (Nat.succ (string_lit_code cs))",
        r"fun (cs : ListType Nat) => @ListType.rec Nat (fun (m : ListType Nat) => @Eq Nat (string_lit_code (string_lit_next m)) (Nat.succ (string_lit_code m)))
  (@Eq.refl Nat (Nat.succ Nat.zero))
  (fun (c : Nat) (rest : ListType Nat) (ih : @Eq Nat (string_lit_code (string_lit_next rest)) (Nat.succ (string_lit_code rest))) =>
    @Nat.rec (fun (d : Nat) => @Eq Nat (string_lit_code (string_lit_next (@ListType.cons Nat d rest))) (Nat.succ (string_lit_code (@ListType.cons Nat d rest))))
      (@Eq.trans Nat (string_lit_code (string_lit_bump (string_lit_next rest))) (literal_nat_code (string_lit_code (string_lit_next rest))) (literal_nat_code (Nat.succ (string_lit_code rest)))
        (string_lit_code_bump (string_lit_next rest))
        (@Eq.cong Nat Nat literal_nat_code (string_lit_code (string_lit_next rest)) (Nat.succ (string_lit_code rest)) ih))
      (fun (k : Nat) (_ : @Eq Nat (string_lit_code (string_lit_next (@ListType.cons Nat k rest))) (Nat.succ (string_lit_code (@ListType.cons Nat k rest)))) =>
        @Eq.refl Nat (Nat.succ (literal_nat_code (string_lit_step k (string_lit_code rest)))))
      c)
  cs",
        "string_lit_next is the successor on payload codes.",
        &["string_lit_code_bump", "string_lit_next", "Eq.trans", "Eq.cong"],
    ),
    (
        "string_lit_code_chars",
        r"forall (n : Nat), @Eq Nat (string_lit_code (string_lit_chars n)) n",
        r"fun (n : Nat) => @Nat.rec (fun (k : Nat) => @Eq Nat (string_lit_code (string_lit_chars k)) k) (@Eq.refl Nat Nat.zero)
  (fun (k : Nat) (ih : @Eq Nat (string_lit_code (string_lit_chars k)) k) =>
    @Eq.trans Nat (string_lit_code (string_lit_next (string_lit_chars k))) (Nat.succ (string_lit_code (string_lit_chars k))) (Nat.succ k)
      (string_lit_code_next (string_lit_chars k))
      (@Eq.cong Nat Nat Nat.succ (string_lit_code (string_lit_chars k)) k ih)) n",
        "Every payload is the code of its decoding: the string encoding is onto, so no literal payload is junk.",
        &["string_lit_code_next", "string_lit_chars", "Eq.trans", "Eq.cong"],
    ),
    (
        "string_lit_step_ne_zero",
        r"forall (c : Nat) (x : Nat), @Eq Nat (string_lit_step c x) Nat.zero -> Empty",
        r"fun (c : Nat) (x : Nat) => @Nat.rec (fun (d : Nat) => @Eq Nat (string_lit_step d x) Nat.zero -> Empty)
  (fun (h : @Eq Nat (string_lit_step Nat.zero x) Nat.zero) => literal_codes_disjoint Nat.zero x (@Eq.symm Nat (string_lit_step Nat.zero x) Nat.zero h))
  (fun (k : Nat) (ih : @Eq Nat (string_lit_step k x) Nat.zero -> Empty) (h : @Eq Nat (string_lit_step (Nat.succ k) x) Nat.zero) =>
    ih (literal_nat_code_injective (string_lit_step k x) Nat.zero h))
  c",
        "A nonempty character list never has the empty list's payload.",
        &["literal_codes_disjoint", "literal_nat_code_injective", "Eq.symm"],
    ),
    (
        "string_lit_step_injective",
        r"forall (a : Nat) (x : Nat) (b : Nat) (y : Nat), @Eq Nat (string_lit_step a x) (string_lit_step b y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat a x) (@ProdType.mk Nat Nat b y)",
        r"fun (a : Nat) (x : Nat) => @Nat.rec (fun (a0 : Nat) => forall (b : Nat) (y : Nat), @Eq Nat (string_lit_step a0 x) (string_lit_step b y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat a0 x) (@ProdType.mk Nat Nat b y))
  (fun (b : Nat) (y : Nat) => @Nat.rec (fun (b0 : Nat) => @Eq Nat (string_lit_step Nat.zero x) (string_lit_step b0 y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat Nat.zero x) (@ProdType.mk Nat Nat b0 y))
    (fun (h : @Eq Nat (string_lit_step Nat.zero x) (string_lit_step Nat.zero y)) =>
      @Eq.cong Nat (ProdType Nat Nat) (fun (z : Nat) => @ProdType.mk Nat Nat Nat.zero z) x y (literal_string_code_injective x y h))
    (fun (k : Nat) (_ : @Eq Nat (string_lit_step Nat.zero x) (string_lit_step k y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat Nat.zero x) (@ProdType.mk Nat Nat k y)) (h : @Eq Nat (string_lit_step Nat.zero x) (string_lit_step (Nat.succ k) y)) =>
      @Empty.rec (fun (_ : Empty) => @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat Nat.zero x) (@ProdType.mk Nat Nat (Nat.succ k) y))
        (literal_codes_disjoint (string_lit_step k y) x (@Eq.symm Nat (string_lit_step Nat.zero x) (string_lit_step (Nat.succ k) y) h)))
    b)
  (fun (a1 : Nat) (ih : forall (b : Nat) (y : Nat), @Eq Nat (string_lit_step a1 x) (string_lit_step b y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat a1 x) (@ProdType.mk Nat Nat b y)) (b : Nat) (y : Nat) =>
    @Nat.rec (fun (b0 : Nat) => @Eq Nat (string_lit_step (Nat.succ a1) x) (string_lit_step b0 y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat (Nat.succ a1) x) (@ProdType.mk Nat Nat b0 y))
      (fun (h : @Eq Nat (string_lit_step (Nat.succ a1) x) (string_lit_step Nat.zero y)) =>
        @Empty.rec (fun (_ : Empty) => @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat (Nat.succ a1) x) (@ProdType.mk Nat Nat Nat.zero y))
          (literal_codes_disjoint (string_lit_step a1 x) y h))
      (fun (k : Nat) (_ : @Eq Nat (string_lit_step (Nat.succ a1) x) (string_lit_step k y) -> @Eq (ProdType Nat Nat) (@ProdType.mk Nat Nat (Nat.succ a1) x) (@ProdType.mk Nat Nat k y)) (h : @Eq Nat (string_lit_step (Nat.succ a1) x) (string_lit_step (Nat.succ k) y)) =>
        @Eq.cong (ProdType Nat Nat) (ProdType Nat Nat) (fun (p : ProdType Nat Nat) => @ProdType.rec Nat Nat (fun (_ : ProdType Nat Nat) => ProdType Nat Nat) (fun (u : Nat) (v : Nat) => @ProdType.mk Nat Nat (Nat.succ u) v) p)
          (@ProdType.mk Nat Nat a1 x) (@ProdType.mk Nat Nat k y)
          (ih k y (literal_nat_code_injective (string_lit_step a1 x) (string_lit_step k y) h)))
      b)
  a",
        "One character step is injective in both the character and the rest's code.",
        &["literal_codes_disjoint", "literal_nat_code_injective", "literal_string_code_injective", "Eq.cong", "Empty.rec"],
    ),
    (
        "string_lit_code_injective",
        r"forall (a : ListType Nat) (b : ListType Nat), @Eq Nat (string_lit_code a) (string_lit_code b) -> @Eq (ListType Nat) a b",
        r"fun (a : ListType Nat) => @ListType.rec Nat (fun (a0 : ListType Nat) => forall (b : ListType Nat), @Eq Nat (string_lit_code a0) (string_lit_code b) -> @Eq (ListType Nat) a0 b)
  (fun (b : ListType Nat) => @ListType.rec Nat (fun (b0 : ListType Nat) => @Eq Nat Nat.zero (string_lit_code b0) -> @Eq (ListType Nat) (@ListType.nil Nat) b0)
    (fun (_ : @Eq Nat Nat.zero Nat.zero) => @Eq.refl (ListType Nat) (@ListType.nil Nat))
    (fun (d : Nat) (rest : ListType Nat) (_ : @Eq Nat Nat.zero (string_lit_code rest) -> @Eq (ListType Nat) (@ListType.nil Nat) rest) (h : @Eq Nat Nat.zero (string_lit_step d (string_lit_code rest))) =>
      @Empty.rec (fun (_ : Empty) => @Eq (ListType Nat) (@ListType.nil Nat) (@ListType.cons Nat d rest))
        (string_lit_step_ne_zero d (string_lit_code rest) (@Eq.symm Nat Nat.zero (string_lit_step d (string_lit_code rest)) h)))
    b)
  (fun (c : Nat) (rest : ListType Nat) (ih : forall (b : ListType Nat), @Eq Nat (string_lit_code rest) (string_lit_code b) -> @Eq (ListType Nat) rest b) (b : ListType Nat) =>
    @ListType.rec Nat (fun (b0 : ListType Nat) => @Eq Nat (string_lit_step c (string_lit_code rest)) (string_lit_code b0) -> @Eq (ListType Nat) (@ListType.cons Nat c rest) b0)
      (fun (h : @Eq Nat (string_lit_step c (string_lit_code rest)) Nat.zero) =>
        @Empty.rec (fun (_ : Empty) => @Eq (ListType Nat) (@ListType.cons Nat c rest) (@ListType.nil Nat)) (string_lit_step_ne_zero c (string_lit_code rest) h))
      (fun (d : Nat) (rest2 : ListType Nat) (_ : @Eq Nat (string_lit_step c (string_lit_code rest)) (string_lit_code rest2) -> @Eq (ListType Nat) (@ListType.cons Nat c rest) rest2) (h : @Eq Nat (string_lit_step c (string_lit_code rest)) (string_lit_step d (string_lit_code rest2))) =>
        @Eq.trans (ListType Nat) (@ListType.cons Nat c rest) (@ListType.cons Nat d rest) (@ListType.cons Nat d rest2)
          (@Eq.cong Nat (ListType Nat) (fun (z : Nat) => @ListType.cons Nat z rest) c d
            (@Eq.cong (ProdType Nat Nat) Nat (fun (p : ProdType Nat Nat) => @ProdType.rec Nat Nat (fun (_ : ProdType Nat Nat) => Nat) (fun (u : Nat) (v : Nat) => u) p)
              (@ProdType.mk Nat Nat c (string_lit_code rest)) (@ProdType.mk Nat Nat d (string_lit_code rest2))
              (string_lit_step_injective c (string_lit_code rest) d (string_lit_code rest2) h)))
          (@Eq.cong (ListType Nat) (ListType Nat) (fun (w : ListType Nat) => @ListType.cons Nat d w) rest rest2
            (ih rest2 (@Eq.cong (ProdType Nat Nat) Nat (fun (p : ProdType Nat Nat) => @ProdType.rec Nat Nat (fun (_ : ProdType Nat Nat) => Nat) (fun (u : Nat) (v : Nat) => v) p)
              (@ProdType.mk Nat Nat c (string_lit_code rest)) (@ProdType.mk Nat Nat d (string_lit_code rest2))
              (string_lit_step_injective c (string_lit_code rest) d (string_lit_code rest2) h)))))
      b)
  a",
        "Distinct character lists never share a string payload.",
        &["string_lit_step_injective", "string_lit_step_ne_zero", "Eq.trans", "Eq.cong", "Empty.rec"],
    ),
    (
        "string_lit_chars_code",
        r"forall (cs : ListType Nat), @Eq (ListType Nat) (string_lit_chars (string_lit_code cs)) cs",
        r"fun (cs : ListType Nat) => string_lit_code_injective (string_lit_chars (string_lit_code cs)) cs (string_lit_code_chars (string_lit_code cs))",
        "Decoding the payload of a character list returns that list.",
        &["string_lit_code_injective", "string_lit_code_chars"],
    ),
    (
        "literal_string_decodes",
        r"forall (n : Nat), @Eq KExpr (literal_string n) (literal_string (string_lit_code (string_lit_chars n)))",
        r"fun (n : Nat) => @Eq.cong Nat KExpr literal_string n (string_lit_code (string_lit_chars n)) (@Eq.symm Nat (string_lit_code (string_lit_chars n)) n (string_lit_code_chars n))",
        "Every string literal leaf is the literal of its decoded character list.",
        &["string_lit_code_chars", "literal_string", "Eq.cong", "Eq.symm"],
    ),
];

/// Every proof this stage registers, in registration order.
pub const STRING_LIT_CODEC_PROOF_NAMES: &[&str] = &[
    "string_lit_code_bump",
    "string_lit_code_next",
    "string_lit_code_chars",
    "string_lit_step_ne_zero",
    "string_lit_step_injective",
    "string_lit_code_injective",
    "string_lit_chars_code",
    "literal_string_decodes",
];

impl Specification {
    /// Register the string payload codec (after `add_literal_model`'s codec
    /// lemmas, which it builds on).
    pub(super) fn add_literal_string_codec(&mut self) -> Result<(), SpecError> {
        for (source, description) in DEFINITIONS {
            self.add_recursive_def(source, description)?;
        }
        for (name, ty, value, description, dependencies) in PROOFS {
            theorem(self, name, ty, value, description, dependencies)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_codec_proof_names_match_the_table() {
        let names: Vec<&str> = PROOFS.iter().map(|(name, ..)| *name).collect();
        assert_eq!(names, STRING_LIT_CODEC_PROOF_NAMES);
    }

    #[test]
    fn string_codec_records_parse() {
        for (source, _) in DEFINITIONS {
            clean_parser::parse_decl(source).expect("codec definition parses");
        }
        for (name, ty, value, ..) in PROOFS {
            clean_parser::parse_decl(&format!("def {name} : {ty} := {value}"))
                .expect("codec proof parses");
        }
    }
}
