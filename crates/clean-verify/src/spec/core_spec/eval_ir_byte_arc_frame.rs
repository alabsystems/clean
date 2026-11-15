// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sparse observation frames for TWO sequential selected Usize64 increments.
//!
//! These operations invoke the existing byte fetch-add model, not a substitute
//! Rust body. Counter bytes, canonical layout, accessible extents and the two
//! old-count bounds are INPUT obligations. They do not establish a live Arc:
//! positive strong counts, provenance, ownership, headers, actual field/tag
//! offsets and source/nominal attachment remain separate caller obligations.
//!
//! Rust Arc::clone checks old_size > isize::MAX AFTER its increment. Equality
//! is allowed. The bounds below describe the sequential non-aborting path;
//! neither abort execution nor nonmutation on abort is claimed. The alias case
//! separately bounds the second OLD count, n + 1, and really produces n + 2.
//! No concurrency, ordering, interference or whole-Name validity is modeled.
//!
//! Observations are arbitrary sparse ranges; unobserved padding may be undef.
//! A supplied valid cached-word predicate is carried, not invented or proved
//! from a guessed hash algorithm. Authentic warm Name::Str composition is a
//! downstream consumer, not established by synthetic fixture addresses.

use super::eval_ir_byte_atomic::with_declaration_name;
use crate::spec::{SpecError, Specification};

const RESULT: &str = "IRByteMemoryResultV1";
const OPTION: &str = "IROption Nat";
const MAX: &str = "9223372036854775807";
const LAYOUT: &str = "IRByteLayoutV1.mk (IRTy.usize_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)";
const ALIGN: &str = "ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1
  (IRByteLayoutV1.mk (IRTy.usize_ 64) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)))";

const DEFINITIONS: &[(&str, &str)] = &[
    (
        "ir_byte_arc_clone_old_allowed_v1",
        r"def ir_byte_arc_clone_old_allowed_v1 (old : Nat) : Prop :=
Nat.le old 9223372036854775807",
    ),
    (
        "ir_byte_arc_count_pair_finish_v1",
        r"def ir_byte_arc_count_pair_finish_v1 (firstOld : IRScalar)
  (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value secondOld memory =>
    IRByteMemoryResultV1.value
      (IRScalar.aggv (IRScalar.vcons firstOld (IRScalar.vcons secondOld IRScalar.vnil))) memory
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory",
    ),
    (
        "ir_byte_arc_count_pair_after_first_v1",
        r"def ir_byte_arc_count_pair_after_first_v1 (ctx : IRByteContextV1) (second : Nat)
  (result : IRByteMemoryResultV1) : IRByteMemoryResultV1 :=
match result with
| IRByteMemoryResultV1.value firstOld memory =>
    ir_byte_arc_count_pair_finish_v1 firstOld
      (ir_byte_fetch_add_relaxed_usize_seq_v1 64 ctx (IRScalar.ptr_ second) (IRScalar.int_ 1) memory)
| IRByteMemoryResultV1.fault outcome memory => IRByteMemoryResultV1.fault outcome memory",
    ),
    (
        "ir_byte_arc_count_pair_seq_v1",
        r"def ir_byte_arc_count_pair_seq_v1 (ctx : IRByteContextV1) (mem : IRByteMemoryV1)
  (first second : Nat) : IRByteMemoryResultV1 :=
ir_byte_arc_count_pair_after_first_v1 ctx second
  (ir_byte_fetch_add_relaxed_usize_seq_v1 64 ctx (IRScalar.ptr_ first) (IRScalar.int_ 1) mem)",
    ),
    (
        "ir_byte_arc_count_pair_old_at_v1",
        r"def ir_byte_arc_count_pair_old_at_v1 (result : IRByteMemoryResultV1)
  (index : Nat) : IROption IRScalar :=
match result with
| IRByteMemoryResultV1.value olds memory => match olds with
  | IRScalar.aggv spine => ir_vals_get spine index
  | _ => @IROption.none IRScalar
| IRByteMemoryResultV1.fault outcome memory => @IROption.none IRScalar",
    ),
    (
        "ir_byte_arc_clone_old_guard_v1",
        r"def ir_byte_arc_clone_old_guard_v1 (old : Nat)
  (allowed : ir_byte_arc_clone_old_allowed_v1 old) :
@Eq Bool (ir_nat_ltb 9223372036854775807 old) Bool.false :=
ir_byte_allocation_ltb_false_v1 9223372036854775807 old allowed",
    ),
    (
        "ir_byte_arc_clone_increment_bounded_v1",
        r"def ir_byte_arc_clone_increment_bounded_v1 (old : Nat)
  (allowed : ir_byte_arc_clone_old_allowed_v1 old) :
Nat.lt (Nat.add old 1) ir_byte_limit_v1 :=
@Nat.le_trans (Nat.succ (Nat.add old 1)) (Nat.succ (Nat.add 9223372036854775807 1))
  ir_byte_limit_v1
  (@Nat.succ_le_succ (Nat.add old 1) (Nat.add 9223372036854775807 1)
    (@Nat.succ_le_succ old 9223372036854775807 allowed))
  (Nat.le_add_right (Nat.succ (Nat.add 9223372036854775807 1)) 9223372036854775807)",
    ),
    (
        "ir_byte_usize64_rep_disjoint_write_v1",
        r"def ir_byte_usize64_rep_disjoint_write_v1
  (mem : IRByteMemoryV1) (readBase writeBase word count : Nat)
  (apart : Or (Nat.le (Nat.add readBase 8) writeBase)
    (Nat.le (Nat.add writeBase 8) readBase))
  (rep : ir_byte_usize64_rep_v1 mem readBase count) :
ir_byte_usize64_rep_v1
  (IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 mem)
    (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) writeBase 8 word)
    (ir_byte_mem_next_v1 mem)) readBase count :=
fun (offset : Nat) (inside : Nat.lt offset 8) =>
  @Eq.trans (IROption Nat)
    (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 mem) writeBase 8 word (Nat.add readBase offset))
    (ir_byte_mem_bytes_v1 mem (Nat.add readBase offset))
    (@IROption.some Nat (Nat.mod (Nat.div count (ir_nat_pow2 (Nat.mul 8 offset))) 256))
    (ir_byte_write_outside_v1 (ir_byte_mem_bytes_v1 mem) writeBase 8 word
      (Nat.add readBase offset)
      (ir_byte_disjoint_range_point_v1 readBase 8 writeBase 8 offset apart inside))
    (rep offset inside)",
    ),
];

fn written(mem: &str, address: &str, word: &str) -> String {
    format!(
        "IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 ({mem}))
  (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 ({mem})) ({address}) 8 ({word}))
  (ir_byte_mem_next_v1 ({mem}))"
    )
}

fn pair(first: &str, second: &str) -> String {
    format!(
        "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ ({first}))
  (IRScalar.vcons (IRScalar.int_ ({second})) IRScalar.vnil))"
    )
}

fn congr(a: &str, b: &str, function: &str, left: &str, right: &str, proof: &str) -> String {
    format!("ir_eq_cong ({a}) ({b}) ({function}) ({left}) ({right}) ({proof})")
}

fn trans(ty: &str, left: &str, middle: &str, right: &str, first: &str, second: &str) -> String {
    format!("@Eq.trans ({ty}) ({left}) ({middle}) ({right})\n  ({first})\n  ({second})")
}

fn common_telescope() -> String {
    format!(
        "(ctx : IRByteContextV1) (mem : IRByteMemoryV1) (p n : Nat)
  (pBound : Nat.lt p ir_byte_limit_v1)
  (layoutFound : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx (IRTy.usize_ 64))
    (@IROption.some IRByteLayoutV1 ({LAYOUT})))
  (pAccess : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) p 8 ({ALIGN})) Bool.true)
  (pRep : ir_byte_usize64_rep_v1 mem p n)"
    )
}

fn telescope(alias: bool) -> String {
    let common = common_telescope();
    if alias {
        format!(
            "{common}
  (secondAllowed : ir_byte_arc_clone_old_allowed_v1 (Nat.add n 1))"
        )
    } else {
        format!(
            "{common} (q m : Nat)
  (qBound : Nat.lt q ir_byte_limit_v1)
  (qAccess : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) q 8 ({ALIGN})) Bool.true)
  (qRep : ir_byte_usize64_rep_v1 mem q m)
  (firstAllowed : ir_byte_arc_clone_old_allowed_v1 n)
  (secondAllowed : ir_byte_arc_clone_old_allowed_v1 m)
  (apart : Or (Nat.le (Nat.add q 8) p) (Nat.le (Nat.add p 8) q))"
        )
    }
}

fn args(alias: bool) -> &'static str {
    if alias {
        "ctx mem p n pBound layoutFound pAccess pRep secondAllowed"
    } else {
        "ctx mem p n pBound layoutFound pAccess pRep q m qBound qAccess qRep firstAllowed secondAllowed apart"
    }
}

fn suffix(alias: bool) -> &'static str {
    if alias {
        "same"
    } else {
        "distinct"
    }
}

fn second_location(alias: bool) -> &'static str {
    if alias {
        "p"
    } else {
        "q"
    }
}

fn second_count(alias: bool) -> &'static str {
    if alias {
        "Nat.add n 1"
    } else {
        "m"
    }
}

fn first_memory() -> String {
    written("mem", "p", "Nat.add n 1")
}

fn final_memory(alias: bool) -> String {
    written(
        &first_memory(),
        second_location(alias),
        &format!("Nat.add ({}) 1", second_count(alias)),
    )
}

fn actual(alias: bool) -> String {
    format!(
        "ir_byte_arc_count_pair_seq_v1 ctx mem p {}",
        second_location(alias)
    )
}

fn expected(alias: bool) -> String {
    format!(
        "{RESULT}.value ({}) ({})",
        pair("n", second_count(alias)),
        final_memory(alias)
    )
}

fn execution(alias: bool) -> String {
    format!(
        "ir_byte_arc_count_pair_{}_v1 {}",
        suffix(alias),
        args(alias)
    )
}

fn execution_source(alias: bool) -> (String, String) {
    let first = first_memory();
    let last = final_memory(alias);
    let q = second_location(alias);
    let m = second_count(alias);
    let allowed = if alias {
        format!("@Nat.le_trans n (Nat.add n 1) {MAX} (Nat.le_add_right n 1) secondAllowed")
    } else {
        "firstAllowed".to_owned()
    };
    let first_proof = format!(
        "ir_byte_fetch_add_relaxed_usize64_seq_below_v1 ctx mem p n 1
  pBound layoutFound pAccess pRep (ir_byte_arc_clone_increment_bounded_v1 n ({allowed}))"
    );
    let rep = if alias {
        "ir_byte_usize64_rep_write_v1 mem p (Nat.add n 1)".to_owned()
    } else {
        "ir_byte_usize64_rep_disjoint_write_v1 mem q p (Nat.add n 1) m apart qRep".to_owned()
    };
    let (bound, access) = if alias {
        ("pBound", "pAccess")
    } else {
        ("qBound", "qAccess")
    };
    let second_proof = format!("ir_byte_fetch_add_relaxed_usize64_seq_below_v1 ctx ({first}) ({q}) ({m}) 1
  {bound} layoutFound {access} ({rep}) (ir_byte_arc_clone_increment_bounded_v1 ({m}) secondAllowed)");
    let first_actual =
        "ir_byte_fetch_add_relaxed_usize_seq_v1 64 ctx (IRScalar.ptr_ p) (IRScalar.int_ 1) mem";
    let first_expected = format!("{RESULT}.value (IRScalar.int_ n) ({first})");
    let after = format!("ir_byte_arc_count_pair_after_first_v1 ctx ({q})");
    let middle = format!("{after} ({first_expected})");
    let second_actual = format!("ir_byte_fetch_add_relaxed_usize_seq_v1 64 ctx (IRScalar.ptr_ ({q})) (IRScalar.int_ 1) ({first})");
    let second_expected = format!("{RESULT}.value (IRScalar.int_ ({m})) ({last})");
    let proof = trans(
        RESULT,
        &actual(alias),
        &middle,
        &expected(alias),
        &congr(
            RESULT,
            RESULT,
            &after,
            first_actual,
            &first_expected,
            &first_proof,
        ),
        &congr(
            RESULT,
            RESULT,
            "ir_byte_arc_count_pair_finish_v1 (IRScalar.int_ n)",
            &second_actual,
            &second_expected,
            &second_proof,
        ),
    );
    let name = format!("ir_byte_arc_count_pair_{}_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} :\n@Eq {RESULT} ({}) ({}) :=\n{proof}",
            telescope(alias),
            actual(alias),
            expected(alias)
        ),
    )
}

enum Observation {
    FirstOld,
    SecondOld,
    Allocations,
    Cursor,
}

fn observation_source(alias: bool, observation: Observation) -> (String, String) {
    let (observation, ty, function, endpoint) = match observation {
        Observation::FirstOld => ("first_old", "IROption IRScalar", "fun (r : IRByteMemoryResultV1) => ir_byte_arc_count_pair_old_at_v1 r 0".to_owned(), "@IROption.some IRScalar (IRScalar.int_ n)".to_owned()),
        Observation::SecondOld => ("second_old", "IROption IRScalar", "fun (r : IRByteMemoryResultV1) => ir_byte_arc_count_pair_old_at_v1 r 1".to_owned(), format!("@IROption.some IRScalar (IRScalar.int_ ({}))", second_count(alias))),
        Observation::Allocations => ("allocations", "IRList IRByteAllocationV1", "fun (r : IRByteMemoryResultV1) => ir_byte_mem_allocs_v1 (ir_byte_fetch_add_memory_v1 r)".to_owned(), "ir_byte_mem_allocs_v1 mem".to_owned()),
        Observation::Cursor => ("cursor", "Nat", "fun (r : IRByteMemoryResultV1) => ir_byte_mem_next_v1 (ir_byte_fetch_add_memory_v1 r)".to_owned(), "ir_byte_mem_next_v1 mem".to_owned()),
    };
    let name = format!("ir_byte_arc_count_pair_{}_{observation}_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} :\n@Eq ({ty}) (({function}) ({})) ({endpoint}) :=\n{}",
            telescope(alias),
            actual(alias),
            congr(
                RESULT,
                ty,
                &function,
                &actual(alias),
                &expected(alias),
                &execution(alias)
            )
        ),
    )
}

fn new_count_source(alias: bool, first_lane: bool) -> (String, String) {
    let first = first_memory();
    let last = final_memory(alias);
    let address = if first_lane {
        "p"
    } else {
        second_location(alias)
    };
    // Both observations of an aliased cell see the FINAL n + 2, not n + 1.
    let word = if alias || !first_lane {
        format!("Nat.add ({}) 1", second_count(alias))
    } else {
        "Nat.add n 1".to_owned()
    };
    let observe = format!(
        "fun (r : {RESULT}) => ir_byte_read_word_v1
  (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 r)) 8 ({address})"
    );
    let middle = format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({last})) 8 ({address})");
    let endpoint = format!("@IROption.some Nat ({word})");
    let write_read = if alias || !first_lane {
        format!(
            "ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 ({first}))
  ({address}) ({word})
  (ir_byte_arc_clone_increment_bounded_v1 ({}) secondAllowed)",
            second_count(alias)
        )
    } else {
        let earlier = format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({first})) 8 p");
        let reverse_apart = "Or.rec
  (fun (before : Nat.le (Nat.add q 8) p) =>
    @Or.inr (Nat.le (Nat.add p 8) q) (Nat.le (Nat.add q 8) p) before)
  (fun (after : Nat.le (Nat.add p 8) q) =>
    @Or.inl (Nat.le (Nat.add p 8) q) (Nat.le (Nat.add q 8) p) after) apart";
        trans(
            OPTION,
            &middle,
            &earlier,
            &endpoint,
            &format!(
                "ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 ({first}))
  p 8 q 8 (Nat.add m 1) ({reverse_apart})"
            ),
            "ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) p (Nat.add n 1)
  (ir_byte_arc_clone_increment_bounded_v1 n firstAllowed)",
        )
    };
    let lane = if first_lane { "first" } else { "second" };
    let name = format!("ir_byte_arc_count_pair_{}_{lane}_new_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} :\n@Eq ({OPTION}) ({}) ({endpoint}) :=\n{}",
            telescope(alias),
            read_post(alias, address, "8"),
            trans(
                OPTION,
                &read_post(alias, address, "8"),
                &middle,
                &endpoint,
                &congr(
                    RESULT,
                    OPTION,
                    &observe,
                    &actual(alias),
                    &expected(alias),
                    &execution(alias)
                ),
                &write_read
            )
        ),
    )
}

fn read_post(alias: bool, base: &str, size: &str) -> String {
    format!(
        "ir_byte_read_word_v1
  (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 ({}))) ({size}) ({base})",
        actual(alias)
    )
}

fn frame_extra(alias: bool) -> String {
    let q = second_location(alias);
    format!("(readBase readSize : Nat)
  (firstApart : Or (Nat.le (Nat.add readBase readSize) p) (Nat.le (Nat.add p 8) readBase))
  (secondApart : Or (Nat.le (Nat.add readBase readSize) ({q})) (Nat.le (Nat.add ({q}) 8) readBase))")
}

fn frame_args() -> &'static str {
    "readBase readSize firstApart secondApart"
}

fn frame_source(alias: bool) -> (String, String) {
    let first = first_memory();
    let last = final_memory(alias);
    let m = second_count(alias);
    let q = second_location(alias);
    let observe = "fun (r : IRByteMemoryResultV1) => ir_byte_read_word_v1
  (ir_byte_mem_bytes_v1 (ir_byte_fetch_add_memory_v1 r)) readSize readBase";
    let middle = format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({last})) readSize readBase");
    let earlier =
        format!("ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 ({first})) readSize readBase");
    let endpoint = "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) readSize readBase";
    let writes = trans(OPTION, &middle, &earlier, endpoint,
        &format!("ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 ({first})) readBase readSize ({q}) 8 (Nat.add ({m}) 1) secondApart"),
        "ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 mem) readBase readSize p 8 (Nat.add n 1) firstApart");
    let name = format!("ir_byte_arc_count_pair_{}_range_frame_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} {} :\n@Eq ({OPTION}) ({}) ({endpoint}) :=\n{}",
            telescope(alias),
            frame_extra(alias),
            read_post(alias, "readBase", "readSize"),
            trans(
                OPTION,
                &read_post(alias, "readBase", "readSize"),
                &middle,
                endpoint,
                &congr(
                    RESULT,
                    OPTION,
                    observe,
                    &actual(alias),
                    &expected(alias),
                    &execution(alias)
                ),
                &writes
            )
        ),
    )
}

fn sparse_source(alias: bool) -> (String, String) {
    let q = second_location(alias);
    let apart = |counter: &str| {
        format!("Or (Nat.le (Nat.add base size) ({counter})) (Nat.le (Nat.add ({counter}) 8) base)")
    };
    let name = format!("ir_byte_arc_count_pair_{}_sparse_frame_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {}
  (observed : Nat -> Nat -> Prop)
  (firstApart : forall (base size : Nat), observed base size -> {})
  (secondApart : forall (base size : Nat), observed base size -> {}) :
forall (base size : Nat), observed base size ->
  @Eq ({OPTION}) ({}) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size base) :=
fun (base size : Nat) (selected : observed base size) =>
  ir_byte_arc_count_pair_{}_range_frame_v1 {} base size
    (firstApart base size selected) (secondApart base size selected)",
            telescope(alias),
            apart("p"),
            apart(q),
            read_post(alias, "base", "size"),
            suffix(alias),
            args(alias)
        ),
    )
}

fn cached_source(alias: bool) -> (String, String) {
    let initial = "ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) readSize readBase";
    let endpoint = "@IROption.some Nat cached";
    let equality = format!(
        "@Eq ({OPTION}) ({}) ({endpoint})",
        read_post(alias, "readBase", "readSize")
    );
    let proof = trans(
        OPTION,
        &read_post(alias, "readBase", "readSize"),
        initial,
        endpoint,
        &format!(
            "ir_byte_arc_count_pair_{}_range_frame_v1 {} {}",
            suffix(alias),
            args(alias),
            frame_args()
        ),
        "cachedRep",
    );
    let name = format!("ir_byte_arc_count_pair_{}_cached_word_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} {}
  (cached : Nat) (valid : Nat -> Prop) (inputValid : valid cached)
  (cachedRep : @Eq ({OPTION}) ({initial}) ({endpoint})) :
And (valid cached) ({equality}) :=
@And.intro (valid cached) ({equality}) inputValid ({proof})",
            telescope(alias),
            frame_extra(alias)
        ),
    )
}

fn builtin_frame_source(alias: bool, atom: &str, length: usize) -> (String, String) {
    let first = first_memory();
    let last = final_memory(alias);
    let q = second_location(alias);
    let m = second_count(alias);
    let decode = |mem: &str| {
        format!("ir_byte_builtin_name_atom_v1 ({mem}) IRTy.fatstr_ (IRScalar.fat_ data {length})")
    };
    let ty = "IROption IRBuiltinNameAtomV1";
    let observer = format!(
        "fun (r : {RESULT}) => {}",
        decode("ir_byte_fetch_add_memory_v1 r")
    );
    let middle = decode(&last);
    let earlier = decode(&first);
    let endpoint = decode("mem");
    let writes = trans(ty, &middle, &earlier, &endpoint,
        &format!("ir_byte_builtin_{atom}_write_frame_v1 (ir_byte_mem_allocs_v1 mem)
  (ir_byte_mem_bytes_v1 ({first})) (ir_byte_mem_next_v1 mem) data ({q}) 8 (Nat.add ({m}) 1) secondApart"),
        &format!("ir_byte_builtin_{atom}_write_frame_v1 (ir_byte_mem_allocs_v1 mem)
  (ir_byte_mem_bytes_v1 mem) (ir_byte_mem_next_v1 mem) data p 8 (Nat.add n 1) firstApart"));
    let name = format!("ir_byte_arc_count_pair_{}_{atom}_frame_v1", suffix(alias));
    (
        name.clone(),
        format!(
            "def {name} {} (data : Nat)
  (firstApart : Or (Nat.le (Nat.add data {length}) p) (Nat.le (Nat.add p 8) data))
  (secondApart : Or (Nat.le (Nat.add data {length}) ({q})) (Nat.le (Nat.add ({q}) 8) data)) :
@Eq ({ty}) (({observer}) ({})) ({endpoint}) :=\n{}",
            telescope(alias),
            actual(alias),
            trans(
                ty,
                &format!("({observer}) ({})", actual(alias)),
                &middle,
                &endpoint,
                &congr(
                    RESULT,
                    ty,
                    &observer,
                    &actual(alias),
                    &expected(alias),
                    &execution(alias)
                ),
                &writes
            )
        ),
    )
}

pub(super) fn declarations() -> Vec<(String, String)> {
    let mut declarations = DEFINITIONS
        .iter()
        .map(|(name, source)| (name.to_string(), source.to_string()))
        .collect::<Vec<_>>();
    for alias in [false, true] {
        declarations.push(execution_source(alias));
        for observation in [
            Observation::FirstOld,
            Observation::SecondOld,
            Observation::Allocations,
            Observation::Cursor,
        ] {
            declarations.push(observation_source(alias, observation));
        }
        declarations.push(new_count_source(alias, true));
        declarations.push(new_count_source(alias, false));
        declarations.push(frame_source(alias));
        declarations.push(sparse_source(alias));
        declarations.push(cached_source(alias));
        declarations.push(builtin_frame_source(alias, "nat", 3));
        declarations.push(builtin_frame_source(alias, "string", 6));
    }
    declarations
}

impl Specification {
    pub(super) fn add_eval_ir_byte_arc_frame_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in declarations() {
            self.add_recursive_def(&source,
                "Two sequential selected Usize64 updates derive exact old values and sparse observation frames from initialized INPUT bytes and bounds; neither live Arc, warm Name/hash correctness, Rust binding, concurrent atomicity nor native proof authority.")
                .map_err(|error| with_declaration_name(&name, error))?;
            self.verify_definition(&name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_arc_frame_tests.rs"]
mod tests;
