// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! **Every coverage claim the EvalIR syntax registers against a `trust_ir`
//! enum, held against the enum itself.**
//!
//! `IRUnOp`'s registered description claimed ALL of `trust_ir::UnOp`, in
//! declaration order, and went on claiming it after trust-ir 4f09dab8
//! (WS3.20) added `CtLz`, `CtTz`, `BSwap` and `BitReverse`. Every gate passed,
//! because every gate counted the CLEAN side — a table of pinned constructor
//! counts, which stayed true. The same wave added `RotL`, `RotR` and
//! `FCopySign` to `BinOp` under prose that kept quoting the old total, and a
//! module doc's `Ty` count trailed the enum by three. Nothing compared a claim
//! with the enum it names.
//!
//! This does, mechanically:
//!
//! * each alphabet below is one EXHAUSTIVE match over the `trust_ir` enum —
//!   no wildcard — so a variant trust-ir adds fails to compile here until
//!   someone classifies it (own constructor, carried by an existing one, or
//!   refused);
//! * the variant list is generated from that same match, and each variant's
//!   discriminant must equal its position, so the list is the enum in
//!   declaration order with nothing skipped or repeated;
//! * the REGISTERED constructors, in order, must be exactly the variants' own
//!   images in declaration order — which is what "in declaration order" says,
//!   and which is also each alphabet's constructor COUNT, derived here rather
//!   than pinned in a second table;
//! * the REGISTERED description must state the split the classification
//!   derives: `n/n of trust_ir::E` when every variant has its own constructor,
//!   otherwise `n of the m trust_ir::E variants` naming every variant without
//!   one;
//! * a variant count the EvalIR sources restate in PROSE — digits or words,
//!   as `n trust_ir::E variants`, `n Rust E spellings` or `n/n of
//!   trust_ir::E` — must be the enum's. A comment is not a registered
//!   description, and that is where the last stale count survived.

use clean_kernel::Name;
use clean_verify::spec::Specification;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

/// How an EvalIR alphabet images one `trust_ir` variant.
#[derive(Clone, Copy, Debug)]
enum Image {
    /// Its own constructor, of this (last-component) name.
    Own(&'static str),
    /// No constructor of its own; an existing one carries it. ByteV1's scalar
    /// Bool connectives land on `and_`/`or_`/`xor_` with `IRTy.bool_`.
    Carried(&'static str),
    /// No image at all: a projection refuses it by name.
    Refused,
}

/// One `trust_ir` enum's variants, in declaration order, with their images.
struct Alphabet {
    rust: &'static str,
    rows: Vec<(String, Image)>,
}

/// Build an [`Alphabet`] from ONE exhaustive match over `trust_ir::inst::$enum`.
macro_rules! alphabet {
    ($enum:ident { $($variant:ident => $image:expr),+ $(,)? }) => {{
        use trust_ir::inst::$enum as E;
        // Exhaustive and wildcard-free: this is the compile-time half.
        fn image(op: E) -> Image {
            match op {
                $(E::$variant => $image),+
            }
        }
        let all = [$(E::$variant),+];
        for (position, op) in all.iter().enumerate() {
            assert_eq!(
                *op as usize,
                position,
                "trust_ir::{}::{op:?} is listed out of declaration order (or twice)",
                stringify!($enum)
            );
        }
        Alphabet {
            rust: stringify!($enum),
            rows: all.iter().map(|op| (format!("{op:?}"), image(*op))).collect(),
        }
    }};
}

/// `trust_ir::ty::Ty`'s variant count, from an exhaustive match over it
/// (`{ .. }` matches unit, tuple and struct variants alike).
macro_rules! ty_variant_count {
    ($($variant:ident),+ $(,)?) => {{
        #[allow(dead_code)]
        fn exhaustive(ty: &trust_ir::ty::Ty) {
            match ty {
                trust_ir::TyG::Ext(e) => e.unreachable(),
                $(trust_ir::ty::Ty::$variant { .. } => {}),+
            }
        }
        [$(stringify!($variant)),+].len()
    }};
}

/// Constructor names (last component) of a registered inductive, in
/// REGISTRATION order — `census::ctor_names` returns a set, which cannot say
/// whether the order claim holds.
fn ctors_in_order(spec: &Specification, inductive: &str) -> Vec<String> {
    spec.env()
        .get_inductive(&Name::from_string(inductive))
        .unwrap_or_else(|| panic!("{inductive} is not registered"))
        .constructor_names
        .iter()
        .map(|n| {
            let n = n.to_string();
            n.rsplit_once('.')
                .map_or_else(|| n.clone(), |(_, last)| last.to_string())
        })
        .collect()
}

fn description<'s>(spec: &'s Specification, inductive: &str) -> &'s str {
    &spec
        .get_definition(inductive)
        .unwrap_or_else(|| panic!("{inductive} has no registered definition"))
        .description
}

fn alphabets() -> Vec<(&'static str, Alphabet)> {
    use Image::{Carried, Own, Refused};
    vec![
        (
            "IRBinOp",
            alphabet!(BinOp {
                Add => Own("add"),
                Sub => Own("sub"),
                Mul => Own("mul"),
                UDiv => Own("udiv"),
                SDiv => Own("sdiv"),
                URem => Own("urem"),
                SRem => Own("srem"),
                FAdd => Own("fadd"),
                FSub => Own("fsub"),
                FMul => Own("fmul"),
                FDiv => Own("fdiv"),
                FRem => Own("frem"),
                FMin => Own("fmin"),
                FMax => Own("fmax"),
                And => Own("and_"),
                Or => Own("or_"),
                Xor => Own("xor_"),
                Shl => Own("shl"),
                LShr => Own("lshr"),
                AShr => Own("ashr"),
                BAnd => Carried("and_"),
                BOr => Carried("or_"),
                BXor => Carried("xor_"),
                RotL => Refused,
                RotR => Refused,
                FCopySign => Refused,
            }),
        ),
        (
            "IRUnOp",
            alphabet!(UnOp {
                Neg => Own("neg"),
                FNeg => Own("fneg"),
                FAbs => Own("fabs"),
                FSqrt => Own("fsqrt"),
                FFloor => Own("ffloor"),
                FCeil => Own("fceil"),
                FTrunc => Own("ftrunc"),
                Not => Own("not_"),
                CtPop => Own("ctpop"),
                CtLz => Refused,
                CtTz => Refused,
                BSwap => Refused,
                BitReverse => Refused,
            }),
        ),
        (
            "IROverflowOp",
            alphabet!(OverflowOp {
                AddOverflow => Own("addoverflow"),
                SubOverflow => Own("suboverflow"),
                MulOverflow => Own("muloverflow"),
            }),
        ),
        (
            "IRICmpOp",
            alphabet!(ICmpOp {
                Eq => Own("eq_"),
                Ne => Own("ne_"),
                Ult => Own("ult"),
                Ule => Own("ule"),
                Ugt => Own("ugt"),
                Uge => Own("uge"),
                Slt => Own("slt"),
                Sle => Own("sle"),
                Sgt => Own("sgt"),
                Sge => Own("sge"),
            }),
        ),
        (
            "IRFCmpOp",
            alphabet!(FCmpOp {
                OEq => Own("oeq"),
                ONe => Own("one_"),
                OLt => Own("olt"),
                OLe => Own("ole"),
                OGt => Own("ogt"),
                OGe => Own("oge"),
                UEq => Own("ueq"),
                UNe => Own("une"),
                ULt => Own("ult"),
                ULe => Own("ule"),
                UGt => Own("ugt"),
                UGe => Own("uge"),
            }),
        ),
        (
            "IRCastOp",
            alphabet!(CastOp {
                Trunc => Own("trunc"),
                ZExt => Own("zext"),
                SExt => Own("sext"),
                FPTrunc => Own("fptrunc"),
                FPExt => Own("fpext"),
                FPToUI => Own("fptoui"),
                FPToSI => Own("fptosi"),
                UIToFP => Own("uitofp"),
                SIToFP => Own("sitofp"),
                PtrToInt => Own("ptrtoint"),
                IntToPtr => Own("inttoptr"),
                PtrToPtr => Own("ptrtoptr"),
                Bitcast => Own("bitcast"),
                Transmute => Own("transmute"),
                ReifyFnPointer => Own("reifyfnpointer"),
                FPToSISat => Own("fptosisat"),
                FPToUISat => Own("fptouisat"),
            }),
        ),
    ]
}

/// The statement an alphabet's description must make, derived from its
/// classification, and the variants without a constructor of their own that
/// it must name (none when the claim is the complete `n/n` form).
fn derived_claim(a: &Alphabet) -> (String, Vec<&str>) {
    let own = a
        .rows
        .iter()
        .filter(|(_, i)| matches!(i, Image::Own(_)))
        .count();
    let without: Vec<&str> = a
        .rows
        .iter()
        .filter(|(_, i)| !matches!(i, Image::Own(_)))
        .map(|(v, _)| v.as_str())
        .collect();
    if without.is_empty() {
        (format!("{own}/{own} of trust_ir::{}", a.rust), without)
    } else {
        (
            format!(
                "{own} of the {} trust_ir::{} variants",
                a.rows.len(),
                a.rust
            ),
            without,
        )
    }
}

/// Every alphabet's registered constructors and description, against its enum.
#[test]
fn eval_ir_operator_alphabet_claims_match_the_trust_ir_enums() {
    let spec = build_eval_ir_spec_with_stack();
    let mut wrong = Vec::new();
    for (clean, a) in alphabets() {
        let registered = ctors_in_order(&spec, clean);
        let own: Vec<&str> = a
            .rows
            .iter()
            .filter_map(|(_, i)| match i {
                Image::Own(c) => Some(*c),
                _ => None,
            })
            .collect();
        if registered != own {
            wrong.push(format!(
                "{clean}: registered constructors {registered:?} are not the own images of \
                 trust_ir::{} in declaration order, {own:?}",
                a.rust
            ));
        }
        for (variant, image) in &a.rows {
            if let Image::Carried(c) = image {
                if !registered.iter().any(|r| r == c) {
                    wrong.push(format!(
                        "{clean}: trust_ir::{}::{variant} is classified as carried by `{c}`, \
                         which is not a constructor",
                        a.rust
                    ));
                }
            }
        }
        let desc = description(&spec, clean);
        let (claim, must_name) = derived_claim(&a);
        if !desc.contains(&claim) {
            wrong.push(format!(
                "{clean}: the registered description does not state `{claim}`, which is what \
                 trust_ir::{} derives; it reads: {desc}",
                a.rust
            ));
        }
        for variant in must_name {
            if !desc.contains(variant) {
                wrong.push(format!(
                    "{clean}: trust_ir::{}::{variant} has no constructor of its own, and the \
                     registered description does not name it",
                    a.rust
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "EvalIR coverage claims disagree with the trust_ir enums they name:\n  {}",
        wrong.join("\n  ")
    );
}

/// `trust_ir::ty::Ty`'s variant count, from the exhaustive match.
fn ty_variant_total() -> usize {
    ty_variant_count!(
        I8, I16, I32, I64, I128, U8, U16, U32, U64, U128, Isize, Usize, Char, Error, F16, F32, F64,
        Bool, Vector, Ptr, FatPtr, Unit, Never, Struct, Array, Tuple, Enum, Func, Ref, RefMut,
        PtrConst, PtrMut, Rc, Set, Sequence, Record, Closure, Refine, Dialect, Handle, Storage,
        Tensor,
    )
}

/// `IRTy`'s description states the `trust_ir::Ty` variant count it mirrors
/// (not one-to-one), and that count is the enum's.
#[test]
fn eval_ir_ty_description_states_the_trust_ir_ty_variant_count() {
    let total = ty_variant_total();
    let spec = build_eval_ir_spec_with_stack();
    let desc = description(&spec, "IRTy");
    let claim = format!("the {total} trust_ir::Ty variants");
    assert!(
        desc.contains(&claim),
        "IRTy's registered description must state `{claim}`; it reads: {desc}"
    );
}

/// The claim derivation itself: a complete alphabet claims `n/n`, a partial
/// one claims `n of the m` and must name exactly its unimaged variants.
#[test]
fn the_derived_claim_distinguishes_complete_from_partial() {
    let complete = Alphabet {
        rust: "X",
        rows: vec![("A".into(), Image::Own("a")), ("B".into(), Image::Own("b"))],
    };
    assert_eq!(
        derived_claim(&complete),
        ("2/2 of trust_ir::X".to_string(), vec![])
    );
    let partial = Alphabet {
        rust: "X",
        rows: vec![
            ("A".into(), Image::Own("a")),
            ("B".into(), Image::Carried("a")),
            ("C".into(), Image::Refused),
        ],
    };
    assert_eq!(
        derived_claim(&partial),
        (
            "1 of the 3 trust_ir::X variants".to_string(),
            vec!["B", "C"]
        )
    );
}

/// `n` from `12` or from an English number word below a hundred
/// (`twenty-three`, `Twenty`, `three`); anything else is not a count.
fn count_word(word: &str) -> Option<usize> {
    const UNITS: [&str; 20] = [
        "zero",
        "one",
        "two",
        "three",
        "four",
        "five",
        "six",
        "seven",
        "eight",
        "nine",
        "ten",
        "eleven",
        "twelve",
        "thirteen",
        "fourteen",
        "fifteen",
        "sixteen",
        "seventeen",
        "eighteen",
        "nineteen",
    ];
    const TENS: [&str; 8] = [
        "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety",
    ];
    if let Ok(n) = word.parse() {
        return Some(n);
    }
    let w = word.to_ascii_lowercase();
    let unit = |s: &str| UNITS.iter().position(|u| *u == s);
    let ten = |s: &str| TENS.iter().position(|t| *t == s).map(|i| 20 + 10 * i);
    match w.split_once('-') {
        None => unit(&w).or_else(|| ten(&w)),
        Some((t, u)) => Some(ten(t)? + unit(u).filter(|u| (1..10).contains(u))?),
    }
}

/// Every place `text` states the size of one of `enums`, as
/// `(line, stated, enum)`: `<count> [Rust] <E> variants|spellings` and
/// `<a>/<b> of trust_ir::<E>` (the denominator), with `E` optionally written
/// `trust_ir::E` and in backticks. Words are read across line breaks, so a
/// count wrapped away from its enum is still read.
fn stated_sizes<'e>(text: &str, enums: &[&'e str]) -> Vec<(usize, usize, &'e str)> {
    let trim: &[char] = &[
        '`', '"', '(', ')', ',', '.', ';', ':', '\'', '*', '\\', '[', ']',
    ];
    let words: Vec<(&str, usize)> = text
        .lines()
        .enumerate()
        .flat_map(|(i, line)| {
            line.split_whitespace()
                .map(move |w| (w.trim_matches(trim), i + 1))
        })
        .filter(|(w, _)| !w.is_empty() && !w.chars().all(|c| c == '/' || c == '!'))
        .collect();
    let enum_of = |w: &str| {
        let bare = ["trust_ir::inst::", "trust_ir::ty::", "trust_ir::"]
            .iter()
            .find_map(|p| w.strip_prefix(p))
            .unwrap_or(w);
        enums.iter().copied().find(|e| *e == bare)
    };
    let mut out = Vec::new();
    for (i, (w, line)) in words.iter().enumerate() {
        let next = |k: usize| words.get(i + k).map(|(w, _)| *w);
        if let Some(e) = enum_of(w) {
            if matches!(next(1), Some("variants" | "spellings")) {
                let mut j = i.checked_sub(1);
                if j.is_some_and(|j| words[j].0 == "Rust") {
                    j = j.and_then(|j| j.checked_sub(1));
                }
                if let Some(n) = j.and_then(|j| count_word(words[j].0)) {
                    out.push((*line, n, e));
                }
            }
        }
        if let Some((_, denominator)) = w.split_once('/') {
            if next(1) == Some("of") {
                if let (Some(e), Ok(n)) = (next(2).and_then(enum_of), denominator.parse()) {
                    out.push((*line, n, e));
                }
            }
        }
    }
    out
}

/// Every variant count of a `trust_ir` enum the EvalIR sources restate in
/// prose is the enum's. Spec-free: the sizes come from the exhaustive matches
/// above, the prose from the source files.
#[test]
fn every_restated_trust_ir_variant_count_is_the_enums() {
    let mut sizes: Vec<(&str, usize)> = alphabets()
        .into_iter()
        .map(|(_, a)| (a.rust, a.rows.len()))
        .collect();
    sizes.push(("Ty", ty_variant_total()));
    let names: Vec<&str> = sizes.iter().map(|(e, _)| *e).collect();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = vec![root.join("tests/eval_ir.rs")];
    for dir in ["tests/eval_ir", "src/spec/core_spec"] {
        for entry in std::fs::read_dir(root.join(dir)).expect("an EvalIR source directory") {
            let path = entry.expect("a directory entry").path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            let evalir = dir == "tests/eval_ir" || name.starts_with("eval_ir");
            if evalir && name.ends_with(".rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    let (mut read, mut wrong) = (0, Vec::new());
    for path in &files {
        let text = std::fs::read_to_string(path).expect("an EvalIR source file");
        for (line, stated, e) in stated_sizes(&text, &names) {
            read += 1;
            let size = sizes.iter().find(|(n, _)| *n == e).map(|(_, s)| *s);
            if size != Some(stated) {
                wrong.push(format!(
                    "{}:{line}: states {stated} for trust_ir::{e}, which has {}",
                    path.strip_prefix(root).unwrap_or(path).display(),
                    size.unwrap_or(0)
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "EvalIR prose restates a trust_ir enum's size wrongly; derive it or delete it:\n  {}",
        wrong.join("\n  ")
    );
    assert!(
        read > 0,
        "the scan read no stated size at all; it is not reading the sources"
    );
}

/// The prose reader on text it has to get right.
#[test]
fn the_stated_size_reader_reads_words_digits_and_wrapped_lines() {
    // Stand-in enum names, so this file's own text restates no real size.
    let e = ["XOp", "YOp"];
    assert_eq!(
        stated_sizes(
            "/// is not a mirror of the twenty-three Rust XOp spellings.",
            &e
        ),
        vec![(1, 23, "XOp")]
    );
    assert_eq!(
        stated_sizes(
            "one each for 20 of \\\n the 26 `trust_ir::XOp` variants",
            &e
        ),
        vec![(2, 26, "XOp")]
    );
    assert_eq!(
        stated_sizes("// covers 9/9 of\n// trust_ir::YOp, in order", &e),
        vec![(1, 9, "YOp")]
    );
    assert!(stated_sizes("the id-carrying XOp variants; grew YOp to 13 variants", &e).is_empty());
    assert_eq!(count_word("Forty-two"), Some(42));
    assert_eq!(count_word("twenty-zero"), None);
}
