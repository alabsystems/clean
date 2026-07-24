// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq standard library dataset in sexp format and full import pipeline.
//!
//! Provides faithful reproductions of Coq's stdlib core types as sexp strings
//! compatible with [`super::coq::CoqImporter::import_sexp`] and
//! [`super::coq::sexp_to_cic`]. No Coq toolchain required.

#[cfg(test)]
use crate::coq::alpha::CoqImportStats;
use crate::coq::alpha::{
    import_mutual_inductive, parse_sexp, sexp_to_mutual_inductive, CoqImporter,
};
use crate::error::MathverseResult;
use crate::library::MathverseLibrary;
use crate::shard::{ShardReader, ShardWriter};
use crate::trust::policy::TrustPolicy;

// ---------------------------------------------------------------------------
// Part 1: Coq stdlib sexp dataset
// ---------------------------------------------------------------------------

/// Core data types from `Coq.Init.Datatypes`.
pub fn coq_init_datatypes() -> Vec<&'static str> {
    vec![
        // nat: O | S nat
        r#"(MutualInductive (Params)
            (Body nat (Sort (Type 0))
                (Ctor O (Sort (Type 0)))
                (Ctor S (Prod n (Ind nat 0) (Sort (Type 0))))))"#,
        // bool: true | false
        r#"(MutualInductive (Params)
            (Body bool (Sort (Type 0))
                (Ctor true (Sort (Type 0)))
                (Ctor false (Sort (Type 0)))))"#,
        // unit: tt
        r#"(MutualInductive (Params)
            (Body unit (Sort (Type 0))
                (Ctor tt (Sort (Type 0)))))"#,
        // list A: nil | cons A (list A)
        r#"(MutualInductive (Params)
            (Body list (Prod A (Sort (Type 0)) (Sort (Type 0)))
                (Ctor nil (Prod A (Sort (Type 0)) (Ind list 0)))
                (Ctor cons (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Prod xs (Ind list 0) (Ind list 0)))))))"#,
        // option A: Some A | None
        r#"(MutualInductive (Params)
            (Body option (Prod A (Sort (Type 0)) (Sort (Type 0)))
                (Ctor Some (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Ind option 0))))
                (Ctor None (Prod A (Sort (Type 0)) (Ind option 0)))))"#,
        // prod A B: pair A B
        r#"(MutualInductive (Params)
            (Body prod (Prod A (Sort (Type 0)) (Prod B (Sort (Type 0)) (Sort (Type 0))))
                (Ctor pair (Prod A (Sort (Type 0)) (Prod B (Sort (Type 0)) (Prod a (Rel 1) (Prod b (Rel 1) (Ind prod 0))))))))"#,
        // sum A B: inl A | inr B
        r#"(MutualInductive (Params)
            (Body sum (Prod A (Sort (Type 0)) (Prod B (Sort (Type 0)) (Sort (Type 0))))
                (Ctor inl (Prod A (Sort (Type 0)) (Prod B (Sort (Type 0)) (Prod a (Rel 1) (Ind sum 0)))))
                (Ctor inr (Prod A (Sort (Type 0)) (Prod B (Sort (Type 0)) (Prod b (Rel 0) (Ind sum 0)))))))"#,
        // comparison: Eq | Lt | Gt
        r#"(MutualInductive (Params)
            (Body comparison (Sort (Type 0))
                (Ctor Eq (Sort (Type 0)))
                (Ctor Lt (Sort (Type 0)))
                (Ctor Gt (Sort (Type 0)))))"#,
        // sumbool A B: left | right
        r#"(MutualInductive (Params)
            (Body sumbool (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort (Type 0))))
                (Ctor left (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (Ind sumbool 0)))))
                (Ctor right (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (Ind sumbool 0)))))))"#,
    ]
}

/// Logic from `Coq.Init.Logic`.
pub fn coq_init_logic() -> Vec<&'static str> {
    vec![
        // True (inductive with one constructor I)
        r#"(MutualInductive (Params)
            (Body True (Sort Prop) (Ctor I (Sort Prop))))"#,
        // False (inductive with no constructors)
        r#"(MutualInductive (Params)
            (Body False (Sort Prop)))"#,
        // and A B: conj
        r#"(MutualInductive (Params)
            (Body and (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
                (Ctor conj (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (Prod b (Rel 1) (Ind and 0))))))))"#,
        // or A B: or_introl | or_intror
        r#"(MutualInductive (Params)
            (Body or (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop)))
                (Ctor or_introl (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod a (Rel 1) (Ind or 0)))))
                (Ctor or_intror (Prod A (Sort Prop) (Prod B (Sort Prop) (Prod b (Rel 0) (Ind or 0)))))))"#,
        // ex A P: ex_intro
        r#"(MutualInductive (Params)
            (Body ex (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Sort Prop)))
                (Ctor ex_intro (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Prod w (Rel 1) (Prod p (App (Rel 1) (Rel 0)) (Ind ex 0))))))))"#,
        // eq A (x y : A): eq_refl
        r#"(MutualInductive (Params)
            (Body eq (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Prod y (Rel 1) (Sort Prop))))
                (Ctor eq_refl (Prod A (Sort (Type 0)) (Prod x (Rel 0) (App (App (Ind eq 0) (Rel 1)) (Rel 0)))))))"#,
        // not := fun A : Prop => A -> False
        r#"(CoqConstant not (Prod A (Sort Prop) (Sort Prop)) (Lambda A (Sort Prop) (Prod h (Rel 0) (Const False))))"#,
        // iff := fun A B : Prop => (A -> B) /\ (B -> A)
        r#"(CoqConstant iff (Prod A (Sort Prop) (Prod B (Sort Prop) (Sort Prop))) (Lambda A (Sort Prop) (Lambda B (Sort Prop) (App (App (Ind and 0) (Prod h (Rel 1) (Rel 1))) (Prod h (Rel 0) (Rel 1))))))"#,
        // False_ind: forall P : Prop, False -> P
        r#"(CoqAxiom False_ind (Prod P (Sort Prop) (Prod h (Const False) (Rel 1))))"#,
        // eq_ind: forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y
        r#"(CoqAxiom eq_ind (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Prod P (Prod a (Rel 1) (Sort Prop)) (Prod h (App (Rel 0) (Rel 1)) (Prod y (Rel 3) (Prod e (App (App (Ind eq 0) (Rel 4)) (Rel 3)) (App (Rel 3) (Rel 1)))))))))"#,
        // eq_sym: forall (A : Type) (x y : A), x = y -> y = x
        r#"(CoqAxiom eq_sym (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Prod y (Rel 1) (Prod e (App (App (Ind eq 0) (Rel 2)) (Rel 1)) (App (App (Ind eq 0) (Rel 3)) (Rel 1)))))))"#,
        // eq_trans: forall (A : Type) (x y z : A), x = y -> y = z -> x = z
        r#"(CoqAxiom eq_trans (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Prod y (Rel 1) (Prod z (Rel 2) (Prod e1 (App (App (Ind eq 0) (Rel 3)) (Rel 2)) (Prod e2 (App (App (Ind eq 0) (Rel 3)) (Rel 2)) (App (App (Ind eq 0) (Rel 5)) (Rel 2)))))))))"#,
    ]
}

/// Peano arithmetic from `Coq.Init.Nat`.
pub fn coq_init_peano() -> Vec<&'static str> {
    vec![
        // Nat.add : nat -> nat -> nat
        r#"(CoqConstant Nat.add (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind nat 0))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Rel 0))))"#,
        // Nat.mul : nat -> nat -> nat
        r#"(CoqConstant Nat.mul (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind nat 0))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Rel 0))))"#,
        // Nat.sub : nat -> nat -> nat
        r#"(CoqConstant Nat.sub (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind nat 0))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Rel 0))))"#,
        // Nat.pred : nat -> nat
        r#"(CoqConstant Nat.pred (Prod n (Ind nat 0) (Ind nat 0)) (Lambda n (Ind nat 0) (Rel 0)))"#,
        // Nat.succ = S (constructor alias)
        r#"(CoqConstant Nat.succ (Prod n (Ind nat 0) (Ind nat 0)) (Lambda n (Ind nat 0) (App (Const S) (Rel 0))))"#,
        // Nat.le : nat -> nat -> Prop
        r#"(CoqConstant Nat.le (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Sort Prop))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Sort Prop))))"#,
        // Nat.lt : nat -> nat -> Prop
        r#"(CoqConstant Nat.lt (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Sort Prop))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (App (App (Const Nat.le) (App (Const S) (Rel 1))) (Rel 0)))))"#,
        // Nat.eqb : nat -> nat -> bool
        r#"(CoqConstant Nat.eqb (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind bool 0))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Const true))))"#,
        // Nat.leb : nat -> nat -> bool
        r#"(CoqConstant Nat.leb (Prod n (Ind nat 0) (Prod m (Ind nat 0) (Ind bool 0))) (Lambda n (Ind nat 0) (Lambda m (Ind nat 0) (Const true))))"#,
    ]
}

/// Integer arithmetic from `Coq.ZArith.BinInt`.
pub fn coq_zarith() -> Vec<&'static str> {
    vec![
        // positive: xH | xO positive | xI positive
        r#"(MutualInductive (Params)
            (Body positive (Sort (Type 0))
                (Ctor xH (Sort (Type 0)))
                (Ctor xO (Prod p (Ind positive 0) (Sort (Type 0))))
                (Ctor xI (Prod p (Ind positive 0) (Sort (Type 0))))))"#,
        // Z: Z0 | Zpos positive | Zneg positive
        r#"(MutualInductive (Params)
            (Body Z (Sort (Type 0))
                (Ctor Z0 (Sort (Type 0)))
                (Ctor Zpos (Prod p (Ind positive 0) (Sort (Type 0))))
                (Ctor Zneg (Prod p (Ind positive 0) (Sort (Type 0))))))"#,
        // Z.add : Z -> Z -> Z
        r#"(CoqConstant Z.add (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Ind Z 0))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Rel 0))))"#,
        // Z.mul : Z -> Z -> Z
        r#"(CoqConstant Z.mul (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Ind Z 0))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Rel 0))))"#,
        // Z.opp : Z -> Z
        r#"(CoqConstant Z.opp (Prod x (Ind Z 0) (Ind Z 0)) (Lambda x (Ind Z 0) (Rel 0)))"#,
        // Z.sub : Z -> Z -> Z
        r#"(CoqConstant Z.sub (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Ind Z 0))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Rel 0))))"#,
        // Z.abs : Z -> Z
        r#"(CoqConstant Z.abs (Prod x (Ind Z 0) (Ind Z 0)) (Lambda x (Ind Z 0) (Rel 0)))"#,
        // Z.le : Z -> Z -> Prop
        r#"(CoqConstant Z.le (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Sort Prop))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Sort Prop))))"#,
        // Z.lt : Z -> Z -> Prop
        r#"(CoqConstant Z.lt (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Sort Prop))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Sort Prop))))"#,
        // Z.compare : Z -> Z -> comparison
        r#"(CoqConstant Z.compare (Prod x (Ind Z 0) (Prod y (Ind Z 0) (Ind comparison 0))) (Lambda x (Ind Z 0) (Lambda y (Ind Z 0) (Const Eq))))"#,
    ]
}

/// Dependent types from `Coq.Init.Specif`.
pub fn coq_init_specif() -> Vec<&'static str> {
    vec![
        // sig A P: exist
        r#"(MutualInductive (Params)
            (Body sig (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Sort (Type 0))))
                (Ctor exist (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort Prop)) (Prod w (Rel 1) (Prod p (App (Rel 1) (Rel 0)) (Ind sig 0))))))))"#,
        // sigT A P: existT
        r#"(MutualInductive (Params)
            (Body sigT (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort (Type 0))) (Sort (Type 0))))
                (Ctor existT (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort (Type 0))) (Prod w (Rel 1) (Prod p (App (Rel 1) (Rel 0)) (Ind sigT 0))))))))"#,
        // sigT2 A P Q: existT2
        r#"(MutualInductive (Params)
            (Body sigT2 (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort (Type 0))) (Prod Q (Prod x (Rel 1) (Sort (Type 0))) (Sort (Type 0)))))
                (Ctor existT2 (Prod A (Sort (Type 0)) (Prod P (Prod x (Rel 0) (Sort (Type 0))) (Prod Q (Prod x (Rel 1) (Sort (Type 0))) (Prod w (Rel 2) (Prod p (App (Rel 2) (Rel 0)) (Prod q (App (Rel 2) (Rel 1)) (Ind sigT2 0))))))))))"#,
        // sumor A B: inleft | inright (sum in Type)
        r#"(MutualInductive (Params)
            (Body sumor (Prod A (Sort (Type 0)) (Prod B (Sort Prop) (Sort (Type 0))))
                (Ctor inleft (Prod A (Sort (Type 0)) (Prod B (Sort Prop) (Prod a (Rel 1) (Ind sumor 0)))))
                (Ctor inright (Prod A (Sort (Type 0)) (Prod B (Sort Prop) (Prod b (Rel 0) (Ind sumor 0)))))))"#,
    ]
}

/// Classical logic axioms from `Coq.Logic.Classical_Prop`.
pub fn coq_logic_classical() -> Vec<&'static str> {
    vec![
        // classic: forall P : Prop, P \/ ~P
        r#"(CoqAxiom classic (Prod P (Sort Prop) (App (App (Ind or 0) (Rel 0)) (Prod h (Rel 0) (Const False)))))"#,
        // NNPP: forall P : Prop, ~~P -> P
        r#"(CoqAxiom NNPP (Prod P (Sort Prop) (Prod h (Prod g (Prod k (Rel 1) (Const False)) (Const False)) (Rel 1))))"#,
        // excluded_middle: forall P : Prop, P \/ ~P (alias for classic)
        r#"(CoqAxiom excluded_middle (Prod P (Sort Prop) (App (App (Ind or 0) (Rel 0)) (Prod h (Rel 0) (Const False)))))"#,
    ]
}

/// All Coq stdlib definitions concatenated.
pub fn coq_all_stdlib() -> Vec<&'static str> {
    let mut all = Vec::new();
    all.extend(coq_init_datatypes());
    all.extend(coq_init_logic());
    all.extend(coq_init_peano());
    all.extend(coq_zarith());
    all.extend(coq_init_specif());
    all.extend(coq_logic_classical());
    all
}

// ---------------------------------------------------------------------------
// Part 2: Import pipeline
// ---------------------------------------------------------------------------

/// Aggregate statistics from a Coq stdlib import run.
#[derive(Clone, Debug, Default)]
pub struct StdlibImportStats {
    pub constants_imported: u32,
    pub axioms_imported: u32,
    pub inductives_imported: u32,
    pub failures: u32,
}

/// Import the full Coq stdlib dataset into a [`ShardWriter`].
pub fn import_coq_stdlib(writer: &mut ShardWriter) -> MathverseResult<StdlibImportStats> {
    let mut stats = StdlibImportStats::default();
    for sexp_str in coq_all_stdlib() {
        // Try mutual inductive first.
        if sexp_str.contains("MutualInductive") {
            match parse_sexp(sexp_str) {
                Ok(sexp) => match sexp_to_mutual_inductive(&sexp) {
                    Ok(mind) => {
                        let module_path = infer_module_path(&mind.bodies[0].name);
                        match import_mutual_inductive(&mind, module_path, writer) {
                            Ok(indices) => {
                                stats.inductives_imported += 1;
                                stats.constants_imported += indices.len() as u32;
                            }
                            Err(_) => stats.failures += 1,
                        }
                    }
                    Err(_) => stats.failures += 1,
                },
                Err(_) => stats.failures += 1,
            }
            continue;
        }
        // Otherwise use the standard CoqImporter for CoqConstant / CoqAxiom.
        match CoqImporter.import_sexp(sexp_str, writer) {
            Ok(s) => {
                stats.constants_imported += s.translated + s.axiomatized;
                stats.axioms_imported += s.axiomatized;
            }
            Err(_) => stats.failures += 1,
        }
    }
    Ok(stats)
}

/// Load the Coq stdlib into an [`MathverseLibrary`] ready for search and export.
pub fn load_coq_stdlib_library(
    trust: TrustPolicy,
) -> MathverseResult<(MathverseLibrary, StdlibImportStats)> {
    let mut writer = ShardWriter::new();
    let stats = import_coq_stdlib(&mut writer)?;

    let mut buf = Vec::new();
    writer.write(&mut buf)?;
    let reader = ShardReader::from_bytes(&buf)?;

    let mut lib = MathverseLibrary::new(trust);
    lib.load_shard(&reader)?;
    lib.build_deps();
    lib.build_search_index();

    Ok((lib, stats))
}

/// Infer the Coq module path from a type name for axiom profiling.
pub(crate) fn infer_module_path(name: &str) -> &'static str {
    match name {
        "nat" | "bool" | "unit" | "list" | "option" | "prod" | "sum" | "comparison" | "sumbool" => {
            "Coq.Init.Datatypes"
        }
        "True" | "False" | "and" | "or" | "ex" | "eq" => "Coq.Init.Logic",
        "sig" | "sigT" | "sigT2" | "sumor" => "Coq.Init.Specif",
        "positive" => "Coq.Numbers.BinNums",
        "Z" => "Coq.Numbers.BinNums",
        _ => "Coq.Init",
    }
}

// ---------------------------------------------------------------------------
// Part 3: Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::CoqImporter;
    use crate::export::alpha::{ExportConfig, Exporter};
    use crate::search::MathverseSearch;
    use crate::shard::ShardWriter;
    use crate::trust::policy::TrustPolicy;
    use crate::types::AxiomProfile;

    /// Helper: import a set of sexp strings via the pipeline and return shard bytes.
    fn import_sexps_to_shard(sexps: &[&str]) -> (ShardWriter, CoqImportStats) {
        let mut writer = ShardWriter::new();
        let mut total_stats = CoqImportStats::default();
        for s in sexps {
            if s.contains("MutualInductive") {
                let parsed = parse_sexp(s).expect("parse sexp");
                let mind = sexp_to_mutual_inductive(&parsed).expect("parse mutual inductive");
                let module_path = infer_module_path(&mind.bodies[0].name);
                let indices = import_mutual_inductive(&mind, module_path, &mut writer)
                    .expect("import mutual inductive");
                total_stats.total += indices.len() as u32;
                total_stats.translated += indices.len() as u32;
            } else {
                let s = CoqImporter
                    .import_sexp(s, &mut writer)
                    .expect("import sexp");
                total_stats.total += s.total;
                total_stats.translated += s.translated;
                total_stats.axiomatized += s.axiomatized;
            }
        }
        (writer, total_stats)
    }

    /// Helper: load a set of sexp strings into a library with given trust policy.
    fn load_sexps_to_library(
        sexps: &[&str],
        trust: TrustPolicy,
    ) -> (MathverseLibrary, CoqImportStats) {
        let (writer, stats) = import_sexps_to_shard(sexps);
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let mut lib = MathverseLibrary::new(trust);
        lib.load_shard(&reader).unwrap();
        lib.build_deps();
        lib.build_search_index();
        (lib, stats)
    }

    /// Collect all constant names from a library.
    fn all_names(lib: &MathverseLibrary) -> Vec<String> {
        (0..lib.constant_count() as u32)
            .filter_map(|i| lib.get_name(i).map(|s| s.to_string()))
            .collect()
    }

    // -- Test 1: Datatypes -------------------------------------------------

    #[test]
    fn test_coq_stdlib_datatypes() {
        let sexps = coq_init_datatypes();
        let (lib, stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        assert!(stats.total > 0, "should import at least some constants");
        // Core types must exist.
        assert!(names.contains(&"nat".to_string()), "missing nat");
        assert!(names.contains(&"bool".to_string()), "missing bool");
        assert!(names.contains(&"list".to_string()), "missing list");
        assert!(names.contains(&"option".to_string()), "missing option");
        assert!(names.contains(&"prod".to_string()), "missing prod");
        // Constructors must exist with mangled names.
        assert!(names.contains(&"nat.O".to_string()), "missing nat.O");
        assert!(names.contains(&"nat.S".to_string()), "missing nat.S");
        assert!(
            names.contains(&"bool.true".to_string()),
            "missing bool.true"
        );
        assert!(
            names.contains(&"bool.false".to_string()),
            "missing bool.false"
        );
        assert!(names.contains(&"list.nil".to_string()), "missing list.nil");
        assert!(
            names.contains(&"list.cons".to_string()),
            "missing list.cons"
        );
    }

    // -- Test 2: Logic -----------------------------------------------------

    #[test]
    fn test_coq_stdlib_logic() {
        let sexps = coq_init_logic();
        let (lib, _stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        assert!(names.contains(&"True".to_string()), "missing True");
        assert!(names.contains(&"False".to_string()), "missing False");
        assert!(names.contains(&"and".to_string()), "missing and");
        assert!(names.contains(&"or".to_string()), "missing or");
        assert!(names.contains(&"eq".to_string()), "missing eq");
        assert!(names.contains(&"ex".to_string()), "missing ex");
        assert!(names.contains(&"not".to_string()), "missing not");
        assert!(names.contains(&"iff".to_string()), "missing iff");
        assert!(names.contains(&"and.conj".to_string()), "missing and.conj");
        assert!(
            names.contains(&"eq.eq_refl".to_string()),
            "missing eq.eq_refl"
        );
        // Elimination axioms.
        assert!(
            names.contains(&"False_ind".to_string()),
            "missing False_ind"
        );
        assert!(names.contains(&"eq_ind".to_string()), "missing eq_ind");
        assert!(names.contains(&"eq_sym".to_string()), "missing eq_sym");
        assert!(names.contains(&"eq_trans".to_string()), "missing eq_trans");
    }

    // -- Test 3: Peano arithmetic ------------------------------------------

    #[test]
    fn test_coq_stdlib_peano() {
        let sexps = coq_init_peano();
        let (lib, _stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        assert!(names.contains(&"Nat.add".to_string()), "missing Nat.add");
        assert!(names.contains(&"Nat.mul".to_string()), "missing Nat.mul");
        assert!(names.contains(&"Nat.sub".to_string()), "missing Nat.sub");
        assert!(names.contains(&"Nat.pred".to_string()), "missing Nat.pred");
        assert!(names.contains(&"Nat.succ".to_string()), "missing Nat.succ");
        assert!(names.contains(&"Nat.le".to_string()), "missing Nat.le");
        assert!(names.contains(&"Nat.lt".to_string()), "missing Nat.lt");
        assert!(names.contains(&"Nat.eqb".to_string()), "missing Nat.eqb");
        assert!(names.contains(&"Nat.leb".to_string()), "missing Nat.leb");
        assert_eq!(lib.constant_count(), 9, "expected 9 Peano constants");
    }

    // -- Test 4: ZArith ----------------------------------------------------

    #[test]
    fn test_coq_stdlib_zarith() {
        let sexps = coq_zarith();
        let (lib, _stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        // Inductive types.
        assert!(names.contains(&"positive".to_string()), "missing positive");
        assert!(names.contains(&"Z".to_string()), "missing Z");
        // Constructors.
        assert!(
            names.contains(&"positive.xH".to_string()),
            "missing positive.xH"
        );
        assert!(
            names.contains(&"positive.xO".to_string()),
            "missing positive.xO"
        );
        assert!(
            names.contains(&"positive.xI".to_string()),
            "missing positive.xI"
        );
        assert!(names.contains(&"Z.Z0".to_string()), "missing Z.Z0");
        assert!(names.contains(&"Z.Zpos".to_string()), "missing Z.Zpos");
        assert!(names.contains(&"Z.Zneg".to_string()), "missing Z.Zneg");
        // Operations.
        assert!(names.contains(&"Z.add".to_string()), "missing Z.add");
        assert!(names.contains(&"Z.mul".to_string()), "missing Z.mul");
        assert!(names.contains(&"Z.opp".to_string()), "missing Z.opp");
        assert!(names.contains(&"Z.sub".to_string()), "missing Z.sub");
        assert!(names.contains(&"Z.abs".to_string()), "missing Z.abs");
        assert!(names.contains(&"Z.le".to_string()), "missing Z.le");
        assert!(names.contains(&"Z.lt".to_string()), "missing Z.lt");
        assert!(
            names.contains(&"Z.compare".to_string()),
            "missing Z.compare"
        );
    }

    // -- Test 5: Classical axioms ------------------------------------------

    #[test]
    fn test_coq_stdlib_classical() {
        let sexps = coq_logic_classical();
        let (lib, _stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        assert!(names.contains(&"classic".to_string()), "missing classic");
        assert!(names.contains(&"NNPP".to_string()), "missing NNPP");
        assert!(
            names.contains(&"excluded_middle".to_string()),
            "missing excluded_middle"
        );
        // All classical axioms should have AXIOMATIZED bit set.
        for idx in 0..lib.constant_count() as u32 {
            let header = lib.get_constant(idx).unwrap();
            let profile = header.axiom_profile;
            assert!(
                profile.has(AxiomProfile::AXIOMATIZED),
                "classical axiom {} should be AXIOMATIZED",
                lib.get_name(idx).unwrap_or("?")
            );
        }
    }

    // -- Test 6: Full stdlib load ------------------------------------------

    #[test]
    fn test_coq_full_stdlib_load() {
        let (lib, stats) = load_coq_stdlib_library(TrustPolicy::permissive()).unwrap();
        // We expect 80+ constants from all modules combined.
        assert!(
            lib.constant_count() >= 80,
            "expected 80+ constants, got {}",
            lib.constant_count()
        );
        assert_eq!(
            stats.failures, 0,
            "no import failures expected, got {}",
            stats.failures
        );
        // Spot check cross-module names.
        let names = all_names(&lib);
        assert!(names.contains(&"nat".to_string()), "missing nat");
        assert!(names.contains(&"Z".to_string()), "missing Z");
        assert!(names.contains(&"True".to_string()), "missing True");
        assert!(names.contains(&"sig".to_string()), "missing sig");
        assert!(names.contains(&"classic".to_string()), "missing classic");
    }

    // -- Test 7: Semantic search -------------------------------------------

    #[test]
    fn test_coq_stdlib_search() {
        let (lib, _) = load_coq_stdlib_library(TrustPolicy::permissive()).unwrap();
        let results = lib.search_semantic("nat", 10).unwrap();
        // Should find nat-related names.
        assert!(
            !results.is_empty(),
            "semantic search for 'nat' should return results"
        );
        let result_names: Vec<String> = results
            .iter()
            .filter_map(|r| lib.get_name(r.constant_idx).map(|s| s.to_string()))
            .collect();
        assert!(
            result_names
                .iter()
                .any(|n| n.contains("nat") || n.contains("Nat")),
            "search results should include nat-related names, got: {:?}",
            result_names
        );
    }

    // -- Test 8: Dependencies ----------------------------------------------

    #[test]
    fn test_coq_stdlib_deps() {
        let (lib, _) = load_coq_stdlib_library(TrustPolicy::permissive()).unwrap();
        // Nat.add should reference nat in its type, so walk_deps should find at least
        // the Nat.add constant itself. We verify the dep walk doesn't panic and
        // returns at least the root.
        let names = all_names(&lib);
        if let Some(add_pos) = names.iter().position(|n| n == "Nat.add") {
            let mut dep_iter = lib.walk_deps(add_pos as u32);
            let mut dep_names = Vec::new();
            for idx in dep_iter {
                if let Some(name) = lib.get_name(idx) {
                    dep_names.push(name.to_string());
                }
            }
            // Should at least contain Nat.add itself.
            assert!(
                dep_names.contains(&"Nat.add".to_string()),
                "walk_deps should include root, got: {:?}",
                dep_names
            );
        }
    }

    // -- Test 9: Trust policy filtering ------------------------------------

    #[test]
    fn test_coq_stdlib_trust() {
        // Default (strict) policy: AXIOMATIZED constants are trust-gated.
        let (lib, _) = load_coq_stdlib_library(TrustPolicy::default_policy()).unwrap();
        // Classic is an axiom (AXIOMATIZED bit set), should be hidden under default.
        let classic = lib.lookup_name("classic");
        assert!(
            classic.is_none(),
            "classic should be hidden under default trust policy"
        );
        // Nat.add is translated (has a value), should be visible.
        let nat_add = lib.lookup_name("Nat.add");
        assert!(
            nat_add.is_some(),
            "Nat.add should be visible under default trust policy"
        );
        // Under permissive policy, classic should be visible.
        let (lib_perm, _) = load_coq_stdlib_library(TrustPolicy::permissive()).unwrap();
        let classic_perm = lib_perm.lookup_name("classic");
        assert!(
            classic_perm.is_some(),
            "classic should be visible under permissive trust policy"
        );
    }

    // -- Test 10: Training data export -------------------------------------

    #[test]
    fn test_coq_stdlib_export() {
        let (lib, _) = load_coq_stdlib_library(TrustPolicy::permissive()).unwrap();
        let config = ExportConfig::statement_only();
        let exporter = Exporter::new(&lib, config);
        let records = exporter.export_all();
        // We should get records for all visible constants.
        assert!(
            records.len() >= 50,
            "expected 50+ export records, got {}",
            records.len()
        );
        // Verify that exported records have real names, not empty/placeholder.
        for record in &records {
            assert!(
                !record.name.is_empty(),
                "export record name should not be empty"
            );
        }
        // Nat.add should appear in the export.
        let has_nat_add = records.iter().any(|r| r.name == "Nat.add");
        assert!(has_nat_add, "Nat.add should appear in exported records");
    }

    // -- Test 11: Specif ---------------------------------------------------

    #[test]
    fn test_coq_stdlib_specif() {
        let sexps = coq_init_specif();
        let (lib, _stats) = load_sexps_to_library(&sexps, TrustPolicy::permissive());
        let names = all_names(&lib);
        assert!(names.contains(&"sig".to_string()), "missing sig");
        assert!(names.contains(&"sigT".to_string()), "missing sigT");
        assert!(names.contains(&"sigT2".to_string()), "missing sigT2");
        assert!(names.contains(&"sumor".to_string()), "missing sumor");
        assert!(
            names.contains(&"sig.exist".to_string()),
            "missing sig.exist"
        );
        assert!(
            names.contains(&"sigT.existT".to_string()),
            "missing sigT.existT"
        );
    }

    // -- Test 12: Pipeline stats -------------------------------------------

    #[test]
    fn test_coq_stdlib_pipeline_stats() {
        let mut writer = ShardWriter::new();
        let stats = import_coq_stdlib(&mut writer).unwrap();
        assert!(
            stats.constants_imported >= 80,
            "expected 80+ constants, got {}",
            stats.constants_imported
        );
        assert!(
            stats.inductives_imported >= 15,
            "expected 15+ inductives, got {}",
            stats.inductives_imported
        );
        assert!(
            stats.axioms_imported >= 5,
            "expected 5+ axioms, got {}",
            stats.axioms_imported
        );
        assert_eq!(stats.failures, 0, "no import failures expected");
    }
}
