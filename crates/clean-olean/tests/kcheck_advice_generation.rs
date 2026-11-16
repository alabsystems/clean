// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Automatic ordinary-core candidates, replayed by the actual adopted checker.
//! Not full Init/C4 coverage, completeness, compiled authority or a Rust proof.
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderData, Expr, FVarId};
use clean_kernel::kcheck_trace::core::advice::produce_ordinary;
use clean_kernel::kcheck_trace::core::Refusal;
use clean_kernel::kcheck_trace::wire::{encode_frames, encode_tokens};
use clean_kernel::kcheck_trace::Token;
use clean_kernel::{Level, Name};
use clean_olean::test_support::compiled_fixture_dir;
use std::process::Command;

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderData::default(), domain, body)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderData::default(), domain, body)
}
fn let_expr(ty: Expr, value: Expr, body: Expr) -> Expr {
    Expr::let_named(Name::anon(), ty, value, body, false)
}

fn definition(name: &str, ty: Expr, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    }
}
fn lean_bytes(bytes: &[u8]) -> String {
    format!(
        "⟨#[{}]⟩",
        bytes
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

#[test]
fn automatic_candidates_replay_with_beta_zeta_and_local_definition_guards() {
    let env = Environment::default();
    let prop = Expr::sort(Level::zero());
    let id_type = pi(prop.clone(), pi(Expr::bvar(0), Expr::bvar(1)));
    let id_value = lam(prop.clone(), lam(Expr::bvar(0), Expr::bvar(0)));
    let beta_codomain = Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(1));
    let beta_type = pi(prop.clone(), pi(Expr::bvar(0), beta_codomain));
    let zeta_type = pi(
        prop.clone(),
        pi(
            Expr::bvar(0),
            let_expr(prop.clone(), Expr::bvar(1), Expr::bvar(0)),
        ),
    );
    let local_value = lam(
        prop.clone(),
        let_expr(
            prop.clone(),
            pi(Expr::bvar(0), Expr::bvar(1)),
            let_expr(
                Expr::bvar(0),
                lam(Expr::bvar(1), Expr::bvar(0)),
                Expr::bvar(0),
            ),
        ),
    );
    // The two functions below differ, but both applications reduce to P.
    // Structural APP/LAM search first emits a failing prefix; only rollback
    // followed by the real beta steps can yield replayable declaration advice.
    let rollback_type = pi(
        prop.clone(),
        pi(
            Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(0)),
            Expr::app(lam(prop.clone(), Expr::bvar(0)), Expr::bvar(1)),
        ),
    );
    let rollback_value = lam(
        prop.clone(),
        lam(
            Expr::app(lam(prop.clone(), Expr::bvar(1)), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    );
    let cases = [
        definition("identityProp", id_type.clone(), id_value.clone()),
        definition("betaResult", beta_type, id_value.clone()),
        definition("zetaResult", zeta_type, id_value),
        definition("localFunction", id_type, local_value),
        definition("rollbackResult", rollback_type, rollback_value),
    ];
    let candidates = cases
        .iter()
        .map(|declaration| {
            produce_ordinary(&env, declaration, 100_000, 256)
                .expect("ordinary-core candidate search")
        })
        .collect::<Vec<_>>();
    // This checks an ordering obligation of the real beta cursor, not merely
    // round-tripping the writer with a native decoder of the same design.
    let zero_depths = candidates
        .iter()
        .map(|candidate| {
            let mut tokens = candidate.tokens.clone();
            match tokens.first_mut() {
                Some(Token::Depth(depth)) => *depth = 0,
                _ => panic!("producer must supply its declaration depth"),
            }
            lean_bytes(&encode_tokens(&tokens))
        })
        .collect::<Vec<_>>()
        .join(",");
    let beta = &candidates[1];
    let guard = beta
        .tokens
        .windows(2)
        .position(|pair| matches!(pair, [Token::CoreR(1), Token::Dom]))
        .expect("beta result conversion emits CORE_R before DOM");
    let mut omitted = beta.tokens.clone();
    omitted.remove(guard + 1);
    let mut reversed = beta.tokens.clone();
    reversed.swap(guard, guard + 1);
    let alias_name = Name::from_string("adviceAliasProp");
    let alias_type = Expr::sort(Level::succ(Level::zero()));
    let alias = definition("adviceAliasProp", alias_type.clone(), prop.clone());
    let alias_candidate =
        produce_ordinary(&env, &alias, 100_000, 256).expect("candidate for dependency prefix");
    let mut prefix = Environment::default();
    prefix.add_decl(alias).expect("native source prefix setup");
    let dependent = definition(
        "identityAlias",
        pi(
            Expr::const_(alias_name.clone(), vec![]),
            pi(Expr::bvar(0), Expr::bvar(1)),
        ),
        lam(prop.clone(), lam(Expr::bvar(0), Expr::bvar(0))),
    );
    let dependent_candidate = produce_ordinary(&prefix, &dependent, 100_000, 256)
        .expect("candidate with an explicit delta step");
    assert!(dependent_candidate
        .tokens
        .iter()
        .any(|token| matches!(token, Token::DeltaR)));
    let dependent_frames = encode_frames(&[alias_candidate.bytes, dependent_candidate.bytes]);
    let mut opaque_prefix = Environment::default();
    opaque_prefix
        .add_decl(Declaration::Opaque {
            name: alias_name,
            level_params: vec![],
            type_: alias_type,
            value: prop,
        })
        .expect("opaque prefix setup");
    assert!(
        produce_ordinary(&opaque_prefix, &dependent, 100_000, 256).is_err(),
        "producer must not unfold an opaque dependency"
    );
    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases

def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)
def pSort : X := srt .zero
def identityType : X := pis pSort (pis (.bvar 0) (.bvar 1))
def identityBody : X := lm pSort (lm (.bvar 0) (.bvar 0))
def betaType : X := pis pSort (pis (.bvar 0) (.app (lm pSort (.bvar 0)) (.bvar 1)))
def zetaType : X := pis pSort (pis (.bvar 0) (.letE `Q pSort (.bvar 1) (.bvar 0) false))
def localBody : X := lm pSort (.letE `T pSort (pis (.bvar 0) (.bvar 1))
  (.letE `f (.bvar 0) (lm (.bvar 1) (.bvar 0)) (.bvar 0) false) false)
def rollbackType : X := pis pSort (pis
  (.app (lm pSort (.bvar 0)) (.bvar 0))
  (.app (lm pSort (.bvar 0)) (.bvar 1)))
def rollbackBody : X := lm pSort (lm
  (.app (lm pSort (.bvar 1)) (.bvar 0)) (.bvar 0))
def accepted (input : DeclarationInput Unit) (bytes : ByteArray) : Bool :=
  match kcheckBytes base input bytes with | .ok _ => true | _ => false

def main : IO Unit := do
  expect "automatic-identity" (accepted (defn "identityProp" identityType identityBody) IDENTITY_BYTES)
  expect "automatic-beta" (accepted (defn "betaResult" betaType identityBody) BETA_BYTES)
  expect "automatic-zeta" (accepted (defn "zetaResult" zetaType identityBody) ZETA_BYTES)
  expect "automatic-local-definition" (accepted (defn "localFunction" identityType localBody) LOCAL_BYTES)
  expect "automatic-failed-branch-rollback" (accepted (defn "rollbackResult" rollbackType rollbackBody) ROLLBACK_BYTES)
  let ordinaryInputs := [defn "identityProp" identityType identityBody,
    defn "betaResult" betaType identityBody, defn "zetaResult" zetaType identityBody,
    defn "localFunction" identityType localBody, defn "rollbackResult" rollbackType rollbackBody]
  let zeroDepths : List ByteArray := [ZERO_DEPTH_BYTES]
  expect "every-ordinary-case-has-depth-refusal"
    (ordinaryInputs.length == 5 && zeroDepths.length == 5 &&
      (ordinaryInputs.zip zeroDepths).all (fun p =>
        match kcheckBytes base p.1 p.2 with | .error .depth => true | _ => false))
  let aliasInput := defn "adviceAliasProp" (srt (.succ .zero)) pSort
  let aliasIdentity := defn "identityAlias" (pis (.const (nm "adviceAliasProp") []) (pis (.bvar 0) (.bvar 1))) identityBody
  expect "automatic-delta-prefix" (match kcheckRun [aliasInput, aliasIdentity] DEPENDENT_FRAMES with
    | .ok (_, [_, _]) => true | _ => false)
  expect "opaque-delta-refused" (match kcheckRun [opq "adviceAliasProp" (srt (.succ .zero)) pSort, aliasIdentity] DEPENDENT_FRAMES with
    | .error (.deltaOpaque _) => true | _ => false)
  expect "missing-dom-refused-at-beta" (match kcheckBytes base (defn "betaResult" betaType identityBody) OMITTED_BYTES with
    | .error (.token .beta _) => true | _ => false)
  expect "reversed-dom-refused-at-conv" (match kcheckBytes base (defn "betaResult" betaType identityBody) REVERSED_BYTES with
    | .error (.token .conv .dom) => true | _ => false)
"#
    .replace("ZERO_DEPTH_BYTES", &zero_depths)
    .replace("ROLLBACK_BYTES", &lean_bytes(&candidates[4].bytes))
    .replace("DEPENDENT_FRAMES", &lean_bytes(&dependent_frames))
    .replace("IDENTITY_BYTES", &lean_bytes(&candidates[0].bytes))
    .replace("BETA_BYTES", &lean_bytes(&candidates[1].bytes))
    .replace("ZETA_BYTES", &lean_bytes(&candidates[2].bytes))
    .replace("LOCAL_BYTES", &lean_bytes(&candidates[3].bytes))
    .replace("OMITTED_BYTES", &lean_bytes(&encode_tokens(&omitted)))
    .replace("REVERSED_BYTES", &lean_bytes(&encode_tokens(&reversed)));
    let scratch = tempfile::tempdir().expect("private actual producer replay scratch");
    let file = scratch.path().join("AutomaticReplay.lean");
    std::fs::write(&file, source).expect("write actual native candidate input");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean executable");
    let output = Command::new(lean)
        .arg("--run")
        .arg(&file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean search path"),
        )
        .output()
        .expect("execute adopted checker on actual generated candidates");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout)
            .expect("UTF-8 replay")
            .lines()
            .collect::<Vec<_>>(),
        [
            "automatic-identity",
            "automatic-beta",
            "automatic-zeta",
            "automatic-local-definition",
            "automatic-failed-branch-rollback",
            "every-ordinary-case-has-depth-refusal",
            "automatic-delta-prefix",
            "opaque-delta-refused",
            "missing-dom-refused-at-beta",
            "reversed-dom-refused-at-conv",
        ]
    );
}

#[test]
fn incomplete_search_never_returns_a_partial_frame() {
    let env = Environment::default();
    let prop = Expr::sort(Level::zero());
    let invalid = definition("external", prop.clone(), Expr::fvar(FVarId::new(0)));
    assert!(
        matches!(produce_ordinary(&env, &invalid, 100, 256), Err(Refusal::Coverage { source_name, .. }) if source_name == "advice_non_core_input")
    );
    let empty_budget = definition("emptyBudget", prop.clone(), prop);
    assert!(matches!(
        produce_ordinary(&env, &empty_budget, 0, 256),
        Err(Refusal::Budget)
    ));
}

#[test]
fn observing_reference_replay_emits_candidates_without_granting_admission() {
    use clean_olean::recheck_closed::reference_base::reference_base_core_tracing;
    use clean_olean::ClosedRecheckOptions;
    use std::collections::BTreeSet;

    let prop = Expr::sort(Level::zero());
    let declaration = definition(
        "callerIdentity",
        pi(prop.clone(), pi(Expr::bvar(0), Expr::bvar(1))),
        lam(prop, lam(Expr::bvar(0), Expr::bvar(0))),
    );
    let mut env = Environment::for_lean_replay();
    env.add_decl(declaration)
        .expect("ordinary input for actual caller");
    let targets = BTreeSet::from([Name::from_string("callerIdentity")]);
    let observe = |operations| {
        let mut rows = Vec::new();
        let report = reference_base_core_tracing(
            &env,
            &targets,
            &ClosedRecheckOptions::default(),
            operations,
            None,
            &mut |row| rows.push(serde_json::to_value(row).expect("serialize actual observation")),
        )
        .expect("actual fenced observing replay");
        assert!(
            report.passed(),
            "candidate search cannot replace the reference verdict"
        );
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["reference_accepted"], true);
        rows.remove(0)
    };
    let exhausted = observe(0);
    assert_eq!(exhausted["advice_candidate"]["status"], "refused");
    assert!(exhausted["advice_candidate"].get("bytes").is_none());
    let candidate = observe(100_000);
    assert_eq!(candidate["advice_candidate"]["status"], "candidate");
    assert_eq!(candidate["advice_candidate"]["depth"], 100_000);
    let bytes = candidate["advice_candidate"]["bytes"]
        .as_array()
        .expect("actual caller exports candidate bytes")
        .iter()
        .map(|byte| u8::try_from(byte.as_u64().expect("byte integer")).expect("byte range"))
        .collect::<Vec<_>>();
    let source = r#"import KCheck.CheckerCases
open CICL KCheck KCheck.CheckerCases
def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)
def callerInput : DeclarationInput Unit := defn "callerIdentity"
  (pis (srt .zero) (pis (.bvar 0) (.bvar 1)))
  (lm (srt .zero) (lm (.bvar 0) (.bvar 0)))
def candidate : ByteArray := CANDIDATE_BYTES
def main : IO Unit := do
  expect "caller-candidate-replayed" (match kcheckBytes base callerInput candidate with
    | .ok _ => true | _ => false)
  expect "caller-trailing-token-refused" (match kcheckBytes base callerInput (candidate.push 0) with
    | .error _ => true | _ => false)
"#
    .replace("CANDIDATE_BYTES", &lean_bytes(&bytes));
    let scratch = tempfile::tempdir().expect("actual caller replay scratch");
    let file = scratch.path().join("CallerReplay.lean");
    std::fs::write(&file, source).expect("write original caller input");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let output = Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg("--run")
        .arg(file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean paths"),
        )
        .output()
        .expect("actual checker on observing-caller bytes");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).expect("UTF-8 replay"),
        "caller-candidate-replayed\ncaller-trailing-token-refused\n"
    );
}
