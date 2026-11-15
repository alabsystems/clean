//! The reader's wire-expansion resource bounds (syntax.rs `MAX_WIRE_DEPTH`,
//! `MAX_WIRE_DAG`) at their boundaries, on the production stack.
use super::*;

const HEADER: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"test"},"lean":{"version":"4.30.0-rc2","githash":"synthetic"},"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"deep"}}
{"ie":0,"sort":0}
{"ie":1,"bvar":0}
"#;

/// `def deep : Prop → … → Prop := fun _ … x => x` with `binders` binders.
/// Both the type and the value have wire depth `binders + 1`.
fn deep_chain(binders: u64) -> String {
    let mut s = HEADER.to_owned();
    let (mut ty, mut value) = (0u64, 1u64);
    for i in 0..binders {
        let pi = i.checked_mul(2).and_then(|x| x.checked_add(2)).unwrap();
        let lam = pi.checked_add(1).unwrap();
        s.push_str(&format!(
            "{{\"ie\":{pi},\"forallE\":{{\"name\":0,\"type\":0,\"body\":{ty},\"binderInfo\":\"default\"}}}}\n"
        ));
        s.push_str(&format!(
            "{{\"ie\":{lam},\"lam\":{{\"name\":0,\"type\":0,\"body\":{value},\"binderInfo\":\"default\"}}}}\n"
        ));
        (ty, value) = (pi, lam);
    }
    s.push_str(&format!(
        "{{\"def\":{{\"name\":1,\"levelParams\":[],\"type\":{ty},\"value\":{value},\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[1]}}}}\n"
    ));
    s
}

/// `def wide : Type := T_k`, `T_0 = Prop`, `T_{j+1} = T_j → T_j`: wire depth
/// `k + 1`, shared, so its tree has 2^(k+1) - 1 binder and sort nodes plus a
/// level node per sort, `3 * 2^k - 1` in all.
fn shared_tree(k: u64) -> String {
    let mut s = HEADER.replace("\"deep\"", "\"wide\"");
    s.push_str("{\"il\":1,\"succ\":0}\n{\"ie\":2,\"sort\":1}\n");
    let mut prev = 0u64;
    for i in 0..k {
        let id = i.checked_add(3).unwrap();
        s.push_str(&format!(
            "{{\"ie\":{id},\"forallE\":{{\"name\":0,\"type\":{prev},\"body\":{prev},\"binderInfo\":\"default\"}}}}\n"
        ));
        prev = id;
    }
    s.push_str(&format!(
        "{{\"def\":{{\"name\":1,\"levelParams\":[],\"type\":2,\"value\":{prev},\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[1]}}}}\n"
    ));
    s
}

/// The production command checks on its main thread; 8 MiB is the main
/// thread's stack on macOS and on Linux by default.
fn on_main_thread_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn test_wire_depth_bound_accepts_at_bound_and_refuses_past_it() {
    let at = deep_chain(syntax::MAX_WIRE_DEPTH - 1);
    let report = on_main_thread_stack(move || replay(at.as_bytes(), Dialect::Lean4Export31))
        .expect("a term at the depth bound is read");
    assert_eq!(report.counts().0, 1, "{report:?}");
    assert!(report.counts().1.is_empty(), "{report:?}");
    let past = deep_chain(syntax::MAX_WIRE_DEPTH);
    let refusal = on_main_thread_stack(move || replay(past.as_bytes(), Dialect::Lean4Export31))
        .expect_err("one deeper is past the bound");
    assert_eq!(refusal.reason(), "resource-limit");
}

#[test]
fn test_former_depth_bound_no_longer_refuses_an_honest_depth() {
    // CIC_L's noConfusion of `CICL.ConstructorCertificate` has depth 151.
    let honest = deep_chain(150);
    let report = on_main_thread_stack(move || replay(honest.as_bytes(), Dialect::Lean4Export31))
        .expect("depth 151 is read");
    assert_eq!(report.counts().0, 1, "{report:?}");
}

#[test]
fn test_shared_wire_dag_is_checked_without_expanding_its_tree() {
    // At 80 links the expanded tree is larger than u64; the DAG is 81
    // expression nodes, so inference must finish in the default fuel.
    let wire = shared_tree(80);
    let report = on_main_thread_stack(move || replay(wire.as_bytes(), Dialect::Lean4Export31))
        .expect("sharing is retained from the wire through inference");
    assert_eq!(report.counts().0, 1, "{report:?}");
    assert!(report.counts().1.is_empty(), "{report:?}");
}

#[test]
fn test_derived_definitions_retain_sharing_between_export_roots() {
    // Two checked casesOn helpers at each of 25 levels reuse both preceding
    // helpers. There are 699 wire records; expanding bodies afresh at each
    // lookup exceeds MAX_WIRE_DAG and rejects the final levels.
    let wire = include_bytes!("../../tests/fixtures/derived-diamond.ndjson");
    let report = on_main_thread_stack(move || replay(&wire[..], Dialect::Lean4Export31))
        .expect("a checked definition diamond remains a DAG");
    assert_eq!(report.counts().0, 73, "{report:?}");
    assert!(report.counts().1.is_empty(), "{report:?}");
}
