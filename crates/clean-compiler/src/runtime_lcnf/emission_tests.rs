use super::super::RuntimeContext;
use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt};
use std::collections::HashMap;

/// `[RuntimeProbe, Init.Prelude]` captured from the pinned-Lean-compiled
/// `runtime_probe` fixture family — the same fail-closed resolver the sibling
/// `runtime_lcnf::tests` module uses (`actual_context`), so the fixture is
/// compiled once per process and no environment variable selects it.
fn context() -> RuntimeContext {
    super::super::tests::actual_context()
}
fn ctor(tag: u32, fields: usize) -> CtorInfo {
    CtorInfo {
        name: Name::anon().str("testCtor").num(tag as u64),
        tag,
        num_scalars: 0,
        num_objects: fields as u32,
        field_types: vec![IRType::Object; fields],
    }
}
fn arg(i: u32) -> IRArg {
    IRArg::Var(VarId(i))
}
fn bind(i: u32, value: IRExpr, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: VarId(i),
        ty: IRType::Object,
        value,
        rest: Box::new(rest),
    }
}
fn decl(name: &str, n: u32, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: (0..n).map(|i| (VarId(i), IRType::Object)).collect(),
        return_type: IRType::Object,
        body,
    }
}

// Independent small heap machine: RC counts represent owned references, not
// just net syntactic inc/dec. Freed reads and residual heap cells fail. This is
// falsification of the bounded IR policy, not native/runtime refinement.
#[derive(Clone, Debug)]
enum Cell {
    Ctor(u32, Vec<usize>),
    Closure(Name, usize, Vec<usize>),
}
struct Heap {
    cells: Vec<Option<(usize, Cell)>>,
    functions: BTreeMap<Name, IRDecl>,
    fuel: usize,
}
impl Heap {
    fn new(decls: &[IRDecl]) -> Self {
        Self {
            cells: vec![],
            functions: decls.iter().map(|d| (d.name.clone(), d.clone())).collect(),
            fuel: 100_000,
        }
    }
    fn step(&mut self) -> Result<(), &'static str> {
        self.fuel = self.fuel.checked_sub(1).ok_or("fuel")?;
        Ok(())
    }
    fn alloc(&mut self, c: Cell) -> usize {
        let i = self.cells.len();
        self.cells.push(Some((1, c)));
        i
    }
    fn get(&self, i: usize) -> Result<&(usize, Cell), &'static str> {
        self.cells.get(i).and_then(|x| x.as_ref()).ok_or("freed")
    }
    fn inc(&mut self, i: usize) -> Result<(), &'static str> {
        self.get(i)?;
        self.cells[i].as_mut().unwrap().0 += 1;
        Ok(())
    }
    fn dec(&mut self, i: usize) -> Result<(), &'static str> {
        self.get(i)?;
        let c = self.cells[i].as_mut().unwrap();
        c.0 = c.0.checked_sub(1).ok_or("underflow")?;
        if c.0 == 0 {
            let (_, c) = self.cells[i].take().unwrap();
            let refs = match c {
                Cell::Ctor(_, v) | Cell::Closure(_, _, v) => v,
            };
            for r in refs {
                self.dec(r)?;
            }
        }
        Ok(())
    }
    fn value(&self, a: &IRArg, env: &HashMap<VarId, usize>) -> Result<usize, &'static str> {
        let IRArg::Var(v) = a else {
            return Err("erased");
        };
        let i = *env.get(v).ok_or("variable")?;
        self.get(i)?;
        Ok(i)
    }
    fn args(
        &self,
        args: &[IRArg],
        env: &HashMap<VarId, usize>,
    ) -> Result<Vec<usize>, &'static str> {
        args.iter().map(|a| self.value(a, env)).collect()
    }
    fn call(&mut self, n: &Name, args: Vec<usize>) -> Result<usize, &'static str> {
        self.step()?;
        let d = self.functions.get(n).ok_or("callee")?.clone();
        if d.params.len() != args.len() {
            return Err("arity");
        }
        let mut env = d
            .params
            .iter()
            .zip(args)
            .map(|((v, _), a)| (*v, a))
            .collect();
        self.body(&d.body, &mut env)
    }
    fn apply(&mut self, c: usize, args: Vec<usize>) -> Result<usize, &'static str> {
        self.step()?;
        let Cell::Closure(name, arity, mut fixed) = self.get(c)?.1.clone() else {
            return Err("not closure");
        };
        // Fresh owned captures before consuming the closure; equivalent for
        // shared and exclusive cells and independent of the producer pass.
        for &v in &fixed {
            self.inc(v)?;
        }
        self.dec(c)?;
        fixed.extend(args);
        if fixed.len() < arity {
            return Ok(self.alloc(Cell::Closure(name, arity, fixed)));
        }
        let extra = fixed.split_off(arity);
        let result = self.call(&name, fixed)?;
        if extra.is_empty() {
            Ok(result)
        } else {
            self.apply(result, extra)
        }
    }
    fn expr(&mut self, e: &IRExpr, env: &HashMap<VarId, usize>) -> Result<usize, &'static str> {
        match e {
            IRExpr::Ctor { info, args } => {
                let refs = self.args(args, env)?;
                Ok(self.alloc(Cell::Ctor(info.tag, refs)))
            }
            IRExpr::Proj { idx, arg, .. } => {
                let i = self.value(arg, env)?;
                let Cell::Ctor(_, fields) = &self.get(i)?.1 else {
                    return Err("ctor");
                };
                let v = *fields.get(*idx as usize).ok_or("field")?;
                self.get(v)?;
                Ok(v)
            }
            IRExpr::Apply { fn_id, args } => self.call(&fn_id.0, self.args(args, env)?),
            IRExpr::PartialApply { fn_id, arity, args } => {
                let refs = self.args(args, env)?;
                Ok(self.alloc(Cell::Closure(fn_id.0.clone(), *arity as usize, refs)))
            }
            IRExpr::ClosureApply { closure, args } => {
                self.apply(self.value(closure, env)?, self.args(args, env)?)
            }
            _ => Err("expression"),
        }
    }
    fn body(&mut self, b: &IRBody, env: &mut HashMap<VarId, usize>) -> Result<usize, &'static str> {
        self.step()?;
        match b {
            IRBody::Ret(a) => self.value(a, env),
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                let i = self.expr(value, env)?;
                env.insert(*var, i);
                self.body(rest, env)
            }
            IRBody::Inc { var, n, rest } => {
                let i = self.value(&IRArg::Var(*var), env)?;
                for _ in 0..*n {
                    self.inc(i)?;
                }
                self.body(rest, env)
            }
            IRBody::Dec { var, rest } => {
                let i = self.value(&IRArg::Var(*var), env)?;
                self.dec(i)?;
                self.body(rest, env)
            }
            IRBody::Case {
                scrutinee,
                alts,
                default,
            } => {
                let i = self.value(&IRArg::Var(*scrutinee), env)?;
                let Cell::Ctor(tag, _) = self.get(i)?.1 else {
                    return Err("tag");
                };
                let branch = alts
                    .iter()
                    .find(|a| a.ctor.tag == tag)
                    .map(|a| a.body.as_ref())
                    .or(default.as_deref())
                    .ok_or("branch")?;
                self.body(branch, env)
            }
            _ => Err("body"),
        }
    }
    fn unary(&mut self, n: usize) -> usize {
        let mut v = self.alloc(Cell::Ctor(0, vec![]));
        for _ in 0..n {
            v = self.alloc(Cell::Ctor(1, vec![v]));
        }
        v
    }
    fn read_unary(&self, mut v: usize) -> usize {
        let mut n = 0;
        loop {
            match &self.get(v).unwrap().1 {
                Cell::Ctor(0, fields) if fields.is_empty() => return n,
                Cell::Ctor(1, fields) if fields.len() == 1 => {
                    n += 1;
                    v = fields[0]
                }
                _ => panic!("wrong unary"),
            }
        }
    }
    fn empty(&self) -> bool {
        self.cells.iter().all(|c| c.is_none())
    }
}

#[test]
fn owned_return_alias_and_repeated_ctor_arguments_balance() {
    let pair = decl(
        "pair",
        1,
        bind(
            1,
            IRExpr::Ctor {
                info: ctor(1, 2),
                args: vec![arg(0), arg(0)],
            },
            IRBody::Ret(arg(1)),
        ),
    );
    let id = decl("id", 1, IRBody::Ret(arg(0)));
    for d in [pair, id] {
        let owned = own(&d, &mut Budget::new(RuntimeLimits::default())).unwrap();
        let mut heap = Heap::new(&[owned]);
        let input = heap.unary(1);
        let out = heap.call(&d.name, vec![input]).unwrap();
        heap.dec(out).unwrap();
        assert!(heap.empty());
    }
}

#[test]
fn owned_shared_closure_under_exact_and_overapplication_balance() {
    let id = decl("id", 1, IRBody::Ret(arg(0)));
    let first = decl("first", 2, IRBody::Ret(arg(0)));
    let returns = decl(
        "returns",
        1,
        bind(
            1,
            IRExpr::PartialApply {
                fn_id: FnId(id.name.clone()),
                arity: 1,
                args: vec![],
            },
            IRBody::Ret(arg(1)),
        ),
    );
    // Same caller object is captured and then reused, and the same closure is
    // applied twice while its original owner stays alive.
    let root = decl(
        "root",
        1,
        bind(
            1,
            IRExpr::PartialApply {
                fn_id: FnId(first.name.clone()),
                arity: 2,
                args: vec![],
            },
            bind(
                2,
                IRExpr::ClosureApply {
                    closure: arg(1),
                    args: vec![arg(0)],
                },
                bind(
                    3,
                    IRExpr::ClosureApply {
                        closure: arg(2),
                        args: vec![arg(0)],
                    },
                    bind(
                        4,
                        IRExpr::ClosureApply {
                            closure: arg(2),
                            args: vec![arg(0)],
                        },
                        IRBody::Ret(arg(4)),
                    ),
                ),
            ),
        ),
    );
    let over = decl(
        "over",
        1,
        bind(
            1,
            IRExpr::PartialApply {
                fn_id: FnId(returns.name.clone()),
                arity: 1,
                args: vec![],
            },
            bind(
                2,
                IRExpr::ClosureApply {
                    closure: arg(1),
                    args: vec![arg(0), arg(0)],
                },
                IRBody::Ret(arg(2)),
            ),
        ),
    );
    let decls = [id, first, returns, root.clone(), over.clone()];
    let owned = decls
        .iter()
        .map(|d| own(d, &mut Budget::new(RuntimeLimits::default())).unwrap())
        .collect::<Vec<_>>();
    for root in [root, over] {
        let mut h = Heap::new(&owned);
        let v = h.unary(2);
        let r = h.call(&root.name, vec![v]).unwrap();
        assert_eq!(h.read_unary(r), 2);
        h.dec(r).unwrap();
        assert!(h.empty());
    }
}

#[test]
fn borrowed_projection_and_separate_branch_cleanup_balance() {
    let d = decl(
        "project",
        1,
        IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                IRAlt {
                    ctor: ctor(0, 0),
                    body: Box::new(IRBody::Ret(arg(0))),
                },
                IRAlt {
                    ctor: ctor(1, 1),
                    body: Box::new(bind(
                        1,
                        IRExpr::Proj {
                            idx: 0,
                            ty: IRType::Object,
                            arg: arg(0),
                        },
                        IRBody::Ret(arg(1)),
                    )),
                },
            ],
            default: None,
        },
    );
    let owned = own(&d, &mut Budget::new(RuntimeLimits::default())).unwrap();
    for n in 0..3 {
        let mut h = Heap::new(std::slice::from_ref(&owned));
        let v = h.unary(n);
        let r = h.call(&d.name, vec![v]).unwrap();
        assert_eq!(h.read_unary(r), n.saturating_sub(1));
        h.dec(r).unwrap();
        assert!(h.empty());
    }
}

#[test]
fn ownership_mutants_fail_independent_heap_checks() {
    let d = decl(
        "pair",
        1,
        bind(
            1,
            IRExpr::Ctor {
                info: ctor(1, 2),
                args: vec![arg(0), arg(0)],
            },
            IRBody::Ret(arg(1)),
        ),
    );
    let mut h = Heap::new(std::slice::from_ref(&d));
    let v = h.unary(0);
    let r = h.call(&d.name, vec![v]).unwrap();
    assert_eq!(h.dec(r), Err("freed"));
    let mut d = own(&d, &mut Budget::new(RuntimeLimits::default())).unwrap();
    d.body = IRBody::Dec {
        var: VarId(0),
        rest: Box::new(d.body),
    };
    let mut h = Heap::new(&[d.clone()]);
    let v = h.unary(0);
    assert_eq!(h.call(&d.name, vec![v]), Err("freed"));
}

#[test]
fn ownership_unknown_scalar_effect_and_resource_shapes_refuse() {
    let mut d = decl("root", 1, IRBody::Ret(arg(0)));
    d.params[0].1 = IRType::UInt64;
    assert!(own(&d, &mut Budget::new(RuntimeLimits::default())).is_err());
    d.params[0].1 = IRType::Object;
    d.body = IRBody::Unreachable;
    assert!(own(&d, &mut Budget::new(RuntimeLimits::default())).is_err());
    d.body = IRBody::Ret(arg(0));
    let limits = RuntimeLimits {
        steps: 0,
        ..RuntimeLimits::default()
    };
    assert!(own(&d, &mut Budget::new(limits)).is_err());
}

#[test]
fn actual_runtime_emits_closed_extern_calls_and_retains_dialect_refusal() {
    let context = context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    // The dumps written below are human-readable diagnostics with no consumer
    // in the tree, so they land in a scratch directory that is discarded with
    // the test. `CLEAN_RUNTIME_EMISSION_OUT` is honoured only as a DESTINATION
    // for a human who wants to keep them (a fresh directory, created here so
    // the `create_new` writes below cannot clobber anything) — never as a skip.
    let scratch = tempfile::tempdir().unwrap();
    let artifact_dir = match std::env::var_os("CLEAN_RUNTIME_EMISSION_OUT") {
        Some(kept) => {
            let kept = std::path::PathBuf::from(kept);
            std::fs::create_dir(&kept).unwrap();
            kept
        }
        None => scratch.path().to_path_buf(),
    };
    for mode in [RuntimeLowering::Dialect, RuntimeLowering::ExternCalls] {
        let output = context
            .lower_trust_ir_diagnostic(&root, RuntimeLimits::default(), mode)
            .unwrap();
        assert!(output
            .captured
            .rows
            .iter()
            .any(|r| matches!(r.status, RuntimeIrStatus::Refused(_))));
        if mode == RuntimeLowering::Dialect {
            let error = output.emission.as_ref().unwrap_err().to_string();
            assert!(error.contains("PartialApply") && error.contains("closures need ExternCalls"));
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(artifact_dir.join("dialect-refusal.txt"))
                .unwrap();
            write!(
                file,
                "{error}\nFull captured rows: {:#?}",
                output.captured.rows
            )
            .unwrap();
            continue;
        }
        let emitted = output.emission.unwrap();
        assert!(trust_ir_build::validate_module(&emitted.module).is_empty());
        assert_eq!(
            emitted.runtime_imports.is_empty(),
            mode == RuntimeLowering::Dialect
        );
        assert_eq!(emitted.before_rc.len(), emitted.owned_ir.len());
        assert!(emitted.dynamic_applications >= 2);
        let source = output
            .captured
            .rows
            .iter()
            .find(|r| r.origin.name == root)
            .unwrap();
        let matcher = &source.specializations[0].generated_name;
        assert!(emitted.named_edges.iter().any(|e| e.caller == root
            && &e.callee == matcher
            && e.kind == RuntimeCallKind::Direct));
        assert!(emitted
            .named_edges
            .iter()
            .any(|e| e.callee == root && e.kind == RuntimeCallKind::Direct));
        assert!(exact_direct_edges(
            &emitted.module,
            &emitted.named_edges,
            &emitted.runtime_imports
        ));
        for n in 0..7 {
            let mut heap = Heap::new(&emitted.owned_ir);
            let v = heap.unary(n);
            let result = heap.call(&root, vec![v]).unwrap();
            assert_eq!(heap.read_unary(result), n);
            heap.dec(result).unwrap();
            assert!(heap.empty(), "residual heap at {n}");
        }
        let label = if mode == RuntimeLowering::Dialect {
            "dialect"
        } else {
            "extern"
        };
        let write = |suffix: &str, bytes: &[u8]| {
            use std::io::Write;
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(artifact_dir.join(format!("{label}.{suffix}")))
                .unwrap();
            file.write_all(bytes).unwrap();
        };
        write(
            "tMBC",
            &crate::emit_trust_ir::serialize_tmbc(&emitted.module)
                .expect("emitted runtime module has a wire identity"),
        );
        // Human-readable diagnostic dumps, not a second persistent runtime
        // wire schema. The module uses the existing versioned tMBC serializer.
        write(
            "owned-ir.txt",
            format!("{:#?}", emitted.owned_ir).as_bytes(),
        );
        let report=format!("scope: diagnostic captured runtime, not G4/native refinement\nroot: {}\nheap inputs passed: 0..=6\ndynamic sites: {}\nfixed runtime imports: {:#?}\nnamed call edges: {:#?}\nfull captured rows: {:#?}\n",
            wire_name(&root),emitted.dynamic_applications,emitted.runtime_imports,emitted.named_edges,output.captured.rows);
        write("report.txt", report.as_bytes());
    }
}

fn exact_direct_edges(
    module: &trust_ir::Module,
    expected: &[RuntimeCallEdge],
    imports: &[RuntimeImport],
) -> bool {
    let excluded = imports
        .iter()
        .map(|r| r.function_index)
        .collect::<BTreeSet<_>>();
    let mut want = BTreeMap::new();
    for e in expected
        .iter()
        .filter(|e| e.kind == RuntimeCallKind::Direct)
    {
        *want
            .entry((wire_name(&e.caller), wire_name(&e.callee)))
            .or_insert(0usize) += 1;
    }
    let mut actual = BTreeMap::new();
    for f in &module.functions {
        for n in f.blocks.iter().flat_map(|b| &b.body) {
            if let trust_ir::inst::Inst::Call { callee, .. } = &n.inst {
                let index = callee.0 as usize;
                if excluded.contains(&index) {
                    continue;
                }
                let Some(callee) = module.functions.get(index) else {
                    return false;
                };
                *actual
                    .entry((f.name.clone(), callee.name.clone()))
                    .or_insert(0usize) += 1;
            }
        }
    }
    want == actual
}

#[test]
fn emitted_direct_edge_multiplicity_rejects_missing_duplicate_and_swapped_calls() {
    let id = decl("leaf", 1, IRBody::Ret(arg(0)));
    let twin = decl("other", 1, IRBody::Ret(arg(0)));
    let root = decl(
        "root",
        1,
        bind(
            1,
            IRExpr::Apply {
                fn_id: FnId(id.name.clone()),
                args: vec![arg(0)],
            },
            bind(
                2,
                IRExpr::Apply {
                    fn_id: FnId(id.name.clone()),
                    args: vec![arg(1)],
                },
                IRBody::Ret(arg(2)),
            ),
        ),
    );
    let module = crate::emit_trust_ir::emit_trust_ir(&[root.clone(), id.clone(), twin]).unwrap();
    let edge = RuntimeCallEdge {
        caller: root.name,
        callee: id.name,
        kind: RuntimeCallKind::Direct,
        supplied: 1,
    };
    let expected = vec![edge.clone(), edge];
    assert!(exact_direct_edges(&module, &expected, &[]));
    for mutation in 0..3 {
        let mut changed = module.clone();
        let body = &mut changed.functions[0].blocks[0].body;
        let index = body
            .iter()
            .position(|n| matches!(n.inst, trust_ir::inst::Inst::Call { .. }))
            .unwrap();
        match mutation {
            0 => {
                body.remove(index);
            }
            1 => {
                body.push(body[index].clone());
            }
            _ => {
                let trust_ir::inst::Inst::Call { callee, .. } = &mut body[index].inst else {
                    panic!()
                };
                *callee = trust_ir::value::FuncId::new(2);
            }
        }
        assert!(!exact_direct_edges(&changed, &expected, &[]));
    }
}

#[test]
fn duplicate_ssa_across_branches_remains_refused() {
    let d = decl(
        "bad",
        1,
        IRBody::Case {
            scrutinee: VarId(0),
            alts: (0..2)
                .map(|tag| IRAlt {
                    ctor: ctor(tag, 0),
                    body: Box::new(bind(
                        1,
                        IRExpr::Ctor {
                            info: ctor(0, 0),
                            args: vec![],
                        },
                        IRBody::Ret(arg(1)),
                    )),
                })
                .collect(),
            default: None,
        },
    );
    assert!(crate::ir_checker::check_decls(&[d])
        .unwrap_err()
        .to_string()
        .contains("duplicate"));
}

#[test]
fn exact_emission_postflight_rejects_runtime_and_source_abi_mutations() {
    let declarations = vec![decl("sourceIdentity", 1, IRBody::Ret(arg(0)))];
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let (emitted, requested) =
        emit_trust_ir_with_runtime_imports(&declarations, &config, &[]).unwrap();
    let original = emitted.module;
    let imports = postflight(
        &original,
        &declarations,
        RuntimeLowering::ExternCalls,
        &requested,
    )
    .unwrap();
    assert!(!imports.is_empty());
    let source = imports.len();
    for mutation in 0..10 {
        let mut changed = original.clone();
        match mutation {
            0 => changed.functions[0].calling_conv = trust_ir::CallingConv::Fast,
            1 => changed.functions[0].id = trust_ir::value::FuncId::new(999),
            2 => {
                let ty = changed.functions[0].ty.0 as usize;
                changed.func_types[ty].params.push(trust_ir::ty::Ty::U64);
            }
            3 => changed.functions[1].name = changed.functions[0].name.clone(),
            4 => changed.functions[source].calling_conv = trust_ir::CallingConv::Fast,
            5 => changed.functions[source].id = trust_ir::value::FuncId::new(0),
            6..=8 => {
                let mut ty = original
                    .func_type(original.functions[source].ty)
                    .unwrap()
                    .clone();
                if mutation == 6 {
                    ty.params.push(trust_ir::ty::Ty::U64);
                } else if mutation == 7 {
                    ty.returns = vec![trust_ir::ty::Ty::U64];
                } else {
                    ty.is_vararg = true;
                }
                changed.functions[source].ty =
                    trust_ir::value::FuncTyId::new(changed.func_types.len() as u32);
                changed.func_types.push(ty);
            }
            _ => changed.functions[source].blocks.clear(),
        }
        assert!(
            postflight(
                &changed,
                &declarations,
                RuntimeLowering::ExternCalls,
                &requested
            )
            .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn postflight_binds_the_sources_requested_runtime_roles() {
    use crate::emit_trust_ir_runtime::RuntimeImport as Role;
    let fields = vec![decl(
        "field",
        1,
        bind(
            1,
            IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: arg(0),
            },
            IRBody::Ret(arg(1)),
        ),
    )];
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let (emitted, requested) = emit_trust_ir_with_runtime_imports(&fields, &config, &[]).unwrap();
    assert_eq!(requested, [Role::CtorGet]);
    let checked = |roles: &[Role]| {
        postflight(
            &emitted.module,
            &fields,
            RuntimeLowering::ExternCalls,
            roles,
        )
    };
    let imports = checked(&requested).unwrap();
    assert_eq!(imports.last().unwrap().symbol, "clean_ctor_get");
    assert!(checked(&[]).is_err());
    assert!(checked(&[Role::CtorGet, Role::CtorGet]).is_err());
    assert!(checked(&[Role::CtorGetUsize]).is_err());
}

#[test]
fn actual_missing_swapped_signature_and_duplicate_callees_refuse_without_externs() {
    let context = context();
    let root = Name::from_string("RuntimeProbe.count._unsafe_rec");
    let output = context.lower_ir(&root, RuntimeLimits::default()).unwrap();
    for mutation in 0..3 {
        let mut changed = output.clone();
        let row = changed
            .rows
            .iter_mut()
            .find(|r| r.origin.name == root)
            .unwrap();
        let RuntimeIrStatus::Lowered(decls) = &mut row.status else {
            panic!()
        };
        match mutation {
            0 => {
                decls.remove(1);
            }
            1 => {
                decls[1].params.push((VarId(999), IRType::Object));
            }
            _ => {
                decls.push(decls[0].clone());
            }
        }
        let count = changed.rows.len();
        assert!(emit(
            &changed,
            RuntimeLimits::default(),
            RuntimeLowering::ExternCalls
        )
        .is_err());
        assert_eq!(changed.rows.len(), count);
    }
}

#[test]
fn actual_quoted_identity_emits_its_own_nonrecursive_body() {
    let root = Name::anon().str("RuntimeProbe").str("count._unsafe_rec");
    for mode in [RuntimeLowering::Dialect, RuntimeLowering::ExternCalls] {
        let output = context()
            .lower_trust_ir_diagnostic(&root, RuntimeLimits::default(), mode)
            .unwrap();
        let emitted = output.emission.unwrap();
        assert_eq!(emitted.owned_ir.len(), 1);
        assert!(emitted.named_edges.is_empty());
        assert_eq!(
            emitted.module.functions.last().unwrap().name,
            wire_name(&root)
        );
        let mut h = Heap::new(&emitted.owned_ir);
        let v = h.unary(2);
        let r = h.call(&root, vec![v]).unwrap();
        assert_eq!(r, v);
        h.dec(r).unwrap();
        assert!(h.empty());
    }
}
