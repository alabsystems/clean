use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name, TypeChecker};
use clean_verify::source_ir_identity as connection;
use std::sync::OnceLock;
use trust_ir::{
    BlockId, CallingConv, Endianness, FuncId, Inst, Module, StructPassingPolicy, TargetInfo, Ty,
    ValueId,
};
use trust_ir_build::{
    core_execution::{
        Assembler, Catalog, Coordinate, EntryTarget, Limits, MachineModel, NatTerm,
        PendingEquality, RootReturnFrame,
    },
    scoped_local::LocalScope,
    source_identity_data::RustU64IdentityModule,
    ModuleBuilder,
};
fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), x)
}
fn nat(n: u64) -> Expr {
    Expr::nat_lit(n)
}
fn list(t: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    let x: Vec<_> = x.into_iter().collect();
    x.into_iter()
        .rev()
        .fold(a("IRList.nil", [c(t)]), |tail, head| {
            a("IRList.cons", [c(t), head, tail])
        })
}
fn eq(t: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [t, l, r],
    )
}
fn refl(t: Expr, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [t, v],
    )
}
fn limits() -> Limits {
    Limits {
        max_operations: 4000,
        max_locals: 100,
        max_list_items: 100,
        max_lookup_candidates: 100,
        lookup_heartbeats: 5_000_000,
        lookup_cache_entries: 100_000,
    }
}
fn environment() -> &'static Environment {
    static E: OnceLock<Environment> = OnceLock::new();
    E.get_or_init(|| connection::environment().unwrap())
}
fn module() -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "source_identity",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::Unclassified,
        },
    );
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let fid = builder.declare_function("identity", signature);
    {
        let mut f = builder.define_function(fid).unwrap();
        f.set_calling_conv(CallingConv::Rust);
        let bb = f.create_block();
        let p = f.add_block_param(bb, Ty::U64);
        f.switch_to_block(bb);
        f.ret(vec![p]);
        f.build();
    }
    let mut module = builder.build().unwrap();
    let f = &mut module.functions[0];
    f.id = FuncId(41);
    f.entry = BlockId(17);
    f.blocks[0].id = BlockId(17);
    f.blocks[0].params[0].0 = ValueId(31);
    f.blocks[0].body[0].inst = Inst::Return {
        values: vec![ValueId(31)],
    };
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}
fn subject(w: &RustU64IdentityModule<'_>, source: &str) -> connection::RawIdentitySubject {
    connection::RawIdentitySubject {
        original_source: source.into(),
        original_function: "identity".into(),
        original_instance: "standalone-syntax-model::identity:u64->u64;NOT-TCX".into(),
        module_bytes: w.original_bytes().to_vec(),
        ir_function_name: w.function_name().into(),
        function_id: w.function_id().index(),
        function_type_id: w.signature_id().index(),
        entry_block: w.entry_block().index(),
        parameter_value: w.parameter().index(),
        return_value: w.returned().index(),
        reflected_context: w.reflected().context_term().clone(),
    }
}
fn proof(w: &RustU64IdentityModule<'_>) -> Expr {
    let env = environment();
    let mut scope = LocalScope::new();
    let mut assem = Assembler::new(&mut scope, limits()).unwrap();
    let mut ps = Vec::new();
    let rho = assem.local(Expr::arrow(c("Nat"), c("Nat"))).unwrap();
    ps.push(rho.clone());
    let world = assem.local(Expr::type_()).unwrap();
    ps.push(world.clone());
    let mem = assem.local(c("IRByteMemoryV1")).unwrap();
    ps.push(mem.clone());
    let host = assem.local(world.term().clone()).unwrap();
    ps.push(host.clone());
    let providers = assem
        .local(a("IRByteProvidersV1", [world.term().clone()]))
        .unwrap();
    ps.push(providers.clone());
    let model = MachineModel::new(
        world.term().clone(),
        w.reflected(),
        providers.term().clone(),
    );
    let mut catalog = Catalog::new(env, w.reflected(), limits()).unwrap();
    let entry = catalog.rust_u64_entry_v1(w.function_id()).unwrap();
    let memory_guard = EntryTarget::memory_admission(mem.term().clone());
    let memory_h = assem
        .local(eq(c("Bool"), memory_guard.clone(), c("Bool.true")))
        .unwrap();
    ps.push(memory_h.clone());
    let memory = PendingEquality::candidate(
        c("Bool"),
        memory_guard,
        c("Bool.true"),
        memory_h.term().clone(),
    );
    let word = Expr::app(rho.term().clone(), nat(0));
    let word_guard = a("ir_nat_ltb", [word.clone(), a("ir_nat_pow2", [nat(64)])]);
    let word_h = assem
        .local(eq(c("Bool"), word_guard, c("Bool.true")))
        .unwrap();
    ps.push(word_h.clone());
    let scalar = a("IRScalar.int_", [word.clone()]);
    let values = list("IRScalar", [scalar]);
    let fits = a(
        "ir_byte_value_matches_v1",
        [
            model.context().clone(),
            a("IRTy.uint_", [nat(64)]),
            a("IRScalar.int_", [word.clone()]),
        ],
    );
    let fits_proof = a(
        "ir_byte_u64_value_fits_v1",
        [model.context().clone(), word, word_h.term().clone()],
    );
    let values_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            fits,
            c("Bool.true"),
            fits_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let admitted = PendingEquality::candidate(
        c("Bool"),
        entry.admission(&model, values.clone()).unwrap(),
        c("Bool.true"),
        values_proof.clone(),
    );
    let initialized = entry
        .initialize(
            &mut assem,
            &model,
            values.clone(),
            mem.term().clone(),
            host.term().clone(),
            memory,
            admitted,
        )
        .unwrap();
    let owner = a("ir_byte_fresh_owner_v1", [mem.term().clone()]);
    let frame = RootReturnFrame {
        returning: initialized.current().frame.clone(),
        legacy_memory: list("IRMemSlot", []),
        legacy_cursor: nat(0),
        memory: mem.term().clone(),
        host: host.term().clone(),
        owner: owner.clone(),
        next: a("Nat.succ", [owner]),
    };
    let site = catalog
        .fetch(Coordinate {
            function: w.function_id(),
            block: w.entry_block(),
            instruction: 0,
        })
        .unwrap();
    let target = catalog.call_target(w.function_id()).unwrap();
    let resolved = assem
        .conversion(
            a("IRList", [c("IRScalar")]),
            a(
                "ir_resolve",
                [
                    frame.current(&model).machine(),
                    list("Nat", [nat(w.returned().index() as u64)]),
                ],
            ),
            values.clone(),
        )
        .unwrap();
    let return_guard = site
        .root_return_admission(&model, &target, &frame, values.clone())
        .unwrap();
    let value_guard = a(
        "ir_byte_values_match_v1",
        [
            model.context().clone(),
            list("IRTy", [a("IRTy.uint_", [nat(64)])]),
            values,
        ],
    );
    let return_proof = a(
        "ir_byte_world_and_intro_v1",
        [
            value_guard,
            c("Bool.true"),
            values_proof,
            refl(c("Bool"), c("Bool.true")),
        ],
    );
    let returned = site
        .return_from_root(
            &mut assem,
            &model,
            &target,
            &frame,
            resolved,
            PendingEquality::candidate(c("Bool"), return_guard, c("Bool.true"), return_proof),
            initialized.valid().clone(),
        )
        .unwrap();
    let initialization = assem
        .congruence_function(
            initialized.equality().clone(),
            model.config_type(),
            model.run_function(&NatTerm::literal(1)),
        )
        .unwrap();
    let full = assem
        .compose(initialization, returned.run().equality().clone())
        .unwrap();
    let mut term = full.term().clone();
    for p in ps.iter().rev() {
        term = p.lam(term);
    }
    drop(assem);
    let term = scope.close(&term).unwrap();
    let actual = connection::ir_claim(&subject(w, "fn identity(x:u64)->u64 { x }")).unwrap();
    let mut tc = TypeChecker::new(env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(&term, &actual).unwrap();
    assert!(!tc.heartbeat_spent());
    term
}
fn rejected(proof: &Expr, goal: &Expr) {
    let mut tc = TypeChecker::new(environment());
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    tc.check_type(goal, &Expr::sort(Level::zero())).unwrap();
    tc.check_type(proof, goal)
        .expect_err("supplied term must refuse the well-typed changed statement");
    assert!(!tc.heartbeat_spent());
}
fn replace(term: &Expr, from: &Expr, to: &Expr) -> Expr {
    if term == from {
        return to.clone();
    }
    match term.kind() {
        ExprKind::App(f, x) => Expr::app(replace(f, from, to), replace(x, from, to)),
        ExprKind::Lam(b, t, x) => Expr::lam(*b, replace(t, from, to), replace(x, from, to)),
        ExprKind::Pi(b, t, x) => Expr::pi(*b, replace(t, from, to), replace(x, from, to)),
        _ => term.clone(),
    }
}
#[test]
fn original_source_actual_ir_universal_entry_ssa_and_root_retirement(
) -> std::result::Result<(), Box<dyn std::error::Error>> {
    let module = module();
    let w = RustU64IdentityModule::from_module(&module, FuncId(41), 4096).unwrap();
    let ir_proof = proof(&w);
    for (i, source) in [
        "fn identity(x:u64)->u64 { x }",
        "fn identity(x:u64)->u64 { (x) }",
        "fn identity(x:u64)->u64 { { x } }",
        "fn identity(x:u64)->u64 { return { x }; }",
    ]
    .iter()
    .enumerate()
    {
        let expected = subject(&w, source);
        let packet = connection::IdentityPacket {
            subject: expected.clone(),
            proof: connection::candidate(&expected, ir_proof.clone()).unwrap(),
        };
        let checked = connection::replay(&expected, &packet).unwrap();
        assert_eq!(checked.subject(), &expected);
        assert_eq!(checked.subject().parameter_value, 31);
        assert_eq!(checked.subject().entry_block, 17);
        if let Ok(dir) = std::env::var("TRUST_G4_BRIDGE_OUT") {
            let dir = std::path::PathBuf::from(dir);
            std::fs::create_dir_all(&dir)?;
            let proof_env = environment();
            let proof_audit = proof_env.audit_certification(checked.claim(), checked.proof());
            let declarations = proof_audit
                .dependencies
                .iter()
                .map(|name| {
                    proof_env
                        .get_const(name)
                        .cloned()
                        .ok_or_else(|| format!("artifact dependency is undeclared: {name}"))
                })
                .collect::<std::result::Result<Vec<_>, String>>()?;
            std::fs::write(
                dir.join(format!("connection-{i}.json")),
                serde_json::to_vec_pretty(
                    &serde_json::json!({"source":source,"source_blake3":checked.source_digest(),"module_blake3":checked.module_digest(),"context":expected.reflected_context,"environment_declarations":declarations,"claim":checked.claim(),"proof":checked.proof(),"scope":"closed source-model/actual reflected IR logical entry only; no TCX/frontend/bodyidentity/physicalABI/SourceNoUB/runtime grade"}),
                )?,
            )?;
            std::fs::write(dir.join("original-module.bin"), w.original_bytes())?;
            std::fs::write(dir.join("ir-proof.json"), serde_json::to_vec(&ir_proof)?)?;
        }
    }
    Ok(())
}
#[test]
fn original_and_actual_subject_binding_and_real_module_refusals() {
    let module = module();
    let w = RustU64IdentityModule::from_module(&module, FuncId(41), 4096).unwrap();
    let expected = subject(&w, "fn identity(x:u64)->u64 { x }");
    let p = connection::IdentityPacket {
        subject: expected.clone(),
        proof: connection::candidate(&expected, proof(&w)).unwrap(),
    };
    for change in 0..10 {
        let mut swapped = p.clone();
        match change {
            0 => swapped.subject.original_source.push(' '),
            1 => swapped.subject.original_function = "other".into(),
            2 => swapped.subject.module_bytes[0] ^= 1,
            3 => swapped.subject.function_id += 1,
            4 => swapped.subject.function_type_id += 1,
            5 => swapped.subject.entry_block += 1,
            6 => swapped.subject.parameter_value += 1,
            7 => swapped.subject.return_value += 1,
            8 => swapped.subject.ir_function_name = "other".into(),
            _ => swapped.subject.original_instance = "other".into(),
        };
        assert!(connection::replay(&expected, &swapped).is_err());
    }
    for change in 0..6 {
        let mut bad = module.clone();
        match change {
            0 => bad.functions[0].entry = BlockId(99),
            1 => bad.functions[0].calling_conv = CallingConv::C,
            2 => {
                bad.functions[0].blocks[0].body[0].inst = Inst::Return {
                    values: vec![ValueId(9)],
                }
            }
            3 => bad.func_types[0].returns = vec![Ty::I64],
            4 => {
                let node = bad.functions[0].blocks[0].body[0].clone();
                bad.functions[0].blocks[0].body.push(node);
            }
            _ => bad.functions[0].blocks[0].params[0].1 = Ty::I64,
        };
        assert!(RustU64IdentityModule::from_module(&bad, FuncId(41), 4096).is_err());
    }
    assert!(connection::claim(&subject(&w, "fn identity(x:u64)->u64 { 0 }")).is_err());
    // Original C/Fast reflector retains its old Rust refusal; no relabelled body.
    assert!(trust_ir_build::core_reflection::reflect_core_module_v1(
        &module,
        &[(FuncId(41), 4096)]
    )
    .is_err());
}
#[test]
fn hostile_universal_result_entry_convention_and_final_world_refuse() {
    let module = module();
    let w = RustU64IdentityModule::from_module(&module, FuncId(41), 4096).unwrap();
    let proof = proof(&w);
    let expected = subject(&w, "fn identity(x:u64)->u64 { x }");
    let goal = connection::ir_claim(&expected).unwrap();
    // Exact word-domain is full64; a real closed kernel witness inhabits both ends.
    for word in [0, u64::MAX] {
        let term = refl(c("Bool"), c("Bool.true"));
        let q = eq(
            c("Bool"),
            a("ir_nat_ltb", [nat(word), a("ir_nat_pow2", [nat(64)])]),
            c("Bool.true"),
        );
        let tc = TypeChecker::new(environment());
        tc.check_type(&term, &q).unwrap();
    }
    let mut bad = expected.clone();
    bad.function_id = 42;
    rejected(&proof, &connection::ir_claim(&bad).unwrap());
    // Mutate actual reflected data rather than inventing a favorable SSA map.
    for cc in [CallingConv::C, CallingConv::Fast] {
        let mut changed = module.clone();
        changed.functions[0].calling_conv = cc;
        let reflected = trust_ir_build::core_reflection::reflect_core_module_v1(
            &changed,
            &[(FuncId(41), 4096)],
        )
        .unwrap();
        bad = expected.clone();
        bad.reflected_context = reflected.context_term().clone();
        rejected(&proof, &connection::ir_claim(&bad).unwrap());
    }
    // Endpoint-correspondence control only: a separate fresh-owner theorem
    // may prove no-retire propositionally equivalent for this allocation-free leaf.
    let bad_retirement = replace(
        &goal,
        &c("ir_byte_retire_v1"),
        &Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::lam(BinderInfo::Default, c("IRByteMemoryV1"), Expr::bvar(0)),
        ),
    );
    assert_ne!(bad_retirement, goal);
    rejected(&proof, &bad_retirement);
    // Changed final owner counter is an explicit well-typed semantic disagreement.
    let bad_next = replace(
        &goal,
        &c("Nat.succ"),
        &Expr::lam(BinderInfo::Default, c("Nat"), Expr::bvar(0)),
    );
    assert_ne!(bad_next, goal);
    rejected(&proof, &bad_next);
}

#[test]
fn universal_preconditions_are_kernel_inhabited_for_full64_and_historical_memory() {
    let module = module();
    let witness = RustU64IdentityModule::from_module(&module, FuncId(41), 4096).unwrap();
    let term = proof(&witness);
    let allocation = |base, size, owner, live| {
        a(
            "IRByteAllocationV1.mk",
            [nat(base), nat(size), nat(owner), c(live)],
        )
    };
    let mem = a(
        "IRByteMemoryV1.mk",
        [
            list(
                "IRByteAllocationV1",
                [
                    allocation(16, 8, 0, "Bool.true"),
                    allocation(48, 8, 7, "Bool.false"),
                ],
            ),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                a("IROption.none", [c("Nat")]),
            ),
            nat(128),
        ],
    );
    let memory_guard = EntryTarget::memory_admission(mem.clone());
    let tc = TypeChecker::new(environment());
    let hmem = refl(c("Bool"), c("Bool.true"));
    tc.check_type(&hmem, &eq(c("Bool"), memory_guard, c("Bool.true")))
        .unwrap();
    let providers = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        Expr::lam(
            BinderInfo::Default,
            a("IRList", [c("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                c("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    a(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            a("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    for word in [0, u64::MAX] {
        let rho = Expr::lam(BinderInfo::Default, c("Nat"), nat(word));
        let hword = refl(c("Bool"), c("Bool.true"));
        let instantiated = Expr::apps(
            term.clone(),
            [
                rho.clone(),
                c("Nat"),
                mem.clone(),
                nat(19),
                providers.clone(),
                hmem.clone(),
                hword.clone(),
            ],
        );
        let mut claim =
            connection::ir_claim(&subject(&witness, "fn identity(x:u64)->u64 { x }")).unwrap();
        for value in [
            rho,
            c("Nat"),
            mem.clone(),
            nat(19),
            providers.clone(),
            hmem.clone(),
            hword,
        ] {
            let ExprKind::Pi(_, _, body) = claim.kind() else {
                panic!("quantified actual IR claim")
            };
            claim = body.instantiate(&value);
        }
        tc.check_type(&instantiated, &claim).unwrap();
    }
    assert!(!tc.heartbeat_spent());
}

#[test]
fn retained_ir_term_rejects_wrong_result_and_real_replacement_module() {
    // A fresh consumer checks the ORIGINAL retained IR proof; this cell never
    // invokes the IR assembler producer or infers universality from examples.
    let path = std::env::var("TRUST_G4_REPLAY_IR_PROOF").unwrap();
    let retained: Expr = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    let module = module();
    let witness = RustU64IdentityModule::from_module(&module, FuncId(41), 4096).unwrap();
    let original = subject(&witness, "fn identity(x:u64)->u64 { x }");
    let goal = connection::ir_claim(&original).unwrap();
    let tc = TypeChecker::new(environment());
    tc.check_type(&retained, &goal).unwrap();
    fn wrong_return(term: &Expr) -> Expr {
        match term.kind() {
            ExprKind::App(f, _) if **f == c("IROutcome.ret") => a(
                "IROutcome.ret",
                [list("IRScalar", [a("IRScalar.int_", [nat(0)])])],
            ),
            ExprKind::App(f, x) => Expr::app(wrong_return(f), wrong_return(x)),
            ExprKind::Lam(b, t, x) => Expr::lam(*b, wrong_return(t), wrong_return(x)),
            ExprKind::Pi(b, t, x) => Expr::pi(*b, wrong_return(t), wrong_return(x)),
            _ => term.clone(),
        }
    }
    let wrong_goal = wrong_return(&goal);
    assert_ne!(wrong_goal, goal);
    rejected(&retained, &wrong_goal);

    // Real valid typed IR replacing the argument with constant zero. The
    // identity witness refuses the extra computation, while the SAME shared
    // general logical reflector preserves its actual two-node body.
    let mut replacement = module.clone();
    let block = &mut replacement.functions[0].blocks[0];
    block.body.insert(
        0,
        trust_ir::InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: trust_ir::Constant::Int(0),
        })
        .with_result(ValueId(32)),
    );
    block.body[1].inst = Inst::Return {
        values: vec![ValueId(32)],
    };
    assert!(trust_ir_build::validate_module(&replacement).is_empty());
    assert!(RustU64IdentityModule::from_module(&replacement, FuncId(41), 4096).is_err());
    let reflected = trust_ir_build::core_reflection::reflect_core_rust_u64_leaf_v1(
        &replacement,
        &[(FuncId(41), 4096)],
    )
    .unwrap();
    let mut wrong = original.clone();
    wrong.module_bytes = trust_ir::binary::serialize_module(&replacement).unwrap();
    wrong.reflected_context = reflected.context_term().clone();
    wrong.return_value = 32;
    rejected(&retained, &connection::ir_claim(&wrong).unwrap());

    // Kernel-checked COUNTEREXAMPLE ONLY: actual replacement execution with
    // input1 returns0 after two steps. This is not the universal positive proof.
    let mem = a(
        "IRByteMemoryV1.mk",
        [
            list("IRByteAllocationV1", []),
            Expr::lam(
                BinderInfo::Default,
                c("Nat"),
                a("IROption.none", [c("Nat")]),
            ),
            nat(128),
        ],
    );
    let providers = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        Expr::lam(
            BinderInfo::Default,
            a("IRList", [c("IRScalar")]),
            Expr::lam(
                BinderInfo::Default,
                c("IRByteMemoryV1"),
                Expr::lam(
                    BinderInfo::Default,
                    c("Nat"),
                    a(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            a("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    );
    let init = a(
        "ir_rust_u64_init_v1",
        [
            c("Nat"),
            reflected.context_term().clone(),
            nat(41),
            list("IRScalar", [a("IRScalar.int_", [nat(1)])]),
            mem.clone(),
            nat(19),
        ],
    );
    let run = a(
        "ir_byte_run_v1",
        [
            c("Nat"),
            reflected.context_term().clone(),
            providers,
            nat(2),
            init,
        ],
    );
    let owner = a("ir_byte_fresh_owner_v1", [mem.clone()]);
    let terminal = a(
        "IRByteConfigV1.halted",
        [
            c("Nat"),
            a(
                "IROutcome.ret",
                [list("IRScalar", [a("IRScalar.int_", [nat(0)])])],
            ),
            a(
                "IRByteWorldV1.mk",
                [
                    c("Nat"),
                    a("ir_byte_retire_v1", [owner.clone(), mem]),
                    nat(19),
                    list("Nat", []),
                    a("Nat.succ", [owner]),
                ],
            ),
        ],
    );
    tc.check_type(
        &refl(a("IRByteConfigV1", [c("Nat")]), terminal.clone()),
        &eq(a("IRByteConfigV1", [c("Nat")]), run, terminal),
    )
    .unwrap();
    assert!(!tc.heartbeat_spent());
}
