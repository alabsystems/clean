// Debug probe (lane B): resolve_instance against imported lean4-core oleans.
//
// Pins the synthOrder/transitivity behavior: `MonadLiftT Id (ReaderT Nat Id)`
// must synthesize via the restored `instMonadLiftTOfMonadLift` (persisted
// synthOrder [3, 4]: solve `[MonadLift n o]` first — its solution pins the
// middle monad `n` — then `[MonadLiftT m n]`).
//
// Loads `Init.Control.Id` (`Id` is defined there, NOT in Init.Prelude; its
// dependency closure includes Init.Prelude, which carries the MonadLift/
// MonadLiftT classes and instances).
use clean_elab::ElabCtx;
use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;

fn main() {
    let home = std::env::var("HOME").expect("HOME");
    let lib = format!("{home}/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean");
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Control.Id", &[lib.into()]).expect("load");

    let zero = Level::zero();
    let id = Expr::const_(Name::interned("Id"), vec![zero.clone()]);
    let reader = Expr::app(
        Expr::app(
            Expr::const_(Name::interned("ReaderT"), vec![zero.clone(), zero.clone()]),
            Expr::const_(Name::interned("Nat"), Vec::<Level>::new()),
        ),
        id.clone(),
    );

    // Reflexive goal first.
    let refl_goal = Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLiftT"),
                vec![zero.clone(), zero.clone(), zero.clone()],
            ),
            id.clone(),
        ),
        id.clone(),
    );
    let mut ctx = ElabCtx::new(&env);
    println!(
        "MonadLiftT Id Id            -> {:?}",
        ctx.resolve_instance(&refl_goal).is_some()
    );

    // The synthOrder gap reproducer: needs the transitivity instance.
    let trans_goal = Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLiftT"),
                vec![zero.clone(), zero.clone(), zero.clone()],
            ),
            id.clone(),
        ),
        reader.clone(),
    );
    let mut ctx2 = ElabCtx::new(&env);
    match ctx2.resolve_instance(&trans_goal) {
        Some(term) => println!("MonadLiftT Id (ReaderT ...) -> true: {term:?}"),
        None => println!("MonadLiftT Id (ReaderT ...) -> false"),
    }

    // Base: MonadLift Id (ReaderT Nat Id)
    let lift_goal = Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLift"),
                vec![zero.clone(), zero.clone(), zero.clone()],
            ),
            id.clone(),
        ),
        reader.clone(),
    );
    let mut ctx3 = ElabCtx::new(&env);
    println!(
        "MonadLift Id (ReaderT ...)  -> {:?}",
        ctx3.resolve_instance(&lift_goal).is_some()
    );

    // NEGATIVE: no instance lifts a ReaderT stack back DOWN into its base.
    let neg_goal = Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLiftT"),
                vec![zero.clone(), zero.clone(), zero],
            ),
            reader,
        ),
        id,
    );
    let mut ctx4 = ElabCtx::new(&env);
    let t = std::time::Instant::now();
    println!(
        "MonadLiftT (ReaderT ...) Id -> {:?} (in {:?})",
        ctx4.resolve_instance(&neg_goal).is_some(),
        t.elapsed()
    );

    for c in ["MonadLiftT", "MonadLift"] {
        let n = Name::interned(c);
        println!(
            "{c}: is_class={} n_inst={} arity={:?}",
            env.is_class(&n),
            env.get_class_instances(&n).len(),
            env.get_class_info(&n).map(|i| i.num_params)
        );
        for i in env.get_class_instances(&n) {
            println!(
                "   {} @{} synthOrder={:?}",
                i.name,
                i.priority,
                env.get_instance_synth_order(&i.name)
            );
        }
    }
}
