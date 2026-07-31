// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Concurrency Theory structures for Environment
//!
//! This module provides axioms and structures for concurrency theory:
//! - Process algebras (CCS, CSP, π-calculus, ACP)
//! - Labeled transition systems and bisimulation
//! - Petri nets and state machines
//! - Message passing and shared memory models
//! - Synchronization primitives and deadlock analysis
//! - Temporal logics for concurrent systems (LTL, CTL, CTL*)
//! - Fairness and liveness properties
//!
//! This module provides foundations for verifying concurrent and
//! distributed systems - essential for modern software verification.

#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

#[cfg(test)]
impl Environment {
    /// Initialize Concurrency Theory module
    ///
    /// Concurrency theory studies the formal foundations of
    /// concurrent and distributed systems: their semantics,
    /// equivalences, and verification methods.
    ///
    /// Key areas:
    /// - Process algebras: compositional reasoning about processes
    /// - Bisimulation: behavioral equivalence of processes
    /// - Temporal logics: specify and verify temporal properties
    /// - Synchronization: coordinate concurrent activities
    /// - Deadlock/livelock: analyze pathological behaviors
    ///
    /// Applications:
    /// - Protocol verification
    /// - Distributed systems design
    /// - Concurrent program analysis
    /// - Hardware verification
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.concurrency_theory_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_concurrency_theory(&mut self) -> Result<(), EnvError> {
        if self.concurrency_theory_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_list()?;
        self.init_option()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Concurrency Theory constants
        for name in &[
            // ================================================================
            // Labeled Transition Systems (LTS)
            // ================================================================
            "ConcurrencyTheory.LTS",            // labeled transition system
            "ConcurrencyTheory.LTS.State",      // states S
            "ConcurrencyTheory.LTS.Action",     // actions A (labels)
            "ConcurrencyTheory.LTS.Transition", // transition relation →
            "ConcurrencyTheory.LTS.Step",       // s --a--> s' single step
            "ConcurrencyTheory.LTS.Initial",    // initial states
            "ConcurrencyTheory.LTS.Terminal",   // terminal/final states
            "ConcurrencyTheory.LTS.Reachable",  // reachable states
            "ConcurrencyTheory.LTS.Trace",      // execution trace
            "ConcurrencyTheory.LTS.WeakStep",   // s ==a==> s' with τ
            "ConcurrencyTheory.LTS.Tau",        // τ (internal/silent action)
            "ConcurrencyTheory.LTS.Deterministic", // at most one successor per action
            "ConcurrencyTheory.LTS.Nondeterministic", // multiple successors possible
            "ConcurrencyTheory.LTS.Finite",     // finitely branching
            "ConcurrencyTheory.LTS.ImageFinite", // image-finite LTS
            // ================================================================
            // Bisimulation and Process Equivalences
            // ================================================================
            "ConcurrencyTheory.Bisim",              // bisimulation relation
            "ConcurrencyTheory.Bisim.Strong",       // strong bisimulation ∼
            "ConcurrencyTheory.Bisim.Weak",         // weak bisimulation ≈
            "ConcurrencyTheory.Bisim.Branching",    // branching bisimulation
            "ConcurrencyTheory.Bisim.DelayBisim",   // delay bisimulation
            "ConcurrencyTheory.Bisim.EtaBisim",     // η-bisimulation
            "ConcurrencyTheory.Bisim.TauLoopBisim", // τ-loop bisimulation
            "ConcurrencyTheory.Bisim.BisimGame",    // bisimulation game
            "ConcurrencyTheory.Bisim.Attacker",     // Attacker/Spoiler in game
            "ConcurrencyTheory.Bisim.Defender",     // Defender/Duplicator in game
            "ConcurrencyTheory.Simulation",         // simulation relation
            "ConcurrencyTheory.Simulation.Forward", // forward simulation
            "ConcurrencyTheory.Simulation.Backward", // backward simulation
            "ConcurrencyTheory.Simulation.Complete", // simulation completeness
            "ConcurrencyTheory.TraceEquiv",         // trace equivalence
            "ConcurrencyTheory.FailureEquiv",       // failure equivalence
            "ConcurrencyTheory.TestingEquiv",       // testing equivalence (may/must)
            "ConcurrencyTheory.MayTest",            // may testing
            "ConcurrencyTheory.MustTest",           // must testing
            "ConcurrencyTheory.ReadyEquiv",         // ready equivalence
            "ConcurrencyTheory.FailureTraceEquiv",  // failure-trace equivalence
            "ConcurrencyTheory.CompletedTraceEquiv", // completed trace equivalence
            // ================================================================
            // CCS (Calculus of Communicating Systems)
            // ================================================================
            "ConcurrencyTheory.CCS",                // CCS calculus
            "ConcurrencyTheory.CCS.Process",        // CCS process
            "ConcurrencyTheory.CCS.Nil",            // 0 (nil/stop process)
            "ConcurrencyTheory.CCS.Action",         // a (action prefix)
            "ConcurrencyTheory.CCS.CoAction",       // ā (co-action)
            "ConcurrencyTheory.CCS.Prefix",         // a.P (action prefix)
            "ConcurrencyTheory.CCS.Sum",            // P + Q (choice/sum)
            "ConcurrencyTheory.CCS.Par",            // P | Q (parallel composition)
            "ConcurrencyTheory.CCS.Restrict",       // P \ L (restriction)
            "ConcurrencyTheory.CCS.Relabel",        // P[f] (relabeling)
            "ConcurrencyTheory.CCS.Rec",            // rec X.P (recursion)
            "ConcurrencyTheory.CCS.Var",            // X (process variable)
            "ConcurrencyTheory.CCS.Tau",            // τ (internal action)
            "ConcurrencyTheory.CCS.Sync",           // synchronization a|ā → τ
            "ConcurrencyTheory.CCS.Expansion",      // expansion law
            "ConcurrencyTheory.CCS.Axioms",         // CCS axioms (A1-A4)
            "ConcurrencyTheory.CCS.UniqueFixpoint", // unique fixpoint theorem
            "ConcurrencyTheory.CCS.Guardedness",    // guarded recursion
            "ConcurrencyTheory.CCS.WeakCCS",        // weak CCS semantics
            // ================================================================
            // CSP (Communicating Sequential Processes)
            // ================================================================
            "ConcurrencyTheory.CSP",                // CSP calculus
            "ConcurrencyTheory.CSP.Process",        // CSP process
            "ConcurrencyTheory.CSP.Stop",           // STOP (deadlock)
            "ConcurrencyTheory.CSP.Skip",           // SKIP (successful termination)
            "ConcurrencyTheory.CSP.Prefix",         // a → P (prefix)
            "ConcurrencyTheory.CSP.ExtChoice",      // P □ Q (external choice)
            "ConcurrencyTheory.CSP.IntChoice",      // P ⊓ Q (internal choice)
            "ConcurrencyTheory.CSP.Par",            // P ∥ Q (alphabetized parallel)
            "ConcurrencyTheory.CSP.Interleave",     // P ||| Q (interleaving)
            "ConcurrencyTheory.CSP.Sync",           // P [A‖B] Q (generalized parallel)
            "ConcurrencyTheory.CSP.Hide",           // P \ A (hiding)
            "ConcurrencyTheory.CSP.Rename",         // P[[R]] (renaming)
            "ConcurrencyTheory.CSP.SeqComp",        // P ; Q (sequential composition)
            "ConcurrencyTheory.CSP.Interrupt",      // P △ Q (interrupt)
            "ConcurrencyTheory.CSP.Timeout",        // P ▷ Q (timeout)
            "ConcurrencyTheory.CSP.Exception",      // P ⟦A⟧▷ Q (exception handling)
            "ConcurrencyTheory.CSP.Rec",            // μ X.P (recursion)
            "ConcurrencyTheory.CSP.Traces",         // traces(P)
            "ConcurrencyTheory.CSP.Failures",       // failures(P)
            "ConcurrencyTheory.CSP.Divergences",    // divergences(P)
            "ConcurrencyTheory.CSP.TraceSem",       // trace semantics T
            "ConcurrencyTheory.CSP.StableFailures", // stable failures model F
            "ConcurrencyTheory.CSP.FailDivergence", // failures-divergence model N
            "ConcurrencyTheory.CSP.Refinement",     // ⊑ refinement relation
            "ConcurrencyTheory.CSP.FDR",            // FDR refinement checking
            // ================================================================
            // π-calculus (Pi-calculus)
            // ================================================================
            "ConcurrencyTheory.Pi",                 // π-calculus
            "ConcurrencyTheory.Pi.Process",         // π-calculus process
            "ConcurrencyTheory.Pi.Nil",             // 0 (nil process)
            "ConcurrencyTheory.Pi.Send",            // x̄⟨y⟩.P (output)
            "ConcurrencyTheory.Pi.Recv",            // x(y).P (input)
            "ConcurrencyTheory.Pi.Par",             // P | Q (parallel)
            "ConcurrencyTheory.Pi.Sum",             // P + Q (choice)
            "ConcurrencyTheory.Pi.Restrict",        // (νx)P (restriction/new)
            "ConcurrencyTheory.Pi.Replicate",       // !P (replication)
            "ConcurrencyTheory.Pi.Match",           // [x=y]P (match)
            "ConcurrencyTheory.Pi.Mismatch",        // [x≠y]P (mismatch)
            "ConcurrencyTheory.Pi.Channel",         // channel name
            "ConcurrencyTheory.Pi.FreeNames",       // free names fn(P)
            "ConcurrencyTheory.Pi.BoundNames",      // bound names bn(P)
            "ConcurrencyTheory.Pi.Names",           // all names n(P)
            "ConcurrencyTheory.Pi.Substitution",    // P{y/x} name substitution
            "ConcurrencyTheory.Pi.ScopeExtrusion",  // scope extrusion
            "ConcurrencyTheory.Pi.AlphaConv",       // α-conversion
            "ConcurrencyTheory.Pi.StructCong",      // ≡ structural congruence
            "ConcurrencyTheory.Pi.ReductionRel",    // → reduction relation
            "ConcurrencyTheory.Pi.LabeledTrans",    // --α--> labeled transition
            "ConcurrencyTheory.Pi.EarlySemantics",  // early semantics
            "ConcurrencyTheory.Pi.LateSemantics",   // late semantics
            "ConcurrencyTheory.Pi.OpenSemantics",   // open semantics
            "ConcurrencyTheory.Pi.GroundBisim",     // ground bisimulation
            "ConcurrencyTheory.Pi.BarredBisim",     // barbed bisimulation
            "ConcurrencyTheory.Pi.CongruentBisim",  // barbed congruence
            "ConcurrencyTheory.Pi.FullAbstraction", // full abstraction result
            // ================================================================
            // Variants of π-calculus
            // ================================================================
            "ConcurrencyTheory.AsyncPi",       // asynchronous π-calculus
            "ConcurrencyTheory.AsyncPi.Send",  // x̄⟨y⟩ (no continuation)
            "ConcurrencyTheory.PolyPi",        // polyadic π-calculus
            "ConcurrencyTheory.PolyPi.Tuple",  // x̄⟨ỹ⟩ (tuple output)
            "ConcurrencyTheory.HigherOrderPi", // higher-order π
            "ConcurrencyTheory.HigherOrderPi.Send", // x̄⟨P⟩ (process passing)
            "ConcurrencyTheory.SpiCalculus",   // spi-calculus (crypto)
            "ConcurrencyTheory.AppliedPi",     // applied π-calculus
            "ConcurrencyTheory.AppliedPi.Term", // terms with functions
            "ConcurrencyTheory.AppliedPi.Active", // active substitution
            "ConcurrencyTheory.PsiCalculus",   // Psi-calculus (generic)
            "ConcurrencyTheory.FusionCalculus", // Fusion calculus
            // ================================================================
            // ACP (Algebra of Communicating Processes)
            // ================================================================
            "ConcurrencyTheory.ACP",               // ACP algebra
            "ConcurrencyTheory.ACP.Process",       // ACP process term
            "ConcurrencyTheory.ACP.Delta",         // δ (deadlock)
            "ConcurrencyTheory.ACP.Epsilon",       // ε (empty process)
            "ConcurrencyTheory.ACP.Action",        // a (atomic action)
            "ConcurrencyTheory.ACP.AltComp",       // P + Q (alternative)
            "ConcurrencyTheory.ACP.SeqComp",       // P · Q (sequential)
            "ConcurrencyTheory.ACP.Merge",         // P ∥ Q (merge)
            "ConcurrencyTheory.ACP.LeftMerge",     // P ⫿ Q (left merge)
            "ConcurrencyTheory.ACP.CommMerge",     // P | Q (communication merge)
            "ConcurrencyTheory.ACP.Encapsulation", // ∂_H(P) (encapsulation)
            "ConcurrencyTheory.ACP.Abstraction",   // τ_I(P) (abstraction)
            "ConcurrencyTheory.ACP.CommFunc",      // γ(a,b) = c communication function
            "ConcurrencyTheory.ACP.Axioms",        // ACP axioms (BPA, PA, ACP)
            "ConcurrencyTheory.ACP.RSP",           // recursive specification principle
            "ConcurrencyTheory.ACP.AIP",           // approximation induction principle
            "ConcurrencyTheory.ACP.TauLaws",       // τ-laws (tau axioms)
            // ================================================================
            // Petri Nets
            // ================================================================
            "ConcurrencyTheory.PetriNet",              // Petri net
            "ConcurrencyTheory.PetriNet.Place",        // places P
            "ConcurrencyTheory.PetriNet.Transition",   // transitions T
            "ConcurrencyTheory.PetriNet.Arc",          // arcs F ⊆ (P×T) ∪ (T×P)
            "ConcurrencyTheory.PetriNet.Weight",       // arc weights W
            "ConcurrencyTheory.PetriNet.Marking",      // marking M : P → ℕ
            "ConcurrencyTheory.PetriNet.Initial",      // initial marking M₀
            "ConcurrencyTheory.PetriNet.Enabled",      // transition enabled
            "ConcurrencyTheory.PetriNet.Fire",         // transition firing
            "ConcurrencyTheory.PetriNet.Reach",        // reachability set
            "ConcurrencyTheory.PetriNet.Coverability", // coverability graph
            "ConcurrencyTheory.PetriNet.Bounded",      // k-bounded net
            "ConcurrencyTheory.PetriNet.Safe",         // 1-safe net
            "ConcurrencyTheory.PetriNet.Live",         // live transition
            "ConcurrencyTheory.PetriNet.DeadlockFree", // deadlock-free net
            "ConcurrencyTheory.PetriNet.Reversible",   // reversible net
            "ConcurrencyTheory.PetriNet.Persistent",   // persistent net
            "ConcurrencyTheory.PetriNet.FreeChoice",   // free-choice net
            "ConcurrencyTheory.PetriNet.Siphon",       // siphon (deadlock)
            "ConcurrencyTheory.PetriNet.Trap",         // trap (liveness)
            "ConcurrencyTheory.PetriNet.Invariant",    // place/transition invariant
            "ConcurrencyTheory.PetriNet.PlaceInv",     // place invariant (P-invariant)
            "ConcurrencyTheory.PetriNet.TransInv",     // transition invariant (T-invariant)
            "ConcurrencyTheory.ColoredPN",             // colored Petri nets
            "ConcurrencyTheory.TimedPN",               // timed Petri nets
            "ConcurrencyTheory.StochasticPN",          // stochastic Petri nets
            // ================================================================
            // Temporal Logic for Concurrent Systems
            // ================================================================
            "ConcurrencyTheory.LTL",                  // Linear Temporal Logic
            "ConcurrencyTheory.LTL.Formula",          // LTL formula
            "ConcurrencyTheory.LTL.Prop",             // atomic proposition
            "ConcurrencyTheory.LTL.Not",              // ¬φ (negation)
            "ConcurrencyTheory.LTL.And",              // φ ∧ ψ (conjunction)
            "ConcurrencyTheory.LTL.Or",               // φ ∨ ψ (disjunction)
            "ConcurrencyTheory.LTL.Implies",          // φ → ψ (implication)
            "ConcurrencyTheory.LTL.Next",             // Xφ (next)
            "ConcurrencyTheory.LTL.Eventually",       // Fφ (eventually/finally)
            "ConcurrencyTheory.LTL.Always",           // Gφ (always/globally)
            "ConcurrencyTheory.LTL.Until",            // φ U ψ (until)
            "ConcurrencyTheory.LTL.Release",          // φ R ψ (release)
            "ConcurrencyTheory.LTL.WeakUntil",        // φ W ψ (weak until)
            "ConcurrencyTheory.LTL.StrongRelease",    // φ M ψ (strong release)
            "ConcurrencyTheory.LTL.Path",             // infinite path
            "ConcurrencyTheory.LTL.Satisfies",        // π ⊨ φ path satisfies
            "ConcurrencyTheory.LTL.Valid",            // ⊨ φ validity
            "ConcurrencyTheory.LTL.Equiv",            // φ ≡ ψ equivalence
            "ConcurrencyTheory.LTL.NNF",              // negation normal form
            "ConcurrencyTheory.LTL.Closure",          // closure(φ)
            "ConcurrencyTheory.LTL.Buchi",            // Büchi automaton translation
            "ConcurrencyTheory.CTL",                  // Computation Tree Logic
            "ConcurrencyTheory.CTL.Formula",          // CTL formula
            "ConcurrencyTheory.CTL.EX",               // EX φ (exists next)
            "ConcurrencyTheory.CTL.AX",               // AX φ (all next)
            "ConcurrencyTheory.CTL.EF",               // EF φ (exists eventually)
            "ConcurrencyTheory.CTL.AF",               // AF φ (all eventually)
            "ConcurrencyTheory.CTL.EG",               // EG φ (exists always)
            "ConcurrencyTheory.CTL.AG",               // AG φ (all always)
            "ConcurrencyTheory.CTL.EU",               // E[φ U ψ] (exists until)
            "ConcurrencyTheory.CTL.AU",               // A[φ U ψ] (all until)
            "ConcurrencyTheory.CTL.FixedPoint",       // fixed-point characterization
            "ConcurrencyTheory.CTL.MinFP",            // μZ.f(Z) least fixed point
            "ConcurrencyTheory.CTL.MaxFP",            // νZ.f(Z) greatest fixed point
            "ConcurrencyTheory.CTL.Satisfies",        // M,s ⊨ φ state satisfies
            "ConcurrencyTheory.CTL.ModelCheck",       // CTL model checking algorithm
            "ConcurrencyTheory.CTLStar",              // CTL* (full branching time)
            "ConcurrencyTheory.CTLStar.Formula",      // CTL* formula
            "ConcurrencyTheory.CTLStar.StateFormula", // state formula
            "ConcurrencyTheory.CTLStar.PathFormula",  // path formula
            "ConcurrencyTheory.CTLStar.E",            // E path quantifier
            "ConcurrencyTheory.CTLStar.A",            // A path quantifier
            "ConcurrencyTheory.CTLStar.Expressive",   // CTL* expressiveness
            "ConcurrencyTheory.MuCalculus",           // modal μ-calculus
            "ConcurrencyTheory.MuCalculus.Formula",   // μ-calculus formula
            "ConcurrencyTheory.MuCalculus.Diamond",   // ⟨a⟩φ (diamond/possibility)
            "ConcurrencyTheory.MuCalculus.Box",       // [a]φ (box/necessity)
            "ConcurrencyTheory.MuCalculus.Mu",        // μX.φ (least fixed point)
            "ConcurrencyTheory.MuCalculus.Nu",        // νX.φ (greatest fixed point)
            "ConcurrencyTheory.MuCalculus.Alternation", // alternation depth
            "ConcurrencyTheory.MuCalculus.Expressive", // μ-calculus expressiveness
            // ================================================================
            // Fairness
            // ================================================================
            "ConcurrencyTheory.Fair",               // fairness
            "ConcurrencyTheory.Fair.WeakFair",      // weak fairness (justice)
            "ConcurrencyTheory.Fair.StrongFair",    // strong fairness (compassion)
            "ConcurrencyTheory.Fair.Unconditional", // unconditional fairness
            "ConcurrencyTheory.Fair.ProcessFair",   // process fairness
            "ConcurrencyTheory.Fair.ActionFair",    // action fairness
            "ConcurrencyTheory.Fair.FairPath",      // fair execution path
            "ConcurrencyTheory.Fair.FairReach",     // fair reachability
            "ConcurrencyTheory.Fair.FairCTL",       // fair CTL semantics
            // ================================================================
            // Liveness and Safety
            // ================================================================
            "ConcurrencyTheory.Safety",            // safety property
            "ConcurrencyTheory.Safety.BadPrefix",  // bad prefix (witness)
            "ConcurrencyTheory.Safety.Invariant",  // state invariant
            "ConcurrencyTheory.Safety.Closure",    // safety = closure
            "ConcurrencyTheory.Liveness",          // liveness property
            "ConcurrencyTheory.Liveness.Dense",    // liveness = dense
            "ConcurrencyTheory.Liveness.Progress", // progress (something good)
            "ConcurrencyTheory.Liveness.Response", // response (request → response)
            "ConcurrencyTheory.TopologicalDecomp", // safety ∩ liveness decomposition
            // ================================================================
            // Deadlock and Livelock
            // ================================================================
            "ConcurrencyTheory.Deadlock",              // deadlock state
            "ConcurrencyTheory.Deadlock.Global",       // global deadlock
            "ConcurrencyTheory.Deadlock.Partial",      // partial deadlock
            "ConcurrencyTheory.Deadlock.Detection",    // deadlock detection
            "ConcurrencyTheory.Deadlock.Prevention",   // deadlock prevention
            "ConcurrencyTheory.Deadlock.Avoidance",    // deadlock avoidance
            "ConcurrencyTheory.Deadlock.Recovery",     // deadlock recovery
            "ConcurrencyTheory.Deadlock.WaitForGraph", // wait-for graph
            "ConcurrencyTheory.Deadlock.Cycle",        // cycle = deadlock
            "ConcurrencyTheory.Livelock",              // livelock (no progress)
            "ConcurrencyTheory.Livelock.Detection",    // livelock detection
            "ConcurrencyTheory.Starvation",            // starvation (unfair)
            // ================================================================
            // Synchronization Primitives
            // ================================================================
            "ConcurrencyTheory.Sync",            // synchronization
            "ConcurrencyTheory.Sync.Mutex",      // mutual exclusion
            "ConcurrencyTheory.Sync.Lock",       // lock (acquire/release)
            "ConcurrencyTheory.Sync.Unlock",     // unlock operation
            "ConcurrencyTheory.Sync.TryLock",    // non-blocking lock
            "ConcurrencyTheory.Sync.Semaphore",  // counting semaphore
            "ConcurrencyTheory.Sync.BinarySem",  // binary semaphore
            "ConcurrencyTheory.Sync.Wait",       // P/wait operation
            "ConcurrencyTheory.Sync.Signal",     // V/signal operation
            "ConcurrencyTheory.Sync.Monitor",    // monitor construct
            "ConcurrencyTheory.Sync.CondVar",    // condition variable
            "ConcurrencyTheory.Sync.Barrier",    // barrier synchronization
            "ConcurrencyTheory.Sync.Rendezvous", // rendezvous (CSP-style)
            "ConcurrencyTheory.Sync.RWLock",     // reader-writer lock
            "ConcurrencyTheory.Sync.Spinlock",   // spinlock
            // ================================================================
            // Shared Memory Concurrency
            // ================================================================
            "ConcurrencyTheory.SharedMem", // shared memory model
            "ConcurrencyTheory.SharedMem.Variable", // shared variable
            "ConcurrencyTheory.SharedMem.Read", // read operation
            "ConcurrencyTheory.SharedMem.Write", // write operation
            "ConcurrencyTheory.SharedMem.CAS", // compare-and-swap
            "ConcurrencyTheory.SharedMem.Atomic", // atomic operation
            "ConcurrencyTheory.SharedMem.Fence", // memory fence
            "ConcurrencyTheory.SharedMem.SC", // sequential consistency
            "ConcurrencyTheory.SharedMem.TSO", // total store ordering
            "ConcurrencyTheory.SharedMem.PSO", // partial store ordering
            "ConcurrencyTheory.SharedMem.RMO", // relaxed memory ordering
            "ConcurrencyTheory.SharedMem.Release", // release semantics
            "ConcurrencyTheory.SharedMem.Acquire", // acquire semantics
            "ConcurrencyTheory.SharedMem.SeqCst", // sequentially consistent fence
            "ConcurrencyTheory.SharedMem.DataRace", // data race
            "ConcurrencyTheory.SharedMem.RaceFree", // race-free program
            "ConcurrencyTheory.SharedMem.DRF", // data-race-freedom guarantee
            // ================================================================
            // Message Passing
            // ================================================================
            "ConcurrencyTheory.MsgPass",            // message passing
            "ConcurrencyTheory.MsgPass.Send",       // send message
            "ConcurrencyTheory.MsgPass.Recv",       // receive message
            "ConcurrencyTheory.MsgPass.Channel",    // communication channel
            "ConcurrencyTheory.MsgPass.Sync",       // synchronous send/recv
            "ConcurrencyTheory.MsgPass.Async",      // asynchronous send/recv
            "ConcurrencyTheory.MsgPass.Buffered",   // buffered channel
            "ConcurrencyTheory.MsgPass.Unbuffered", // unbuffered (rendezvous)
            "ConcurrencyTheory.MsgPass.Multicast",  // multicast message
            "ConcurrencyTheory.MsgPass.Broadcast",  // broadcast message
            "ConcurrencyTheory.MsgPass.Select",     // select/poll multiple channels
            "ConcurrencyTheory.MsgPass.FIFO",       // FIFO ordering
            "ConcurrencyTheory.MsgPass.Causal",     // causal ordering
            "ConcurrencyTheory.MsgPass.Total",      // total ordering
            // ================================================================
            // Actors Model
            // ================================================================
            "ConcurrencyTheory.Actor",                 // actor model
            "ConcurrencyTheory.Actor.Behavior",        // actor behavior
            "ConcurrencyTheory.Actor.Mailbox",         // actor mailbox
            "ConcurrencyTheory.Actor.Create",          // create new actor
            "ConcurrencyTheory.Actor.Send",            // send message to actor
            "ConcurrencyTheory.Actor.Become",          // change behavior
            "ConcurrencyTheory.Actor.Address",         // actor address/reference
            "ConcurrencyTheory.Actor.Receptionist",    // actor receptionist
            "ConcurrencyTheory.Actor.Supervision",     // supervision tree
            "ConcurrencyTheory.Actor.LetItCrash",      // let-it-crash philosophy
            "ConcurrencyTheory.Actor.EventualConsist", // eventual consistency
            // ================================================================
            // Concurrent Object Models
            // ================================================================
            "ConcurrencyTheory.ConcObj", // concurrent objects
            "ConcurrencyTheory.ConcObj.Linearizable", // linearizability
            "ConcurrencyTheory.ConcObj.SeqSpec", // sequential specification
            "ConcurrencyTheory.ConcObj.LinPoint", // linearization point
            "ConcurrencyTheory.ConcObj.Serializable", // serializability
            "ConcurrencyTheory.ConcObj.StrictSerial", // strict serializability
            "ConcurrencyTheory.ConcObj.Atomic", // atomic object
            "ConcurrencyTheory.ConcObj.WaitFree", // wait-free implementation
            "ConcurrencyTheory.ConcObj.LockFree", // lock-free implementation
            "ConcurrencyTheory.ConcObj.ObstrFree", // obstruction-free
            "ConcurrencyTheory.ConcObj.Consensus", // consensus object
            "ConcurrencyTheory.ConcObj.ConsensusNum", // consensus number
            "ConcurrencyTheory.ConcObj.Universal", // universal construction
            // ================================================================
            // Distributed Systems
            // ================================================================
            "ConcurrencyTheory.Dist",                  // distributed systems
            "ConcurrencyTheory.Dist.Process",          // distributed process
            "ConcurrencyTheory.Dist.LocalState",       // local state
            "ConcurrencyTheory.Dist.GlobalState",      // global state (snapshot)
            "ConcurrencyTheory.Dist.CausalOrder",      // causal ordering →
            "ConcurrencyTheory.Dist.HappensBefore",    // happens-before relation
            "ConcurrencyTheory.Dist.Concurrent",       // concurrent events
            "ConcurrencyTheory.Dist.VectorClock",      // vector clock
            "ConcurrencyTheory.Dist.LamportClock",     // Lamport logical clock
            "ConcurrencyTheory.Dist.MatrixClock",      // matrix clock
            "ConcurrencyTheory.Dist.Snapshot",         // consistent snapshot
            "ConcurrencyTheory.Dist.Cut",              // consistent cut
            "ConcurrencyTheory.Dist.FLP",              // FLP impossibility
            "ConcurrencyTheory.Dist.CAP",              // CAP theorem
            "ConcurrencyTheory.Dist.Consensus",        // distributed consensus
            "ConcurrencyTheory.Dist.Paxos",            // Paxos algorithm
            "ConcurrencyTheory.Dist.Raft",             // Raft algorithm
            "ConcurrencyTheory.Dist.TwoPhaseCommit",   // 2PC protocol
            "ConcurrencyTheory.Dist.ThreePhaseCommit", // 3PC protocol
            "ConcurrencyTheory.Dist.ByzFault",         // Byzantine fault tolerance
            "ConcurrencyTheory.Dist.PBFT",             // practical BFT
            "ConcurrencyTheory.Dist.Quorum",           // quorum systems
            "ConcurrencyTheory.Dist.Replication",      // state machine replication
            // ================================================================
            // Session Types and Protocols
            // ================================================================
            "ConcurrencyTheory.Session",              // session types
            "ConcurrencyTheory.Session.Type",         // session type S
            "ConcurrencyTheory.Session.End",          // end (session end)
            "ConcurrencyTheory.Session.Send",         // !T.S (send T continue S)
            "ConcurrencyTheory.Session.Recv",         // ?T.S (recv T continue S)
            "ConcurrencyTheory.Session.Choice",       // ⊕{l:S} (internal choice)
            "ConcurrencyTheory.Session.Branch",       // &{l:S} (external choice)
            "ConcurrencyTheory.Session.Rec",          // μX.S (recursive type)
            "ConcurrencyTheory.Session.Dual",         // S̄ dual of S
            "ConcurrencyTheory.Session.Subtype",      // S <: T subtyping
            "ConcurrencyTheory.Session.Delegation",   // session delegation
            "ConcurrencyTheory.Session.Progress",     // deadlock freedom
            "ConcurrencyTheory.Session.Multiparty",   // multiparty session types
            "ConcurrencyTheory.Session.GlobalType",   // global type G
            "ConcurrencyTheory.Session.Projection",   // projection G↾p
            "ConcurrencyTheory.Session.Choreography", // choreographic programming
            // ================================================================
            // Verification Methods
            // ================================================================
            "ConcurrencyTheory.Verify",            // verification methods
            "ConcurrencyTheory.Verify.ModelCheck", // model checking
            "ConcurrencyTheory.Verify.SymbolicMC", // symbolic model checking
            "ConcurrencyTheory.Verify.BDD",        // binary decision diagrams
            "ConcurrencyTheory.Verify.SAT",        // SAT-based BMC
            "ConcurrencyTheory.Verify.CEGAR",      // counterexample-guided abstraction refinement
            "ConcurrencyTheory.Verify.StaticAnalysis", // static analysis
            "ConcurrencyTheory.Verify.AbstractInterp", // abstract interpretation
            "ConcurrencyTheory.Verify.PartialOrder", // partial-order reduction
            "ConcurrencyTheory.Verify.Stubborn",   // stubborn sets
            "ConcurrencyTheory.Verify.Ample",      // ample sets
            "ConcurrencyTheory.Verify.Sleep",      // sleep sets
            "ConcurrencyTheory.Verify.DPOR",       // dynamic POR
            "ConcurrencyTheory.Verify.OwenGraph",  // Owicki-Gries method
            "ConcurrencyTheory.Verify.RelyGuarantee", // rely-guarantee reasoning
            "ConcurrencyTheory.Verify.ConcSepLogic", // concurrent separation logic
            "ConcurrencyTheory.Verify.Iris",       // Iris framework
            "ConcurrencyTheory.Verify.RGSep",      // RGSep logic
            "ConcurrencyTheory.Verify.TaDA",       // TaDA logic
            "ConcurrencyTheory.Verify.Prophecy",   // prophecy variables
            "ConcurrencyTheory.Verify.History",    // history variables
            // ================================================================
            // Concurrent Data Structures
            // ================================================================
            "ConcurrencyTheory.DS",              // concurrent data structures
            "ConcurrencyTheory.DS.ConcQueue",    // concurrent queue
            "ConcurrencyTheory.DS.MichaelScott", // Michael-Scott queue
            "ConcurrencyTheory.DS.ConcStack",    // concurrent stack
            "ConcurrencyTheory.DS.Treiber",      // Treiber stack
            "ConcurrencyTheory.DS.ConcList",     // concurrent linked list
            "ConcurrencyTheory.DS.HarrisLinkedList", // Harris non-blocking list
            "ConcurrencyTheory.DS.SkipList",     // concurrent skip list
            "ConcurrencyTheory.DS.ConcHashMap",  // concurrent hash map
            "ConcurrencyTheory.DS.ConcTree",     // concurrent tree
            "ConcurrencyTheory.DS.CRDT",         // conflict-free replicated data type
            "ConcurrencyTheory.DS.GCounter",     // grow-only counter CRDT
            "ConcurrencyTheory.DS.PNCounter",    // positive-negative counter
            "ConcurrencyTheory.DS.LWWRegister",  // last-writer-wins register
            "ConcurrencyTheory.DS.MVRegister",   // multi-value register
            "ConcurrencyTheory.DS.GSet",         // grow-only set
            "ConcurrencyTheory.DS.ORSet",        // observed-remove set
        ] {
            let decl = Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            };
            self.add_decl(decl)?;
        }

        self.concurrency_theory_init = true;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    #[test]
    fn test_concurrency_theory_lts() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.LTS");
        assert_const(&env, "ConcurrencyTheory.LTS.State");
        assert_const(&env, "ConcurrencyTheory.LTS.Transition");
        assert_const(&env, "ConcurrencyTheory.LTS.Tau");
    }

    #[test]
    fn test_concurrency_theory_bisimulation() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Bisim");
        assert_const(&env, "ConcurrencyTheory.Bisim.Strong");
        assert_const(&env, "ConcurrencyTheory.Bisim.Weak");
        assert_const(&env, "ConcurrencyTheory.Bisim.Branching");
    }

    #[test]
    fn test_concurrency_theory_ccs() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.CCS");
        assert_const(&env, "ConcurrencyTheory.CCS.Nil");
        assert_const(&env, "ConcurrencyTheory.CCS.Prefix");
        assert_const(&env, "ConcurrencyTheory.CCS.Par");
    }

    #[test]
    fn test_concurrency_theory_csp() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.CSP");
        assert_const(&env, "ConcurrencyTheory.CSP.Stop");
        assert_const(&env, "ConcurrencyTheory.CSP.ExtChoice");
        assert_const(&env, "ConcurrencyTheory.CSP.Refinement");
    }

    #[test]
    fn test_concurrency_theory_pi_calculus() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Pi");
        assert_const(&env, "ConcurrencyTheory.Pi.Send");
        assert_const(&env, "ConcurrencyTheory.Pi.Recv");
        assert_const(&env, "ConcurrencyTheory.Pi.Restrict");
    }

    #[test]
    fn test_concurrency_theory_temporal_logic() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.LTL");
        assert_const(&env, "ConcurrencyTheory.LTL.Always");
        assert_const(&env, "ConcurrencyTheory.LTL.Eventually");
        assert_const(&env, "ConcurrencyTheory.CTL");
        assert_const(&env, "ConcurrencyTheory.CTL.AG");
    }

    #[test]
    fn test_concurrency_theory_petri_nets() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.PetriNet");
        assert_const(&env, "ConcurrencyTheory.PetriNet.Place");
        assert_const(&env, "ConcurrencyTheory.PetriNet.Transition");
        assert_const(&env, "ConcurrencyTheory.PetriNet.Marking");
    }

    #[test]
    fn test_concurrency_theory_sync() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Sync.Mutex");
        assert_const(&env, "ConcurrencyTheory.Sync.Semaphore");
        assert_const(&env, "ConcurrencyTheory.Sync.Monitor");
        assert_const(&env, "ConcurrencyTheory.Sync.Barrier");
    }

    #[test]
    fn test_concurrency_theory_deadlock() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Deadlock");
        assert_const(&env, "ConcurrencyTheory.Deadlock.Detection");
        assert_const(&env, "ConcurrencyTheory.Safety");
        assert_const(&env, "ConcurrencyTheory.Liveness");
    }

    #[test]
    fn test_concurrency_theory_distributed() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Dist");
        assert_const(&env, "ConcurrencyTheory.Dist.VectorClock");
        assert_const(&env, "ConcurrencyTheory.Dist.Consensus");
        assert_const(&env, "ConcurrencyTheory.Dist.Paxos");
    }

    #[test]
    fn test_concurrency_theory_session_types() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Session");
        assert_const(&env, "ConcurrencyTheory.Session.Dual");
        assert_const(&env, "ConcurrencyTheory.Session.Multiparty");
        assert_const(&env, "ConcurrencyTheory.Session.Choreography");
    }

    #[test]
    fn test_concurrency_theory_verification() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Verify.ModelCheck");
        assert_const(&env, "ConcurrencyTheory.Verify.DPOR");
        assert_const(&env, "ConcurrencyTheory.Verify.RelyGuarantee");
        assert_const(&env, "ConcurrencyTheory.Verify.Iris");
    }

    #[test]
    fn test_concurrency_theory_crdts() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.DS.CRDT");
        assert_const(&env, "ConcurrencyTheory.DS.GCounter");
        assert_const(&env, "ConcurrencyTheory.DS.ORSet");
        assert_const(&env, "ConcurrencyTheory.DS.LWWRegister");
    }

    #[test]
    fn test_concurrency_theory_memory_models() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.SharedMem.SC");
        assert_const(&env, "ConcurrencyTheory.SharedMem.TSO");
        assert_const(&env, "ConcurrencyTheory.SharedMem.Release");
        assert_const(&env, "ConcurrencyTheory.SharedMem.Acquire");
    }

    #[test]
    fn test_concurrency_theory_actors() {
        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();

        assert_const(&env, "ConcurrencyTheory.Actor");
        assert_const(&env, "ConcurrencyTheory.Actor.Behavior");
        assert_const(&env, "ConcurrencyTheory.Actor.Mailbox");
        assert_const(&env, "ConcurrencyTheory.Actor.Supervision");
    }

    #[test]
    fn test_concurrency_theory_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_concurrency_theory().unwrap();
        let tc = TypeChecker::new(&env);

        // Verify key constants have well-formed types via tc.infer_type
        for name in &[
            "ConcurrencyTheory.LTS",
            "ConcurrencyTheory.Bisim",
            "ConcurrencyTheory.CCS",
            "ConcurrencyTheory.CSP",
            "ConcurrencyTheory.LTL",
            "ConcurrencyTheory.PetriNet",
        ] {
            let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            // All concurrency theory axioms are declared as Sort(succ(u)),
            // so at u=0 the inferred type should be Sort(1) = Type 0
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }

        // Verify universe level params are present
        let lts_info = env
            .get_const(&Name::from_string("ConcurrencyTheory.LTS"))
            .expect("ConcurrencyTheory.LTS");
        assert!(
            !lts_info.level_params.is_empty(),
            "ConcurrencyTheory.LTS should have universe parameters"
        );
    }
}
