-- ImportPasses: consumed by crates/clean-olean/src/import/tests_import_passes_fixture.rs.
-- README.md beside this file records the recipe and what each shape pins.
--
-- The per-module `.olean` import decides `is_large_elim` for the module's own
-- inductives (`Environment::recompute_imported_large_elim`) and recovers
-- projection field tables (`import/projection_scan.rs`). Every inductive here
-- is a shape on which that decision has a definite answer from Lean's own
-- kernel (`src/kernel/inductive.cpp`, `elim_only_at_universe_zero`), readable
-- in this very `.olean`: a large-eliminating recursor carries one more
-- universe parameter than its inductive.
--
-- `prelude` with no imports, no `module` header: one base `.olean`, closure-free.
prelude

-- Lean's auxiliary constructions for the mutual block below name `PUnit`
-- (measured: `(kernel) unknown constant 'PUnit'` without it), so the
-- prelude's own definition is repeated here to keep the module closure-free.
universe u
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

inductive ImportPasses.N : Type where
  | zero : ImportPasses.N
  | succ (n : ImportPasses.N) : ImportPasses.N

-- A Type-valued field that IS a bare index argument: large.
inductive ImportPasses.Idx : ImportPasses.N → Prop where
  | mk (n : ImportPasses.N) : ImportPasses.Idx n

-- The field occurs only under a constructor application: Prop only.
inductive ImportPasses.NotIdx : ImportPasses.N → Prop where
  | mk (n : ImportPasses.N) : ImportPasses.NotIdx (ImportPasses.N.succ n)

-- The `Nonempty` shape: Prop only.
inductive ImportPasses.NE (α : Sort u) : Prop where
  | intro (v : α) : ImportPasses.NE α

-- A mutual block of predicates: Prop only, although each member alone
-- (one constructor, Prop fields) would eliminate into any universe.
mutual
inductive ImportPasses.MA : Prop where
  | mk (h : ImportPasses.MB) : ImportPasses.MA
inductive ImportPasses.MB : Prop where
  | mk : ImportPasses.MB
end

-- The field's TYPE mentions a CONSTRUCTOR of this module: deciding it needs
-- the module's constructors resident, not only its inductives. Large.
inductive ImportPasses.AtZero : Prop where
  | mk (h : ImportPasses.Idx ImportPasses.N.zero) : ImportPasses.AtZero

-- The field's type is a DEFINITION of this module. Lean decides with the
-- definition in scope: large. Clean also computes the derived elimination
-- flag with the same-part definitions resident; the consumer requires parity.
def ImportPasses.Pred (n : ImportPasses.N) : Prop := ImportPasses.Idx n

structure ImportPasses.ViaDef (n : ImportPasses.N) : Prop where
  h : ImportPasses.Pred n

-- A structure: Lean's structure extension carries its field table.
structure ImportPasses.S : Type where
  a : ImportPasses.N
  b : ImportPasses.N

-- A structure-LIKE `inductive` has no structure-extension entry; numeric
-- projections on it elaborate to raw `Expr.proj`, which is the shape the
-- projection-derived fallback reads.
inductive ImportPasses.Pair : Type where
  | mk (x y : ImportPasses.N) : ImportPasses.Pair

def ImportPasses.Pair.first (p : ImportPasses.Pair) : ImportPasses.N := p.1
def ImportPasses.Pair.second (p : ImportPasses.Pair) : ImportPasses.N := p.2
