-- Minimal repro: retained-certificate kernel inference DIVERGES on this file
-- (exponential ProofCert materialization; 50+ min CPU / 30+ GB RSS observed
-- 2026-08-21 at 97efa0e6c before being killed).
-- See docs/issues/2026-08-21-cert-clone-exponential-tree-mirror.md.
-- Byte-identical to the R100 everyday-battery snippet `data_tree-mirror-size`
-- (crates/clean-elab/src/lean4_corpus_tests.rs, reconstructed-2026-08-10 set).
inductive data_Tree where
  | leaf
  | node : data_Tree → data_Tree → data_Tree

def data_Tree.size : data_Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

def data_Tree.mirror : data_Tree → data_Tree
  | .leaf => .leaf
  | .node l r => .node r.mirror l.mirror

theorem data_tree_mirror_size (t : data_Tree) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
    simp [data_Tree.mirror, data_Tree.size, ihl, ihr, Nat.add_comm]
