/-
  parser parse-parity ground-truth regeneration recipe
  =====================================================
  Toolchain oracle (pinned): leanprover/lean4 v4.30.0-rc2 (commit 3dc1a088),
    $HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean
  Source probes: 8 verified family specs (
    228 probes captured live from that binary on 2026-07-08).

  This is the REPRODUCTION RECIPE for the `lean_tree` column of
  tests/fixtures/parser_parity/ground_truth.tsv. Two steps:

    (1) ORACLE — run each command below through the pinned `lean`. Each is
        `set_option pp.parens true in #check <input>` (fully-parenthesized
        parse tree) or `#eval <input>` (value). A probe whose `#check`
        fails to PARSE ('expected token' / 'unexpected token') is an ERROR
        row; one that yields a tree is a TREE row.

    (2) NORMALIZE — fold each oracle tree into the parse_parity skeleton
        S-expression (desugared head + parenthesization shape, binders
        abstracted). The clean side is normalized by the SAME renderer,
        `crates/clean-parser/tests/parse_parity_support/render.rs`; the
        grammar and the Lean→skeleton mapping are documented in
        tests/fixtures/parser_parity/README.md.

  Notes on running as-is:
   * Many inputs are Mathlib-only (∑ ∏ ⨆ ⨅ {x|p} ×ˢ ∃!) — the PLAIN
     toolchain rejects them at parse time; that rejection IS the ground
     truth (expected_kind = ERROR). Do NOT add Mathlib to reproduce them.
   * Free identifiers below are declared as `variable`s with generic types
     so the TREE probes elaborate; some probes carry their own binders and
     ignore these. Where a probe needs a specific shape (structures P/Q/R,
     W, Std.HashSet, ...), consult the originating spec file — the recipe
     favors the parse tree, which is context-insensitive.
-/

set_option pp.parens true

-- Generic context for free identifiers used across probes (parse-only;
-- elaboration types are indicative, not authoritative).
variable (a b c d o s t : Nat) (m n : Option Nat)
variable (f g h k : Nat → Nat) (p : Nat → Prop)
variable (x y z i j : Nat) (xs arr helper : List Nat)

/- ── bigop: Big-operator binder notations ∑ ∏ ⨆ ⨅ (Mathlib-only) vs core Σ/Σ' ── -/
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ is Mathlib-only, absent from plain toolchain)
#check ∑ i, i
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check fun (f : Nat → Nat) => ∑ i, f i
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∏ Mathlib-only)
#check ∏ i, (i : Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (⨆ Mathlib-only)
#check ⨆ i, (i : Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (⨅ Mathlib-only)
#check ⨅ i, (i : Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑' Mathlib-only)
#check ∑' i, (i : Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∏' Mathlib-only)
#check ∏' i, (i : Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ ∈ Mathlib-only)
#check ∑ i ∈ [1,2,3], i
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (⋃ Mathlib-only)
#check ⋃ i, ({i} : List Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (⋂ Mathlib-only)
#check ⋂ i, ({i} : List Nat)
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ is not an identifier char)
#check ∑
-- [TREE] expected skeleton: (Sigma (fun (Fin i)))
#check Σ i : Nat, Fin i
-- [TREE] expected skeleton: (loud gap — clean rejects; Lean parse skeleton)
#check Σ' i : Nat, Fin i
-- [TREE] expected skeleton: (Sigma (fun (Prod (Fin i) (Fin (HAdd.hAdd i 1)))))
#check Σ i : Nat, Fin i × Fin (i+1)
-- [TREE] expected skeleton: (Sigma (fun (Fin i)))
#check (i : Nat) × Fin i
-- [TREE] expected skeleton: (. (Sigma.mk 2 (: 1 (Fin 2))) fst)
#check (Sigma.mk 2 (1 : Fin 2)).fst
#eval (Sigma.mk 2 (1 : Fin 2)).fst    -- => 2
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i, f i + g i
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i, f i * 2
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i j, i * j
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i, i + 1
#eval ∑ i, i + 1    -- => 4
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i, i * 2
#eval ∑ i, i * 2    -- => 6

/- ── getelem: GetElem bracket indexing xs[i] / xs[i]! / xs[i]? / xs[i]'h ── -/
-- [TREE] expected skeleton: (getElem xs 1 _)
#check xs[1]
#eval xs[1]    -- => 20
-- [TREE] expected skeleton: (getElem! xs 1)
#check xs[1]!
#eval xs[1]!    -- => 20
-- [TREE] expected skeleton: (getElem? xs 1)
#check xs[1]?
#eval xs[1]?    -- => some 20
-- [TREE] expected skeleton: (getElem? xs 5)
#check xs[5]?
#eval xs[5]?    -- => none
-- [TREE] expected skeleton: (getElem arr 2 _)
#check arr[2]
#eval arr[2]    -- => 300
-- [TREE] expected skeleton: (getElem (getElem m 1 _) 0 _)
#check m[1][0]
#eval m[1][0]    -- => 3
-- [TREE] expected skeleton: (getElem! (getElem! m 1) 0)
#check m[1]![0]!
#eval m[1]![0]!    -- => 3
-- [TREE] expected skeleton: (HAdd.hAdd (getElem xs 0 _) (getElem xs 1 _))
#check xs[0] + xs[1]
#eval xs[0] + xs[1]    -- => 30
-- [TREE] expected skeleton: (Nat.succ (getElem xs 1 _))
#check Nat.succ xs[1]
#eval Nat.succ xs[1]    -- => 21
-- [TREE] expected skeleton: (getElem xs (HAdd.hAdd 1 1) _)
#check xs[1 + 1]
#eval xs[1 + 1]    -- => 30
-- [TREE] expected skeleton: (getElem xs 1 _)
#check xs[ 1 ]
#eval xs[ 1 ]    -- => 20
-- [TREE] expected skeleton: (getElem xs 1 #by)
#check xs[1]'(by decide)
#eval xs[1]'(by decide)    -- => 20
-- [TREE] expected skeleton: (fun (getElem l 1 h))
#check fun (l : List Nat) (h : 1 < l.length) => l[1]'h
-- [TREE] expected skeleton: ((getElem? xs 1).getD 0)
#check xs[1]?.getD 0
#eval xs[1]?.getD 0    -- => 20
-- [TREE] expected skeleton: (getElem! xs 1).succ
#check xs[1]!.succ
#eval xs[1]!.succ    -- => 21
-- [TREE] expected skeleton: (Option.getD (getElem? xs 1) 5)
#check Option.getD xs[1]? 5
#eval Option.getD xs[1]? 5    -- => 20
-- [TREE] expected skeleton: (xs (List.cons 1 List.nil))
#check xs [1]
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected end of input (`!` after ws is prefix Not)
#check xs[1] !
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected end of input (`?` after ws is hole prefix)
#check xs[1] ?
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token ]' (xs[i]'h is lead-prec, illegal as bare arg)
#check fun (l : List Nat) (h : 1 < l.length) => Nat.succ l[1]'h
-- [TREE] expected skeleton: (fun (Nat.succ (getElem l 1 h)))
#check fun (l : List Nat) (h : 1 < l.length) => Nat.succ (l[1]'h)
-- [TREE] expected skeleton: (getElem (List.cons 10 (List.cons 20 (List.cons 30 List.nil))) 1 _)
#check [10, 20, 30][1]
#eval [10, 20, 30][1]    -- => 20
-- [TREE] expected skeleton: (getElem xs.reverse 0 _)
#check xs.reverse[0]
#eval xs.reverse[0]    -- => 30
-- [TREE] expected skeleton: (getElem xs 1 #by)
#check xs[1]' (by decide)
#eval xs[1]' (by decide)    -- => 20
-- [TREE] expected skeleton: (loud gap — clean rejects; Lean parse skeleton)
#check xs[1] 'h'
-- [TREE] expected skeleton: (fun (getElem xs 1 h'))
#check fun (h' : 1 < xs.length) => xs[1]'h'
-- [TREE] expected skeleton: (fun (getElem l 1 (. h 1)))
#check fun (l : List Nat) (h : (1 < l.length) ∧ True) => l[1]'h.1
-- [TREE] expected skeleton: (Array.toSubarray arr 0 2)
#check arr[0:2]

/- ── monadic: Monadic/applicative operators <$> <*> <&> =<< >=> <=< <* *> ── -/
-- [TREE] expected skeleton: (Seq.seq (Seq.seq (Functor.map f a) b) c)
#check f <$> a <*> b <*> c
-- [TREE] expected skeleton: (Seq.seq (Seq.seq (Functor.map (fun (HAdd.hAdd (HAdd.hAdd x y) z)) (some 1)) (some 2)) (some 3))
#check (fun x y z => x + y + z) <$> some 1 <*> some 2 <*> some 3
#eval (fun x y z => x + y + z) <$> some 1 <*> some 2 <*> some 3    -- => some 6
-- [TREE] expected skeleton: (Functor.map f (Functor.map g a))
#check f <$> g <$> a
-- [TREE] expected skeleton: (Functor.map (fun (HAdd.hAdd · 1)) (Functor.map (fun (HMul.hMul · 2)) (some 3)))
#check (· + 1) <$> (· * 2) <$> some 3
#eval (· + 1) <$> (· * 2) <$> some 3    -- => some 7
-- [TREE] expected skeleton: (Functor.map (fun (HAdd.hAdd · 1)) (some 3))
#check (· + 1) <$> some 3
#eval (· + 1) <$> some 3    -- => some 4
-- [TREE] expected skeleton: (Functor.map (fun (HMul.hMul · 2)) (List.cons 1 (List.cons 2 (List.cons 3 List.nil))))
#check (· * 2) <$> [1, 2, 3]
#eval (· * 2) <$> [1, 2, 3]    -- => [2, 4, 6]
-- [TREE] expected skeleton: (Seq.seq (some (fun (HAdd.hAdd · 1))) (some 10))
#check some (· + 1) <*> some 10
#eval some (· + 1) <*> some 10    -- => some 11
-- [TREE] expected skeleton: (Seq.seq (Seq.seq (pure (fun (HAdd.hAdd · ·))) (some 3)) (some 4))
#check pure (· + ·) <*> some 3 <*> some 4
#eval pure (· + ·) <*> some 3 <*> some 4    -- => some 7
-- [TREE] expected skeleton: (Seq.seq (: none (Option (-> Nat Nat))) (some 10))
#check (none : Option (Nat → Nat)) <*> some 10
#eval (none : Option (Nat → Nat)) <*> some 10    -- => none
-- [TREE] expected skeleton: (Seq.seq (List.cons (fun (HAdd.hAdd · 1)) (List.cons (fun (HMul.hMul · 2)) List.nil)) (List.cons 10 (List.cons 20 List.nil)))
#check [(· + 1), (· * 2)] <*> [10, 20]
-- [TREE] expected skeleton: (Functor.mapRev (some 3) (fun (HAdd.hAdd · 1)))
#check some 3 <&> (· + 1)
#eval some 3 <&> (· + 1)    -- => some 4
-- [TREE] expected skeleton: (Functor.mapRev (some 3) (Functor.mapRev (fun (HAdd.hAdd · 1)) (fun (HMul.hMul · 2))))
#check some 3 <&> (· + 1) <&> (· * 2)
-- [TREE] expected skeleton: (Functor.mapRev a (Functor.mapRev f g))
#check a <&> f <&> g
-- [TREE] expected skeleton: (Functor.map f (Functor.mapRev a g))
#check f <$> a <&> g
-- [TREE] expected skeleton: (Bind.bindLeft f (Bind.bindLeft g a))
#check f =<< g =<< a
-- [TREE] expected skeleton: (Bind.bindLeft (fun (some (HAdd.hAdd x 1))) (Bind.bindLeft (fun (some (HMul.hMul x 2))) (some 3)))
#check (fun x => some (x + 1)) =<< (fun x => some (x * 2)) =<< some 3
#eval (fun x => some (x + 1)) =<< (fun x => some (x * 2)) =<< some 3    -- => some 7
-- [TREE] expected skeleton: (Bind.kleisliRight f (Bind.kleisliRight g h))
#check f >=> g >=> h
-- [TREE] expected skeleton: ((Bind.kleisliRight (fun (some (HAdd.hAdd x 1))) (Bind.kleisliRight (fun (some (HMul.hMul y 2))) (fun (some (HAdd.hAdd z 10))))) 3)
#check ((fun x => some (x + 1)) >=> (fun y => some (y * 2)) >=> fun z => some (z + 10)) 3
#eval ((fun x => some (x + 1)) >=> (fun y => some (y * 2)) >=> fun z => some (z + 10)) 3    -- => some 18
-- [TREE] expected skeleton: (Bind.kleisliLeft f (Bind.kleisliLeft g h))
#check f <=< g <=< h
-- [TREE] expected skeleton: (Bind.bindLeft g (Functor.map f a))
#check g =<< f <$> a
#eval g =<< f <$> a    -- => some 7
-- [TREE] expected skeleton: (Bind.bind (Functor.map (fun (HAdd.hAdd · 1)) (some 3)) (fun (some (HMul.hMul x 2))))
#check (· + 1) <$> some 3 >>= fun x => some (x * 2)
#eval (· + 1) <$> some 3 >>= fun x => some (x * 2)    -- => some 8
-- [TREE] expected skeleton: (Bind.bindLeft f (Bind.bind a g))
#check f =<< a >>= g
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected end of input (infixr:55 =<< cannot extend infixl:55 >>=)
#check a >>= f =<< b
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected end of input (>=> cannot extend >>=)
#check a >>= f >=> g
-- [TREE] expected skeleton: (Bind.bindLeft f (Bind.kleisliRight g h))
#check f =<< g >=> h
-- [TREE] expected skeleton: (SeqRight.seqRight (SeqLeft.seqLeft (Seq.seq a b) c) d)
#check a <*> b <* c *> d
-- [TREE] expected skeleton: (SeqRight.seqRight (SeqLeft.seqLeft (some 1) (some 2)) (some 3))
#check some 1 <* some 2 *> some 3
#eval some 1 <* some 2 *> some 3    -- => some 3
-- [TREE] expected skeleton: (HAndThen.hAndThen a (SeqRight.seqRight b c))
#check a >> b *> c
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected end of input (*> level 60 cannot be lhs of >>)
#check a *> b >> c
-- [TREE] expected skeleton: (HAdd.hAdd (Functor.map f a) b)
#check f <$> a + b
-- [TREE] expected skeleton: (HPow.hPow (Functor.map f a) b)
#check f <$> a ^ b
-- [TREE] expected skeleton: (Function.comp f (Functor.map g x))
#check f ∘ g <$> x
-- [TREE] expected skeleton: (Seq.seq (Functor.map (fun (HAdd.hAdd x y)) a) b)
#check (fun x y => x + y) <$> a <*> b
-- [TREE] expected skeleton: (Functor.map f a)
#check f<$>a
#eval f<$>a    -- => (·+1)<$>some 3 = some 4; some 3<&>(·+1) 

/- ── brace: Brace-form terms: subtype {x // p}, collections {a}, structInst, ⟨⟩ ── -/
-- [TREE] expected skeleton: (Subtype (fun (GT.gt x 3)))
#check { x // x > 3 }
-- [TREE] expected skeleton: (Subtype (fun (GT.gt x 3)))
#check { x : Nat // x > 3 }
-- [TREE] expected skeleton: (Subtype (fun (GT.gt x 3)))
#check { x : Nat // x > 3 }
-- [TREE] expected skeleton: (Subtype (fun (Eq (HMod.hMod n 2) 0)))
#check {n : Nat // n % 2 = 0}
-- [TREE] expected skeleton: (Subtype (fun (LT.lt (. x val) 5)))
#check { x : { y : Nat // y > 0 } // x.val < 5 }
-- [TREE] expected skeleton: (fun (HAdd.hAdd (. s val) 1))
#check fun (s : { n : Nat // n > 0 }) => s.val + 1
-- [TREE] expected skeleton: (: (anonymousCtor 5 #by) (Subtype (fun (GT.gt x 3))))
#check (⟨5, by decide⟩ : { x : Nat // x > 3 })
#eval (⟨5, by decide⟩ : { x : Nat // x > 3 })    -- => 5
-- [TREE] expected skeleton: (: (singleton 5) (List Nat))
#check ({5} : List Nat)
-- [TREE] expected skeleton: (: (singleton 5) (Std.HashSet Nat))
#check ({5} : Std.HashSet Nat)
#eval ({5} : Std.HashSet Nat)    -- => #eval ({5} : Std.HashSet Nat).toList = [
-- [TREE] expected skeleton: (: (insert 1 (insert 2 (singleton 3))) (Std.HashSet Nat))
#check ({1, 2, 3} : Std.HashSet Nat)
#eval ({1, 2, 3} : Std.HashSet Nat)    -- => #eval sorted toList = [1, 2, 3]
-- [TREE] expected skeleton: ((: (insert 1 (insert 2 (insert 2 (singleton 3)))) (Std.HashSet Nat)).toList.mergeSort (fun (LE.le · ·)))
#check ({1, 2, 2, 3} : Std.HashSet Nat).toList.mergeSort (· ≤ ·)
#eval ({1, 2, 2, 3} : Std.HashSet Nat).toList.mergeSort (· ≤ ·)    -- => [1, 2, 3]
-- [TREE] expected skeleton: (insert 1 (insert 2 (singleton 3)))
#check {1, 2, 3}
-- [TREE] expected skeleton: parse-ok in Lean; elab err (trailing comma → structInst abbrev)
#check ({1, 2,} : Std.HashSet Nat).toList
-- [TREE] expected skeleton: (: (structInst) (List Nat))
#check ({} : List Nat)
#eval ({} : List Nat)    -- => []
-- [TREE] expected skeleton: (: (structInst) P2)
#check ({} : P2)
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token '}'; expected '=>' (set-builder is Mathlib-only)
#check { x | x > 3 }
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token '|'; expected '}' (sep set-builder Mathlib-only)
#check { x ∈ s | x > 1 }
-- [TREE] expected skeleton: (: (structInst a:=1 b:=2) P)
#check ({ a := 1, b := 2 } : P)
#eval ({ a := 1, b := 2 } : P)    -- => { a := 1, b := 2 } (both forms)
-- [TREE] expected skeleton: (structInst with=p0 a:=5)
#check { p0 with a := 5 }
#eval { p0 with a := 5 }    -- => { a := 5, b := 2 }
-- [TREE] expected skeleton: (fun (structInst with=r n:=9))
#check fun (r : R) => { r with n := 9 }
-- [TREE] expected skeleton: (: (structInst a:=a) Q)
#check ({a} : Q)
#eval ({a} : Q)    -- => { a := 7 }
-- [TREE] expected skeleton: (: (structInst a:=a b:=9) P)
#check ({ a, b := 9 } : P)
#eval ({ a, b := 9 } : P)    -- => { a := 7, b := 9 }
-- [TREE] expected skeleton: (: (structInst a:=1 b:=2) P)
#check ({ a := 1, b := 2, .. } : P)
-- [TREE] expected skeleton: (: (anonymousCtor 1 2) P)
#check (⟨1, 2⟩ : P)
#eval (⟨1, 2⟩ : P)    -- => { a := 1, b := 2 }
-- [TREE] expected skeleton: (: (anonymousCtor 1 2 3) (Prod Nat (Prod Nat Nat)))
#check (⟨1, 2, 3⟩ : Nat × (Nat × Nat))
#eval (⟨1, 2, 3⟩ : Nat × (Nat × Nat))    -- => (1, 2, 3)
-- [TREE] expected skeleton: (: (anonymousCtor 1 2) (Prod Nat Nat))
#check (⟨1, 2,⟩ : Nat × Nat)
-- [TREE] expected skeleton: (: (anonymousCtor) Unit)
#check (⟨⟩ : Unit)
-- [TREE] expected skeleton: (: (structInst p:=(structInst a:=1 b:=2) n:=3) R)
#check ({ p := { a := 1, b := 2 }, n := 3 } : R)
#eval ({ p := { a := 1, b := 2 }, n := 3 } : R)    -- => { p := { a := 1, b := 2 }, n := 3 }

/- ── binder: Binder syntaxes: ⦃⦄ strict-implicit, [inst], Σ/Σ', ∃!, pattern-fun ── -/
-- [TREE] expected skeleton: (fun x)
#check fun ⦃x : Nat⦄ => x
-- [TREE] expected skeleton: (fun x)
#check fun {{x : Nat}} => x
-- [TREE] expected skeleton: (fun x)
#check fun { {x : Nat} } => x
-- [TREE] expected skeleton: (fun x)
#check fun ⦃x⦄ => x
-- [TREE] expected skeleton: (fun x)
#check fun ⦃x y : Nat⦄ => x
-- [TREE] expected skeleton: (fun (HAdd.hAdd (HAdd.hAdd x y) z))
#check fun ⦃x : Nat⦄ {y : Nat} (z : Nat) => x + y + z
-- [TREE] expected skeleton: (pi (pi Nat))
#check ⦃x : Nat⦄ → Fin x → Nat
-- [TREE] expected skeleton: (pi (Eq x x))
#check ∀ ⦃x : Nat⦄, x = x
-- [TREE] expected skeleton: ((fun x) (: rfl (Eq 3 3)))
#check (fun ⦃x : Nat⦄ (h : x = x) => x) (rfl : (3 : Nat) = 3)
#eval (fun ⦃x : Nat⦄ (h : x = x) => x) (rfl : (3 : Nat) = 3)    -- => 3
-- [TREE] expected skeleton: (fun (: (HAdd.hAdd 1 2) Nat))
#check fun [inst : Add Nat] => (1 + 2 : Nat)
-- [TREE] expected skeleton: (fun (: (HAdd.hAdd 1 2) Nat))
#check fun [Add Nat] => (1 + 2 : Nat)
-- [TREE] expected skeleton: (fun (HAdd.hAdd a a))
#check fun {α : Type} [inst : Add α] (a : α) => a + a
-- [TREE] expected skeleton: ((fun (HAdd.hAdd a a)) 5)
#check (fun [inst : Add Nat] (a : Nat) => a + a) 5
#eval (fun [inst : Add Nat] (a : Nat) => a + a) 5    -- => 10
-- [TREE] expected skeleton: (pi Nat)
#check [inst : Add Nat] → Nat
-- [TREE] expected skeleton: (Sigma (fun (Fin n)))
#check Σ n : Nat, Fin n
-- [TREE] expected skeleton: (Sigma (fun (Fin n)))
#check Σ n, Fin n
-- [TREE] expected skeleton: (PSigma (fun (GT.gt n 0)))
#check Σ' n : Nat, n > 0
-- [TREE] expected skeleton: (Sigma (fun (Sigma (fun (Fin (HAdd.hAdd a b))))))
#check Σ (a : Nat) (b : Nat), Fin (a + b)
-- [TREE] expected skeleton: (Sigma (fun (Sigma (fun (Fin (HAdd.hAdd a b))))))
#check Σ a b : Nat, Fin (a + b)
-- [TREE] expected skeleton: (Sigma (fun (Sigma (fun (Fin (HAdd.hAdd a b))))))
#check Σ (a b : Nat), Fin (a + b)
-- [TREE] expected skeleton: (Sigma (fun (Prod (Fin n) (Fin n))))
#check Σ n : Nat, Fin n × Fin n
-- [TREE] expected skeleton: (Sigma (fun (-> (Fin n) Nat)))
#check Σ n : Nat, Fin n → Nat
-- [TREE] expected skeleton: (-> Nat (Sigma (fun (Fin n))))
#check Nat → Σ n : Nat, Fin n
-- [TREE] expected skeleton: (Prod Nat (Sigma (fun (Fin n))))
#check Nat × Σ n : Nat, Fin n
-- [TREE] expected skeleton: (-> (Sigma (fun (Fin n))) Nat)
#check (Σ n : Nat, Fin n) → Nat
-- [TREE] expected skeleton: (Sigma (fun (Fin n)))
#check (n : Nat) × Fin n
-- [TREE] expected skeleton: (Sigma (fun (Sigma (fun (Fin (HAdd.hAdd a b))))))
#check (a : Nat) × (b : Nat) × Fin (a + b)
-- [TREE] expected skeleton: (PSigma (fun (GT.gt n 0)))
#check (n : Nat) ×' n > 0
-- [TREE] expected skeleton: (: (anonymousCtor 3 2) (Sigma (fun (Fin n))))
#check (⟨3, 2⟩ : Σ n : Nat, Fin n)
#eval (⟨3, 2⟩ : Σ n : Nat, Fin n)    -- => ⟨3, 2⟩
-- [TREE] expected skeleton: (. (: (anonymousCtor 3 2) (Sigma (fun (Fin n)))) 1)
#check (⟨3, 2⟩ : Σ n : Nat, Fin n).1
#eval (⟨3, 2⟩ : Σ n : Nat, Fin n).1    -- => 3
-- [TREE] expected skeleton: (. (: (anonymousCtor 3 2) (Sigma (fun (Fin n)))) 2)
#check (⟨3, 2⟩ : Σ n : Nat, Fin n).2
#eval (⟨3, 2⟩ : Σ n : Nat, Fin n).2    -- => 2
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token '!' (∃! is Mathlib-only)
#check ∃! x : Nat, x = 1
-- [TREE] expected skeleton: (Exists (fun (Eq x 1)))
#check ∃ x : Nat, x = 1
-- [TREE] expected skeleton: (: (pfun (match _x 1)) (-> (Prod Nat Nat) Nat))
#check (fun (a, b) => a + b : Nat × Nat → Nat)
-- [TREE] expected skeleton: (pfun (match _x 1))
#check fun (a, b) => a + b
-- [TREE] expected skeleton: ((: (pfun (match _x 1)) (-> (Prod Nat Nat) Nat)) (Prod.mk 2 3))
#check (fun (a, b) => a + b : Nat × Nat → Nat) (2, 3)
#eval (fun (a, b) => a + b : Nat × Nat → Nat) (2, 3)    -- => 5
-- [TREE] expected skeleton: ((: (pfun (match _x 1)) (-> (Prod Nat Nat) Nat)) (Prod.mk 2 3))
#check (fun ⟨a, b⟩ => a + b : Nat × Nat → Nat) (2, 3)
#eval (fun ⟨a, b⟩ => a + b : Nat × Nat → Nat) (2, 3)    -- => 5
-- [TREE] expected skeleton: ((: (pfun (match _x 1)) (-> (Prod Nat Nat) (-> Nat Nat))) (Prod.mk 1 2) 3)
#check (fun (a, b) c => a + b + c : Nat × Nat → Nat → Nat) (1, 2) 3
#eval (fun (a, b) c => a + b + c : Nat × Nat → Nat → Nat) (1, 2) 3    -- => 6
-- [TREE] expected skeleton: (: (fun (HAdd.hAdd x y)) (-> Nat (-> Nat Nat)))
#check (fun (x y) => x + y : Nat → Nat → Nat)
-- [TREE] expected skeleton: ((: (pfun (match _x 1)) (-> (Option Nat) Nat)) (some 5))
#check (fun (some x) => x : Option Nat → Nat) (some 5)

/- ── lowprec: Low-precedence sequencing/pipeline: $ <| |> |>. >> <;> ── -/
-- [TREE] expected skeleton: (f (g x))
#check f $ g $ x
-- [TREE] expected skeleton: (fun (f (g x)))
#check fun (f g : Nat → Nat) (x : Nat) => f $ g $ x
-- [TREE] expected skeleton: ((fun (HAdd.hAdd x 1)) (HMul.hMul 2 3))
#check (fun x => x + 1) $ 2 * 3
#eval (fun x => x + 1) $ 2 * 3    -- => 7
-- [TREE] expected skeleton: parse-ok in Lean as `f $x` (antiquot); elab err
#check f $x
-- [TREE] expected skeleton: (g (f a))
#check a |> f |> g
-- [TREE] expected skeleton: (fun (g (f x)))
#check fun (x : Nat) (f g : Nat → Nat) => x |> f |> g
-- [TREE] expected skeleton: (List.length (List.map (fun (HAdd.hAdd a 1)) (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))))
#check [1, 2, 3] |> List.map (fun a => a + 1) |> List.length
#eval [1, 2, 3] |> List.map (fun a => a + 1) |> List.length    -- => 3
-- [TREE] expected skeleton: (f (g x))
#check f <| g <| x
-- [TREE] expected skeleton: (List.length (List.map (fun (HAdd.hAdd a 1)) (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))))
#check List.length <| List.map (fun a => a + 1) <| [1, 2, 3]
#eval List.length <| List.map (fun a => a + 1) <| [1, 2, 3]    -- => 3
-- [TREE] expected skeleton: ((x.pipe f) $ y → (Nat.sub 10 4)-shape)
#check x |> f $ y
#eval x |> f $ y    -- => #eval 10 |> Nat.sub $ 4  ==> 6  (= Nat.s
-- [TREE] expected skeleton: (f (g x))
#check f $ x |> g
#eval f $ x |> g    -- => #eval (fun x => x * 2) $ 3 |> (fun x => 
-- [TREE] expected skeleton: (f x y)
#check x |> f <| y
#eval x |> f <| y    -- => #eval 10 |> Nat.sub <| 4  ==> 6
-- [TREE] expected skeleton: (HAndThen.hAndThen m (HAndThen.hAndThen n o))
#check m >> n >> o
-- [TREE] expected skeleton: (Bind.bind m (HAndThen.hAndThen k n))
#check m >>= k >> n
-- [TREE] expected skeleton: (Bind.bind (HAndThen.hAndThen m n) k)
#check m >> n >>= k
-- [TREE] expected skeleton: (HOrElse.hOrElse a (HAndThen.hAndThen b c))
#check a <|> b >> c
-- [TREE] expected skeleton: (a (HOrElse.hOrElse b c))
#check a <| b <|> c
-- [TREE] expected skeleton: parse-ok in Lean; elab err (no HAndThen Option instance)
#check (some 1 >> some 2 >> some 3 : Option Nat)
-- [TREE] expected skeleton: parse-ok in Lean; elab err (no HAndThen IO instance)
#check (IO.println "a" >> IO.println "b" : IO Unit)
-- [TREE] expected skeleton: (fun (HAndThen.hAndThen a (fun b)))
#check fun (a b : P) => a >> b
#eval fun (a b : P) => a >> b    -- => #eval (⟨1⟩ >> ⟨2⟩ >> ⟨3⟩ : P).v  ==> 6
-- [TREE] expected skeleton: (fun (HAndThen.hAndThen a (HAndThen.hAndThen b (fun c))))
#check fun (a b c : P) => a >> b >> c
-- [TREE] expected skeleton: (x.foo y)
#check x |>.foo y
#eval x |>.foo y    -- => #eval [1, 2, 3] |>.map (fun a => a + 1) 
-- [TREE] expected skeleton: x.succ
#check x |> .succ
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected end of input (|>. checkNoWsBefore forbids ws before field)
#check x |>. succ
-- [TREE] expected skeleton: 1.succ.succ
#check 1 |>.succ.succ
-- [ERROR (parse-reject)] expected skeleton: ERROR: tactic seq `<;>` is not a term operator
#check skip <;> trivial <;> rfl
-- [ERROR (parse-reject)] expected skeleton: ERROR: tactic-paren `( ; )` is not a term
#check (skip; skip <;> trivial)
-- [ERROR (parse-reject)] expected skeleton: ERROR: tactic seq `<;>` is not a term operator
#check constructor <;> [skip; rfl]
-- [TREE] expected skeleton: #by
#check by constructor <;> trivial
#eval by constructor <;> trivial    -- => success

/- ── rewrite: Rewrite/algebraic term operators: ▸ ∣ • ×ˢ ── -/
-- [TREE] expected skeleton: (Eq.rec h rfl)
#check h ▸ rfl
-- [TREE] expected skeleton: (Eq.rec a (Eq.rec b c))
#check a ▸ b ▸ c
-- [TREE] expected skeleton: (fun (Eq.rec h hp))
#check fun (a b : Nat) (p : Nat → Prop) (h : a = b) (hp : p a) => h ▸ hp
-- [TREE] expected skeleton: (HAdd.hAdd (Eq.rec a b) c)
#check a ▸ b + c
-- [TREE] expected skeleton: (HAdd.hAdd a (Eq.rec b c))
#check a + b ▸ c
-- [TREE] expected skeleton: (Eq.rec h₁ (Eq.rec h₂ rfl))
#check h₁ ▸ h₂ ▸ rfl
-- [TREE] expected skeleton: (Dvd.dvd a (HAdd.hAdd b c))
#check a ∣ b + c
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected end of input (infix:50 ∣ does not chain)
#check a ∣ b ∣ c
-- [TREE] expected skeleton: parse-ok in Lean (silent (fun..)∣c reassoc); elab err
#check fun (a b c : Nat) => a ∣ b ∣ c
-- [TREE] expected skeleton: (decide (Dvd.dvd (: 2 Nat) 4))
#check decide ((2 : Nat) ∣ 4)
#eval decide ((2 : Nat) ∣ 4)    -- => true / false
-- [TREE] expected skeleton: (HSMul.hSMul a (HSMul.hSMul b c))
#check a • b • c
-- [TREE] expected skeleton: ((HSMul.hSMul (: (anonymousCtor 1) W) (HSMul.hSMul (: (anonymousCtor 2) W) (: (anonymousCtor 3) W))).val)
#check ((⟨1⟩:W) • (⟨2⟩:W) • (⟨3⟩:W)).val
#eval ((⟨1⟩:W) • (⟨2⟩:W) • (⟨3⟩:W)).val    -- => 9
-- [TREE] expected skeleton: (HAdd.hAdd a (HSMul.hSMul b c))
#check a + b • c
-- [TREE] expected skeleton: (HSMul.hSMul (: 2 Nat) 3)
#check (2:Nat) • 3
#eval (2:Nat) • 3    -- => 6 / 8 / 18
-- [TREE] expected skeleton: (HSMul.hSMul a (Eq.rec b c))
#check a • b ▸ c
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (ˢ U+02E2 is not an identifier char in Lean)
#check aˢ
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (×ˢ is Mathlib-only; ˢ not a token)
#check (1, 2) ×ˢ 3
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (×ˢ is Mathlib-only)
#check (a, b) ×ˢ s
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (×ˢ is Mathlib-only)
#check a ×ˢ b ×ˢ c
#eval a ×ˢ b ×ˢ c    -- => [((1, 2), 3)]
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (×ˢ is Mathlib-only)
#check [1, 2] ×ˢ [10, 20]
#eval [1, 2] ×ˢ [10, 20]    -- => [(1, 10), (1, 20), (2, 10), (2, 20)] / [
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (×ˢ is Mathlib-only)
#check a ×ˢ b ^ c

/- ── freqsweep: Frequency-ranked corpus syntax-gap sweep (Brick-3 order) ── -/
-- [TREE] expected skeleton: #do
#check do let x ← pure 1; pure (x + (← pure 2))
#eval do let x ← pure 1; pure (x + (← pure 2))    -- => 3
-- [TREE] expected skeleton: (fun (getElem xs n h))
#check fun xs n h => xs[n]'h
#eval fun xs n h => xs[n]'h    -- => 20 / none / 1
-- [TREE] expected skeleton: (HAdd.hAdd helper 1)
#check helper + 1
#eval helper + 1    -- => 42
-- [TREE] expected skeleton: (Nat.succ (Nat.succ 3))
#check Nat.succ <| Nat.succ <| 3
#eval Nat.succ <| Nat.succ <| 3    -- => 5
-- [TREE] expected skeleton: #by
#check by constructor <;> trivial
-- [TREE] expected skeleton: (. (List.reverse (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))) head!)
#check [1, 2, 3] |> List.reverse |>.head!
#eval [1, 2, 3] |> List.reverse |>.head!    -- => 3
-- [TREE] expected skeleton: (fun (Eq.rec h2 (Eq.rec h1 p)))
#check fun {α} {P : α → Prop} (a b c : α) (h1 : a = b) (h2 : b = c) (p : P a) => (h2 ▸ h1 ▸ p : P c)
-- [TREE] expected skeleton: (Dvd.dvd 3 9)
#check (3 ∣ 9)
#eval (3 ∣ 9)    -- => true
-- [TREE] expected skeleton: (fun (Seq.seq (Functor.map f a) b))
#check fun (f : Nat → Nat → Nat) (a b : Option Nat) => f <$> a <*> b
-- [TREE] expected skeleton: (. (List.reverse (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))) head!)
#check [1, 2, 3] |> List.reverse |>.head!
#eval [1, 2, 3] |> List.reverse |>.head!    -- => 3
-- [TREE] expected skeleton: (fun (HAndThen.hAndThen a (HAndThen.hAndThen b c)))
#check fun (a b c : List Nat) => a >> b >> c
#eval fun (a b c : List Nat) => a >> b >> c    -- => [1, 2, 3]
-- [TREE] expected skeleton: (loud gap — clean rejects; Lean parse skeleton)
#check (none <|> some 4 <|> some 5 : Option Nat)
#eval (none <|> some 4 <|> some 5 : Option Nat)    -- => some 4
-- [TREE] expected skeleton: (loud gap — clean rejects; Lean parse skeleton)
#check {n : Nat // n > 0}
-- [TREE] expected skeleton: (: rfl (Eq 1 1))
#check show 1 = 1 from rfl
-- [TREE] expected skeleton: (loud gap — clean rejects; Lean parse skeleton)
#check Nat.succ $ Nat.succ $ 3
#eval Nat.succ $ Nat.succ $ 3    -- => 5
-- [TREE] expected skeleton: (fun (Bind.bind (Bind.bind a f) g))
#check fun (a : Option Nat) (f g : Nat → Option Nat) => a >>= f >>= g
-- [TREE] expected skeleton: (match n 2)
#check match h : n with | 0 => 0 | m + 1 => m
#eval match h : n with | 0 => 0 | m + 1 => m    -- => mh 5 = 4
-- [TREE] expected skeleton: (fun (HSMul.hSMul a b))
#check fun {α β γ : Type} [HSMul α β γ] (a : α) (b : β) => a • b
-- [TREE] expected skeleton: (SeqRight.seqRight (pure 1) (pure 2))
#check (pure 1 *> pure 2 : Option Nat)
#eval (pure 1 *> pure 2 : Option Nat)    -- => some 2 (for *>)
-- [TREE] expected skeleton: (@ sifun)
#check @sifun
-- [TREE] expected skeleton: (: #calc (LE.le 2 4))
#check (calc 2 ≤ 3 := Nat.le_succ 2; _ ≤ 4 := Nat.le_succ 3 : 2 ≤ 4)
-- [TREE] expected skeleton: (fun (Bind.bindLeft f x))
#check fun (f : Nat → Option Nat) (x : Option Nat) => f =<< x
-- [TREE] expected skeleton: (Bind.kleisliRight f g)
#check f >=> g
#eval f >=> g    -- => some 8
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token 'if'; expected '=>' (match guards are not Lean 4)
#check match n with | m if m > 2 => 1 | _ => 0
-- [ERROR (parse-reject)] expected skeleton: ERROR: unexpected token '}'; expected '=>' (set-builder Mathlib-only)
#check {n : Nat | n > 0}
-- [ERROR (parse-reject)] expected skeleton: ERROR: expected token (∑ Mathlib-only)
#check ∑ i ∈ Finset.range 3, i
-- [TREE] expected skeleton: (Sigma (fun (Fin n)))
#check Σ n : Nat, Fin n
