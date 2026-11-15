// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive site-catalog uniqueness from a checked increasing rank.
//! The conclusion is the original pairwise uniqueness predicate. A rank is
//! only useful when equal original keys imply equal ranks; no runtime guard
//! or original site field is replaced by the certificate.

use crate::spec::{SpecError, Specification};

impl Specification {
    pub(super) fn add_eval_ir_byte_site_order_v1(&mut self) -> Result<(), SpecError> {
        for source in [RANK, KEY_RANK, CHAIN, KEY_NE, OR_FALSE, CONTAINS, UNIQUE] {
            self.add_recursive_def(source, "Increasing ranks prove the original complete site-key uniqueness guard; all rank compatibility and chain premises remain checked.")?;
        }
        Ok(())
    }
}

const RANK: &str = r"def ir_byte_site_rank_v1 (functionStride blockStride : Nat) (site : IRByteSiteV1) : Nat :=
Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 site) functionStride)
  (Nat.add (Nat.mul (ir_byte_site_block_v1 site) blockStride) (ir_byte_site_pc_v1 site)))";

const KEY_RANK: &str = r"def ir_byte_site_key_rank_v1 (functionStride blockStride : Nat) (a b : IRByteSiteV1)
  (same : @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.true) :
@Eq Nat (ir_byte_site_rank_v1 functionStride blockStride a) (ir_byte_site_rank_v1 functionStride blockStride b) :=
let first := ir_byte_world_and_left_v1
  (ir_nat_eqb (ir_byte_site_fid_v1 a) (ir_byte_site_fid_v1 b))
  (Bool.and (ir_nat_eqb (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b))
    (ir_nat_eqb (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b))) same
let rest := ir_byte_world_and_right_v1
  (ir_nat_eqb (ir_byte_site_fid_v1 a) (ir_byte_site_fid_v1 b))
  (Bool.and (ir_nat_eqb (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b))
    (ir_nat_eqb (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b))) same
let second := ir_byte_world_and_left_v1
  (ir_nat_eqb (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b))
  (ir_nat_eqb (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b)) rest
let third := ir_byte_world_and_right_v1
  (ir_nat_eqb (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b))
  (ir_nat_eqb (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b)) rest
@Eq.trans Nat (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 a) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 a) blockStride) (ir_byte_site_pc_v1 a)))) (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 a) blockStride) (ir_byte_site_pc_v1 a)))) (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 b) blockStride) (ir_byte_site_pc_v1 b))))
  (ir_eq_cong Nat Nat (fun f => Nat.succ (Nat.add (Nat.mul f functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 a) blockStride) (ir_byte_site_pc_v1 a)))) (ir_byte_site_fid_v1 a) (ir_byte_site_fid_v1 b) (ir_byte_nat_eqb_sound_v1 (ir_byte_site_fid_v1 a) (ir_byte_site_fid_v1 b) first))
  (@Eq.trans Nat (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 a) blockStride) (ir_byte_site_pc_v1 a)))) (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 b) blockStride) (ir_byte_site_pc_v1 a)))) (Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 b) blockStride) (ir_byte_site_pc_v1 b))))
    (ir_eq_cong Nat Nat (fun block => Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul block blockStride) (ir_byte_site_pc_v1 a)))) (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b) (ir_byte_nat_eqb_sound_v1 (ir_byte_site_block_v1 a) (ir_byte_site_block_v1 b) second))
    (ir_eq_cong Nat Nat (fun pc => Nat.succ (Nat.add (Nat.mul (ir_byte_site_fid_v1 b) functionStride) (Nat.add (Nat.mul (ir_byte_site_block_v1 b) blockStride) pc))) (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b) (ir_byte_nat_eqb_sound_v1 (ir_byte_site_pc_v1 a) (ir_byte_site_pc_v1 b) third)))";

const CHAIN: &str = r"def ir_byte_site_rank_chain_v1 (rank : IRByteSiteV1 -> Nat) (sites : IRList IRByteSiteV1) (lower : Nat) : Prop :=
@IRList.rec IRByteSiteV1 (fun _ => Nat -> Prop) (fun _ => True)
  (fun site rest ih bound => And (Nat.lt bound (rank site)) (ih (rank site))) sites lower";

const KEY_NE: &str = r"def ir_byte_site_rank_key_ne_v1 (rank : IRByteSiteV1 -> Nat)
  (compatible : forall (a b : IRByteSiteV1), @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.true -> @Eq Nat (rank a) (rank b))
  (a b : IRByteSiteV1) (less : Nat.lt (rank b) (rank a)) : @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.false :=
@Bool.rec (fun flag => @Eq Bool (ir_byte_site_key_eq_v1 a b) flag -> @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.false)
  (fun same => same)
  (fun same => @False.elim (@Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.false)
    (Nat.lt_irrefl (rank b) (@Eq.subst Nat (fun right => Nat.lt (rank b) right)
      (rank a) (rank b) (compatible a b same) less)))
  (ir_byte_site_key_eq_v1 a b) (@Eq.refl Bool (ir_byte_site_key_eq_v1 a b))";

const OR_FALSE: &str = r"def ir_byte_site_or_false_v1 (a b : Bool)
  (first : @Eq Bool a Bool.false) (second : @Eq Bool b Bool.false) : @Eq Bool (Bool.or a b) Bool.false :=
@Eq.trans Bool (Bool.or a b) (Bool.or Bool.false b) Bool.false
  (ir_eq_cong Bool Bool (fun flag => Bool.or flag b) a Bool.false first)
  (@Eq.trans Bool (Bool.or Bool.false b) (Bool.or Bool.false Bool.false) Bool.false
    (ir_eq_cong Bool Bool (fun flag => Bool.or Bool.false flag) b Bool.false second)
    (@Eq.refl Bool Bool.false))";

const CONTAINS: &str = r"def ir_byte_sites_rank_contain_false_v1 (rank : IRByteSiteV1 -> Nat)
  (compatible : forall (a b : IRByteSiteV1), @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.true -> @Eq Nat (rank a) (rank b))
  (sites : IRList IRByteSiteV1) : forall (lower : Nat) (key : IRByteSiteV1),
    Nat.le (rank key) lower -> ir_byte_site_rank_chain_v1 rank sites lower ->
    @Eq Bool (ir_byte_sites_contain_v1 sites key) Bool.false :=
@IRList.rec IRByteSiteV1
  (fun items => forall (lower : Nat) (key : IRByteSiteV1), Nat.le (rank key) lower ->
    ir_byte_site_rank_chain_v1 rank items lower -> @Eq Bool (ir_byte_sites_contain_v1 items key) Bool.false)
  (fun lower key bounded chain => @Eq.refl Bool Bool.false)
  (fun site rest ih lower key bounded chain =>
    let first := @And.left (Nat.lt lower (rank site)) (ir_byte_site_rank_chain_v1 rank rest (rank site)) chain
    let tail := @And.right (Nat.lt lower (rank site)) (ir_byte_site_rank_chain_v1 rank rest (rank site)) chain
    let less := @Nat.lt_of_le_of_lt (rank key) lower (rank site) bounded first
    ir_byte_site_or_false_v1 (ir_byte_site_key_eq_v1 site key) (ir_byte_sites_contain_v1 rest key)
      (ir_byte_site_rank_key_ne_v1 rank compatible site key less)
      (ih (rank site) key (@Nat.le_of_lt (rank key) (rank site) less) tail)) sites";

const UNIQUE: &str = r"def ir_byte_sites_unique_rank_chain_v1 (rank : IRByteSiteV1 -> Nat)
  (compatible : forall (a b : IRByteSiteV1), @Eq Bool (ir_byte_site_key_eq_v1 a b) Bool.true -> @Eq Nat (rank a) (rank b))
  (sites : IRList IRByteSiteV1) : forall (lower : Nat), ir_byte_site_rank_chain_v1 rank sites lower ->
    @Eq Bool (ir_byte_sites_unique_v1 sites) Bool.true :=
@IRList.rec IRByteSiteV1
  (fun items => forall (lower : Nat), ir_byte_site_rank_chain_v1 rank items lower ->
    @Eq Bool (ir_byte_sites_unique_v1 items) Bool.true)
  (fun lower chain => @Eq.refl Bool Bool.true)
  (fun site rest ih lower chain =>
    let tail := @And.right (Nat.lt lower (rank site)) (ir_byte_site_rank_chain_v1 rank rest (rank site)) chain
    let absent := ir_byte_sites_rank_contain_false_v1 rank compatible rest (rank site) site (Nat.le_refl (rank site)) tail
    ir_byte_world_and_intro_v1 (Bool.not (ir_byte_sites_contain_v1 rest site)) (ir_byte_sites_unique_v1 rest)
      (ir_eq_cong Bool Bool Bool.not (ir_byte_sites_contain_v1 rest site) Bool.false absent)
      (ih (rank site) tail)) sites";

#[cfg(test)]
mod tests {
    use clean_kernel::Name;

    fn site(pc: u64) -> String {
        format!("(IRByteSiteV1.mkt 0 0 {pc} 0 0 (@IRList.nil IRTy) (@IRList.nil IRByteOperandV1))")
    }
    fn list(pcs: &[u64]) -> String {
        pcs.iter()
            .rev()
            .fold("(@IRList.nil IRByteSiteV1)".into(), |tail, pc| {
                format!("(@IRList.cons IRByteSiteV1 {} {tail})", site(*pc))
            })
    }
    const RANK: &str = "(ir_byte_site_rank_v1 16 4)";
    const COMPATIBLE: &str = "(ir_byte_site_key_rank_v1 16 4)";

    fn chain() -> String {
        let pcs = [0, 1, 2];
        let mut proof = "True.intro".to_owned();
        for index in (0..pcs.len()).rev() {
            let lower = index;
            let upper = index + 1;
            let tail = list(&pcs[index + 1..]);
            proof = format!("(@And.intro (Nat.lt {lower} {upper}) (ir_byte_site_rank_chain_v1 {RANK} {tail} {upper}) (Nat.le_refl {upper}) {proof})");
        }
        proof
    }
    #[test]
    fn site_rank_chain_proves_original_uniqueness_and_refuses_wrong_order_or_duplicate() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
            for name in [
                "ir_byte_site_key_rank_v1",
                "ir_byte_site_rank_key_ne_v1",
                "ir_byte_sites_rank_contain_false_v1",
                "ir_byte_sites_unique_rank_chain_v1",
            ] {
                spec.verify_definition(name).unwrap();
                let name = Name::from_string(name);
                assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
                assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
            }
            let theorem = |name: &str, pcs: &[u64]| {
                let sites = list(pcs);
                format!("def {name} : @Eq Bool (ir_byte_sites_unique_v1 {sites}) Bool.true := ir_byte_sites_unique_rank_chain_v1 {RANK} {COMPATIBLE} {sites} 0 {}", chain())
            };
            spec.add_recursive_def(
                &theorem("ranked_sites_original", &[0, 1, 2]),
                "Original uniqueness from checked ranks",
            )
            .unwrap();
            spec.verify_definition("ranked_sites_original").unwrap();
            for (name, pcs) in [
                ("ranked_sites_adjacent_duplicate", [0, 0, 1]),
                ("ranked_sites_nonadjacent_duplicate", [0, 1, 0]),
                ("ranked_sites_unsorted", [1, 0, 2]),
            ] {
                let error = spec
                    .add_recursive_def(
                        &theorem(name, &pcs),
                        "Unchanged rank certificate on wrong original site keys",
                    )
                    .expect_err("wrong order/duplicate must not acquire the old uniqueness proof");
                crate::test_utils::assert_type_mismatch_rejection(&error, name);
                assert!(spec.get_definition(name).is_none());
            }
        });
    }
}
