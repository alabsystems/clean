// Canonical source spellings for the fixed positive-division law catalog.
// Historical probes and the production installer share these exact literals.

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "nat_add_zero_left",
        "def nat_add_zero_left (a : Nat) : @Eq Nat (Nat.add Nat.zero a) a := \
                 @Nat.rec (fun (k : Nat) => @Eq Nat (Nat.add Nat.zero k) k) \
                 (@Eq.refl Nat Nat.zero) \
                 (fun (k : Nat) (ih : @Eq Nat (Nat.add Nat.zero k) k) => \
                 @Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) \
                 (Nat.add Nat.zero k) k ih) a",
    ),
    (
        "nat_add_succ_left",
        "def nat_add_succ_left (a : Nat) (b : Nat) : \
                 @Eq Nat (Nat.add (Nat.succ a) b) (Nat.succ (Nat.add a b)) := \
                 @Nat.rec (fun (k : Nat) => \
                 @Eq Nat (Nat.add (Nat.succ a) k) (Nat.succ (Nat.add a k))) \
                 (@Eq.refl Nat (Nat.succ a)) \
                 (fun (k : Nat) (ih : @Eq Nat (Nat.add (Nat.succ a) k) \
                 (Nat.succ (Nat.add a k))) => \
                 @Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) \
                 (Nat.add (Nat.succ a) k) (Nat.succ (Nat.add a k)) ih) b",
    ),
    (
        "nat_add_assoc_local",
        "def nat_add_assoc_local (a : Nat) (b : Nat) (c : Nat) : \
                 @Eq Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) := \
                 @Nat.rec (fun (k : Nat) => \
                 @Eq Nat (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k))) \
                 (@Eq.refl Nat (Nat.add a b)) \
                 (fun (k : Nat) (ih : @Eq Nat (Nat.add (Nat.add a b) k) \
                 (Nat.add a (Nat.add b k))) => \
                 @Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) \
                 (Nat.add (Nat.add a b) k) (Nat.add a (Nat.add b k)) ih) c",
    ),
    (
        "nat_add_comm_local",
        "def nat_add_comm_local (a : Nat) (b : Nat) : \
                 @Eq Nat (Nat.add a b) (Nat.add b a) := \
                 @Nat.rec (fun (k : Nat) => @Eq Nat (Nat.add a k) (Nat.add k a)) \
                 (@Eq.symm Nat (Nat.add Nat.zero a) a (nat_add_zero_left a)) \
                 (fun (k : Nat) (ih : @Eq Nat (Nat.add a k) (Nat.add k a)) => \
                 @Eq.trans Nat (Nat.succ (Nat.add a k)) (Nat.succ (Nat.add k a)) \
                 (Nat.add (Nat.succ k) a) \
                 (@Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) \
                 (Nat.add a k) (Nat.add k a) ih) \
                 (@Eq.symm Nat (Nat.add (Nat.succ k) a) (Nat.succ (Nat.add k a)) \
                 (nat_add_succ_left k a))) b",
    ),
    (
        "ir_nat_mul_succ_left",
        "def ir_nat_mul_succ_left (a : Nat) (b : Nat) : @Eq Nat (ir_nat_mul (Nat.succ a) b) (Nat.add b (ir_nat_mul a b)) := @Nat.rec (fun (k : Nat) => @Eq Nat (ir_nat_mul (Nat.succ a) k) (Nat.add k (ir_nat_mul a k))) (@Eq.refl Nat Nat.zero) (fun (k : Nat) (ih : @Eq Nat (ir_nat_mul (Nat.succ a) k) (Nat.add k (ir_nat_mul a k))) => @Eq.trans Nat (Nat.add (Nat.succ a) (ir_nat_mul (Nat.succ a) k)) (Nat.add (Nat.succ a) (Nat.add k (ir_nat_mul a k))) (Nat.add (Nat.succ k) (Nat.add a (ir_nat_mul a k))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add (Nat.succ a) z) (ir_nat_mul (Nat.succ a) k) (Nat.add k (ir_nat_mul a k)) ih) (@Eq.trans Nat (Nat.add (Nat.succ a) (Nat.add k (ir_nat_mul a k))) (Nat.succ (Nat.add a (Nat.add k (ir_nat_mul a k)))) (Nat.add (Nat.succ k) (Nat.add a (ir_nat_mul a k))) (nat_add_succ_left a (Nat.add k (ir_nat_mul a k))) (@Eq.trans Nat (Nat.succ (Nat.add a (Nat.add k (ir_nat_mul a k)))) (Nat.succ (Nat.add k (Nat.add a (ir_nat_mul a k)))) (Nat.add (Nat.succ k) (Nat.add a (ir_nat_mul a k))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) (Nat.add a (Nat.add k (ir_nat_mul a k))) (Nat.add k (Nat.add a (ir_nat_mul a k))) (@Eq.trans Nat (Nat.add a (Nat.add k (ir_nat_mul a k))) (Nat.add (Nat.add a k) (ir_nat_mul a k)) (Nat.add k (Nat.add a (ir_nat_mul a k))) (@Eq.symm Nat (Nat.add (Nat.add a k) (ir_nat_mul a k)) (Nat.add a (Nat.add k (ir_nat_mul a k))) (nat_add_assoc_local a k (ir_nat_mul a k))) (@Eq.trans Nat (Nat.add (Nat.add a k) (ir_nat_mul a k)) (Nat.add (Nat.add k a) (ir_nat_mul a k)) (Nat.add k (Nat.add a (ir_nat_mul a k))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add z (ir_nat_mul a k)) (Nat.add a k) (Nat.add k a) (nat_add_comm_local a k)) (nat_add_assoc_local k a (ir_nat_mul a k))))) (@Eq.symm Nat (Nat.add (Nat.succ k) (Nat.add a (ir_nat_mul a k))) (Nat.succ (Nat.add k (Nat.add a (ir_nat_mul a k)))) (nat_add_succ_left k (Nat.add a (ir_nat_mul a k))))))) b",
    ),
    (
        "nat_add_swap_first_two",
        "def nat_add_swap_first_two (a : Nat) (b : Nat) (c : Nat) : \
                 @Eq Nat (Nat.add a (Nat.add b c)) (Nat.add b (Nat.add a c)) := \
                 @Eq.trans Nat (Nat.add a (Nat.add b c)) (Nat.add (Nat.add a b) c) (Nat.add b (Nat.add a c)) (@Eq.symm Nat (Nat.add (Nat.add a b) c) (Nat.add a (Nat.add b c)) (nat_add_assoc_local a b c)) (@Eq.trans Nat (Nat.add (Nat.add a b) c) (Nat.add (Nat.add b a) c) (Nat.add b (Nat.add a c)) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add z c) (Nat.add a b) (Nat.add b a) (nat_add_comm_local a b)) (nat_add_assoc_local b a c))",
    ),
    (
        "ir_nat_mul_add_right",
        "def ir_nat_mul_add_right (a : Nat) (b : Nat) (c : Nat) : @Eq Nat (ir_nat_mul a (Nat.add b c)) (Nat.add (ir_nat_mul a b) (ir_nat_mul a c)) := @Nat.rec (fun (k : Nat) => @Eq Nat (ir_nat_mul a (Nat.add b k)) (Nat.add (ir_nat_mul a b) (ir_nat_mul a k))) (@Eq.refl Nat (ir_nat_mul a b)) (fun (k : Nat) (ih : @Eq Nat (ir_nat_mul a (Nat.add b k)) (Nat.add (ir_nat_mul a b) (ir_nat_mul a k))) => @Eq.trans Nat (Nat.add a (ir_nat_mul a (Nat.add b k))) (Nat.add a (Nat.add (ir_nat_mul a b) (ir_nat_mul a k))) (Nat.add (ir_nat_mul a b) (Nat.add a (ir_nat_mul a k))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add a z) (ir_nat_mul a (Nat.add b k)) (Nat.add (ir_nat_mul a b) (ir_nat_mul a k)) ih) (nat_add_swap_first_two a (ir_nat_mul a b) (ir_nat_mul a k))) c",
    ),
    (
        "ir_nat_dbl_is_add",
        "def ir_nat_dbl_is_add (n : Nat) : \
                 @Eq Nat (ir_nat_dbl n) (Nat.add n n) := \
                 @Nat.rec (fun (k : Nat) => @Eq Nat (ir_nat_dbl k) (Nat.add k k)) \
                 (@Eq.refl Nat Nat.zero) \
                 (fun (p : Nat) (_ih : @Eq Nat (ir_nat_dbl p) (Nat.add p p)) => \
                 @Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) \
                 (Nat.succ (Nat.add p p)) (Nat.add (Nat.succ p) p) \
                 (@Eq.symm Nat (Nat.add (Nat.succ p) p) (Nat.succ (Nat.add p p)) \
                 (nat_add_succ_left p p))) n",
    ),
    (
        "nat_add_exchange",
        "def nat_add_exchange (a : Nat) (b : Nat) (x : Nat) (y : Nat) : \
                 @Eq Nat (Nat.add (Nat.add a b) (Nat.add x y)) \
                 (Nat.add (Nat.add a x) (Nat.add b y)) := \
                 @Eq.trans Nat (Nat.add (Nat.add a b) (Nat.add x y)) (Nat.add a (Nat.add b (Nat.add x y))) (Nat.add (Nat.add a x) (Nat.add b y)) (nat_add_assoc_local a b (Nat.add x y)) (@Eq.trans Nat (Nat.add a (Nat.add b (Nat.add x y))) (Nat.add a (Nat.add (Nat.add b x) y)) (Nat.add (Nat.add a x) (Nat.add b y)) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add a z) (Nat.add b (Nat.add x y)) (Nat.add (Nat.add b x) y) (@Eq.symm Nat (Nat.add (Nat.add b x) y) (Nat.add b (Nat.add x y)) (nat_add_assoc_local b x y))) (@Eq.trans Nat (Nat.add a (Nat.add (Nat.add b x) y)) (Nat.add a (Nat.add (Nat.add x b) y)) (Nat.add (Nat.add a x) (Nat.add b y)) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add a (Nat.add z y)) (Nat.add b x) (Nat.add x b) (nat_add_comm_local b x)) (@Eq.trans Nat (Nat.add a (Nat.add (Nat.add x b) y)) (Nat.add a (Nat.add x (Nat.add b y))) (Nat.add (Nat.add a x) (Nat.add b y)) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add a z) (Nat.add (Nat.add x b) y) (Nat.add x (Nat.add b y)) (nat_add_assoc_local x b y)) (@Eq.symm Nat (Nat.add (Nat.add a x) (Nat.add b y)) (Nat.add a (Nat.add x (Nat.add b y))) (nat_add_assoc_local a x (Nat.add b y))))))",
    ),
    (
        "ir_nat_mul_add_left",
        "def ir_nat_mul_add_left (a : Nat) (b : Nat) (c : Nat) : @Eq Nat (ir_nat_mul (Nat.add a b) c) (Nat.add (ir_nat_mul a c) (ir_nat_mul b c)) := @Nat.rec (fun (k : Nat) => @Eq Nat (ir_nat_mul (Nat.add a b) k) (Nat.add (ir_nat_mul a k) (ir_nat_mul b k))) (@Eq.refl Nat Nat.zero) (fun (k : Nat) (ih : @Eq Nat (ir_nat_mul (Nat.add a b) k) (Nat.add (ir_nat_mul a k) (ir_nat_mul b k))) => @Eq.trans Nat (Nat.add (Nat.add a b) (ir_nat_mul (Nat.add a b) k)) (Nat.add (Nat.add a b) (Nat.add (ir_nat_mul a k) (ir_nat_mul b k))) (Nat.add (Nat.add a (ir_nat_mul a k)) (Nat.add b (ir_nat_mul b k))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add (Nat.add a b) z) (ir_nat_mul (Nat.add a b) k) (Nat.add (ir_nat_mul a k) (ir_nat_mul b k)) ih) (nat_add_exchange a b (ir_nat_mul a k) (ir_nat_mul b k))) c",
    ),
    (
        "ir_nat_mul_dbl_shift",
        "def ir_nat_mul_dbl_shift (q : Nat) (w : Nat) : @Eq Nat (ir_nat_mul q (ir_nat_dbl w)) (ir_nat_mul (ir_nat_dbl q) w) := @Eq.trans Nat (ir_nat_mul q (ir_nat_dbl w)) (Nat.add (ir_nat_mul q w) (ir_nat_mul q w)) (ir_nat_mul (ir_nat_dbl q) w) (@Eq.trans Nat (ir_nat_mul q (ir_nat_dbl w)) (ir_nat_mul q (Nat.add w w)) (Nat.add (ir_nat_mul q w) (ir_nat_mul q w)) (@Eq.cong Nat Nat (fun (z : Nat) => ir_nat_mul q z) (ir_nat_dbl w) (Nat.add w w) (ir_nat_dbl_is_add w)) (ir_nat_mul_add_right q w w)) (@Eq.symm Nat (ir_nat_mul (ir_nat_dbl q) w) (Nat.add (ir_nat_mul q w) (ir_nat_mul q w)) (@Eq.trans Nat (ir_nat_mul (ir_nat_dbl q) w) (ir_nat_mul (Nat.add q q) w) (Nat.add (ir_nat_mul q w) (ir_nat_mul q w)) (@Eq.cong Nat Nat (fun (z : Nat) => ir_nat_mul z w) (ir_nat_dbl q) (Nat.add q q) (ir_nat_dbl_is_add q)) (ir_nat_mul_add_left q q w)))",
    ),
    (
        "ir_nat_ltb_walk_zero_right",
        "def ir_nat_ltb_walk_zero_right (r : Nat) : @Eq Bool (ir_nat_ltb_walk r Nat.zero) Bool.false := @Nat.rec (fun (k : Nat) => @Eq Bool (ir_nat_ltb_walk k Nat.zero) Bool.false) (@Eq.refl Bool Bool.false) (fun (p : Nat) (_ih : @Eq Bool (ir_nat_ltb_walk p Nat.zero) Bool.false) => @Eq.refl Bool Bool.false) r",
    ),
    (
        "ir_nat_ltb_walk_add_cancel_right",
        "def ir_nat_ltb_walk_add_cancel_right (d : Nat) (e : Nat) (k : Nat) : @Eq Bool (ir_nat_ltb_walk (Nat.add d k) (Nat.add e k)) (ir_nat_ltb_walk d e) := @Nat.rec (fun (m : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.add d m) (Nat.add e m)) (ir_nat_ltb_walk d e)) (@Eq.refl Bool (ir_nat_ltb_walk d e)) (fun (m : Nat) (ih : @Eq Bool (ir_nat_ltb_walk (Nat.add d m) (Nat.add e m)) (ir_nat_ltb_walk d e)) => ih) k",
    ),
    (
        "ir_nat_sub_add_cancel_walk",
        "def ir_nat_sub_add_cancel_walk (w : Nat) : forall (r : Nat), @Eq Bool (ir_nat_ltb_walk r w) Bool.false -> @Eq Nat (Nat.add (Nat.sub r w) w) r := @Nat.rec (fun (m : Nat) => forall (r : Nat), @Eq Bool (ir_nat_ltb_walk r m) Bool.false -> @Eq Nat (Nat.add (Nat.sub r m) m) r) (fun (r : Nat) (_h : @Eq Bool (ir_nat_ltb_walk r Nat.zero) Bool.false) => @Eq.refl Nat r) (fun (wp : Nat) (ih : forall (r : Nat), @Eq Bool (ir_nat_ltb_walk r wp) Bool.false -> @Eq Nat (Nat.add (Nat.sub r wp) wp) r) => fun (r : Nat) => @Nat.rec (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk z (Nat.succ wp)) Bool.false -> @Eq Nat (Nat.add (Nat.sub z (Nat.succ wp)) (Nat.succ wp)) z) (fun (h : @Eq Bool (ir_nat_ltb_walk Nat.zero (Nat.succ wp)) Bool.false) => ir_bool_false_ne_true (@Eq Nat (Nat.add (Nat.sub Nat.zero (Nat.succ wp)) (Nat.succ wp)) Nat.zero) (@Eq.symm Bool Bool.true Bool.false h)) (fun (rp : Nat) (_inner : @Eq Bool (ir_nat_ltb_walk rp (Nat.succ wp)) Bool.false -> @Eq Nat (Nat.add (Nat.sub rp (Nat.succ wp)) (Nat.succ wp)) rp) => fun (h : @Eq Bool (ir_nat_ltb_walk (Nat.succ rp) (Nat.succ wp)) Bool.false) => @Eq.cong Nat Nat (fun (z : Nat) => Nat.succ z) (Nat.add (Nat.sub (Nat.succ rp) (Nat.succ wp)) wp) rp (@Eq.trans Nat (Nat.add (Nat.sub (Nat.succ rp) (Nat.succ wp)) wp) (Nat.add (Nat.sub rp wp) wp) rp (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add z wp) (Nat.sub (Nat.succ rp) (Nat.succ wp)) (Nat.sub rp wp) (ir_nat_sub_succ_succ rp wp)) (ih rp h))) r) w",
    ),
    (
        "ir_nat_sub_bound_walk",
        "def ir_nat_sub_bound_walk (w : Nat) (r : Nat) (hlt : @Eq Bool (ir_nat_ltb_walk r (Nat.add w w)) Bool.true) (hge : @Eq Bool (ir_nat_ltb_walk r w) Bool.false) : @Eq Bool (ir_nat_ltb_walk (Nat.sub r w) w) Bool.true := @Eq.trans Bool (ir_nat_ltb_walk (Nat.sub r w) w) (ir_nat_ltb_walk r (Nat.add w w)) Bool.true (@Eq.trans Bool (ir_nat_ltb_walk (Nat.sub r w) w) (ir_nat_ltb_walk (Nat.add (Nat.sub r w) w) (Nat.add w w)) (ir_nat_ltb_walk r (Nat.add w w)) (@Eq.symm Bool (ir_nat_ltb_walk (Nat.add (Nat.sub r w) w) (Nat.add w w)) (ir_nat_ltb_walk (Nat.sub r w) w) (ir_nat_ltb_walk_add_cancel_right (Nat.sub r w) w w)) (@Eq.cong Nat Bool (fun (z : Nat) => ir_nat_ltb_walk z (Nat.add w w)) (Nat.add (Nat.sub r w) w) r (ir_nat_sub_add_cancel_walk w r hge))) hlt",
    ),
    (
        "ir_dm_step2_gen",
        "def ir_dm_step2_gen (inc : Nat) (w : Nat) (r : Nat) (q : Nat) (b : Bool) : IRDivMod := @Bool.rec (fun (_ : Bool) => IRDivMod) (IRDivMod.mk (Nat.sub r w) (Nat.add (ir_nat_dbl q) inc)) (IRDivMod.mk r (ir_nat_dbl q)) b",
    ),
    (
        "ir_dm_step_eq",
        "def ir_dm_step_eq (w : Nat) (r : Nat) (q : Nat) : @Eq Nat (Nat.add (ir_nat_mul (ir_dm_quot (ir_dm_step2 (Nat.succ Nat.zero) w r q)) w) (ir_dm_rem (ir_dm_step2 (Nat.succ Nat.zero) w r q))) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r) := @Bool.rec (fun (b : Bool) => @Eq Bool (ir_nat_ltb r w) b -> @Eq Nat (Nat.add (ir_nat_mul (ir_dm_quot (ir_dm_step2_gen (Nat.succ Nat.zero) w r q b)) w) (ir_dm_rem (ir_dm_step2_gen (Nat.succ Nat.zero) w r q b))) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r)) (fun (h : @Eq Bool (ir_nat_ltb r w) Bool.false) => @Eq.trans Nat (Nat.add (ir_nat_mul (Nat.succ (ir_nat_dbl q)) w) (Nat.sub r w)) (Nat.add (Nat.add w (ir_nat_mul (ir_nat_dbl q) w)) (Nat.sub r w)) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add z (Nat.sub r w)) (ir_nat_mul (Nat.succ (ir_nat_dbl q)) w) (Nat.add w (ir_nat_mul (ir_nat_dbl q) w)) (ir_nat_mul_succ_left (ir_nat_dbl q) w)) (@Eq.trans Nat (Nat.add (Nat.add w (ir_nat_mul (ir_nat_dbl q) w)) (Nat.sub r w)) (Nat.add w (Nat.add (ir_nat_mul (ir_nat_dbl q) w) (Nat.sub r w))) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r) (nat_add_assoc_local w (ir_nat_mul (ir_nat_dbl q) w) (Nat.sub r w)) (@Eq.trans Nat (Nat.add w (Nat.add (ir_nat_mul (ir_nat_dbl q) w) (Nat.sub r w))) (Nat.add (ir_nat_mul (ir_nat_dbl q) w) (Nat.add w (Nat.sub r w))) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r) (nat_add_swap_first_two w (ir_nat_mul (ir_nat_dbl q) w) (Nat.sub r w)) (@Eq.trans Nat (Nat.add (ir_nat_mul (ir_nat_dbl q) w) (Nat.add w (Nat.sub r w))) (Nat.add (ir_nat_mul (ir_nat_dbl q) w) r) (Nat.add (ir_nat_mul q (ir_nat_dbl w)) r) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add (ir_nat_mul (ir_nat_dbl q) w) z) (Nat.add w (Nat.sub r w)) r (@Eq.trans Nat (Nat.add w (Nat.sub r w)) (Nat.add (Nat.sub r w) w) r (nat_add_comm_local w (Nat.sub r w)) (ir_nat_sub_add_cancel_walk w r (@Eq.trans Bool (ir_nat_ltb_walk r w) (ir_nat_ltb r w) Bool.false (@Eq.symm Bool (ir_nat_ltb r w) (ir_nat_ltb_walk r w) (ir_nat_ltb_walk_eq r w)) h)))) (@Eq.cong Nat Nat (fun (z : Nat) => Nat.add z r) (ir_nat_mul (ir_nat_dbl q) w) (ir_nat_mul q (ir_nat_dbl w)) (@Eq.symm Nat (ir_nat_mul q (ir_nat_dbl w)) (ir_nat_mul (ir_nat_dbl q) w) (ir_nat_mul_dbl_shift q w))))))) (fun (h : @Eq Bool (ir_nat_ltb r w) Bool.true) => @Eq.cong Nat Nat (fun (z : Nat) => Nat.add z r) (ir_nat_mul (ir_nat_dbl q) w) (ir_nat_mul q (ir_nat_dbl w)) (@Eq.symm Nat (ir_nat_mul q (ir_nat_dbl w)) (ir_nat_mul (ir_nat_dbl q) w) (ir_nat_mul_dbl_shift q w))) (ir_nat_ltb r w) (@Eq.refl Bool (ir_nat_ltb r w))",
    ),
    (
        "ir_dm_step_bound",
        "def ir_dm_step_bound (w : Nat) (r : Nat) (q : Nat) (hr : @Eq Bool (ir_nat_ltb_walk r (ir_nat_dbl w)) Bool.true) : @Eq Bool (ir_nat_ltb_walk (ir_dm_rem (ir_dm_step2 (Nat.succ Nat.zero) w r q)) w) Bool.true := @Bool.rec (fun (b : Bool) => @Eq Bool (ir_nat_ltb r w) b -> @Eq Bool (ir_nat_ltb_walk (ir_dm_rem (ir_dm_step2_gen (Nat.succ Nat.zero) w r q b)) w) Bool.true) (fun (h : @Eq Bool (ir_nat_ltb r w) Bool.false) => ir_nat_sub_bound_walk w r (@Eq.trans Bool (ir_nat_ltb_walk r (Nat.add w w)) (ir_nat_ltb_walk r (ir_nat_dbl w)) Bool.true (@Eq.cong Nat Bool (fun (z : Nat) => ir_nat_ltb_walk r z) (Nat.add w w) (ir_nat_dbl w) (@Eq.symm Nat (ir_nat_dbl w) (Nat.add w w) (ir_nat_dbl_is_add w))) hr) (@Eq.trans Bool (ir_nat_ltb_walk r w) (ir_nat_ltb r w) Bool.false (@Eq.symm Bool (ir_nat_ltb r w) (ir_nat_ltb_walk r w) (ir_nat_ltb_walk_eq r w)) h)) (fun (h : @Eq Bool (ir_nat_ltb r w) Bool.true) => (@Eq.trans Bool (ir_nat_ltb_walk r w) (ir_nat_ltb r w) Bool.true (@Eq.symm Bool (ir_nat_ltb r w) (ir_nat_ltb_walk r w) (ir_nat_ltb_walk_eq r w)) h)) (ir_nat_ltb r w) (@Eq.refl Bool (ir_nat_ltb r w))",
    ),
];
