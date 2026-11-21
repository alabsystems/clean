/- EqsatPacked: a rule with two 8-bit variables checked on 256 assignments at
   a time, and what a `true` proves (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `exhaust8p r T` is a second decision procedure for `EqsatRule.Sound r T`,
   beside `EqsatExhaust.exhaust8`, and `exhaust8p_sound : exhaust8p r T = true
   → Sound r T` is its one theorem. The proof of a rule a search found is

       EqsatDecide.exhaust8p_sound <rule literal> <type> EqsatDecide.rflTrue

   which the kernel accepts only by evaluating the procedure on the literal.
   Nothing here is trusted and nothing here is part of what a rule means:
   `EqsatRule.Sound` does not reach this module, and a wrong `exhaust8p` has
   no `exhaust8p_sound`.

   Why a second procedure. `exhaust8` tests one assignment per kernel
   evaluation of both sides, so a rule with two 8-bit variables costs 65,536
   of them and over a million heartbeats, and `exhaust8` answers `false` on
   it. Here the 256 values of one variable are evaluated at once: a lane
   vector is one natural number of 256 sixteen-bit lanes, lane `i` holding
   the residue of the pattern where that variable is `i`. `add` and `sub` of
   two residues below 256 stay below 512, so they never carry into the next
   lane, and one `Nat.land` with 255 in every lane reduces every lane modulo
   256; `and or xor` act on each lane by themselves; two sides are equal on
   all 256 assignments exactly when their two vectors are one number
   (`Packed.pack_inj`). The kernel does each of these as one operation on a
   4,096-bit literal, so a rule with two variables is 256 comparisons.

   What `exhaust8p r T` answers `true` on. All six must hold:
   * `T` is `i8` or `u8`. At every other type, `bool` included, the answer
     is `false` before the rule is read (`Packed.exhaust8p_run`), so the term
     above cannot be reused at another width;
   * every variable is of sort `t` (`Packed.allT`). A rule with a Boolean
     variable is `exhaust8`'s, or nobody's;
   * the rule has at most `Packed.maxVars` (2) variables: the variable of
     rank 0 is the one on the lanes, and every other variable is a counter
     of 256. Three variables would be 65,536 comparisons (measured with the
     limit raised, under the pinned Lean's own kernel: 11.5 s and 22.2 s for
     two rules, against 13 to 22 ms for two variables), so the answer is
     `false` at once, as `exhaust8`'s is over its size limit;
   * the rule has no side condition (`Packed.noConds`). A rule with a `where`
     clause is answered `false`, whatever the clause;
   * both sides are patterns of the lane fragment (`Packed.frag`): variables
     the rule binds (`?v` and `(const ?v)`), integer literals, `add sub and
     or xor`, `neg` and `not`. Any other operator (`mul`, the divisions and
     remainders, the shifts and rotations, `band bor bxor`, the bit counts,
     `bswap`, `bitreverse`), a comparison, a `select`, `true`, `false` and
     an unbound variable make the answer `false`, wherever they stand;
   * the two sides are one lane vector under every assignment of the other
     variables (`Packed.sweepP`).

   No operator of the fragment is undefined behaviour and no pattern of it
   is `bad`: on every assignment each side is a value
   (`Packed.evalS_evalR`). So the two directions ask the same thing here,
   one common value on every assignment, and a rule is admitted under
   either; and a rule that is admitted says something: `exhaust8p_defined`
   gives `EqsatDecide.Defined r T` and `exhaust8p_satisfiable` gives
   `EqsatRule.Satisfiable r T` from the same `true`.

   So `false` is not a refutation. It says the rule is not proved by this
   procedure: the type is not covered, a variable is Boolean, there are
   three variables or more, there is a side condition, a side is outside
   the fragment, or some assignment fails. `exhaust8p_sound` is the claim;
   completeness is not stated.

   The proof, in the order of the module:
   * `Packed.pack L f n` is the lane vector of `f`: the sum of
     `f i * 2^(L*i)` over `i < n`. Addition, a scalar factor and a
     subtraction without borrow are lane-wise by linearity (`pack_add`,
     `mul_pack`, `pack_sub`); `and or xor` are lane-wise on lanes that fit
     their width (`pack_and`, `pack_or`, `pack_xor`, from `bitwise_split`);
     and two vectors of lanes that fit are one number only when they agree
     on every lane (`pack_inj`);
   * the four constants `ones`, `iota`, `mask`, `mods` are the vectors of 1,
     of the lane's index, of 255 and of 256 (`ones_eq` and its siblings).
     The kernel checks that by reading each lane with a shift and a
     remainder (`lanesOk`, `pack_of_lanesOk`), not by evaluating `pack`:
     Clean's kernel leaves `Nat.pow` unreduced above 1,024 bits, and `pack`
     raises 2 to a lane's offset;
   * the invariant, `Packed.evalV_lanes`: where `F` gives each variable its
     residue on each lane, the vector `evalV` answers for a pattern under
     the lane vectors `F.map (pack L · N)` holds on lane `i` the residue
     `evalS` answers under lane `i`'s assignment `F.map (· i)`. By
     induction on the pattern, at every lane count and every lane width of
     nine bits or more;
   * `Packed.evalS_evalR`: on a pattern of the fragment the residue
     evaluator of `EqsatResidue` answers the value `evalS` computes, at
     width 8 and modulus 256. `evalR_agrees` then carries it to
     `EqsatRule.Pat.eval`;
   * `Packed.sweepP_spec`: an admitted assignment `y :: ys` is lane `y` of
     the comparison `sweepP` made for the counters `ys`, so the two sides
     are one residue there; `Packed.runP_sound` and `exhaust8p_sound` are
     the lift to `Sound`, as `EqsatExhaust.sweep_sound` lifts its sweep.

   How it is written, and why: as `EqsatResidue` and `EqsatExhaust`, every
   definition the kernel evaluates per assignment is one recursor
   application with closed minor premises, and the fragment is tested once
   per rule (`frag`), not once per assignment: `evalV` answers a bare `Nat`
   and has no failure outcome to test (outside the fragment it answers 0,
   and `frag` has already said `false`). The kernel operations it needs on
   4,096-bit literals are `Nat.add`, `Nat.sub`, `Nat.land`, `Nat.lor`,
   `Nat.xor`, `Nat.beq`, and `Nat.mul` by a residue (a variable's or a
   literal's value in every lane is that residue times `ones`).

   What is left out: three variables or more; side conditions; Boolean
   variables; every operator outside the fragment. `mul` of a counted
   variable by a lane vector would fit sixteen-bit lanes (255 * 255 is below
   2^16) and is not done; two variables on the lanes at once (65,536 lanes)
   is not done either, and would need literals of a million bits and no
   `Nat.mul` (Clean's kernel leaves a product above 16,384 bits unreduced).
-/
import EqsatExhaust

namespace EqsatDecide
open SemR EqsatRule

namespace Packed

/-! ## Lane vectors -/

/-- The lane vector of `f` on `n` lanes of `L` bits: lane `i` holds `f i`,
    so the number is the sum of `f i * 2^(L*i)` over `i < n`. -/
def pack (L : Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => ih + f k * 2 ^ (L * k)) n

theorem pack_zero (L : Nat) (f : Nat → Nat) : pack L f 0 = 0 := rfl

theorem pack_succ (L : Nat) (f : Nat → Nat) (n : Nat) :
    pack L f (n + 1) = pack L f n + f n * 2 ^ (L * n) := rfl

/-- A lane vector reads `f` on its lanes only. -/
theorem pack_congr {L : Nat} {f g : Nat → Nat} :
    ∀ (n : Nat), (∀ i, i < n → f i = g i) → pack L f n = pack L g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [pack_succ, pack_succ, pack_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h n (Nat.lt_succ_self n)]

theorem pack_const_zero (L : Nat) : ∀ (n : Nat), pack L (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by rw [pack_succ, pack_const_zero L n, Nat.zero_mul]

theorem two_pow_succ_lanes (L n : Nat) : 2 ^ (L * (n + 1)) = 2 ^ L * 2 ^ (L * n) := by
  rw [Nat.mul_succ, Nat.add_comm, Nat.pow_add]

/-- Lanes that fit their width leave the vector below `2^(L*n)`: lane `n`
    starts above everything the lanes below it hold. -/
theorem pack_lt {L : Nat} {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ L) :
    ∀ (n : Nat), pack L f n < 2 ^ (L * n)
  | 0 => by rw [pack_zero]; exact Nat.pow_pos (by decide)
  | n + 1 => by
    rw [pack_succ, two_pow_succ_lanes]
    have ih := pack_lt hf n
    have h1 : (f n + 1) * 2 ^ (L * n) ≤ 2 ^ L * 2 ^ (L * n) := Nat.mul_le_mul_right _ (hf n)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- Addition is lane-wise, with no hypothesis: the vector is linear in its
    lanes. (A lane that outgrows its width spills into the next; the
    bitwise lemmas are the ones that need the lanes to fit.) -/
theorem pack_add (L : Nat) (f g : Nat → Nat) :
    ∀ (n : Nat), pack L f n + pack L g n = pack L (fun i => f i + g i) n
  | 0 => rfl
  | n + 1 => by
    rw [pack_succ, pack_succ, pack_succ, ← pack_add L f g n, Nat.add_mul]
    omega

/-- A scalar multiplies every lane. -/
theorem mul_pack (L c : Nat) (f : Nat → Nat) :
    ∀ (n : Nat), c * pack L f n = pack L (fun i => c * f i) n
  | 0 => rfl
  | n + 1 => by
    rw [pack_succ, pack_succ, ← mul_pack L c f n, Nat.mul_add, Nat.mul_assoc]

/-- A scalar times the all-ones vector is the constant vector. -/
theorem mul_ones (L c n : Nat) : c * pack L (fun _ => 1) n = pack L (fun _ => c) n := by
  rw [mul_pack]
  exact pack_congr n fun i _ => Nat.mul_one c

/-- Subtraction is lane-wise when no lane borrows. -/
theorem pack_sub {L : Nat} {f g : Nat → Nat} (h : ∀ i, g i ≤ f i) (n : Nat) :
    pack L f n - pack L g n = pack L (fun i => f i - g i) n := by
  have h1 := pack_add L (fun i => f i - g i) g n
  have h2 : pack L (fun i => f i - g i + g i) n = pack L f n :=
    pack_congr n fun i _ => Nat.sub_add_cancel (h i)
  rw [h2] at h1
  omega

/-- A bitwise operator on two numbers that split at bit `k` acts on the two
    low parts and on the two high parts. -/
theorem bitwise_split (op : Nat → Nat → Nat)
    (hdiv : ∀ a b n, op a b / 2 ^ n = op (a / 2 ^ n) (b / 2 ^ n))
    (hmod : ∀ a b n, op a b % 2 ^ n = op (a % 2 ^ n) (b % 2 ^ n))
    {a b k : Nat} (x y : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    op (a + x * 2 ^ k) (b + y * 2 ^ k) = op a b + op x y * 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hm : op (a + x * 2 ^ k) (b + y * 2 ^ k) % 2 ^ k = op a b := by
    rw [hmod, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb]
  have hd : op (a + x * 2 ^ k) (b + y * 2 ^ k) / 2 ^ k = op x y := by
    rw [hdiv, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_div_right _ _ hpos,
      Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.zero_add, Nat.zero_add]
  have h := Nat.mod_add_div (op (a + x * 2 ^ k) (b + y * 2 ^ k)) (2 ^ k)
  rw [hm, hd, Nat.mul_comm] at h
  exact h.symm

/-- A bitwise operator is lane-wise on lanes that fit their width. -/
theorem pack_bitwise (op : Nat → Nat → Nat)
    (hdiv : ∀ a b n, op a b / 2 ^ n = op (a / 2 ^ n) (b / 2 ^ n))
    (hmod : ∀ a b n, op a b % 2 ^ n = op (a % 2 ^ n) (b % 2 ^ n))
    (h0 : op 0 0 = 0) {L : Nat} {f g : Nat → Nat}
    (hf : ∀ i, f i < 2 ^ L) (hg : ∀ i, g i < 2 ^ L) :
    ∀ (n : Nat), op (pack L f n) (pack L g n) = pack L (fun i => op (f i) (g i)) n
  | 0 => h0
  | n + 1 => by
    rw [pack_succ, pack_succ, pack_succ,
      bitwise_split op hdiv hmod _ _ (pack_lt hf n) (pack_lt hg n),
      pack_bitwise op hdiv hmod h0 hf hg n]

theorem pack_and {L : Nat} {f g : Nat → Nat} (hf : ∀ i, f i < 2 ^ L) (hg : ∀ i, g i < 2 ^ L)
    (n : Nat) : Nat.land (pack L f n) (pack L g n) = pack L (fun i => Nat.land (f i) (g i)) n :=
  pack_bitwise Nat.land (fun _ _ _ => Nat.and_div_two_pow) (fun _ _ _ => Nat.and_mod_two_pow)
    (by decide) hf hg n

theorem pack_or {L : Nat} {f g : Nat → Nat} (hf : ∀ i, f i < 2 ^ L) (hg : ∀ i, g i < 2 ^ L)
    (n : Nat) : Nat.lor (pack L f n) (pack L g n) = pack L (fun i => Nat.lor (f i) (g i)) n :=
  pack_bitwise Nat.lor (fun _ _ _ => Nat.or_div_two_pow) (fun _ _ _ => Nat.or_mod_two_pow)
    (by decide) hf hg n

theorem pack_xor {L : Nat} {f g : Nat → Nat} (hf : ∀ i, f i < 2 ^ L) (hg : ∀ i, g i < 2 ^ L)
    (n : Nat) : Nat.xor (pack L f n) (pack L g n) = pack L (fun i => Nat.xor (f i) (g i)) n :=
  pack_bitwise Nat.xor (fun _ _ _ => Nat.xor_div_two_pow) (fun _ _ _ => Nat.xor_mod_two_pow)
    (by decide) hf hg n

/-- Two vectors of lanes that fit their width are one number only when they
    agree on every lane: the comparison of two sides on all lanes is one
    equality of naturals. -/
theorem pack_inj {L : Nat} {f g : Nat → Nat} (hf : ∀ i, f i < 2 ^ L) (hg : ∀ i, g i < 2 ^ L) :
    ∀ (n : Nat), pack L f n = pack L g n → ∀ i, i < n → f i = g i
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    rw [pack_succ, pack_succ] at h
    have hpos : 0 < 2 ^ (L * n) := Nat.pow_pos (by decide)
    have hm := congrArg (· % 2 ^ (L * n)) h
    have hd := congrArg (· / 2 ^ (L * n)) h
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (pack_lt hf n),
      Nat.mod_eq_of_lt (pack_lt hg n)] at hm
    simp only [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (pack_lt hf n),
      Nat.div_eq_of_lt (pack_lt hg n), Nat.zero_add] at hd
    by_cases hin : i = n
    · rw [hin]; exact hd
    · exact pack_inj hf hg n hm i (by omega)

/-- The low `n` lanes of any number, read lane by lane. -/
theorem mod_lanes {L : Nat} {f : Nat → Nat} {v : Nat} :
    ∀ (n : Nat), (∀ i, i < n → v / 2 ^ (L * i) % 2 ^ L = f i) → v % 2 ^ (L * n) = pack L f n
  | 0, _ => by rw [Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1, h => by
    rw [pack_succ, ← mod_lanes n (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      ← h n (Nat.lt_succ_self n), two_pow_succ_lanes, Nat.mul_comm (2 ^ L), Nat.mod_mul,
      Nat.mul_comm (2 ^ (L * n))]

noncomputable section

/-- `v` is the lane vector of `f` on `n` lanes of `L` bits, tested lane by
    lane: nothing above lane `n - 1`, and lane `i` is `f i`. The test reads
    a lane with a shift and a remainder, so the kernel evaluates it without
    raising 2 to a lane's offset (`pack` does, and Clean's kernel leaves a
    power above 1,024 bits unreduced). -/
def lanesOk (L n : Nat) (f : Nat → Nat) (v : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (allBelow n fun i => Nat.beq (Nat.shiftRight v (L * i) % 2 ^ L) (f i))
    (Nat.beq (Nat.shiftRight v (L * n)) 0)

end

/-- A number that passes `lanesOk` is the lane vector. -/
theorem pack_of_lanesOk {L n : Nat} {f : Nat → Nat} {v : Nat} (h : lanesOk L n f v = true) :
    v = pack L f n := by
  obtain ⟨h0, h1⟩ := guard_true h
  have h0' : v / 2 ^ (L * n) = 0 := by
    have := Nat.eq_of_beq_eq_true h0
    rwa [show Nat.shiftRight v (L * n) = v >>> (L * n) from rfl, Nat.shiftRight_eq_div_pow] at this
  have hlt : v < 2 ^ (L * n) := Nat.lt_of_div_eq_zero (Nat.pow_pos (by decide)) h0'
  rw [← mod_lanes n fun i hi => by
    have := Nat.eq_of_beq_eq_true (allBelow_spec _ _ h1 i hi)
    rwa [show Nat.shiftRight v (L * i) = v >>> (L * i) from rfl, Nat.shiftRight_eq_div_pow] at this]
  exact (Nat.mod_eq_of_lt hlt).symm

/-! ## The four constants of 256 sixteen-bit lanes -/

/-- 1 in every lane. -/
def ones : Nat := 15936352810149576664251967814398785116044315999807488828629487804744852490601319246949367695658771013060045879521465824948311183919825949603467400440243614525764201976710307443966759596160581648194523079451528896412242600738501758536237654449448182154525183622580357123236195143665501016471625509782528862541953749551869806758936532084996733662921789172698916141039546752774227893735750360383218364869059823909136972401285388180888025239762140423277584116886992314778491143078890572493077753124787855165477237659016042868878202719368228058856917552966456873751712716050478760207919406430340196610400483321769964401065179002262083021678978185398452866744530926530826248604763393876218916230952698251646241235527357520787121612987855885557073174843970573766602137893204151836183304864267819559773906375578462150991428535307773037120515787334453279740335377255521721330784247728997071039469632671928226464952026335590388905572722100502643327197680199920370271816177978946627802851908079592443724257294188217253657585526141134510999146570124657559556737736602149180922352533713052762943775348394025191525397281973729840213808343702189392802914132114185184800534085639939989161923753971030916786494556828229700710921550388469373665281
/-- The lane's index in every lane: 0, 1, …, 255. -/
def iota : Nat := 4063769723414985565832307575810962129535450789086241919439852134095070447667577033571856108858727118610757063433831273399267662751601334401864280139386552309950476894093905132623556290798935713887197828007937542323904247986630289336151473384759519920859141866098974928783402902152057704412730874543251508570631065799208153407288535542259623939210484438904109437298476639252816031202335671481143886166377709601143288622479259432294323434872461856426812815639949472144729252647226761372313411115215606282457927532899740828320745403239726424357288541400242902189354420143605034940548857231795857019909442078202888617854677011409149744388168098618206375222146272897985603277082619893865840023742007544477287484446197224833484443643914954672155733941309622365712449311662490270768867770016662580588618197582893511454486650175130323019587677131912391331828097833477986211468372874346641472475742224839329976712206481318643157487170547885409105997881523419151199348674758001681095348235982712978931444308053285028305294309050241590819247760303637527009352199178436473237905611785353155656136690436564798081362947242092869783553854983520510741314511289420386628825521196022712953998817552171837453693873698766181398845066899810428234301440
/-- 255 in every lane. -/
def mask : Nat := 4063769966588142049384251792671690204591300579950909651300519390209937385103336407972088762392986608330311699277973785361819351899555617148884187112262121704069871504061128398211523697020948320289603385260139868585121863188317948426740601884609286449403921823757991066425229761634702759200264504994544859948198206135726800723528815681674167084045056239038223615965084421957428112902616341897720683041610255096829927962327773986126446436139345807935783949806183040268515241485117095985734827046820903067196695603049090931563941693438898155008513976006446502806686742592872083853019448639736750135652123247051340922271620645576831170528139437276605481019855386265360693394214665438435823638892938054169791515059476167800716011311903250817053659585212496310483545162767058718226742740388293987742346125772507848502814276503482124465731525770285586333785521200158038939349983170894253115064756331341697748562766715575549170921044135628174048435408450979694419313125384631390089727236560296073149685610017995399682684309165989300304782375381787677686968122833548041135199896096828454550662713840476423838976306903301109254521127644058295164743103689117222124136191838184697236290557262612883780556111991198573681284995349059690284646655
/-- 256 in every lane. -/
def mods : Nat := 4079706319398291626048503760486088989707344895950717140129148878014682237593937727219038130088645379343371745157495251186767663083475443098487654512702365318595635706037838705655490456617108901937797908339591397481534105789056450185276839539058734631558447007380571423548465956778368260216736130504327388810740159885278670530287752213759163817707978028210922532106123968710202340796352092258103901406479314920739064934729059374307334461379107948359061533923070032583293732628195986558227904799945690922362172840708106974432819896158266383067370893559412959680438455308922562613227368046167090332262523730373110886672685824579093253549818415462003933886599917191891519642819428832312042555123890752421437756295003525321503132924891106702610732760056466884250147300660262870062926045252561807302120032148086310653805705038789897502852041557620039613525856577413560660680767418623250186104225964013625975027718741911139559826616857728676691762606131179614789584941562610336717530088468375665593409867312183616936341894692130434815781521951912335246524860570150190316122248630541507313606489188870449030501704185274839094734935987760484557546017821231407308936725923824637225452481016583914697342606548026803381995916899448159658311936

/-- Each constant is the lane vector its name says, by `lanesOk`: the
    kernel reads its 256 lanes once, when it checks these four theorems
    (`rflTrue` has the type `lanesOk … = true` only by that evaluation). -/
theorem ones_eq : ones = pack 16 (fun _ => 1) 256 := pack_of_lanesOk rflTrue
theorem iota_eq : iota = pack 16 (fun i => i % 256) 256 := pack_of_lanesOk rflTrue
theorem mask_eq : mask = pack 16 (fun _ => 255) 256 := pack_of_lanesOk rflTrue
theorem mods_eq : mods = pack 16 (fun _ => 256) 256 := pack_of_lanesOk rflTrue

/-! ## The two evaluators -/

noncomputable section

/-- The entry of rank `i`; 0 for an unbound rank (`frag` refuses a pattern
    that reads one). -/
def getN (env : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun v _ ih i => Nat.rec (motive := fun _ => Nat) v (fun j _ => ih j) i) env i

/-- A binary operator on two lane vectors whose lanes are residues below
    256: `add` and `sub` cannot carry out of a lane (511 at most) and are
    masked back to eight bits; `and or xor` stay below 256. Every other
    operator is 0 (`frag` refuses it). -/
def binV (mask mods : Nat) (op : BinOp) (a b : Nat) : Nat :=
  BinOp.rec (motive := fun _ => Nat)
    (Nat.land (a + b) mask)
    (Nat.land (a + (mods - b)) mask)
    0 0 0 0 0
    (Nat.land a b) (Nat.lor a b) (Nat.xor a b)
    0 0 0 0 0 0 0 0 op

/-- A unary operator on a lane vector: `neg` is 256 minus the lane, masked;
    `not` is 255 minus the lane. Every other operator is 0. -/
def unV (mask mods : Nat) (op : UnOp) (a : Nat) : Nat :=
  UnOp.rec (motive := fun _ => Nat)
    (Nat.land (mods - a) mask) (mask - a) 0 0 0 0 0 op

/-- The pattern on every lane at once. `env` holds one lane vector per
    variable; `ones`, `mask` and `mods` are the vectors of 1, 255 and 256.
    The operators are `binV` and `unV` unfolded (`evalV_bin` and `evalV_un`
    state it folded): one kernel step less per operator and assignment. -/
def evalV (ones mask mods : Nat) (env : List Nat) (p : Pat) : Nat :=
  Pat.rec (motive := fun _ => Nat)
    (fun i => getN env i)
    (fun i => getN env i)
    (fun neg mag => litR (nat_lit 8) neg mag * ones)
    0 0
    (fun op _ _ a b => BinOp.rec (motive := fun _ => Nat)
      (Nat.land (a + b) mask)
      (Nat.land (a + (mods - b)) mask)
      0 0 0 0 0
      (Nat.land a b) (Nat.lor a b) (Nat.xor a b)
      0 0 0 0 0 0 0 0 op)
    (fun op _ a => UnOp.rec (motive := fun _ => Nat)
      (Nat.land (mods - a) mask) (mask - a) 0 0 0 0 0 op)
    (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ _ _ => 0)
    p

/-- The operators of the lane fragment. -/
def binOk (op : BinOp) : Bool :=
  BinOp.rec (motive := fun _ => Bool)
    true true false false false false false true true true
    false false false false false false false false op

def unOk (op : UnOp) : Bool :=
  UnOp.rec (motive := fun _ => Bool) true true false false false false false op

/-- The pattern is in the lane fragment of a rule with `n` variables:
    variables of rank below `n`, integer literals, `add sub and or xor`,
    `neg` and `not`. Read once per rule, not once per assignment. -/
def frag (n : Nat) (p : Pat) : Bool :=
  Pat.rec (motive := fun _ => Bool)
    (fun i => Nat.blt i n)
    (fun i => Nat.blt i n)
    (fun _ _ => true)
    false false
    (fun op _ _ fa fb => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false fb fa) (binOk op))
    (fun op _ fa => Bool.rec (motive := fun _ => Bool) false fa (unOk op))
    (fun _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ => false)
    p

end

/-- A binary operator of the fragment on two residues, written as
    `EqsatDecide.intBinR` writes it at modulus 256; 0 for every other
    operator. -/
def binS (op : BinOp) (a b : Nat) : Nat :=
  match op with
  | .add => (a + b) % 256
  | .sub => (a + (256 - b % 256)) % 256
  | .and => Nat.land a b % 256
  | .or => Nat.lor a b % 256
  | .xor => Nat.xor a b % 256
  | _ => 0

/-- A unary operator of the fragment on a residue, as `EqsatDecide.intUnR`
    writes it at modulus 256; 0 for every other operator. -/
def unS (op : UnOp) (a : Nat) : Nat :=
  match op with
  | .neg => (256 - a % 256) % 256
  | .not => 256 - 1 - a % 256
  | _ => 0

/-- The pattern on one assignment of residues: what one lane of `evalV`
    holds (`evalV_lanes`), and the residue `Pat.evalR` answers on a pattern
    of the fragment (`evalS_evalR`). -/
noncomputable def evalS (env : List Nat) : Pat → Nat
  | .var i => getN env i
  | .cvar i => getN env i
  | .lit neg mag => litR 8 neg mag
  | .tt => 0
  | .ff => 0
  | .bin op a b => binS op (evalS env a) (evalS env b)
  | .un op a => unS op (evalS env a)
  | .cmp _ _ _ => 0
  | .sel _ _ _ => 0

/-! ## What the definitions reduce to -/

theorem getN_nil (i : Nat) : getN [] i = 0 := rfl
theorem getN_zero (v : Nat) (vs : List Nat) : getN (v :: vs) 0 = v := rfl
theorem getN_succ (v : Nat) (vs : List Nat) (i : Nat) : getN (v :: vs) (i + 1) = getN vs i := rfl

theorem evalV_var (ones mask mods : Nat) (env : List Nat) (i : Nat) :
    evalV ones mask mods env (.var i) = getN env i := rfl
theorem evalV_cvar (ones mask mods : Nat) (env : List Nat) (i : Nat) :
    evalV ones mask mods env (.cvar i) = getN env i := rfl
theorem evalV_lit (ones mask mods : Nat) (env : List Nat) (neg : Bool) (mag : Nat) :
    evalV ones mask mods env (.lit neg mag) = litR 8 neg mag * ones := rfl
theorem evalV_bin (ones mask mods : Nat) (env : List Nat) (op : BinOp) (a b : Pat) :
    evalV ones mask mods env (.bin op a b) =
      binV mask mods op (evalV ones mask mods env a) (evalV ones mask mods env b) := rfl
theorem evalV_un (ones mask mods : Nat) (env : List Nat) (op : UnOp) (a : Pat) :
    evalV ones mask mods env (.un op a) = unV mask mods op (evalV ones mask mods env a) := rfl

theorem frag_bin (n : Nat) (op : BinOp) (a b : Pat) :
    frag n (.bin op a b) = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (frag n b) (frag n a)) (binOk op) := rfl
theorem frag_un (n : Nat) (op : UnOp) (a : Pat) :
    frag n (.un op a) = Bool.rec (motive := fun _ => Bool) false (frag n a) (unOk op) := rfl

/-! ## Ranges -/

theorem getN_lt : ∀ (env : List Nat), (∀ v, v ∈ env → v < 256) → ∀ i, getN env i < 256
  | [], _, _ => (by decide : (0 : Nat) < 256)
  | v :: _, h, 0 => h v (List.mem_cons_self ..)
  | _ :: vs, h, i + 1 => getN_lt vs (fun u hu => h u (List.mem_cons_of_mem _ hu)) i

theorem binS_lt (op : BinOp) (a b : Nat) : binS op a b < 256 := by
  cases op <;> simp only [binS] <;> omega

theorem unS_lt (op : UnOp) (a : Nat) : unS op a < 256 := by
  cases op <;> simp only [unS] <;> omega

/-- On residues below 256 every pattern is a residue below 256. -/
theorem evalS_lt {env : List Nat} (henv : ∀ v, v ∈ env → v < 256) :
    ∀ (p : Pat), evalS env p < 256
  | .var i => getN_lt env henv i
  | .cvar i => getN_lt env henv i
  | .lit neg mag => litR_lt 8 neg mag
  | .tt => (by decide : (0 : Nat) < 256)
  | .ff => (by decide : (0 : Nat) < 256)
  | .bin op _ _ => binS_lt op _ _
  | .un op _ => unS_lt op _
  | .cmp _ _ _ => (by decide : (0 : Nat) < 256)
  | .sel _ _ _ => (by decide : (0 : Nat) < 256)

/-! ## The lane invariant -/

theorem land_255 (x : Nat) : Nat.land x 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

/-- `binV` is `binS` on every lane. -/
theorem binV_lanes {L N mask mods : Nat} (hL : 512 ≤ 2 ^ L)
    (hmask : mask = pack L (fun _ => 255) N) (hmods : mods = pack L (fun _ => 256) N)
    (op : BinOp) {f g : Nat → Nat} (hf : ∀ i, f i < 256) (hg : ∀ i, g i < 256) :
    binV mask mods op (pack L f N) (pack L g N) = pack L (fun i => binS op (f i) (g i)) N := by
  have hfL : ∀ i, f i < 2 ^ L := fun i => by have := hf i; omega
  have hgL : ∀ i, g i < 2 ^ L := fun i => by have := hg i; omega
  have h255 : ∀ i : Nat, (fun _ : Nat => 255) i < 2 ^ L := fun _ => by show 255 < 2 ^ L; omega
  subst hmask; subst hmods
  cases op
  case add =>
    show Nat.land (pack L f N + pack L g N) (pack L (fun _ => 255) N) = _
    rw [pack_add, pack_and (fun i => by have := hf i; have := hg i; omega) h255]
    exact pack_congr N fun i _ => land_255 _
  case sub =>
    show Nat.land (pack L f N + (pack L (fun _ => 256) N - pack L g N))
      (pack L (fun _ => 255) N) = _
    rw [pack_sub (fun i => Nat.le_of_lt (hg i)), pack_add,
      pack_and (fun i => by have := hf i; have := hg i; omega) h255]
    refine pack_congr N fun i _ => ?_
    show Nat.land (f i + (256 - g i)) 255 = (f i + (256 - g i % 256)) % 256
    rw [land_255, Nat.mod_eq_of_lt (hg i)]
  case and =>
    show Nat.land (pack L f N) (pack L g N) = _
    rw [pack_and hfL hgL]
    refine pack_congr N fun i _ => ?_
    show Nat.land (f i) (g i) = Nat.land (f i) (g i) % 256
    have h1 : Nat.land (f i) (g i) ≤ f i := Nat.and_le_left
    have := hf i
    rw [Nat.mod_eq_of_lt (by omega)]
  case or =>
    show Nat.lor (pack L f N) (pack L g N) = _
    rw [pack_or hfL hgL]
    refine pack_congr N fun i _ => ?_
    show Nat.lor (f i) (g i) = Nat.lor (f i) (g i) % 256
    exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) (hf i) (hg i))).symm
  case xor =>
    show Nat.xor (pack L f N) (pack L g N) = _
    rw [pack_xor hfL hgL]
    refine pack_congr N fun i _ => ?_
    show Nat.xor (f i) (g i) = Nat.xor (f i) (g i) % 256
    exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 8) (hf i) (hg i))).symm
  all_goals exact (pack_const_zero L N).symm

/-- `unV` is `unS` on every lane. -/
theorem unV_lanes {L N mask mods : Nat} (hL : 512 ≤ 2 ^ L)
    (hmask : mask = pack L (fun _ => 255) N) (hmods : mods = pack L (fun _ => 256) N)
    (op : UnOp) {f : Nat → Nat} (hf : ∀ i, f i < 256) :
    unV mask mods op (pack L f N) = pack L (fun i => unS op (f i)) N := by
  have h255 : ∀ i : Nat, (fun _ : Nat => 255) i < 2 ^ L := fun _ => by show 255 < 2 ^ L; omega
  subst hmask; subst hmods
  cases op
  case neg =>
    show Nat.land (pack L (fun _ => 256) N - pack L f N) (pack L (fun _ => 255) N) = _
    rw [pack_sub (fun i => Nat.le_of_lt (hf i)),
      pack_and (fun i => by show 256 - f i < 2 ^ L; omega) h255]
    refine pack_congr N fun i _ => ?_
    show Nat.land (256 - f i) 255 = (256 - f i % 256) % 256
    rw [land_255, Nat.mod_eq_of_lt (hf i)]
  case not =>
    show pack L (fun _ => 255) N - pack L f N = _
    rw [pack_sub (fun i => by have := hf i; omega)]
    refine pack_congr N fun i _ => ?_
    show 255 - f i = 256 - 1 - f i % 256
    rw [Nat.mod_eq_of_lt (hf i)]
  all_goals exact (pack_const_zero L N).symm

/-- A variable's lane vector, lane by lane. -/
theorem getN_lanes (L N : Nat) :
    ∀ (F : List (Nat → Nat)) (j : Nat),
      getN (F.map fun f => pack L f N) j = pack L (fun i => getN (F.map fun f => f i) j) N
  | [], _ => (pack_const_zero L N).symm
  | _ :: _, 0 => rfl
  | _ :: F, j + 1 => getN_lanes L N F j

/-- The invariant of the packed evaluator. `F` gives each variable its
    residue on each lane; under the assignment of lane vectors
    `F.map (pack L · N)`, the vector `evalV` answers for a pattern holds on
    lane `i` the residue `evalS` answers under lane `i`'s assignment
    `F.map (· i)`. It holds for every pattern, at every lane count `N` and
    every lane width `L` of nine bits or more, for any `ones`, `mask` and
    `mods` that are the vectors of 1, 255 and 256. -/
theorem evalV_lanes {L N ones mask mods : Nat} (hL : 512 ≤ 2 ^ L)
    (hones : ones = pack L (fun _ => 1) N)
    (hmask : mask = pack L (fun _ => 255) N) (hmods : mods = pack L (fun _ => 256) N)
    (F : List (Nat → Nat)) (hF : ∀ f, f ∈ F → ∀ i, f i < 256) (p : Pat) :
    evalV ones mask mods (F.map fun f => pack L f N) p =
      pack L (fun i => evalS (F.map fun f => f i) p) N := by
  have hlt : ∀ (q : Pat) (i : Nat), evalS (F.map fun f => f i) q < 256 := fun q i =>
    evalS_lt (fun v hv => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
      exact hF f hf i) q
  induction p with
  | var j => exact getN_lanes L N F j
  | cvar j => exact getN_lanes L N F j
  | lit neg mag =>
    rw [evalV_lit, hones, mul_ones]
    rfl
  | tt => exact (pack_const_zero L N).symm
  | ff => exact (pack_const_zero L N).symm
  | bin op a b iha ihb =>
    rw [evalV_bin, iha, ihb, binV_lanes hL hmask hmods op (hlt a) (hlt b)]
    rfl
  | un op a iha =>
    rw [evalV_un, iha, unV_lanes hL hmask hmods op (hlt a)]
    rfl
  | cmp op a b _ _ => exact (pack_const_zero L N).symm
  | sel c a b _ _ _ => exact (pack_const_zero L N).symm

/-! ## The scalar evaluator against the residue evaluator -/

theorem getR_map_res : ∀ (env : List Nat) (i : Nat), i < env.length →
    getR (env.map RV.res) i = .ok (.res (getN env i))
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _ => rfl
  | _ :: vs, i + 1, h => getR_map_res vs i (Nat.lt_of_succ_lt_succ h)

/-- On a pattern of the fragment the residue evaluator of `EqsatResidue`
    answers the value `evalS` computes, at width 8 and modulus 256: never
    undefined behaviour and never `bad`. -/
theorem evalS_evalR (env : List Nat) :
    ∀ (p : Pat), frag env.length p = true →
      p.evalR true 8 256 (env.map RV.res) = .ok (.res (evalS env p)) := by
  intro p
  induction p with
  | var i =>
    intro h
    exact getR_map_res env i (Nat.blt_eq.mp h)
  | cvar i =>
    intro h
    exact getR_map_res env i (Nat.blt_eq.mp h)
  | lit neg mag => intro _; rfl
  | tt => intro h; exact Bool.noConfusion (show false = true from h)
  | ff => intro h; exact Bool.noConfusion (show false = true from h)
  | bin op a b iha ihb =>
    intro h
    rw [frag_bin] at h
    obtain ⟨hop, h2⟩ := guard_true h
    obtain ⟨ha, hb⟩ := guard_true h2
    rw [evalR_bin, iha ha, ihb hb, bind_ok, bind_ok]
    cases op <;> first | rfl | exact Bool.noConfusion (show false = true from hop)
  | un op a iha =>
    intro h
    rw [frag_un] at h
    obtain ⟨hop, ha⟩ := guard_true h
    rw [evalR_un, iha ha, bind_ok]
    cases op <;> first | rfl | exact Bool.noConfusion (show false = true from hop)
  | cmp op a b _ _ => intro h; exact Bool.noConfusion (show false = true from h)
  | sel c a b _ _ _ => intro h; exact Bool.noConfusion (show false = true from h)

/-! ## The procedure's tests -/

noncomputable section

/-- The number of variables. -/
def lenS (s : Sorts) : Nat :=
  Sorts.rec (motive := fun _ => Nat) 0 (fun _ _ _ ih => Nat.succ ih) s

/-- Every variable is of sort `t`. -/
def allT (s : Sorts) : Bool :=
  Sorts.rec (motive := fun _ => Bool) true
    (fun srt _ _ ih => Srt.rec (motive := fun _ => Bool) ih false srt) s

/-- The rule has no side condition. -/
def noConds (cs : Conds) : Bool :=
  Conds.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs

/-- `k` is `true` on the lane vectors of every assignment of the variables
    `s` to residues below 256: a variable that holds `x` on every lane is
    `x * ones`. One counter of 256 per variable, as `EqsatDecide.allFrom`. -/
def outer (ones : Nat) (s : Sorts) : (List Nat → Bool) → Bool :=
  Sorts.rec (motive := fun _ => (List Nat → Bool) → Bool)
    (fun k => k [])
    (fun _ _ _ ih k => allBelow (nat_lit 256) fun x => ih fun vs => k (x * ones :: vs))
    s

/-- The two sides are one vector under every assignment of lane vectors: the
    variable of rank 0 holds every residue at once (`iota`: lane `i` holds
    `i`), and every other variable is enumerated by `outer`. A rule with no
    variable is one comparison. -/
def sweepP (ones iota mask mods : Nat) (vars : Sorts) (lhs rhs : Pat) : Bool :=
  Sorts.rec (motive := fun _ => Bool)
    (Nat.beq (evalV ones mask mods [] lhs) (evalV ones mask mods [] rhs))
    (fun _ _ rest _ => outer ones rest fun vs =>
      Nat.beq (evalV ones mask mods (iota :: vs) lhs) (evalV ones mask mods (iota :: vs) rhs))
    vars

/-- The most variables `exhaust8p` takes: one on the lanes and one counter
    of 256 (the module header has the cost behind it). -/
def maxVars : Nat := 2

/-- The procedure at eight bits: every variable of sort `t`, at most
    `maxVars` of them, no side condition, both sides in the lane fragment,
    then `sweepP`; the first `false` is the answer. -/
def runP (r : Rule) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun _ vars lhs rhs cs =>
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (Bool.rec (motive := fun _ => Bool) false
                (sweepP ones iota mask mods vars lhs rhs)
                (frag (lenS vars) rhs))
              (frag (lenS vars) lhs))
            (noConds cs))
          (Nat.ble (lenS vars) maxVars))
        (allT vars))
    r

end

end Packed

noncomputable section

/-- The procedure: `Packed.runP` at `i8` and `u8`, and `false` at every
    other type. -/
def exhaust8p (r : Rule) (T : STy) : Bool :=
  STy.rec (motive := fun _ => Bool)
    (fun t => IntTy.rec (motive := fun _ => Bool)
      (Packed.runP r) false false false false false
      (Packed.runP r) false false false false false t)
    false
    T

end

namespace Packed

/-! ## The enumeration reaches every assignment -/

/-- A `true` of `outer` is `k = true` on the lane vectors of every
    assignment of residues below 256. -/
theorem outer_spec (ones : Nat) :
    ∀ (s : Sorts) (k : List Nat → Bool), outer ones s k = true →
      ∀ (ys : List Nat), ys.length = lenS s → (∀ y, y ∈ ys → y < 256) →
        k (ys.map fun x => x * ones) = true := by
  intro s
  induction s with
  | nil =>
    intro k h ys hlen _
    cases ys with
    | nil => exact h
    | cons y ys => cases hlen
  | cons srt c rest ih =>
    intro k h ys hlen hys
    cases ys with
    | nil => cases hlen
    | cons y ys =>
      have h1 : allBelow 256 (fun x => outer ones rest fun vs => k (x * ones :: vs)) = true := h
      have h2 := allBelow_spec _ _ h1 y (hys y (List.mem_cons_self ..))
      exact ih (fun vs => k (y * ones :: vs)) h2 ys (Nat.succ.inj hlen)
        (fun u hu => hys u (List.mem_cons_of_mem _ hu))

/-- An assignment the variables admit, when every variable is of sort `t`
    at an integer type: one residue below the modulus per variable. -/
theorem admits_allT {pb : Nat} {t : IntTy} :
    ∀ (s : Sorts) (env : List Val), allT s = true → Admits pb (.int t) s env →
      ∃ ys : List Nat, ys.length = lenS s ∧ (∀ y, y ∈ ys → y < modulus (t.bits pb)) ∧
        env = (ys.map RV.res).map (RV.val (.int t)) := by
  intro s
  induction s with
  | nil =>
    intro env _ hadm
    rw [admits_nil] at hadm
    subst hadm
    exact ⟨[], rfl, fun y hy => absurd hy List.not_mem_nil, rfl⟩
  | cons srt c rest ih =>
    intro env hT hadm
    cases srt with
    | bool => exact Bool.noConfusion (show false = true from hT)
    | t =>
      obtain ⟨x, vs, rfl, hx, hrest⟩ := admits_cons_t_int.mp hadm
      obtain ⟨ys, hlen, hys, rfl⟩ := ih vs hT hrest
      refine ⟨x :: ys, congrArg Nat.succ hlen, fun y hy => ?_, rfl⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hx
      · exact hys y hy'

theorem envWF_res :
    ∀ (ys : List Nat), (∀ y, y ∈ ys → y < 256) → EnvWF true 256 (ys.map RV.res)
  | [], _ => trivial
  | y :: ys, h =>
    ⟨⟨rfl, h y (List.mem_cons_self ..)⟩,
      envWF_res ys fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

/-- The lane vectors of variables that hold one residue on every lane. -/
theorem map_consts : ∀ (ys : List Nat),
    ((ys.map fun x _ => x).map fun f => pack 16 f 256) = ys.map fun x => x * ones
  | [] => rfl
  | x :: ys => by
    have hx : pack 16 (fun _ => x) 256 = x * ones := by rw [ones_eq, mul_ones]
    exact congr (congrArg List.cons hx) (map_consts ys)

/-- And their residues on any one lane. -/
theorem map_consts_at (i : Nat) : ∀ (ys : List Nat),
    ((ys.map fun x (_ : Nat) => x).map fun f => f i) = ys
  | [] => rfl
  | x :: ys => congrArg (x :: ·) (map_consts_at i ys)

/-- Sixteen-bit lanes hold 511. -/
theorem lanes16 : 512 ≤ 2 ^ 16 := by decide

/-- What a `true` of `sweepP` proves: on every assignment of residues below
    256 the two sides are one residue in `evalS`. The assignment is the
    lane `y` of the vectors `sweepP` compared, `y` the residue of the
    variable of rank 0. -/
theorem sweepP_spec (vars : Sorts) (lhs rhs : Pat)
    (h : sweepP ones iota mask mods vars lhs rhs = true) (ys : List Nat)
    (hlen : ys.length = lenS vars) (hys : ∀ y, y ∈ ys → y < 256) :
    evalS ys lhs = evalS ys rhs := by
  have hS : ∀ (F : List (Nat → Nat)), (∀ f, f ∈ F → ∀ i, f i < 256) →
      ∀ (p : Pat) (i : Nat), evalS (F.map fun f => f i) p < 2 ^ 16 := fun F hF p i => by
    have : evalS (F.map fun f => f i) p < 256 := evalS_lt (fun v hv => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
      exact hF f hf i) p
    exact Nat.lt_of_lt_of_le this (by decide)
  cases vars with
  | nil =>
    cases ys with
    | cons y ys => cases hlen
    | nil =>
      have h1 : evalV ones mask mods [] lhs = evalV ones mask mods [] rhs :=
        Nat.eq_of_beq_eq_true h
      have hF : ∀ f, f ∈ ([] : List (Nat → Nat)) → ∀ i, f i < 256 :=
        fun f hf => absurd hf List.not_mem_nil
      have hl := evalV_lanes lanes16 ones_eq mask_eq mods_eq [] hF lhs
      have hr := evalV_lanes lanes16 ones_eq mask_eq mods_eq [] hF rhs
      rw [List.map_nil] at hl hr
      rw [hl, hr] at h1
      exact pack_inj (hS [] hF lhs) (hS [] hF rhs) 256 h1 0 (by decide)
  | cons srt c rest =>
    cases ys with
    | nil => cases hlen
    | cons y ys =>
      have hy : y < 256 := hys y (List.mem_cons_self ..)
      have hys' : ∀ u, u ∈ ys → u < 256 := fun u hu => hys u (List.mem_cons_of_mem _ hu)
      have h0 : outer ones rest (fun vs =>
          Nat.beq (evalV ones mask mods (iota :: vs) lhs)
            (evalV ones mask mods (iota :: vs) rhs)) = true := h
      have h1 := Nat.eq_of_beq_eq_true
        (outer_spec ones rest _ h0 ys (Nat.succ.inj hlen) hys')
      -- the residue of each variable on each lane
      let F : List (Nat → Nat) := (fun i => i % 256) :: ys.map fun x _ => x
      have hF : ∀ f, f ∈ F → ∀ i, f i < 256 := by
        intro f hf i
        rcases List.mem_cons.mp hf with rfl | hf'
        · exact Nat.mod_lt _ (by decide)
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf'
          exact hys' x hx
      have hV : (F.map fun f => pack 16 f 256) = iota :: ys.map fun x => x * ones := by
        exact congr (congrArg List.cons iota_eq.symm) (map_consts ys)
      have hE : (F.map fun f => f y) = y :: ys := by
        exact congr (congrArg List.cons (Nat.mod_eq_of_lt hy)) (map_consts_at y ys)
      have hl := evalV_lanes lanes16 ones_eq mask_eq mods_eq F hF lhs
      have hr := evalV_lanes lanes16 ones_eq mask_eq mods_eq F hF rhs
      rw [hV] at hl hr
      rw [hl, hr] at h1
      have h2 := pack_inj (hS F hF lhs) (hS F hF rhs) 256 h1 y hy
      rw [hE] at h2
      exact h2

/-! ## What a `true` proves -/

/-- The six tests of a `runP` that answered `true`. -/
theorem runP_parts {d : Dir} {vars : Sorts} {lhs rhs : Pat} {cs : Conds}
    (h : runP (Rule.mk d vars lhs rhs cs) = true) :
    allT vars = true ∧ noConds cs = true ∧ frag (lenS vars) lhs = true ∧
      frag (lenS vars) rhs = true ∧ sweepP ones iota mask mods vars lhs rhs = true := by
  obtain ⟨h1, h⟩ := guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
  obtain ⟨_, h⟩ := guard_true h
  obtain ⟨h3, h⟩ := guard_true h
  obtain ⟨h4, h⟩ := guard_true h
  obtain ⟨h5, h⟩ := guard_true h
  exact ⟨h1, h3, h4, h5, h⟩

/-- What a `true` of `runP` proves at an integer type of eight bits: the
    body of `EqsatRule.Sound r (.int t)` at pointer width `pb`, and that both
    sides are one common value there. -/
theorem runP_sound {pb : Nat} {t : IntTy} (ht : t.bits pb = 8) (r : Rule)
    (h : runP r = true) (env : List Val) (hadm : Admits pb (.int t) r.vars env) :
    ∃ v, r.lhs.eval pb (.int t) env = .ok v ∧ r.rhs.eval pb (.int t) env = .ok v := by
  cases r with
  | mk d vars lhs rhs cs =>
    obtain ⟨hT, _, hfl, hfr, hsw⟩ := runP_parts h
    obtain ⟨ys, hlen, hys, rfl⟩ := admits_allT vars env hT hadm
    have hys' : ∀ y, y ∈ ys → y < 256 := fun y hy => by
      have h1 := hys y hy
      rw [ht] at h1
      exact h1
    have heq := sweepP_spec vars lhs rhs hsw ys hlen hys'
    have hw : WidthOf pb (.int t) 8 := ht
    have hwf := envWF_res ys hys'
    have hl := evalR_agrees (pb := pb) (T := .int t) (m := 256) hw rfl hwf lhs
    have hr := evalR_agrees (pb := pb) (T := .int t) (m := 256) hw rfl hwf rhs
    rw [show isInt (.int t) = true from rfl, evalS_evalR ys lhs (hlen ▸ hfl)] at hl
    rw [show isInt (.int t) = true from rfl, evalS_evalR ys rhs (hlen ▸ hfr), ← heq] at hr
    exact ⟨_, hl.2, hr.2⟩

/-- `exhaust8p` answers `true` only at `i8` and `u8`, and there it is
    `runP`. At every other type it is `false` whatever the rule. -/
theorem exhaust8p_run {r : Rule} {T : STy} (h : exhaust8p r T = true) :
    ∃ t, T = .int t ∧ (∀ pb, t.bits pb = 8) ∧ runP r = true := by
  cases T with
  | bool => exact Bool.noConfusion (show false = true from h)
  | int t =>
    cases t
    case i8 => exact ⟨.i8, rfl, fun _ => rfl, h⟩
    case u8 => exact ⟨.u8, rfl, fun _ => rfl, h⟩
    all_goals exact Bool.noConfusion (show false = true from h)

/-- Every variable bound to the residue 0. -/
def zeros (t : IntTy) : Sorts → List Val
  | .nil => []
  | .cons _ _ rest => .int t 0 :: zeros t rest

/-- Variables of sort `t` admit the assignment of 0 to each. -/
theorem admits_zeros {pb : Nat} {t : IntTy} :
    ∀ (s : Sorts), allT s = true → Admits pb (.int t) s (zeros t s)
  | .nil, _ => trivial
  | .cons .t _ rest, h =>
    admits_cons_t_int.mpr ⟨0, _, rfl, modulus_pos _, admits_zeros rest h⟩
  | .cons .bool _ _, h => Bool.noConfusion (show false = true from h)

/-- A rule `noConds` passes has no side condition to meet. -/
theorem condsHold_of_noConds {pb : Nat} {T : STy} {env : List Val} :
    ∀ (cs : Conds), noConds cs = true → CondsHold pb T env cs
  | .nil, _ => trivial
  | .cons _ _, h => Bool.noConfusion (show false = true from h)

end Packed

/-- The soundness of the procedure, with no other hypothesis: a rule on
    which `exhaust8p` answers `true` at `T` is `Sound` at `T`. -/
theorem exhaust8p_sound (r : Rule) (T : STy) (h : exhaust8p r T = true) : Sound r T := by
  intro pb env _ hadm _
  obtain ⟨t, rfl, ht, hrun⟩ := Packed.exhaust8p_run h
  obtain ⟨v, hl, hr⟩ := Packed.runP_sound (ht pb) r hrun env hadm
  rw [hl, hr]
  cases r.dir
  · exact ⟨v, rfl, rfl⟩
  · exact .inr ⟨v, rfl, rfl⟩

/-- A rule on which `exhaust8p` answers `true` at `T` says something there
    (`EqsatDecide.Defined`): at every pointer width the assignment of 0 to
    every variable is admitted, the rule has no side condition, and both
    sides are one common value on it. The procedure admits no rule for want
    of an assignment or of a defined left side: a pattern of the lane
    fragment is a value on every assignment. -/
theorem exhaust8p_defined (r : Rule) (T : STy) (h : exhaust8p r T = true) : Defined r T := by
  intro pb _
  obtain ⟨t, rfl, ht, hrun⟩ := Packed.exhaust8p_run h
  cases r with
  | mk d vars lhs rhs cs =>
    obtain ⟨hT, hc, _⟩ := Packed.runP_parts hrun
    have hadm : Admits pb (.int t) vars (Packed.zeros t vars) := Packed.admits_zeros vars hT
    obtain ⟨v, hl, hr⟩ := Packed.runP_sound (ht pb) _ hrun _ hadm
    exact ⟨_, v, hadm, Packed.condsHold_of_noConds cs hc, hl, hr⟩

/-- A rule on which `exhaust8p` answers `true` at `T` has side conditions
    some assignment satisfies there: it has none (the first half of
    `exhaust8p_defined`, in the `eqsat_rules` family's own statement). -/
theorem exhaust8p_satisfiable (r : Rule) (T : STy) (h : exhaust8p r T = true) :
    Satisfiable r T := by
  intro pb hpb
  obtain ⟨env, _, hadm, hc, _⟩ := exhaust8p_defined r T h pb hpb
  exact ⟨env, hadm, hc⟩

end EqsatDecide
