/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeProgressionPrefix

/-!
# Derive an exact order from retained collision labels

A positive collision distance is an annihilator, not necessarily the
order. The reduction below uses its ordinary prime factorization and
public power equalities to remove excess prime powers. Its input does
not include the numerical order. The resulting exact-order prime tests
feed the already proved common-modulus progression branch.

This closes the information transport for a bounded collision. It does
not establish universal seed coverage, handle orders beyond the lookup
cap, or prove the complete backend bit-operation bound.
-/

namespace RiemannGaussian.SemiprimeCollisionPeeling

open SemiprimeGroupSelection SemiprimeCartesianCompletion
open SemiprimeProgressionPrefix

/-- Find the first prime whose removal still annihilates the public base. -/
def removablePrime {G : Type*} [Group G] [DecidableEq G] (g : G) (m : ℕ) : Option ℕ :=
  m.primeFactorsList.find? (fun r => decide (g^(m/r)=1))

theorem removablePrime_some {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m r : ℕ} (h : removablePrime g m=some r) :
    r.Prime ∧ r∣m ∧ g^(m/r)=1 := by
  have hmem := List.mem_of_find?_eq_some h
  have htest := List.find?_some h
  exact ⟨Nat.prime_of_mem_primeFactorsList hmem,
    Nat.dvd_of_mem_primeFactorsList hmem, by simpa only [decide_eq_true_eq] using htest⟩

theorem removablePrime_none {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m : ℕ} (hpos : 0<m) (h : removablePrime g m=none) :
    ∀ r, r.Prime → r∣m → g^(m/r)≠1 := by
  intro r hr hrdvd
  have hmem := (Nat.mem_primeFactorsList_iff_dvd hpos.ne' hr).mpr hrdvd
  have hn := List.find?_eq_none.mp h r hmem
  simpa only [decide_eq_true_eq] using hn

/-- Repeatedly strip a prime using a public power equality. Zero input
is totalized to zero; every collision application supplies positive input. -/
def peelOrder {G : Type*} [Group G] [DecidableEq G] (g : G) (m : ℕ) : ℕ :=
  if _hpos : 0<m then
    match _h : removablePrime g m with
    | none => m
    | some r => peelOrder g (m/r)
  else 0
termination_by m
decreasing_by
  exact Nat.div_lt_self _hpos (removablePrime_some g _h).1.one_lt

/-- No numerical order is an input: public power tests recover it from
any positive annihilator, including a nonexact collision distance. -/
theorem peelOrder_eq_order {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m : ℕ} (hpos : 0<m) (hpow : g^m=1) : peelOrder g m=orderOf g := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [peelOrder, dif_pos hpos]
    cases hrem : removablePrime g m with
    | none =>
      change m=orderOf g
      exact (orderOf_eq_of_pow_and_pow_div_prime hpos hpow
        (removablePrime_none g hpos hrem)).symm
    | some r =>
      change peelOrder g (m/r)=orderOf g
      obtain ⟨hr, hrdvd, hquotpow⟩ := removablePrime_some g hrem
      exact ih (m/r) (Nat.div_lt_self hpos hr.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hpos hrdvd) hr.pos) hquotpow

/-- Every stripping result remains a positive divisor of its input,
including outside the annihilator case. -/
theorem peelOrder_pos_dvd {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m : ℕ} (hpos : 0<m) : 0<peelOrder g m ∧ peelOrder g m∣m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [peelOrder, dif_pos hpos]
    cases hrem : removablePrime g m with
    | none => exact ⟨hpos, dvd_refl m⟩
    | some r =>
      obtain ⟨hr, hrdvd, _⟩ := removablePrime_some g hrem
      obtain ⟨hpositive, hdivides⟩ := ih (m/r) (Nat.div_lt_self hpos hr.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hpos hrdvd) hr.pos)
      exact ⟨hpositive, hdivides.trans (Nat.div_dvd_of_dvd hrdvd)⟩

/-- Count the successful stripping divisions, retaining the same path. -/
def peelRounds {G : Type*} [Group G] [DecidableEq G] (g : G) (m : ℕ) : ℕ :=
  if _hpos : 0<m then
    match _h : removablePrime g m with
    | none => 0
    | some r => 1+peelRounds g (m/r)
  else 0
termination_by m
decreasing_by
  exact Nat.div_lt_self _hpos (removablePrime_some g _h).1.one_lt

/-- Every successful division removes at least a factor two. This
bounds the recursion logarithmically; prime-search costs are separate. -/
theorem peelRounds_pow_le {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m : ℕ} (hpos : 0<m) : 2^(peelRounds g m)≤m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [peelRounds, dif_pos hpos]
    cases hrem : removablePrime g m with
    | none => change (1 : ℕ)≤m; omega
    | some r =>
      change 2^(1+peelRounds g (m/r))≤m
      obtain ⟨hr, hrdvd, _⟩ := removablePrime_some g hrem
      have hi := ih (m/r) (Nat.div_lt_self hpos hr.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hpos hrdvd) hr.pos)
      calc
        2^(1+peelRounds g (m/r))=2*2^(peelRounds g (m/r)) := by rw [pow_add]; simp
        _≤2*(m/r) := Nat.mul_le_mul_left 2 hi
        _≤r*(m/r) := Nat.mul_le_mul_right (m/r) hr.two_le
        _=m := Nat.mul_div_cancel' hrdvd

/-- The retained prime factor list has logarithmic length. -/
theorem primeFactors_length_pow_le {m : ℕ} (hpos : 0<m) :
    2^m.primeFactorsList.length≤m := by
  have hlist : ∀ l : List ℕ, (∀ r∈l, 2≤r) → 2^l.length≤l.prod := by
    intro l
    induction l with
    | nil => simp
    | cons r tail ih =>
      intro h
      have hr := h r List.mem_cons_self
      have ht := ih (fun s hs => h s (List.mem_cons_of_mem r hs))
      simp only [List.length_cons, List.prod_cons, pow_succ]
      simpa only [Nat.mul_comm tail.prod r] using Nat.mul_le_mul ht hr
  simpa only [Nat.prod_primeFactorsList hpos.ne'] using
    hlist m.primeFactorsList (fun r hr => (Nat.prime_of_mem_primeFactorsList hr).two_le)

/-- Public power tests made by the literal first-removable-prime search. -/
def primeSearchPowerCount {G : Type*} [Group G] [DecidableEq G]
    (g : G) (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r::tail => 1+if g^(m/r)=1 then 0 else primeSearchPowerCount g m tail

theorem primeSearchPowerCount_le {G : Type*} [Group G] [DecidableEq G]
    (g : G) (m : ℕ) (l : List ℕ) : primeSearchPowerCount g m l≤l.length := by
  induction l with
  | nil => rfl
  | cons r tail ih =>
    simp only [primeSearchPowerCount, List.length_cons]
    split_ifs <;> omega

/-- All stripping-search power queries, before final GCD certification. -/
def peelPowerCount {G : Type*} [Group G] [DecidableEq G] (g : G) (m : ℕ) : ℕ :=
  if _hpos : 0<m then
    primeSearchPowerCount g m m.primeFactorsList+
      match _h : removablePrime g m with
      | none => 0
      | some r => peelPowerCount g (m/r)
  else 0
termination_by m
decreasing_by
  exact Nat.div_lt_self _hpos (removablePrime_some g _h).1.one_lt

/-- There are at most (rounds+1) searches, each with at most the input's
prime-list length. Both factors are logarithmic in a positive input. -/
theorem peelPowerCount_le {G : Type*} [Group G] [DecidableEq G] (g : G)
    {m : ℕ} (hpos : 0<m) :
    peelPowerCount g m≤(peelRounds g m+1)*m.primeFactorsList.length := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [peelPowerCount, peelRounds, dif_pos hpos, dif_pos hpos]
    cases hrem : removablePrime g m with
    | none =>
      simpa only [add_zero, zero_add, one_mul] using
        primeSearchPowerCount_le g m m.primeFactorsList
    | some r =>
      obtain ⟨hr, hrdvd, _⟩ := removablePrime_some g hrem
      have hi := ih (m/r) (Nat.div_lt_self hpos hr.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hpos hrdvd) hr.pos)
      have hlen := (Nat.primeFactorsList_sublist_of_dvd
        (Nat.div_dvd_of_dvd hrdvd) hpos.ne').length_le
      have hsearch := primeSearchPowerCount_le g m m.primeFactorsList
      have hm := Nat.mul_le_mul_left (peelRounds g (m/r)+1) hlen
      dsimp only
      nlinarith

/-- Original public power-test residues, with all prime labels retained. -/
noncomputable def primePowerValues (N m : ℕ) (g : (ZMod N)ˣ) : List ℕ :=
  m.primeFactorsList.map fun r => (((g^(m/r) : (ZMod N)ˣ) : ZMod N)-1).val

theorem primePowerValues_length (N m : ℕ) (g : (ZMod N)ˣ) :
    (primePowerValues N m g).length=m.primeFactorsList.length := by
  simp only [primePowerValues, List.length_map]

/-- The clear public certificate suppresses every proper-factor test. -/
theorem primePowerValues_clear_none {N m : ℕ} (g : (ZMod N)ˣ)
    (hclear : ∀ r, r.Prime → r∣m →
      N.gcd (((g^(m/r) : (ZMod N)ˣ) : ZMod N)-1).val=1) :
    scanProper N (primePowerValues N m g)=none := by
  apply (scanProper_none_iff _ _).mpr
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
  have hc := hclear r (Nat.prime_of_mem_primeFactorsList hr)
    (Nat.dvd_of_mem_primeFactorsList hr)
  simp only [checkedSignal, hc, lt_self_iff_false, false_and, if_false]

/-- For an exact positive order, a failed proper-factor scan is itself
a clear prime-divisor certificate; whole-modulus tests are excluded. -/
theorem primePowerValues_none_clear {N m : ℕ} [NeZero N] (g : (ZMod N)ˣ)
    (hm : orderOf g=m) (hpos : 0<m)
    (hs : scanProper N (primePowerValues N m g)=none) :
    ∀ r, r.Prime → r∣m → N.gcd (((g^(m/r) : (ZMod N)ˣ) : ZMod N)-1).val=1 := by
  intro r hr hrdvd
  let z : ZMod N := ((g^(m/r) : (ZMod N)ˣ) : ZMod N)-1
  have hmem : z.val∈primePowerValues N m g :=
    List.mem_map.mpr ⟨r, (Nat.mem_primeFactorsList_iff_dvd hpos.ne' hr).mpr hrdvd, rfl⟩
  have hn := (scanProper_none_iff _ _).mp hs z.val hmem
  have hnotN : N.gcd z.val≠N := by
    intro he
    have hz := SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus z he
    exact order_prime_test_ne_one g hm hpos hr hrdvd (Units.ext (sub_eq_zero.mp hz))
  have hNpos : 0<N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hgpos := Nat.gcd_pos_of_pos_left z.val hNpos
  have hgle := Nat.gcd_le_left z.val hNpos
  change N.gcd z.val=1
  by_contra he
  have hproper : 1<N.gcd z.val ∧ N.gcd z.val<N := by omega
  have hsome : checkedSignal N z.val=some (N.gcd z.val) := by
    simp only [checkedSignal, if_pos hproper]
  rw [hsome] at hn
  contradiction

/-- Exact prime-power tests expose a proper factor or feed one common
progression. The numerical order is derived internally from e. -/
noncomputable def factorAnnihilator (N B : ℕ) (g : (ZMod N)ˣ) (e : ℕ) : Option ℕ :=
  let m := peelOrder g e
  match scanProper N (primePowerValues N m g) with
  | some d => some d
  | none => if B≤m then factorProgression N m B else none

theorem factorAnnihilator_sound {N B e d : ℕ} (g : (ZMod N)ˣ)
    (h : factorAnnihilator N B g e=some d) : ProperDivisor N d := by
  unfold factorAnnihilator at h
  dsimp only at h
  cases hs : scanProper N (primePowerValues N (peelOrder g e) g) with
  | some d' =>
    simp only [hs, Option.some.injEq] at h
    subst d'
    exact scanProper_sound hs
  | none =>
    simp only [hs] at h
    split_ifs at h with hsize
    exact factorProgression_sound h

/-- Queries after order stripping: one prime-power GCD scan and the
progression's column/leaf recovery. Polynomial construction is separate. -/
noncomputable def annihilatorGcdCount (N B : ℕ) (g : (ZMod N)ˣ) (e : ℕ) : ℕ :=
  let m := peelOrder g e
  scanGcdCount N (primePowerValues N m g)+
    match scanProper N (primePowerValues N m g) with
    | some _ => 0
    | none => if B≤m then
        recoveryGcdCount N (blockLeaves N m B) (blockColumns N m B) else 0

theorem annihilatorGcdCount_le {N B e : ℕ} (g : (ZMod N)ˣ) (he : 0<e) :
    annihilatorGcdCount N B g e≤e.primeFactorsList.length+2*B := by
  have hscan := scanGcdCount_le N (primePowerValues N (peelOrder g e) g)
  rw [primePowerValues_length] at hscan
  have hdiv := (peelOrder_pos_dvd g he).2
  have hlen := (Nat.primeFactorsList_sublist_of_dvd hdiv he.ne').length_le
  have hrec := factorProgression_gcd_count N (peelOrder g e) B
  unfold annihilatorGcdCount
  dsimp only
  split
  · omega
  · split_ifs <;> omega

/-- The actual public reduction succeeds for every useful annihilator.
The size premise concerns the true order for coverage only; that order
is not supplied to factorAnnihilator. -/
theorem factorAnnihilator_semiprime {p q B e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (g : (ZMod (p*q))ˣ) (he : 0<e) (hpow : g^e=1)
    (hB : 0<B) (hsize : B≤orderOf g) (hbudget : p*q≤B^6) (hcover : B^2<p*q)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) :
    ∃ d, factorAnnihilator (p*q) B g e=some d := by
  classical
  have hm := peelOrder_eq_order g he hpow
  obtain htests | hprogression := known_order_factor_or_progression hp hq hpq g
    (m:=peelOrder g e) hm.symm hB (by simpa only [hm] using hsize) hbudget hcover hnone
  · obtain ⟨r, hr, hrdvd, d, hd⟩ := htests
    have hpos : 0<peelOrder g e := by simpa only [hm] using hB.trans_le hsize
    have hmem : (((g^((peelOrder g e)/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val∈
        primePowerValues (p*q) (peelOrder g e) g := by
      exact List.mem_map.mpr ⟨r, (Nat.mem_primeFactorsList_iff_dvd hpos.ne' hr).mpr hrdvd, rfl⟩
    cases hs : scanProper (p*q) (primePowerValues (p*q) (peelOrder g e) g) with
    | some d' => exact ⟨d', by simp only [factorAnnihilator, hs]⟩
    | none =>
      have hn := (scanProper_none_iff _ _).mp hs _ hmem
      rw [hd] at hn
      contradiction
  · obtain ⟨d, hd⟩ := hprogression
    cases hs : scanProper (p*q) (primePowerValues (p*q) (peelOrder g e) g) with
    | some d' => exact ⟨d', by simp only [factorAnnihilator, hs]⟩
    | none =>
      refine ⟨d, ?_⟩
      simpa only [factorAnnihilator, hs, if_pos (hm ▸ hsize)] using hd

/-- A complete bounded collision branch: retain labels, derive their
annihilator, reduce it and attempt the certified public factor tests. -/
noncomputable def factorCollision (N B b : ℕ) (g : (ZMod N)ˣ) : Option ℕ :=
  match boundedCollision N b g with
  | none => none
  | some (i,j) => factorAnnihilator N B g (j*b-i)

theorem factorCollision_sound {N B b d : ℕ} (g : (ZMod N)ˣ)
    (h : factorCollision N B b g=some d) : ProperDivisor N d := by
  unfold factorCollision at h
  split at h
  · contradiction
  · exact factorAnnihilator_sound g h

/-- The literal sorted lookup and stripping function recover every
prefix-clear semiprime when the supplied unit's order is in [B,b^2].
Neither hidden factors nor the numerical order are algorithm inputs. -/
theorem factorCollision_semiprime {p q B b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (g : (ZMod (p*q))ˣ) (hB : 0<B)
    (hsize : B≤orderOf g) (hcap : orderOf g≤b^2) (hbudget : p*q≤B^6)
    (hcover : B^2<p*q)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) :
    ∃ d, factorCollision (p*q) B b g=some d := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  obtain ⟨⟨i, j⟩, hs⟩ := boundedCollision_succeeds g hcap
  obtain ⟨he, _, hpow⟩ := boundedCollision_annihilator g hs
  obtain ⟨d, hd⟩ := factorAnnihilator_semiprime hp hq hpq g he hpow hB hsize
    hbudget hcover hnone
  exact ⟨d, by simp only [factorCollision, hs, hd]⟩

/-- The saved order-four control starts from the nonexact annihilator
eight; reduction derives four rather than receiving it as input. -/
theorem control_nonexact_peeling (g : (ZMod 2929)ˣ)
    (hg : (g : ZMod 2929)=2535) : peelOrder g 8=4 := by
  obtain ⟨hpow, hclear⟩ := control_small_common_certificate g hg
  have hm : orderOf g=4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro r hr hrdvd he
    have hc := hclear r hr hrdvd
    rw [he, Units.val_one, sub_self, ZMod.val_zero, Nat.gcd_zero_right] at hc
    contradiction
  have hpow8 : g^8=1 := by
    change g^(4*2)=1
    rw [pow_mul, hpow, one_pow]
  rw [peelOrder_eq_order g (by decide) hpow8, hm]

/-- The literal public annihilator reduction and progression return
29 on the control that defeated the previous carry scan. -/
theorem control_nonexact_factor (g : (ZMod 2929)ˣ)
    (hg : (g : ZMod 2929)=2535) : factorAnnihilator 2929 4 g 8=some 29 := by
  have hpeel := control_nonexact_peeling g hg
  have hclear := (control_small_common_certificate g hg).2
  have hscan := primePowerValues_clear_none g hclear
  simpa only [factorAnnihilator, hpeel, hscan, show (4 : ℕ)≤4 from le_rfl, if_true] using
    control_small_progression_result

/-- The formerly unknown rough control now passes through the actual
sorted lookup and internally derived order to a proper divisor. -/
theorem control_active_rough_factor (g : (ZMod 13747)ˣ)
    (hg : (g : ZMod 13747)=4) : ∃ d, factorCollision 13747 5 10 g=some d := by
  have hm := (SemiprimeCommonOrder.control_active_rough_kernel_order g hg).1
  apply factorCollision_semiprime (p:=59) (q:=233) (by norm_num) (by norm_num)
    (by norm_num) g (by norm_num) (by rw [hm]; norm_num) (by rw [hm]; norm_num)
    (by norm_num) (by norm_num)
  apply (SemiprimeStrassenPrefix.prefix_none_iff_clear (by norm_num)).mpr
  norm_num [SemiprimeGroupCoverage.prefixProduct_eq_factorial]

end RiemannGaussian.SemiprimeCollisionPeeling
