/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCollisionPeeling

/-!
# Deterministic seed extension by a growing common modulus

A degree-M power polynomial cannot vanish at M+1 distinct small residues.
After the ordinary prefix these integer seeds are units. A bounded order
whose public prime tests are clear extends a known common modulus by LCM;
the extension doubles whenever the new seed was not annihilated by M.
The remaining large-order branch must still be handled at sixth-root cost.
-/

namespace RiemannGaussian.SemiprimeSeedLcm

open Polynomial SemiprimeGroupSelection SemiprimeCartesianCompletion
open SemiprimeProgressionPrefix SemiprimeCollisionPeeling

/-- A positive power polynomial misses at least one of the next M+1
distinct integers in a prime field. -/
theorem small_power_nonroot {p M : ℕ} (hp : p.Prime) (hM : 0<M)
    (hsmall : M+1<p) : ∃ k, 0<k ∧ k≤M+1 ∧ (k : ZMod p)^M≠1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let f : Fin (M+1) → ZMod p := fun i => ((i.val+1 : ℕ) : ZMod p)
  have hf : Function.Injective f := by
    intro i j he
    have hei := congrArg ZMod.val he
    have hi : i.val+1<p := by omega
    have hj : j.val+1<p := by omega
    change (((i.val+1 : ℕ) : ZMod p)).val=(((j.val+1 : ℕ) : ZMod p)).val at hei
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hei
    apply Fin.ext
    omega
  by_contra hn
  push Not at hn
  have heval : ∀ i, ((X : (ZMod p)[X])^M-C 1).eval (f i)=0 := by
    intro i
    simp only [eval_sub, eval_pow, eval_X, eval_C, f]
    exact sub_eq_zero.mpr (hn (i.val+1) (by omega) (by omega))
  have hdegree : ((X : (ZMod p)[X])^M-C 1).natDegree<M+1 := by
    rw [natDegree_X_pow_sub_C]
    omega
  have hz := eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    ((X : (ZMod p)[X])^M-C 1) hf heval (by simpa only [Fintype.card_fin] using hdegree)
  exact X_pow_sub_C_ne_zero hM 1 hz

/-- A new order not dividing M increases its positive LCM by at least
a factor two; equality and fractional increases cannot occur. -/
theorem lcm_doubles {M m : ℕ} (hM : 0<M) (hm : 0<m) (hnot : ¬m∣M) :
    2*M≤Nat.lcm M m := by
  have hpos := Nat.lcm_pos hM hm
  obtain ⟨a, ha⟩ := Nat.dvd_lcm_left M m
  have hne : a≠1 := by
    intro he
    have heq : Nat.lcm M m=M := by simpa only [he, mul_one] using ha
    exact hnot (heq ▸ Nat.dvd_lcm_right M m)
  have hapos : 0<a := by nlinarith
  have ha2 : 2≤a := by omega
  nlinarith

/-- Public search for a seed not annihilated by the current exponent. -/
noncomputable def seedChoice (N M : ℕ) : Option ℕ :=
  ((List.range (M+1)).map fun i => i+1).find?
    (fun k => decide ((k : ZMod N)^M≠1))

theorem seedChoice_some {N M k : ℕ} (hs : seedChoice N M=some k) :
    0<k ∧ k≤M+1 ∧ (k : ZMod N)^M≠1 := by
  have hmem := List.mem_of_find?_eq_some hs
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
  have hb := List.mem_range.mp hi
  have htest := List.find?_some hs
  exact ⟨by omega, by omega, by simpa only [decide_eq_true_eq] using htest⟩

/-- The actual public scan cannot exhaust before the prime-field degree
bound. No reference prime enters the scan itself. -/
theorem seedChoice_succeeds {N p M : ℕ} (hp : p.Prime) (hpN : p∣N)
    (hM : 0<M) (hsmall : M+1<p) : ∃ k, seedChoice N M=some k := by
  obtain ⟨k, hk, hkM, hnonroot⟩ := small_power_nonroot hp hM hsmall
  have hn : (k : ZMod N)^M≠1 := by
    intro he
    have hcast := congrArg (ZMod.castHom hpN (ZMod p)) he
    apply hnonroot
    simpa only [map_pow, map_natCast, map_one] using hcast
  have hmem : k∈(List.range (M+1)).map (fun i => i+1) := by
    apply List.mem_map.mpr
    exact ⟨k-1, List.mem_range.mpr (by omega), by omega⟩
  cases hs : seedChoice N M with
  | some k' => exact ⟨k', rfl⟩
  | none =>
    have ht := List.find?_eq_none.mp hs k hmem
    simp only [decide_eq_true_eq] at ht
    contradiction

/-- A failed complete prefix makes every selected small seed a public
unit; this is derived rather than supplied as hidden local-order data. -/
theorem seedChoice_unit_after_prefix {N B M k : ℕ} (hM : 0<M) (hMB : M<B)
    (hcover : B^2<N) (hnone : SemiprimeStrassenPrefix.factorPrefix N B=none)
    (hs : seedChoice N M=some k) : N.Coprime k := by
  obtain ⟨hk, hkM, _⟩ := seedChoice_some hs
  apply SemiprimeStrassenPrefix.prefix_none_coprime_integer hcover hnone hk
  have hB : 1≤B := by omega
  nlinarith

/-- A clear bounded order extends the preceding common modulus and
retains its geometric growth certificate. -/
theorem certified_lcm_extension {p q M e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ) (hM : 0<M) (hmp : M∣p-1) (hmq : M∣q-1)
    (he : 0<e) (hpow : g^e=1) (hnot : g^M≠1)
    (hs : scanProper (p*q) (primePowerValues (p*q) (peelOrder g e) g)=none) :
    0<Nat.lcm M (peelOrder g e) ∧
      Nat.lcm M (peelOrder g e)∣p-1 ∧
      Nat.lcm M (peelOrder g e)∣q-1 ∧
      2*M≤Nat.lcm M (peelOrder g e) := by
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hm := peelOrder_eq_order g he hpow
  have hmpos := (peelOrder_pos_dvd g he).1
  have hclear := primePowerValues_none_clear g hm.symm hmpos hs
  have hmpow : g^(peelOrder g e)=1 := by rw [hm]; exact pow_orderOf_eq_one g
  obtain ⟨hdp, hdq⟩ := SemiprimeCommonOrder.common_modulus_of_public_checks hp hq g hmpos hmpow hclear
  have hnotdvd : ¬peelOrder g e∣M := by
    rw [hm]
    exact fun hd => hnot ((orderOf_dvd_iff_pow_eq_one).mp hd)
  exact ⟨Nat.lcm_pos hM hmpos, Nat.lcm_dvd hmp hdp, Nat.lcm_dvd hmq hdq,
    lcm_doubles hM hmpos hnotdvd⟩

/-- A successful factor, an explicit above-cap seed, or a failed attempt. -/
inductive Route where
  | factor (d : ℕ)
  | largeBase (k : ℕ)
  | unresolved
  deriving DecidableEq

/-- The complete mathematical certificate carried by a successful route. -/
def GoodRoute (N b : ℕ) : Route → Prop
  | .factor d => ProperDivisor N d
  | .largeBase k => ∃ hc : k.Coprime N, b^2<orderOf (ZMod.unitOfCoprime k hc)
  | .unresolved => False

/-- Preserve a checked factor result in the public routing datatype. -/
def factorRoute : Option ℕ → Route
  | some d => .factor d
  | none => .unresolved

/-- Deterministic small-seed loop. A derived order is only accumulated
after its prime-power GCD scan has supplied a clear common certificate. -/
noncomputable def seedLoop (N B b : ℕ) : ℕ → ℕ → Route
  | 0, M => if B≤M then factorRoute (factorProgression N M B) else .unresolved
  | fuel+1, M =>
    if B≤M then factorRoute (factorProgression N M B) else
      match seedChoice N M with
      | none => .unresolved
      | some k =>
        match checkedSignal N ((k : ZMod N)^M-1).val with
        | some d => .factor d
        | none =>
          if hc : k.Coprime N then
            let g := ZMod.unitOfCoprime k hc
            match boundedCollision N b g with
            | none => .largeBase k
            | some (i,j) =>
              let m := peelOrder g (j*b-i)
              match scanProper N (primePowerValues N m g) with
              | some d => .factor d
              | none => seedLoop N B b fuel (Nat.lcm M m)
          else factorRoute (checkedSignal N k)

/-- Sufficient logarithmic fuel discharges every seed and small-order
branch. The only nonfactor outcome is a certified above-cap public unit. -/
theorem seedLoop_progress {p q B b fuel M : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hB : 0<B) (hbudget : p*q≤B^6) (hcover : B^2<p*q)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none)
    (hM : 0<M) (hmp : M∣p-1) (hmq : M∣q-1) (hpay : B≤2^fuel*M) :
    GoodRoute (p*q) b (seedLoop (p*q) B b fuel M) := by
  classical
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hpB := SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hp
    (dvd_mul_right p q) hnone
  induction fuel generalizing M with
  | zero =>
    have hsize : B≤M := by simpa only [pow_zero, one_mul] using hpay
    obtain ⟨d, hd⟩ := factorProgression_semiprime hp hq hpq hB hsize hpB hbudget hmp hmq
    simp only [seedLoop, if_pos hsize, hd, factorRoute, GoodRoute]
    exact factorProgression_sound hd
  | succ fuel ih =>
    by_cases hsize : B≤M
    · obtain ⟨d, hd⟩ := factorProgression_semiprime hp hq hpq hB hsize hpB hbudget hmp hmq
      simp only [seedLoop, if_pos hsize, hd, factorRoute, GoodRoute]
      exact factorProgression_sound hd
    · have hMB : M<B := by omega
      have hsmall : M+1<p :=
        (show M+1≤B by omega).trans_lt ((Nat.le_pow (by decide : 0<2)).trans_lt hpB)
      obtain ⟨k, hseed⟩ := seedChoice_succeeds hp (dvd_mul_right p q) hM hsmall
      have hunit : k.Coprime (p*q) :=
        (seedChoice_unit_after_prefix hM hMB hcover hnone hseed).symm
      let g := ZMod.unitOfCoprime k hunit
      have hg : (g : ZMod (p*q))=(k : ZMod (p*q)) := ZMod.coe_unitOfCoprime k hunit
      have hnot : g^M≠1 := by
        intro he
        have hv := congrArg (fun u : (ZMod (p*q))ˣ => (u : ZMod (p*q))) he
        exact (seedChoice_some hseed).2.2 (by
          simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hv)
      cases hsignal : checkedSignal (p*q) ((k : ZMod (p*q))^M-1).val with
      | some d =>
        simp only [seedLoop, if_neg hsize, hseed, hsignal, GoodRoute]
        exact checkedSignal_sound hsignal
      | none =>
        have hstep : seedLoop (p*q) B b (fuel+1) M=
            (match boundedCollision (p*q) b g with
            | none => .largeBase k
            | some (i,j) =>
              match scanProper (p*q) (primePowerValues (p*q) (peelOrder g (j*b-i)) g) with
              | some d => .factor d
              | none => seedLoop (p*q) B b fuel (Nat.lcm M (peelOrder g (j*b-i)))) := by
          simp only [seedLoop, if_neg hsize, hseed, hsignal, dif_pos hunit]
          rfl
        rw [hstep]
        cases hcollision : boundedCollision (p*q) b g with
        | none =>
          simp only [GoodRoute]
          exact ⟨hunit, boundedCollision_none_large g hcollision⟩
        | some pair =>
          obtain ⟨i,j⟩ := pair
          dsimp only
          obtain ⟨he, _, hpow⟩ := boundedCollision_annihilator g hcollision
          cases hscan : scanProper (p*q) (primePowerValues (p*q) (peelOrder g (j*b-i)) g) with
          | some d => exact scanProper_sound hscan
          | none =>
            obtain ⟨hpositive, hdp, hdq, hdoubles⟩ :=
              certified_lcm_extension hp hq g hM hmp hmq he hpow hnot hscan
            have hnewpay : B≤2^fuel*Nat.lcm M (peelOrder g (j*b-i)) := by
              have hmul := Nat.mul_le_mul_left (2^fuel) hdoubles
              have heq : 2^(fuel+1)*M=2^fuel*(2*M) := by rw [pow_succ]; ring
              rw [heq] at hpay
              exact hpay.trans hmul
            exact ih hpositive hdp hdq hnewpay

/-- Squares and the complete small-factor prefix are checked before
the logarithmically fueled common-modulus loop. -/
noncomputable def routeByWidth (N B : ℕ) : Route :=
  if B<4 then factorRoute (SemiprimeLehmanCoverage.factor N) else
    match SemiprimeCommonOrder.recoverSquare N with
    | some d => .factor d
    | none =>
      match SemiprimeStrassenPrefix.factorPrefix N B with
      | some d => .factor d
      | none => seedLoop N B (2*B) (Nat.clog 2 B) 1

/-- The early classical fallback has a constant numerical-input ceiling. -/
theorem small_width_input_bound {N B : ℕ} (hbudget : N≤B^6) (hsmall : B<4) :
    N≤729 := by
  calc
    N≤B^6 := hbudget
    _≤3^6 := by gcongr; omega
    _=729 := by norm_num

/-- Every semiprime is routed into a proper factor or a certified unit
of order above 4B^2. No seed menu or hidden order premise is assumed. -/
theorem routeByWidth_semiprime {p q B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hbudget : p*q≤B^6) (hlower : (B-1)^6<p*q) :
    GoodRoute (p*q) (2*B) (routeByWidth (p*q) B) := by
  unfold routeByWidth
  split_ifs with hsmall
  · obtain ⟨d, hd, hproper⟩ := SemiprimeLehmanCoverage.factor_semiprime hp hq
    simpa only [hd, factorRoute, GoodRoute] using hproper
  · have hB : 4≤B := by omega
    cases hsquare : SemiprimeCommonOrder.recoverSquare (p*q) with
    | some d => exact SemiprimeCommonOrder.recoverSquare_sound hsquare
    | none =>
      dsimp only
      cases hprefix : SemiprimeStrassenPrefix.factorPrefix (p*q) B with
      | some d => exact SemiprimeStrassenPrefix.prefix_sound hprefix
      | none =>
        dsimp only
        apply seedLoop_progress hp hq hpq (by omega) hbudget
          (SemiprimeStrassenPrefix.sixth_budget_prefix_below_input hB hlower)
          hprefix (by decide) (one_dvd _) (one_dvd _)
        simpa only [mul_one] using Nat.le_pow_clog (by decide : 1<2) B

/-- One public input, with every seed selected and every order derived
inside the procedure. The above-cap branch remains a research frontier. -/
noncomputable def publicRoute (N : ℕ) : Route :=
  routeByWidth N (SemiprimeLehmanCoverage.sixthWidth N)

/-- Universal factor-or-large-order coverage for the literal N-only
procedure, including squares and arbitrary semiprime factor ratios. -/
theorem publicRoute_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    GoodRoute (p*q) (2*SemiprimeLehmanCoverage.sixthWidth (p*q)) (publicRoute (p*q)) := by
  have hbudget := SemiprimeLehmanCoverage.sixthWidth_upper (p*q)
  have hlower := SemiprimeLehmanCoverage.sixthWidth_lower (Nat.mul_pos hp.pos hq.pos)
  unfold publicRoute
  rcases le_total p q with hpq | hqp
  · exact routeByWidth_semiprime hp hq hpq hbudget hlower
  · have h := routeByWidth_semiprime (B:=SemiprimeLehmanCoverage.sixthWidth (p*q)) hq hp hqp
      (by simpa only [Nat.mul_comm q p] using hbudget)
      (by simpa only [Nat.mul_comm q p] using hlower)
    simpa only [Nat.mul_comm q p] using h

/-- Retain each modulus at which the literal loop attempts seed selection. -/
noncomputable def seedModuli (N B b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel+1, M =>
    if B≤M then [] else M::
      match seedChoice N M with
      | none => []
      | some k =>
        match checkedSignal N ((k : ZMod N)^M-1).val with
        | some _ => []
        | none =>
          if hc : k.Coprime N then
            let g := ZMod.unitOfCoprime k hc
            match boundedCollision N b g with
            | none => []
            | some (i,j) =>
              let m := peelOrder g (j*b-i)
              match scanProper N (primePowerValues N m g) with
              | some _ => []
              | none => seedModuli N B b fuel (Nat.lcm M m)
          else []

/-- The actual control path has at most fuel seed stages and at most
B*fuel candidate power tests, including all small-order extensions. -/
theorem seedModuli_budget (N B b fuel M : ℕ) :
    (seedModuli N B b fuel M).length≤fuel ∧
      ((seedModuli N B b fuel M).map (fun a => a+1)).sum≤B*fuel := by
  induction fuel generalizing M with
  | zero => simp only [seedModuli, List.length_nil, List.map_nil, List.sum_nil, mul_zero, le_refl, and_self]
  | succ fuel ih =>
    rw [seedModuli]
    split_ifs with hsize
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    · have hstep : ∀ tail : List ℕ, tail.length≤fuel ∧
          (tail.map (fun a => a+1)).sum≤B*fuel →
          (M::tail).length≤fuel+1 ∧ ((M::tail).map (fun a => a+1)).sum≤B*(fuel+1) := by
        intro tail ht
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        constructor
        · omega
        · rw [Nat.mul_add, Nat.mul_one]
          omega
      apply hstep
      repeat' first
        | exact ih _
        | exact ⟨Nat.zero_le _, Nat.zero_le _⟩
        | split
      dsimp only
      repeat' first
        | exact ih _
        | exact ⟨Nat.zero_le _, Nat.zero_le _⟩
        | split

/-- With the literal public fuel and block, all candidate powers fit
B*clog(2,B), and the two lookup lists fit 4B*clog(2,B) records in total.
Sorting, stripping and polynomial arithmetic are separate work categories. -/
theorem logarithmic_setup_budget (N B : ℕ) :
    ((seedModuli N B (2*B) (Nat.clog 2 B) 1).map (fun a => a+1)).sum≤B*Nat.clog 2 B ∧
      4*B*(seedModuli N B (2*B) (Nat.clog 2 B) 1).length≤4*B*Nat.clog 2 B := by
  have h := seedModuli_budget N B (2*B) (Nat.clog 2 B) 1
  exact ⟨h.2, Nat.mul_le_mul_left (4*B) h.1⟩

/-- The saved Mersenne control has both primes beyond the prefix and
an actual common order below the public sixth-root width. -/
theorem control_mersenne_arithmetic :
    Nat.Prime 13367 ∧ Nat.Prime 164511353 ∧ 13367*164511353=2199023255551 ∧
      114^6<(2199023255551 : ℕ) ∧ 2199023255551≤115^6 ∧ (115 : ℕ)^2<13367 := by
  norm_num

/-- The small-order control's public annihilating power is exact. -/
theorem control_mersenne_power : (2 : ZMod 2199023255551)^41=1 := by
  reduce_mod_char

/-- This literal order is verified from public powers, not supplied to
the runtime loop as numerical advice. -/
theorem control_mersenne_order (g : (ZMod 2199023255551)ˣ)
    (hg : (g : ZMod 2199023255551)=2) : orderOf g=41 := by
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  have hpow : g^41=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using control_mersenne_power
  have hne : g≠1 := by
    intro he
    have hv := congrArg (fun u : (ZMod 2199023255551)ˣ => (u : ZMod 2199023255551)) he
    simp only [hg, Units.val_one] at hv
    exact (by decide : (2 : ZMod 2199023255551)≠1) hv
  exact orderOf_eq_prime hpow hne

set_option maxRecDepth 32768 in
/-- The actual small-integer scan leaves the order-41 seed for base three. -/
theorem control_mersenne_next_seed : seedChoice 2199023255551 41=some 3 := by
  have hlist : (List.range (41+1)).map (fun i => i+1)=
      1::2::3::(List.range' 3 39).map (fun i => i+1) := by decide
  have hthree : (3 : ZMod 2199023255551)^41≠1 := by decide
  rw [seedChoice, hlist]
  simp [List.find?, control_mersenne_power, hthree]

/-- All semiprime and width premises of the new route are discharged
on the prefix-clear control with a formerly unresolved small order. -/
theorem control_mersenne_routing :
    GoodRoute 2199023255551 230 (routeByWidth 2199023255551 115) := by
  obtain ⟨hp, hq, hprod, hlower, hbudget, _⟩ := control_mersenne_arithmetic
  have h := routeByWidth_semiprime hp hq (by norm_num)
    (B:=115) (by simpa only [hprod] using hbudget)
    (by simpa only [hprod, show (115-1 : ℕ)=114 from rfl] using hlower)
  simpa only [hprod] using h

end RiemannGaussian.SemiprimeSeedLcm
