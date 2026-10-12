/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import RiemannGaussian.ZetaPrimeMomentCoherence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0

/-!
# Broad symmetric binomial corridors and their literal prime window

Keep every actual binomial and prime-power valuation. The interval
`a < k < n-a` has its native integer endpoints. For `3*a<n`, its complete
first-carry intersection is just `d<=n<=d+a`, at EVERY positive denominator.
For large actual primes this is the exact GCD valuation; no independent
prime cancellation is supplied by this identity.
-/

namespace RiemannGaussian.ArithmeticOperatorKummerCorridorAudit
noncomputable section
open Complex Filter MeasureTheory Set
open ArithmeticOperatorKummerCutoff SuzukiCarryCorrelation
open scoped BigOperators Classical Topology

/-- The literal non-prefix symmetric split interval, without relaxed endpoints. -/
def corridorSplits (n a : ℕ) : Finset ℕ := Finset.Ioo a (n-a)

/-- GCD of every selected actual binomial coefficient, including all valuations. -/
def corridorGcd (n a : ℕ) : ℕ := (corridorSplits n a).gcd n.choose

theorem midpoint_mem {n a : ℕ} (hn : 2≤n) (ha : 3*a<n) :
    n/2∈corridorSplits n a := by
  simp only [corridorSplits,Finset.mem_Ioo]
  omega

theorem split_bounds {n a k : ℕ} (hk : k∈corridorSplits n a) :
    0<k ∧ k<n := by
  have h := Finset.mem_Ioo.mp hk
  have hh := Nat.sub_le n a
  omega

theorem corridorGcd_ne_zero {n a : ℕ} (hn : 2≤n) (ha : 3*a<n) :
    corridorGcd n a≠0 := by
  exact Finset.gcd_ne_zero_iff.mpr ⟨n/2,midpoint_mem hn ha,
    Nat.choose_ne_zero (Nat.div_le_self _ _)⟩

theorem carry_le_one (a b d : ℕ) : binomialCarry a b d≤1 := by
  have h := Nat.add_div_le_div_add_div_add_one a b d
  unfold binomialCarry
  omega

theorem carry_zero_of_dvd_right {a b d : ℕ} (hb : d∣b) :
    binomialCarry a b d=0 := by
  simp only [binomialCarry,Nat.add_div_of_dvd_left hb]
  omega

theorem carry_zero_of_dvd_left {a b d : ℕ} (ha : d∣a) :
    binomialCarry a b d=0 := by
  simp only [binomialCarry,Nat.add_div_of_dvd_right ha]
  omega

/-- The entire corridor's first-order intersection is a single native
window. This theorem uses no primality or arithmetic coefficient assumption. -/
theorem all_firstCarry_iff {n a d : ℕ} (hn : 2≤n) (ha : 3*a<n) (hd : 0<d) :
    (∀ k∈corridorSplits n a,binomialCarry (n-k) k d=1) ↔ d≤n ∧ n≤d+a := by
  constructor
  · intro hall
    have hdn : d≤n := by
      by_contra h
      have hnd : n<d := by omega
      have hk := split_bounds (midpoint_mem hn ha)
      have hc : binomialCarry (n-n/2) (n/2) d=0 := by
        simp only [binomialCarry,Nat.sub_add_cancel (Nat.div_le_self n 2),
          Nat.div_eq_of_lt hnd,Nat.div_eq_of_lt (hk.2.trans hnd),
          Nat.div_eq_of_lt ((Nat.sub_le n (n/2)).trans_lt hnd)]
      have hh := hall _ (midpoint_mem hn ha)
      omega
    refine ⟨hdn,?_⟩
    by_contra h
    have hbad : d+a<n := by omega
    by_cases h2 : n<2*d
    · have hk : n-d∈corridorSplits n a := by
        simp only [corridorSplits,Finset.mem_Ioo]
        omega
      have hv : d∣n-(n-d) := by simpa only [Nat.sub_sub_self hdn] using dvd_refl d
      have hc := carry_zero_of_dvd_left (b := n-d) hv
      have hh := hall _ hk
      omega
    · by_cases h3 : n≤3*d
      · have hk : d∈corridorSplits n a := by
          simp only [corridorSplits,Finset.mem_Ioo]
          omega
        have hc := carry_zero_of_dvd_right (a := n-d) (dvd_refl d)
        have hh := hall _ hk
        omega
      · let q := n/(3*d)
        let k := (q+1)*d
        have hmod := Nat.mod_lt n (show 0<3*d by omega)
        have hdiv := Nat.mod_add_div n (3*d)
        have hkb : n<3*k ∧ 3*k≤2*n := by
          dsimp [k,q]
          constructor <;> nlinarith [Nat.zero_le (n%(3*d))]
        have han : a≤n := by omega
        have hsub := Nat.sub_add_cancel han
        have hk : k∈corridorSplits n a := by
          simp only [corridorSplits,Finset.mem_Ioo]
          constructor <;> omega
        have hkd : d∣k := ⟨q+1,by dsimp [k]; ring⟩
        have hc := carry_zero_of_dvd_right (a := n-k) hkd
        have hh := hall _ hk
        omega
  · rintro ⟨hdn,hna⟩ k hk
    obtain ⟨hka,hkn⟩ := Finset.mem_Ioo.mp hk
    have hle : k≤n := by omega
    have hkd : k<d := by omega
    have hnd : n-k<d := by omega
    have hq : n/d=1 := by
      have hlo := (Nat.le_div_iff_mul_le hd).mpr (show 1*d≤n by omega)
      have hup := (Nat.div_lt_iff_lt_mul hd).mpr (show n<2*d by omega)
      omega
    simp only [binomialCarry,Nat.sub_add_cancel hle,hq,
      Nat.div_eq_of_lt hkd,Nat.div_eq_of_lt hnd]

/-- Exact indicator before the prime/valuation specialization. -/
def firstIntersection (n a d : ℕ) : ℕ :=
  if ∀ k∈corridorSplits n a,binomialCarry (n-k) k d=1 then 1 else 0

theorem firstIntersection_eq {n a d : ℕ} (hn : 2≤n) (ha : 3*a<n) (hd : 0<d) :
    firstIntersection n a d=if d≤n ∧ n≤d+a then 1 else 0 := by
  simp only [firstIntersection,all_firstCarry_iff hn ha hd]

/-- Every positive prime-power carry is retained; the higher ones really
have empty support when the literal row lies below p squared. -/
theorem choose_factorization_first {p n k : ℕ} (hp : p.Prime) (hk : k≤n)
    (hn : 0<n) (hlarge : n<p^2) :
    (n.choose k).factorization p=binomialCarry (n-k) k p := by
  let : Fact p.Prime := ⟨hp⟩
  have hsum : n-k+k=n := Nat.sub_add_cancel hk
  have hlog : Nat.log p (n-k+k)<2 := by
    rw [hsum]
    exact (Nat.log_lt_iff_lt_pow hp.one_lt hn.ne').mpr hlarge
  have he := valuation_eq_carry_count (a := n-k) (b := k) hlog
  have hi : Finset.Ico (1 : ℕ) 2={1} := by
    ext i
    simp only [Finset.mem_Ico,Finset.mem_singleton]
    omega
  have hc : binomialCarry (n-k) k p=if p≤(n-k)%p+k%p then 1 else 0 := by
    unfold binomialCarry
    rw [Nat.add_div hp.pos]
    split_ifs <;> omega
  rw [Nat.factorization_def _ hp]
  rw [hsum,hi] at he
  simp only [pow_one,Finset.filter_singleton] at he
  rw [he,hc]
  split_ifs <;> simp_all [add_comm]
  omega

/-- The exact GCD valuation on large actual primes, including the original
binomial endpoints. No approximation of a prime-power order is used. -/
theorem corridorGcd_factorization_large {p n a : ℕ} (hp : p.Prime)
    (hn : 2≤n) (ha : 3*a<n) (hlarge : n<p^2) :
    (corridorGcd n a).factorization p=if p≤n ∧ n≤p+a then 1 else 0 := by
  have hg := corridorGcd_ne_zero hn ha
  have hfac (k : ℕ) (hk : k∈corridorSplits n a) :
      (n.choose k).factorization p=binomialCarry (n-k) k p :=
    choose_factorization_first hp (split_bounds hk).2.le (by omega) hlarge
  by_cases hwindow : p≤n ∧ n≤p+a
  · rw [ite_eq_left hwindow]
    have hall := (all_firstCarry_iff hn ha hp.pos).mpr hwindow
    have hlo : p∣corridorGcd n a := by
      apply Finset.dvd_gcd
      intro k hk
      have hkn := (split_bounds hk).2.le
      have hd := (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr
        (show 1≤(n.choose k).factorization p by rw [hfac k hk,hall k hk])
      simpa only [pow_one] using hd
    have hle := (Nat.factorization_le_iff_dvd hg
      (Nat.choose_ne_zero (Nat.div_le_self n 2))).mpr
      (Finset.gcd_dvd (f := n.choose) (midpoint_mem hn ha)) p
    rw [hfac _ (midpoint_mem hn ha),hall _ (midpoint_mem hn ha)] at hle
    have hge := (hp.pow_dvd_iff_le_factorization hg).mp
      (show p^1∣corridorGcd n a by simpa only [pow_one] using hlo)
    omega
  · rw [ite_eq_right hwindow]
    have hnot := mt (all_firstCarry_iff hn ha hp.pos).mp hwindow
    push Not at hnot
    obtain ⟨k,hk,hbad⟩ := hnot
    have hc := carry_le_one (n-k) k p
    have hzero : binomialCarry (n-k) k p=0 := by omega
    have hle := (Nat.factorization_le_iff_dvd hg
      (Nat.choose_ne_zero (split_bounds hk).2.le)).mpr (Finset.gcd_dvd hk) p
    rw [hfac k hk,hzero] at hle
    omega

/-- Uniform Kummer ceiling at the ORIGINAL physical dyadic cutoff. -/
theorem choose_factorization_le_orders {p n k J : ℕ} (hp : p.Prime)
    (hk : k≤n) (hX : n≤2^(2*J)) : (n.choose k).factorization p≤2*J := by
  let : Fact p.Prime := ⟨hp⟩
  have hsum : n-k+k=n := Nat.sub_add_cancel hk
  have hlog : Nat.log p (n-k+k)<2*J+1 := by
    rw [hsum]
    apply Nat.log_lt_of_lt_pow' (by omega)
    exact (hX.trans (Nat.pow_le_pow_left hp.two_le _)).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt (by omega))
  have he := valuation_eq_carry_count (a := n-k) (b := k) hlog
  rw [hsum] at he
  rw [Nat.factorization_def _ hp,he]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [Nat.card_Ico])

theorem corridorGcd_factorization_le_orders {p n a J : ℕ} (hp : p.Prime)
    (hn : 2≤n) (ha : 3*a<n) (hX : n≤2^(2*J)) :
    (corridorGcd n a).factorization p≤2*J := by
  have hh := (Nat.factorization_le_iff_dvd (corridorGcd_ne_zero hn ha)
    (Nat.choose_ne_zero (Nat.div_le_self n 2))).mpr
    (Finset.gcd_dvd (f := n.choose) (midpoint_mem hn ha)) p
  exact hh.trans (choose_factorization_le_orders hp (Nat.div_le_self n 2) hX)

/-- All prime divisors of the selected GCD are genuine primes at most n. -/
theorem corridorGcd_prime_support {n a : ℕ} (hn : 2≤n) (ha : 3*a<n) :
    ∀ p∈(corridorGcd n a).primeFactors,p.Prime ∧ p≤n := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨hprime,?_⟩
  by_contra h
  have hnp : n<p := by omega
  have hpp : n<p^2 := hnp.trans_le (by nlinarith [hprime.two_le])
  have hz := corridorGcd_factorization_large hprime hn ha hpp
  have hv : (corridorGcd n a).factorization p≠0 := Finsupp.mem_support_iff.mp hp
  rw [ite_eq_right (by omega)] at hz
  exact hv hz

/-- Exact prime-indexed GCD, including every actual valuation and base-prime phase. -/
def corridorPacket (P : Finset ℕ) (n a : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p∈P,(Real.log p : ℂ)*phase p*((corridorGcd n a).factorization p : ℂ)

/-- The old literal prime interval; the lower endpoint is INCLUDED. -/
def windowPacket (P : Finset ℕ) (n a : ℕ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p∈P,if p≤n ∧ n≤p+a then (Real.log p : ℂ)*phase p else 0

/-- On a complete support, the untwisted packet is exactly the logarithm
of the full selected integer GCD. -/
theorem corridorPacket_eq_log {n a : ℕ} (hn : 2≤n) (ha : 3*a<n)
    (P : Finset ℕ) (hP : ∀ p,p.Prime → p≤n → p∈P) :
    corridorPacket P n a (fun _ => 1)=(Real.log (corridorGcd n a) : ℂ) := by
  rw [Real.log_nat_eq_sum_factorization,Finsupp.sum,Complex.ofReal_sum]
  have hsub : (corridorGcd n a).factorization.support⊆P := by
    intro p hp
    obtain ⟨hp,hpn⟩ := corridorGcd_prime_support hn ha p hp
    exact hP p hp hpn
  unfold corridorPacket
  rw [←Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro p _
    push_cast
    ring
  · intro p _ hp
    simp only [Finsupp.notMem_support_iff.mp hp,Nat.cast_zero,mul_zero]

/-- All higher carries and small-prime discrepancies stay in this exact
correction, rather than being removed from the definition. -/
def corridorCorrection (P : Finset ℕ) (n a : ℕ) (phase : ℕ → ℂ) : ℂ :=
  corridorPacket P n a phase-windowPacket P n a phase

theorem corridorCorrection_eq_small {n a J : ℕ} (hn : 2≤n) (ha : 3*a<n)
    (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (hX : n≤2^(2*J)) (phase : ℕ → ℂ) :
    corridorCorrection P n a phase=
      corridorCorrection (P.filter (fun p => p≤2^J)) n a phase := by
  have he (Q : Finset ℕ) : corridorCorrection Q n a phase=
      ∑ p∈Q,(Real.log p : ℂ)*phase p*
        (((corridorGcd n a).factorization p : ℂ)-
          (if p≤n ∧ n≤p+a then 1 else 0)) := by
    unfold corridorCorrection corridorPacket windowPacket
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  rw [he,he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpnot
  have hlarge : 2^J<p := by
    by_contra h
    exact hpnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  have hpp : n<p^2 := by
    apply hX.trans_lt
    rw [show 2*J=J*2 by omega,pow_mul]
    exact Nat.pow_lt_pow_left hlarge (by omega)
  rw [corridorGcd_factorization_large (hP p hp) hn ha hpp]
  split_ifs <;> simp

/-- Square-root/polylogarithmic payment AFTER the full valuation-minus-
window join. The actual prime interval remains signed and unpaid. -/
theorem norm_corridorCorrection_le {n a J : ℕ} (hn : 2≤n) (ha : 3*a<n)
    (P : Finset ℕ) (hP : ∀ p∈P,p.Prime) (hX : n≤2^(2*J)) (phase : ℕ → ℂ)
    (hphase : ∀ p∈P,‖phase p‖≤1) :
    ‖corridorCorrection P n a phase‖≤(2 : ℝ)^J*(2*(J : ℝ)+1)^2*Real.log 2 := by
  rw [corridorCorrection_eq_small hn ha P hP hX]
  let Q := P.filter (fun p => p≤2^J)
  have hcard : (Q.card : ℝ)≤(2 : ℝ)^J := by
    have hs : Q⊆Finset.Icc 1 (2^J) := by
      intro p hp
      obtain ⟨hp,hpb⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(hP p hp).pos,hpb⟩
    exact_mod_cast (by simpa using Finset.card_le_card hs : Q.card≤2^J)
  have hbound (p : ℕ) (hp : p∈Q) :
      ‖(Real.log p : ℂ)*phase p*
        (((corridorGcd n a).factorization p : ℂ)-
          (if p≤n ∧ n≤p+a then 1 else 0))‖≤(2*(J : ℝ)+1)^2*Real.log 2 := by
    obtain ⟨hpP,hpb⟩ := Finset.mem_filter.mp hp
    have hlog : ‖(Real.log p : ℂ)‖≤(2*(J : ℝ)+1)*Real.log 2 := by
      rw [Complex.norm_real,Real.norm_of_nonneg (Real.log_natCast_nonneg p)]
      have he := Real.log_le_log (by exact_mod_cast (hP p hpP).pos)
        (by exact_mod_cast hpb : (p : ℝ)≤(2 : ℝ)^J)
      rw [Real.log_pow] at he
      have hR := Real.log_nonneg (by norm_num : (1 : ℝ)≤2)
      nlinarith [Nat.cast_nonneg (α := ℝ) J]
    have hv : ‖((corridorGcd n a).factorization p : ℂ)‖≤2*(J : ℝ) := by
      rw [Complex.norm_natCast]
      exact_mod_cast corridorGcd_factorization_le_orders (hP p hpP) hn ha hX
    have hm : ‖(if p≤n ∧ n≤p+a then (1 : ℂ) else 0)‖≤1 := by
      split_ifs <;> norm_num
    have hd := (norm_sub_le _ _).trans (add_le_add hv hm)
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ((2*(J : ℝ)+1)*Real.log 2)*1*(2*(J : ℝ)+1) :=
        mul_le_mul (mul_le_mul hlog (hphase p hpP) (norm_nonneg _) (by positivity))
          hd (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have he : corridorCorrection Q n a phase=
      ∑ p∈Q,(Real.log p : ℂ)*phase p*
        (((corridorGcd n a).factorization p : ℂ)-
          (if p≤n ∧ n≤p+a then 1 else 0)) := by
    unfold corridorCorrection corridorPacket windowPacket
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p∈Q,(2*(J : ℝ)+1)^2*Real.log 2 := Finset.sum_le_sum hbound
    _ = (Q.card : ℝ)*((2*(J : ℝ)+1)^2*Real.log 2) := by simp
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)

/-- The full GCD and actual prime window are source-equivalent at EVERY
power beta>1/2, for moving corridors and arbitrary bounded phases. -/
theorem tendsto_scaled_corridorCorrection (P : ℕ → Finset ℕ) (n a : ℕ → ℕ)
    (phase : ℕ → ℕ → ℂ) (hP : ∀ J p,p∈P J → p.Prime)
    (hn : ∀ᶠ J : ℕ in atTop,2≤n J) (ha : ∀ᶠ J : ℕ in atTop,3*a J<n J)
    (hX : ∀ᶠ J : ℕ in atTop,n J≤2^(2*J))
    (hphase : ∀ J p,p∈P J → ‖phase J p‖≤1) {beta : ℝ} (hb : 1/2<beta) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      corridorCorrection (P J) (n J) (a J) (phase J)) atTop (𝓝 0) := by
  let q := Real.exp ((1-2*beta)*Real.log 2)
  have hq0 : 0≤q := (Real.exp_pos _).le
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by linarith) (Real.log_pos (by norm_num)))
  have he : Real.exp (-2*beta*Real.log 2)*2=q := by
    calc
      _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ = _ := by dsimp [q];rw [←Real.exp_add];congr 1;ring
  have hpoly := tendsto_pow_const_mul_const_pow_of_lt_one (2 : ℕ) hq0 hq1
  have ht : Tendsto (fun J : ℕ => (2*(J : ℝ)+1)^2*q^J*Real.log 2) atTop (𝓝 0) := by
    have hq := tendsto_pow_const_mul_const_pow_of_lt_one (1 : ℕ) hq0 hq1
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    convert (((hpoly.const_mul 4).add (hq.const_mul 4)).add h0).mul_const (Real.log 2) using 1
    · funext J
      simp only [pow_one]
      ring
    · simp
  apply squeeze_zero_norm' (a := fun J : ℕ => (2*(J : ℝ)+1)^2*q^J*Real.log 2) _ ht
  filter_upwards [hn,ha,hX] with J hn ha hX
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply (mul_le_mul_of_nonneg_left
    (norm_corridorCorrection_le hn ha (P J) (hP J) hX (phase J) (hphase J))
    (by positivity)).trans_eq
  rw [←he,mul_pow]
  ring

/-- Whole-mask collapse holds for arbitrary arrays. It grants no actual
prime, binomial or Gamma data to those controls. -/
theorem joined_firstIntersection_eq_scalar (S D : Finset ℕ) (n a : ℕ → ℕ)
    (hn : ∀ i∈S,2≤n i) (ha : ∀ i∈S,3*a i<n i) (hD : ∀ d∈D,0<d)
    (W : ℕ → ℕ → ℂ) (f : ℕ → ℂ) :
    (∑ i∈S,∑ d∈D,W i d*f d*(firstIntersection (n i) (a i) d : ℂ))=
      ∑ d∈D,f d*(∑ i∈S,if d≤n i ∧ n i≤d+a i then W i d else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [firstIntersection_eq (hn i hi) (ha i hi) (hD d hd)]
  split_ifs <;> simp
  ring

/-- This is an exact limit equivalence for the NATIVE GCD and prime
window, not an inference of a new masked source from complete moments. -/
theorem native_source_tendsto_iff (P : ℕ → Finset ℕ) (n a : ℕ → ℕ)
    (phase : ℕ → ℕ → ℂ) (hP : ∀ J p,p∈P J → p.Prime)
    (hn : ∀ᶠ J : ℕ in atTop,2≤n J) (ha : ∀ᶠ J : ℕ in atTop,3*a J<n J)
    (hX : ∀ᶠ J : ℕ in atTop,n J≤2^(2*J))
    (hphase : ∀ J p,p∈P J → ‖phase J p‖≤1) {beta : ℝ} (hb : 1/2<beta)
    (v : ℂ) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      corridorPacket (P J) (n J) (a J) (phase J)) atTop (𝓝 v) ↔
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      windowPacket (P J) (n J) (a J) (phase J)) atTop (𝓝 v) := by
  have he := tendsto_scaled_corridorCorrection P n a phase hP hn ha hX hphase hb
  constructor
  · intro h
    convert h.sub he using 1
    · funext J
      unfold corridorCorrection
      ring
    · simp
  · intro h
    convert h.add he using 1
    · funext J
      unfold corridorCorrection
      ring
    · simp

/-- The same native limit equivalence keeps the ACTUAL fixed-height
prime phases exactly; no absolute Fourier allowance is introduced. -/
theorem native_phased_source_tendsto_iff (P : ℕ → Finset ℕ) (n a : ℕ → ℕ)
    (hP : ∀ J p,p∈P J → p.Prime) (hn : ∀ᶠ J : ℕ in atTop,2≤n J)
    (ha : ∀ᶠ J : ℕ in atTop,3*a J<n J) (hX : ∀ᶠ J : ℕ in atTop,n J≤2^(2*J))
    (y : ℝ) {beta : ℝ} (hb : 1/2<beta) (v : ℂ) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      corridorPacket (P J) (n J) (a J) (primePhase y)) atTop (𝓝 v) ↔
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      windowPacket (P J) (n J) (a J) (primePhase y)) atTop (𝓝 v) :=
  native_source_tendsto_iff P n a (fun _ => primePhase y) hP hn ha hX
    (fun _ p _ => (norm_primePhase y p).le) hb v

/-- Associated continuous logarithmic prime window. This is NOT a
relaxation of the native integer corridor or a paid floor replacement. -/
def windowWidth : ℝ := Real.log (3/2)

theorem windowWidth_pos : 0<windowWidth := Real.log_pos (by norm_num)

/-- Exact Mellin multiplier of the continuous log-window. -/
def windowMultiplier (v : ℂ) : ℂ := (1-Complex.exp (-v*windowWidth))/v

/-- A single genuine-prime atom, with the original prime-leg phase
and the full complex Mellin variable both retained. -/
def primeWindowAtom (y : ℝ) (w : ℂ) (p : ℕ) : ℂ :=
  ∫ t in Real.log p..Real.log p+windowWidth,
    (Real.log p : ℂ)*primePhase y p*Complex.exp (-(w-I*y)*(t : ℂ))

theorem primeWindowAtom_eq (y : ℝ) {w : ℂ} (hw : w-I*y≠0) (p : ℕ) :
    primeWindowAtom y w p=windowMultiplier (w-I*y)*(Real.log p : ℂ)*
      zetaPrimeFeature w p := by
  have hp : primePhase y p*Complex.exp (-(w-I*y)*(Real.log p : ℂ))=
      zetaPrimeFeature w p := by
    unfold primePhase zetaPrimeFeature
    rw [←Complex.exp_add]
    congr 1
    ring
  rw [primeWindowAtom,intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (neg_ne_zero.mpr hw)]
  have hex : -(w-I*y)*((Real.log p+windowWidth : ℝ) : ℂ)=
      -(w-I*y)*(Real.log p : ℂ)+(-(w-I*y)*windowWidth) := by push_cast;ring
  rw [hex,Complex.exp_add]
  calc
    _ = windowMultiplier (w-I*y)*(Real.log p : ℂ)*
        (primePhase y p*Complex.exp (-(w-I*y)*(Real.log p : ℂ))) := by
      unfold windowMultiplier
      field_simp
      ring
    _ = _ := by rw [hp]

theorem windowMultiplier_analytic {v : ℂ} (hv : v≠0) :
    AnalyticAt ℂ windowMultiplier v := by
  unfold windowMultiplier
  fun_prop

theorem windowMultiplier_ne_zero {v : ℂ} (hv : 0<v.re) :
    windowMultiplier v≠0 := by
  have hv0 : v≠0 := by intro h;simp [h] at hv
  have hex : ‖Complex.exp (-v*windowWidth)‖<1 := by
    rw [Complex.norm_exp]
    have hr : (-v*(windowWidth : ℂ)).re=-v.re*windowWidth := by simp
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) windowWidth_pos)
  unfold windowMultiplier
  apply div_ne_zero _ hv0
  intro hz
  have he := sub_eq_zero.mp hz
  rw [←he] at hex
  norm_num at hex

/-- The ordinary-prime Euler response, with the proper-power correction
explicit. It is not a convergent prime series in the zero strip. -/
def ordinaryResponse (w : ℂ) : ℂ :=
  -(logDeriv riemannZeta w+zetaProperPrimePowerSeries w)

theorem ordinaryResponse_eq_primeSeries {w : ℂ} (hw : 1<w.re) :
    ordinaryResponse w=zetaOrdinaryPrimeLogMoment 0 w := by
  have h := (LSeriesHasSum_zetaMoebiusPrimeDerivative hw).neg
  have he : -(fun n => if n.Prime then zetaMoebiusDerivativeCoefficient n else 0)=
      fun n => ((if n.Prime then ArithmeticFunction.vonMangoldt n else 0 : ℝ) : ℂ) := by
    funext n
    by_cases hp : n.Prime <;>
      simp [zetaMoebiusDerivativeCoefficient,hp,
        ArithmeticFunction.moebius_apply_prime,ArithmeticFunction.vonMangoldt_apply_prime]
  rw [he] at h
  have ht := h.tsum_eq
  simp_rw [LSeries_term_eq_zetaPrimeFeature
    (fun n => ((if n.Prime then ArithmeticFunction.vonMangoldt n else 0 : ℝ) : ℂ))
    (by norm_num)] at ht
  rw [ordinaryResponse,←ht]
  unfold zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro n
  by_cases hp : n.Prime <;> simp [zetaPrimeLogKernel,hp]

/-- Continued response of the associated CONTINUOUS prime-window
observation; no native-cutoff residue or new arithmetic bound is inferred. -/
def windowResponse (y : ℝ) (w : ℂ) : ℂ :=
  windowMultiplier (w-I*y)*ordinaryResponse w

theorem finite_windowAtom_eq (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (y : ℝ) {w : ℂ} (hw : w-I*y≠0) :
    (∑ p∈P,primeWindowAtom y w p)=windowMultiplier (w-I*y)*
      (∑ p∈P,(ArithmeticFunction.vonMangoldt p : ℂ)*zetaPrimeLogKernel 0 w p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [primeWindowAtom_eq y hw p,ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
  simp only [zetaPrimeLogKernel,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
  ring

/-- Finite prime-window transforms converge on the EULER half-plane.
Every finite atom is integrated exactly; no short interval theorem is used. -/
theorem tendsto_primeWindowAtoms (y : ℝ) {w : ℂ} (hw : 1<w.re) :
    Tendsto (fun M : ℕ => ∑ p∈(Finset.range M).filter Nat.Prime,
      primeWindowAtom y w p) atTop (𝓝 (windowResponse y w)) := by
  have hn : w-I*y≠0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have he (M : ℕ) :
      (∑ p∈(Finset.range M).filter Nat.Prime,primeWindowAtom y w p)=
      windowMultiplier (w-I*y)*∑ p∈Finset.range M,
        if p.Prime then (ArithmeticFunction.vonMangoldt p : ℂ)*zetaPrimeLogKernel 0 w p else 0 := by
    rw [finite_windowAtom_eq _ (fun _ hp => (Finset.mem_filter.mp hp).2) y hn,
      Finset.sum_filter]
  simp_rw [he]
  have ht := (summable_zetaOrdinaryPrimeLogMoment 0 hw).hasSum.tendsto_sum_nat
  rw [windowResponse,ordinaryResponse_eq_primeSeries hw]
  exact ht.const_mul _

/-- Density pole removed at transform level, without modifying any
literal arithmetic packet or assuming its zero response vanishes. -/
def centeredWindowResponse (y : ℝ) (w : ℂ) : ℂ :=
  windowResponse y w-windowMultiplier (w-I*y)/(w-1)

theorem centered_density_analytic (y : ℝ) :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧ centeredWindowResponse y=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  have hA := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hn : riemannZeta₁ (1 : ℂ)≠0 := by simp
  have hv : (1 : ℂ)-I*y≠0 := by intro h;have hh := congrArg Complex.re h;simp at hh
  have hphi : AnalyticAt ℂ (fun w : ℂ => windowMultiplier (w-I*y)) 1 :=
    (windowMultiplier_analytic hv).comp (f := fun w : ℂ => w-I*y)
      (analyticAt_id.sub analyticAt_const)
  have hQ := analyticAt_zetaProperPrimePowerSeries (by norm_num : (1/2 : ℝ)<(1 : ℂ).re)
  refine ⟨fun w => windowMultiplier (w-I*y)*
    (-logDeriv riemannZeta₁ w-zetaProperPrimePowerSeries w),
    hphi.mul ((hA.deriv.div hA hn).neg.sub hQ),?_⟩
  filter_upwards [hA.continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw (hw1 : w≠1)
  have hz : riemannZeta w≠0 := by
    rw [riemannZeta_eq_inv_sub_mul hw1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hw1)) hw
  rw [centeredWindowResponse,windowResponse,ordinaryResponse,neg_add,
    neg_logDeriv_riemannZeta_eq_pole_sub hw1 hz]
  ring

/-- Every actual right-half zero retains its genuine multiplicity in
the associated continuous observation, without exposure or simplicity. -/
theorem actual_window_zero_source (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun w : ℂ => (w-rho.1)*windowResponse rho.1.im w)
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        windowMultiplier (rho.1-I*rho.1.im))) := by
  have h := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  have hp : ContinuousAt (fun w : ℂ => (w-rho.1)*zetaProperPrimePowerSeries w) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul
      (analyticAt_zetaProperPrimePowerSeries hrho).continuousAt
  have ht : Tendsto (fun w : ℂ => (w-rho.1)*zetaProperPrimePowerSeries w)
      (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hp.tendsto.mono_left nhdsWithin_le_nhds
  have hv : rho.1-I*rho.1.im≠0 := by
    intro hh
    have hh := congrArg Complex.re hh
    simp at hh
    linarith
  have hphi : ContinuousAt (fun w : ℂ => windowMultiplier (w-I*rho.1.im)) rho.1 :=
    (windowMultiplier_analytic hv).continuousAt.comp (f := fun w : ℂ => w-I*rho.1.im)
      (continuousAt_id.sub continuousAt_const)
  convert (h.sub ht).mul (hphi.tendsto.mono_left nhdsWithin_le_nhds) using 1
  · funext w
    unfold windowResponse ordinaryResponse
    ring
  · simp only [analyticZetaZeroMultiplicity,sub_zero]

theorem centered_actual_window_zero_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    Tendsto (fun w : ℂ => (w-rho.1)*centeredWindowResponse rho.1.im w)
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        windowMultiplier (rho.1-I*rho.1.im))) := by
  have hv : rho.1-I*rho.1.im≠0 := by
    intro hh
    have hh := congrArg Complex.re hh
    simp at hh
    linarith
  have hc : ContinuousAt (fun w : ℂ => (w-rho.1)*
      (windowMultiplier (w-I*rho.1.im)/(w-1))) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul
      (((windowMultiplier_analytic hv).continuousAt.comp (f := fun w : ℂ => w-I*rho.1.im)
        (continuousAt_id.sub continuousAt_const)).div
        (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr rho.2.2.2))
  have ht : Tendsto (fun w : ℂ => (w-rho.1)*
      (windowMultiplier (w-I*rho.1.im)/(w-1))) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [centeredWindowResponse,mul_sub,sub_zero] using
    (actual_window_zero_source rho hrho).sub ht

theorem window_source_ne_zero (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*windowMultiplier (rho.1-I*rho.1.im)≠0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho)))
  · apply windowMultiplier_ne_zero
    simpa using (show 0<rho.1.re by linarith)

/-- The scalar window observation cannot provide source payment by an
identity alone: at every actual right-half zero its centered residue persists. -/
theorem centered_window_not_source_small (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    ¬Tendsto (fun w : ℂ => (w-rho.1)*centeredWindowResponse rho.1.im w)
      (𝓝[≠] rho.1) (𝓝 0) := by
  intro h
  exact window_source_ne_zero rho hrho
    (tendsto_nhds_unique (centered_actual_window_zero_source rho hrho) h)

theorem centered_window_no_analytic_extension (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) :
    ¬∃ E : ℂ → ℂ,AnalyticAt ℂ E rho.1 ∧
      centeredWindowResponse rho.1.im=ᶠ[𝓝[≠] rho.1] E := by
  rintro ⟨E,hE,he⟩
  have hc : ContinuousAt (fun w : ℂ => (w-rho.1)*E w) rho.1 :=
    (continuousAt_id.sub continuousAt_const).mul hE.continuousAt
  have ht : Tendsto (fun w : ℂ => (w-rho.1)*E w) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply centered_window_not_source_small rho hrho
  apply ht.congr'
  filter_upwards [he] with w hw
  rw [hw]

end
end RiemannGaussian.ArithmeticOperatorKummerCorridorAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerCorridorAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty corridor audit."
  logInfo m!"Kummer-corridor audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-corridor"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-corridor/axioms.json"
    (Json.mkObj [("scope",toJson "broad symmetric corridors retain the old prime window; no independent prime estimate or native zero source inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
