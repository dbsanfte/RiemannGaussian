/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompanionMask

/-!
# Size bounds for the actual support comparison

The retained count schedule bounds every quadratic-head divisor by a quarter-order logarithmic budget. The original optimized cofactor schedule has the same bound, including its literal floors and minimum.
-/

namespace RiemannGaussian.ZetaRieszMaskSupport

noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszGeneralCofactorTilt ZetaRieszCofactorTiltRate
open ZetaRieszCompanionMask ZetaRieszWeightedCount

/-- The actual dyadic moment schedule has an explicit logarithmic upper bound from index 32 onward. -/
theorem log_dyadicMoment_le (j : ℕ) (hj : 32 ≤ j) :
    Real.log (dyadicMomentOrder j) ≤ (j:ℝ)+4 := by
  have hlogj : Real.log ((j:ℝ)+4) ≤ ((j:ℝ)+4)/4 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ ((j:ℝ)+4)/4)
    have hjR : (32:ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  have he : Real.log (dyadicMomentOrder j) = Real.log 8 + Real.log ((j:ℝ)+4) + ((j:ℝ)+3)*Real.log 2 := by
    simp only [dyadicMomentOrder, dyadicPrimeCount, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, Real.log_mul (by positivity : (8:ℝ) ≠ 0) (by positivity : (j:ℝ)+4 ≠ 0),
      Real.log_mul (by positivity : (8:ℝ)*((j:ℝ)+4) ≠ 0) (by positivity : (2:ℝ)^(j+3) ≠ 0), Real.log_pow]
  have h8 : Real.log (8:ℝ) = 3*Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]
    norm_num
  rw [he,h8]
  have hjR : (32:ℝ) ≤ j := by exact_mod_cast hj
  nlinarith [Real.log_two_lt_d9]

/-- Every quadratic-head divisor of a retained lower-count squarefree integer spends at most one quarter of the moment-order log budget. -/
theorem few_smooth_divisor_log_le (j : ℕ) (hj : 32 ≤ j) {a n : ℕ}
    (hn : Squarefree n) (had : a ∣ n) (hc : n.primeFactors.card < dyadicPrimeCount j)
    (ha : ∀ p ∈ a.primeFactors, p ≤ (dyadicMomentOrder j)^2) :
    Real.log a ≤ (dyadicMomentOrder j:ℝ)/4 := by
  have has := hn.squarefree_of_dvd had
  have hsub : a.primeFactors ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans had, hn.ne_zero⟩
  have hcard : (a.primeFactors.card:ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Nat.le_of_lt hc)
  have hNpos : (0:ℝ) < dyadicMomentOrder j := by
    have := four_le_dyadicPrimeCount j
    dsimp only [dyadicMomentOrder]
    positivity
  have hb : Real.log a ≤ (a.primeFactors.card:ℝ)*(2*Real.log (dyadicMomentOrder j)) := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum has]
    calc
      _ ≤ ∑ _p ∈ a.primeFactors, 2*Real.log (dyadicMomentOrder j) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
          (by exact_mod_cast ha p hp : (p:ℝ) ≤ ((dyadicMomentOrder j)^2:ℕ))
        simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
      _ = _ := by simp
  have hlog := log_dyadicMoment_le j hj
  have hlog0 := Real.log_natCast_nonneg (dyadicMomentOrder j)
  have hprod := mul_le_mul hcard (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤2))
    (by positivity : (0:ℝ)≤2*Real.log (dyadicMomentOrder j)) (Nat.cast_nonneg (dyadicPrimeCount j))
  have hN : (dyadicMomentOrder j:ℝ) = 8*((j:ℝ)+4)*(dyadicPrimeCount j:ℝ) := by simp [dyadicMomentOrder]
  rw [hN]
  nlinarith

/-- The original analytically optimized composite-cofactor growth rate fits the same quarter-order budget throughout the reserve range. -/
theorem optimal_growth_log_le_quarter {u : ℝ} (hu : 1/2<u)
    (huh : u ≤ Real.exp (-(11/16:ℝ))) :
    Real.log (growthRate u (optimalTilt u)) ≤ (1/4:ℝ) := by
  have hu0 : 0<u := by linarith
  have hu1 : u<1 := huh.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlog : Real.log u ≤ -(11/16:ℝ) := by
    have h := Real.log_le_log hu0 huh
    simpa only [Real.log_exp] using h
  have hqhalf := optimalTilt_gt_half hu hu1
  have hq1 : optimalTilt u ≤ 1 := by
    unfold optimalTilt
    apply (div_le_one (by linarith : 0 < -2*Real.log u)).mpr
    linarith
  have hlo : -Real.log 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hu.le
    rw [Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0), Real.log_one] at h
    linarith
  have hrate : -(2*Real.log 2) ≤ Real.log (tiltRate u (optimalTilt u)) := by
    rw [tiltRate, Real.log_div (Real.exp_pos _).ne' (by linarith : optimalTilt u ≠ 0), Real.log_exp]
    have hql : Real.log (optimalTilt u) ≤ 0 := Real.log_nonpos (by linarith) hq1
    have hln := Real.log_neg hu0 hu1
    nlinarith
  rw [growthRate, Real.log_exp]
  apply (div_le_iff₀ (by linarith : 0 < 2*(optimalTilt u+5/2))).mpr
  linarith [Real.log_two_lt_d9]

/-- The exact floor-and-minimum cofactor schedule retains the quarter-order logarithmic ceiling. -/
theorem tiltedSchedule_log_le_quarter {u : ℝ} (hu : 1/2<u)
    (huh : u ≤ Real.exp (-(11/16:ℝ))) {N a : ℕ} (ha0 : 0<a)
    (ha : a ≤ tiltedSchedule u (optimalTilt u) N) : Real.log a ≤ (N:ℝ)/4 := by
  have hbase : 0 ≤ growthRate u (optimalTilt u)^N := by unfold growthRate; positivity
  have har : (a:ℝ) ≤ growthRate u (optimalTilt u)^N := by
    have hai : a ≤ ⌊growthRate u (optimalTilt u)^N⌋₊ := ha.trans (min_le_left _ _)
    have hair : (a:ℝ) ≤ (⌊growthRate u (optimalTilt u)^N⌋₊:ℕ) := by exact_mod_cast hai
    exact hair.trans (Nat.floor_le hbase)
  have hlog := Real.log_le_log (by exact_mod_cast ha0) har
  rw [Real.log_pow] at hlog
  have h := mul_le_mul_of_nonneg_left (optimal_growth_log_le_quarter hu huh) (Nat.cast_nonneg (α:=ℝ) N)
  linarith


/-- A product of two primes has at most two distinct prime factors, including the diagonal. -/
theorem pair_prime_count_le_two {a p : ℕ} (ha : a.Prime) (hp : p.Prime) :
    (a*p).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul ha.ne_zero hp.ne_zero, ha.primeFactors, hp.primeFactors]
  have h := Finset.card_union_le ({a}:Finset ℕ) {p}
  simpa only [Finset.card_singleton] using h

/-- Every original product-band label has its actual selected prime-cofactor factorization. -/
theorem productBand_factorization (keep : ℕ → Prop) (A Q : Finset ℕ) (N n : ℕ)
    (hn : n ∈ ZetaRieszSmoothPrimePrefix.productBand keep A Q N) :
    ∃ a ∈ A, ∃ p ∈ Q, p*a=n := by
  obtain ⟨hi,_hb⟩ := Finset.mem_filter.mp hn
  obtain ⟨⟨a,p⟩,hap,he⟩ := Finset.mem_image.mp hi
  exact ⟨a,(Finset.mem_product.mp hap).1,p,(Finset.mem_product.mp hap).2,he⟩


end
end RiemannGaussian.ZetaRieszMaskSupport
