/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszDominantSector

/-!
# The source after paying every eligible dominant prime

The complete dominant-prime response vanishes with an explicit two-rate
allowance. Only the remaining original signed atoms carry the exact source.
Their independent cofinal real floor remains open.
-/

namespace RiemannGaussian.ZetaRieszDominantAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszMaskSupport ZetaRieszPrimeCountFrequency
open ZetaRieszCompanionMask

/-- The original retained support with only the independently bounded dominant-prime sector deleted. -/
def nondominantBand (u : ℝ) (N K : ℕ) : Finset ℕ := retainedBand u N K \ dominantSector u N K

/-- The full signed response on the remaining original labels, with the exact unassigned multiplier. -/
def nondominantResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ nondominantBand u N K,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n

/-- The paid sector is exactly the difference of the two actual finite signed carriers. -/
theorem retained_sub_nondominant (u y : ℝ) (N K : ℕ) :
    retainedResponse u y N K - nondominantResponse u y N K =
      ∑ n ∈ dominantSector u N K,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n *
            zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n := by
  have hsub : dominantSector u N K ⊆ retainedBand u N K := Finset.filter_subset _ _
  have hs := Finset.sum_sdiff (f := fun n =>
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) hsub
  dsimp only [retainedResponse, nondominantResponse, nondominantBand]
  linear_combination -hs

/-- The original source normalization and count schedule on the smaller arithmetic support. -/
def nondominantRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    nondominantResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- The entire removed response tends to zero for arbitrary moving heights, independently of zeros. -/
theorem tendsto_retained_sub_nondominant_moving (y : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j => retainedRemainder u (y j) j - nondominantRemainder u (y j) j)
      atTop (𝓝 0) := by
  have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one rates_bounds.1.1 rates_bounds.1.2).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one rates_bounds.2.1 rates_bounds.2.2)).comp
      tendsto_dyadicMomentOrder).mul_const (zetaMoebiusLogMajorantMass referenceExponent)
  simp only [Function.comp_def, add_zero, zero_mul] at ht
  apply squeeze_zero_norm' (a := fun j =>
    (upperRate ^ dyadicMomentOrder j + lowerRate ^ dyadicMomentOrder j) *
      zetaMoebiusLogMajorantMass referenceExponent) ?_ ht
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 320)] with j hj
  dsimp only [retainedRemainder, nondominantRemainder]
  rw [← mul_sub, retained_sub_nondominant]
  exact dominantSector_bound _ _ hj (y j) hu huh

/-- All earlier reductions and the new dominant-prime deletion form one independently vanishing error for arbitrary moving heights. -/
theorem tendsto_arithmetic_sub_nondominant_moving (y : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 < u) (huh : u ≤ Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j => ZetaRieszJointCofactor.arithmeticRemainder u (y j) j -
      nondominantRemainder u (y j) j) atTop (𝓝 0) := by
  have h := (tendsto_arithmetic_sub_retained_moving y hu huh).add
    (tendsto_retained_sub_nondominant_moving y hu.le huh)
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- The exact evaluated harmonic source survives after the entire dominant-prime sector is paid; the remaining signed floor is still open. -/
theorem tendsto_nondominant_exact_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (nondominantRemainder (3 / 2 - rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (retainedCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_retained_exact_source rho hrho hexposed huh).sub
    (tendsto_retained_sub_nondominant_moving (fun _ => rho.1.im) hu huh.le)
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- Every prime divisor of a squarefree integer with at least three prime factors has an eligible composite cofactor. -/
theorem eligible_of_three_prime_factors {n p : ℕ} (hn : Squarefree n)
    (hc : 3 ≤ n.primeFactors.card) (hp : p ∈ n.primeFactors) :
    eligibleCofactor p (n / p) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have he : p * (n / p) = n := Nat.mul_div_cancel' hpd
  have hs : Squarefree (p * (n / p)) := by rw [he]; exact hn
  have hsplit := Nat.squarefree_mul_iff.mp hs
  refine ⟨hsplit.2.2, ?_, ?_, hpp.coprime_iff_not_dvd.mp hsplit.1⟩
  · intro ha
    rw [ha, mul_one] at he
    rw [← he, hpp.primeFactors, Finset.card_singleton] at hc
    omega
  · intro ha
    have htwo := pair_prime_count_le_two hpp ha
    rw [he] at htwo
    omega

/-- Every nonzero surviving label has all its prime logarithms strictly below thirteen twentieths of the total; the actual count, window and cutoff discharge eligibility. -/
theorem nondominant_prime_log_lt (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hnB : n ∈ nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hcoeff : residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    ∀ p ∈ n.primeFactors, Real.log p < (13 / 20 : ℝ) * Real.log n := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  obtain ⟨hnret, hnnot⟩ := Finset.mem_sdiff.mp hnB
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew, hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral, hc3, hcK⟩ := Finset.mem_filter.mp hnfew
  have hn : Squarefree n := by
    by_contra h
    apply hcoeff
    simp [residualCoefficient, SquarefreeVaughanLogSource.coefficient, h]
  have hnp : ¬n.Prime := by
    intro h
    rw [h.primeFactors, Finset.card_singleton] at hc3
    omega
  have hpX : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2
  intro p hp
  by_contra hdom
  have hdom' : (13 / 20 : ℝ) * Real.log n ≤ Real.log p := le_of_not_gt hdom
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hn1 : 1 < n := lt_of_lt_of_le hpp.one_lt
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hpd)
  have hpN : N ^ 2 < p := by
    by_contra hh
    have hpN' : p ≤ N ^ 2 := le_of_not_gt hh
    have hsmall := few_smooth_divisor_log_le j hj hn hpd hcK (by
      intro q hq
      have hqp : q = p := by simpa only [hpp.primeFactors, Finset.mem_singleton] using hq
      simpa only [hqp] using hpN')
    have hlo : (7 / 4 : ℝ) * N < Real.log n := hw.1
    change Real.log p ≤ (N : ℝ) / 4 at hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpA : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N :=
    (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr ⟨hpp, hpN, hpX p hp⟩
  apply hnnot
  exact Finset.mem_filter.mpr ⟨hnret, hn, hn1, hnp, p, hp, hpA,
    eligible_of_three_prime_factors hn hc3 hp, hdom'⟩

/-- The stronger rational deficit is preserved on the smaller support; an independent cofinal floor at minus three fortieths remains the required contradiction input. -/
theorem eventually_nondominant_re_lt_neg_three_fortieths (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ∀ᶠ j in atTop,
      (nondominantRemainder (3 / 2 - rho.1.re) rho.1.im j).re < -(3 / 40 : ℝ) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hc := retainedCost_lt_thirtyseven_fortieths hu huh.le
  have h := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_nondominant_exact_source rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, one_mul, Complex.add_re,
    Complex.neg_re, Complex.one_re, Complex.ofReal_re] at h
  exact h.eventually (eventually_lt_nhds (by linarith))

end
end RiemannGaussian.ZetaRieszDominantAllocation
