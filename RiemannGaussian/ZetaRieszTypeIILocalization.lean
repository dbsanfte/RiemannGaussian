/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNondominantCarrier

/-!
# The fixed narrow window for the Type-II go/no-go test

Only the already independently bounded outer logarithmic tails are removed.
All masks and the exact allocation factor of the nondominant carrier remain.
This localization does not assume a Type-II estimate or a zeta zero.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open LogarithmicDeviation ZetaArithmeticDeviationBounds
open ZetaRieszDominantAllocation ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency

/-- The closed upper radius in the requested restricted test. -/
def radiusCeiling : ℝ := 5001 / 10000

/-- The test interval lies strictly inside the existing signed-source range. -/
theorem radiusCeiling_lt_source_ceiling : radiusCeiling < Real.exp (-(11 / 16 : ℝ)) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num [radiusCeiling])).mp
  have h := Real.log_le_sub_one_of_pos (by norm_num [radiusCeiling] : (0 : ℝ) < 2 * radiusCeiling)
  rw [Real.log_mul (by norm_num) (by norm_num [radiusCeiling])] at h
  dsimp [radiusCeiling] at h ⊢
  linarith [Real.log_two_gt_d9]

/-- Both endpoints have a strict deviation margin throughout the test interval. -/
theorem narrow_window_costs :
    Real.log (2 * radiusCeiling) < deviationCost (39 / 20) ∧
      Real.log (2 * radiusCeiling) < deviationCost (41 / 20) := by
  have hlo : Real.log (radiusCeiling * (39 / 20)) < -(1 / 40 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [radiusCeiling])).mpr
    have hbase : (159 / 160 : ℝ) < Real.exp (-(1 / 160 : ℝ)) := by
      have h := Real.add_one_lt_exp (by norm_num : -(1 / 160 : ℝ) ≠ 0)
      linarith
    have hpow := pow_lt_pow_left₀ hbase (by norm_num : (0 : ℝ) ≤ 159 / 160)
      (by norm_num : (4 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow
    dsimp [radiusCeiling]
    norm_num at hpow ⊢
    linarith
  have hhi : Real.log (radiusCeiling * (41 / 20)) < (1 / 40 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 40) 3
    norm_num [Finset.sum_range_succ, radiusCeiling] at h ⊢
    linarith
  have h₀ := log_rate_eq_deviation (by norm_num [radiusCeiling] : 0 < radiusCeiling)
    (by norm_num : (0 : ℝ) < 39 / 20)
  have h₁ := log_rate_eq_deviation (by norm_num [radiusCeiling] : 0 < radiusCeiling)
    (by norm_num : (0 : ℝ) < 41 / 20)
  constructor <;> linarith

/-- The literal original masks, intersected with 1.95N < log n <= 2.05N. -/
def narrowBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  deviationBand (nondominantBand u N K) (39 / 20) (41 / 20) N

/-- The narrowed signed sum, retaining the actual allocation and factorial kernel. -/
def narrowResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ narrowBand u N K,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n

/-- The narrowed response on the original, unmodified cofinal order schedule. -/
def narrowRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    narrowResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- The entire localization error has an independent geometric bound, uniform
in height, count cutoff and radius on the requested closed interval. -/
theorem exists_narrow_window_error :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ radiusCeiling →
        ‖(u : ℂ) ^ (N + 1) *
          (nondominantResponse u y N K - narrowResponse u y N K)‖ ≤ r ^ N * C := by
  obtain ⟨r, C, hr0, hr1, hC, h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [radiusCeiling]) (by norm_num : (0 : ℝ) < 39 / 20)
    (by norm_num) (by norm_num : (2 : ℝ) < 41 / 20)
    narrow_window_costs.1 narrow_window_costs.2
  refine ⟨r, C, hr0, hr1, hC, ?_⟩
  intro N K y u hu huU
  simpa only [nondominantResponse, narrowResponse, narrowBand,
    SquarefreeEulerQuadratic.primeFilterKernel_one, zetaPrimeLogKernel] using
    h N (nondominantBand u N K)
      (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N)
      (fun n _ => norm_residualCoefficient_le _ (SquarefreeVaughanLogSource.length_pos u N) N n)
      y u hu huU

/-- The narrowed and original carriers differ by o(1) at the exact source scale. -/
theorem tendsto_nondominant_sub_narrow {u : ℝ} (hu : 0 ≤ u)
    (huU : u ≤ radiusCeiling) (y : ℝ) :
    Tendsto (fun j => nondominantRemainder u y j - narrowRemainder u y j)
      atTop (𝓝 0) := by
  obtain ⟨r, C, hr0, hr1, _, hb⟩ := exists_narrow_window_error
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).comp
    tendsto_dyadicMomentOrder
  simp only [Function.comp_def, zero_mul] at ht
  apply squeeze_zero_norm (fun j => ?_) ht
  simpa only [nondominantRemainder, narrowRemainder, ← mul_sub] using
    hb (dyadicMomentOrder j) (dyadicPrimeCount j) y u hu huU

end
end RiemannGaussian.ZetaRieszTypeII
