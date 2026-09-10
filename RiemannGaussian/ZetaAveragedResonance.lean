/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteFourierSymbolMass
import RiemannGaussian.ZetaSievedLogWindow

/-!
# A smaller zeta frequency region from the actual symbol density

The stronger lower endpoint of the physical window gives arithmetic mass
decay. Averaging the inverse-square difference symbol charges only one
inverse gap. Together these facts justify the threshold `(6/7)^N`, with
explicit geometric errors for every dominated moving complex family.
The complete centered products inside the smaller region are unchanged.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The window's lower endpoint gives a stronger geometric arithmetic
mass bound, uniformly over all dominated complex coefficient choices. -/
theorem sum_norm_zetaArithmeticWindowSamples_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (N : ℕ) :
    (∑ j, ‖zetaArithmeticWeightedSamples (zetaLogWindowCoefficient a N) N j‖) ≤
      (20 / 21 : ℝ) ^ N * zetaMoebiusLogMajorantMass (9 / 8) := by
  have hb : Real.exp (-(1 / 20 : ℝ)) ≤ 20 / 21 := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp (1 / 20)
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 21 / 20)
      (by linarith : (21 / 20 : ℝ) ≤ Real.exp (1 / 20))
    simpa only [one_div, inv_div, inv_one, mul_one] using hi
  have hpow : Real.exp (-(N : ℝ) / 20) ≤ (20 / 21 : ℝ) ^ N := by
    rw [show -(N : ℝ) / 20 = (N : ℝ) * (-(1 / 20)) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hb N
  have he (j : ZMod (2 ^ (32 * N) + 1)) :
      ‖zetaArithmeticWeightedSamples (zetaLogWindowCoefficient a N) N j‖ =
      zetaLogBandSamples N (fun n ↦ ‖zetaLogWindowCoefficient a N n‖ *
        zetaPrimeExpWeight (5 / 4) n) j := by
    by_cases hj : j.val ∈ zetaPrimeLogBand N <;>
      simp [zetaArithmeticWeightedSamples, zetaLogBandSamples, hj, norm_zetaPrimeFeature]
  simp_rw [he]
  rw [sum_zetaLogBandSamples]
  have hpoint (n : ℕ) : ‖zetaLogWindowCoefficient a N n‖ * zetaPrimeExpWeight (5 / 4) n ≤
      (20 / 21 : ℝ) ^ N * (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (9 / 8) n) := by
    by_cases hn : n ∈ zetaLogWindow N
    · have hw : zetaPrimeExpWeight (5 / 4) n ≤
          Real.exp (-(N : ℝ) / 20) * zetaPrimeExpWeight (9 / 8) n := by
        unfold zetaPrimeExpWeight
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [hn.1])
      simp only [zetaLogWindowCoefficient, if_pos hn]
      have h := mul_le_mul (ha n) (hw.trans (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le))
        (Real.exp_pos _).le (zetaMoebiusLogMajorant_nonneg n)
      exact h.trans_eq (by ring)
    · simp only [zetaLogWindowCoefficient, if_neg hn, norm_zero, zero_mul]
      exact mul_nonneg (by positivity)
        (mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
  calc
    _ ≤ ∑ n ∈ zetaPrimeLogBand N, (20 / 21 : ℝ) ^ N *
        (zetaMoebiusLogMajorant n * zetaPrimeExpWeight (9 / 8) n) :=
      Finset.sum_le_sum (fun n _ ↦ hpoint n)
    _ = (20 / 21 : ℝ) ^ N * ∑ n ∈ zetaPrimeLogBand N,
        zetaMoebiusLogMajorant n * zetaPrimeExpWeight (9 / 8) n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum (zetaPrimeLogBand N)
        (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
        (summable_zetaMoebiusLogMajorant (by norm_num : (1 : ℝ) < 9 / 8))) (by positivity)

/-- The complete geometric difference allowance after averaging the
cyclic spectrum. The two terms retain interior and cyclic boundary costs. -/
def zetaQuarterAveragedGapError (p : Polynomial ℂ) (N : ℕ) (y b r : ℝ) : ℝ :=
  (81 / 64 : ℝ) *
    (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
      2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
        (b * r⁻¹ * (8 / 9)) ^ N +
    (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
      (b * r⁻¹ * (1 / 2)) ^ N

private theorem averaged_gap_budget_eq (p : Polynomial ℂ) (N : ℕ) (y b r : ℝ) (hN : 2 ≤ N) :
    b ^ N * (r ^ N)⁻¹ *
      ((8 / 9 : ℝ) ^ (N - 2) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) =
      zetaQuarterAveragedGapError p N y b r := by
  have hs : (8 / 9 : ℝ) ^ (N - 2) = (81 / 64 : ℝ) * (8 / 9 : ℝ) ^ N := by
    have h := pow_add (8 / 9 : ℝ) (N - 2) 2
    rw [Nat.sub_add_cancel hN] at h
    nlinarith
  have he (v : ℝ) : b ^ N * (r ^ N)⁻¹ * v ^ N = (b * r⁻¹ * v) ^ N := by
    rw [← inv_pow, ← mul_pow, ← mul_pow]
  rw [hs]
  calc
    _ = (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
          (b ^ N * (r ^ N)⁻¹ * (8 / 9 : ℝ) ^ N) +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
          (b ^ N * (r ^ N)⁻¹ * (1 / 2 : ℝ) ^ N) := by ring
    _ = _ := by rw [he, he]; rfl

/-- The new admissible-rate criterion is linear in the gap rate,
covering a continuum of choices with both geometric costs included. -/
theorem tendsto_zetaQuarterAveragedGapError (p : Polynomial ℂ) (y : ℝ)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hgap : b * (8 / 9) < r) :
    Tendsto (fun N ↦ zetaQuarterAveragedGapError p N y b r) atTop (𝓝 0) := by
  have he (N : ℕ) : zetaQuarterAveragedGapError p N y b r =
      zetaQuarterGapError p N y b (Real.sqrt r) := by
    simp only [zetaQuarterAveragedGapError, zetaQuarterGapError, inv_pow, Real.sq_sqrt hr.le]
  simp_rw [he]
  exact tendsto_zetaQuarterGapError p y hb (Real.sqrt_pos.mpr hr)
    (by rwa [Real.sq_sqrt hr.le])

/-- The whole complementary centered interaction has the averaged
gap bound, for every dominated coefficient family in the physical window. -/
theorem norm_zetaArithmeticWindowCenteredPart_compl_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) {r : ℝ} (hr : 0 < r) (hN : 2 ≤ N) :
    ‖zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
      (zetaMoebiusResonantModes N (r ^ N))ᶜ‖ ≤
      4 * zetaMoebiusLogMajorantMass (9 / 8) *
        zetaQuarterAveragedGapError p N y (20 / 21) r := by
  have hM := zetaMoebiusLogMajorantMass_nonneg (9 / 8)
  apply (norm_centeredFourierPart_le_averaged_gap
    (zetaArithmeticWeightedSamples (zetaLogWindowCoefficient a N) N)
    (zetaQuarterKernelSamples p N y) (zetaMoebiusResonantModes N (r ^ N))ᶜ
    (pow_pos hr N) (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)).trans
  rw [← averaged_gap_budget_eq p N y (20 / 21) r hN]
  calc
    _ ≤ (4 / r ^ N) * ((20 / 21 : ℝ) ^ N * zetaMoebiusLogMajorantMass (9 / 8)) *
        ((8 / 9 : ℝ) ^ (N - 2) *
          (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
            2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
          8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) := by
      gcongr
      · exact sum_norm_zetaArithmeticWindowSamples_le a ha N
      · exact sum_norm_cyclicSecond_quarterKernel_le p N y hN
    _ = _ := by ring

/-- Every rate beyond the explicit averaged-spectrum threshold gives
vanishing complementary interaction for all moving dominated families.
The condition is an independently checked scalar inequality. -/
theorem tendsto_zetaArithmeticWindowCenteredPart_compl (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (y : ℝ) {r : ℝ} (hr : 0 < r) (hgap : (160 / 189 : ℝ) < r) :
    Tendsto (fun N ↦ zetaArithmeticCenteredPart (zetaLogWindowCoefficient (a N) N) p N y
      (zetaMoebiusResonantModes N (r ^ N))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦
    norm_zetaArithmeticWindowCenteredPart_compl_le (a N) (ha N) p N y hr hN⟩)
  have h := (tendsto_zetaQuarterAveragedGapError p y
    (by norm_num : (0 : ℝ) ≤ 20 / 21) hr (by norm_num at hgap ⊢; exact hgap)).const_mul
      (4 * zetaMoebiusLogMajorantMass (9 / 8))
  simpa only [mul_zero] using h

/-- The concrete smaller symbol threshold from the averaged spectrum. -/
def zetaAveragedResonanceThreshold (N : ℕ) : ℝ := (6 / 7 : ℝ) ^ N

/-- The retained region is a subset of the preceding region at every
order, using the same original Fourier symbol. -/
theorem zetaAveragedResonantModes_subset (N : ℕ) :
    zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N) ⊆
      zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N) := by
  intro k hk
  have h : zetaAveragedResonanceThreshold N ≤ zetaDominatedResonanceThreshold N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hk' : ‖cyclicDifferenceSymbol k‖ < zetaAveragedResonanceThreshold N := by
    simpa [zetaMoebiusResonantModes] using hk
  simpa [zetaMoebiusResonantModes] using hk'.trans_le h

/-- Both concrete error rates are rational and strictly below one;
the boundary and complete interior second-difference costs stay separate. -/
theorem zetaQuarterAveragedGapError_six_sevenths_eq (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaQuarterAveragedGapError p N y (20 / 21) (6 / 7) =
      (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) * (80 / 81 : ℝ) ^ N +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) * (5 / 9 : ℝ) ^ N := by
  norm_num [zetaQuarterAveragedGapError]

/-- The complete allowance for both physical shells and the whole
complement of the smaller frequency region. -/
def zetaAveragedWindowError (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  zetaLogWindowError p N + 4 * zetaMoebiusLogMajorantMass (9 / 8) *
    zetaQuarterAveragedGapError p N y (20 / 21) (6 / 7)

/-- Every term in the new complete localization allowance tends to zero. -/
theorem tendsto_zetaAveragedWindowError (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaAveragedWindowError p N y) atTop (𝓝 0) := by
  unfold zetaAveragedWindowError
  have h := (tendsto_zetaLogWindowError p).add
    ((tendsto_zetaQuarterAveragedGapError p y (by norm_num : (0 : ℝ) ≤ 20 / 21)
      (by norm_num : (0 : ℝ) < 6 / 7) (by norm_num)).const_mul
        (4 * zetaMoebiusLogMajorantMass (9 / 8)))
  simpa only [mul_zero, add_zero] using h

/-- The full arithmetic filter differs from the smaller retained
interaction only by the independently bounded complete localization error. -/
theorem norm_zetaArithmeticFilter_sub_averaged_window_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))‖ ≤
      zetaAveragedWindowError p N y := by
  have he : zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N)) =
      (zetaArithmeticFilter a p N (3 / 2 + I * y) -
        zetaArithmeticFilter (zetaLogWindowCoefficient a N) p N (3 / 2 + I * y)) +
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))ᶜ := by
    rw [zetaArithmeticFilter_window_eq_band a p N y (by omega),
      zetaArithmeticBand_eq_centered_parts _ _ _ _
        (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_zetaArithmeticFilter_sub_window_le a ha p N y)
    (norm_zetaArithmeticWindowCenteredPart_compl_le a ha p N y (by norm_num) hN))

/-- The stronger localization applies to arbitrary moving dominated
complex families, including all original divisor and sieve schedules. -/
theorem tendsto_zetaArithmeticFilter_sub_averaged_window (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient (a N) N) p N y
        (zetaMoebiusResonantModes N (zetaAveragedResonanceThreshold N))) atTop (𝓝 0) :=
  squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦
    norm_zetaArithmeticFilter_sub_averaged_window_le (a N) (ha N) p N y hN⟩)
    (tendsto_zetaAveragedWindowError p y)

end
end RiemannGaussian
