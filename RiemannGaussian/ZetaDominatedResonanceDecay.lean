/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaDominatedWeightedFourier
import RiemannGaussian.ZetaMoebiusResonanceDecay

/-!
# A smaller resonant region from the actual logarithmic band

The arithmetic band mass and the cyclic kernel differences decay together.
Their product permits a smaller symbol threshold than the earlier estimate
using constant arithmetic mass. The result holds for every dominated moving
complex coefficient family. All cyclic boundary terms and centering terms
are included; the signed interaction within the retained region is unchanged.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The geometric difference allowance after combining arithmetic mass
decay at rate `b` with a symbol threshold `r^N`. Both interior and cyclic
boundary contributions remain explicit. -/
def zetaQuarterGapError (p : Polynomial ℂ) (N : ℕ) (y b r : ℝ) : ℝ :=
  (81 / 64 : ℝ) *
    (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
      2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
        (b * r⁻¹ ^ 2 * (8 / 9)) ^ N +
    (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
      (b * r⁻¹ ^ 2 * (1 / 2)) ^ N

private theorem gap_budget_eq (p : Polynomial ℂ) (N : ℕ) (y b r : ℝ) (hN : 2 ≤ N) :
    b ^ N * (r ^ N)⁻¹ ^ 2 *
      ((8 / 9 : ℝ) ^ (N - 2) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) =
      zetaQuarterGapError p N y b r := by
  have hs : (8 / 9 : ℝ) ^ (N - 2) = (81 / 64 : ℝ) * (8 / 9 : ℝ) ^ N := by
    have h := pow_add (8 / 9 : ℝ) (N - 2) 2
    rw [Nat.sub_add_cancel hN] at h
    nlinarith
  have he (v : ℝ) : b ^ N * (r ^ N)⁻¹ ^ 2 * v ^ N = (b * r⁻¹ ^ 2 * v) ^ N := by
    rw [← inv_pow, pow_right_comm, ← mul_pow, ← mul_pow]
  rw [hs]
  calc
    _ = (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
          (b ^ N * (r ^ N)⁻¹ ^ 2 * (8 / 9 : ℝ) ^ N) +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
          (b ^ N * (r ^ N)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ N) := by ring
    _ = _ := by rw [he, he]; rfl

/-- The exact admissible-rate criterion pays simultaneously for the
interior second differences and all cyclic boundary samples. -/
theorem tendsto_zetaQuarterGapError (p : Polynomial ℂ) (y : ℝ)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hgap : b * (8 / 9) < r ^ 2) :
    Tendsto (fun N ↦ zetaQuarterGapError p N y b r) atTop (𝓝 0) := by
  have ha : b * r⁻¹ ^ 2 * (8 / 9) < 1 := by
    have he : b * r⁻¹ ^ 2 * (8 / 9) = (b * (8 / 9)) / r ^ 2 := by ring
    rw [he]
    exact (div_lt_one (sq_pos_of_pos hr)).mpr hgap
  have hb' : b * r⁻¹ ^ 2 * (1 / 2) < 1 := by
    have hn : 0 ≤ b * r⁻¹ ^ 2 := mul_nonneg hb (sq_nonneg _)
    nlinarith
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ha
  have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hb'
  have h := (h₁.const_mul ((81 / 64 : ℝ) *
    (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
      2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k))).add
        (h₂.const_mul (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k))
  simpa only [zetaQuarterGapError, mul_zero, add_zero] using h

private theorem centered_gap_bound (a : ℕ → ℂ) (p : Polynomial ℂ) (N : ℕ)
    (y b M r : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hr : 0 < r) (hN : 2 ≤ N)
    (hmass : (∑ j, ‖zetaArithmeticWeightedSamples a N j‖) ≤ b ^ N * M) :
    ‖zetaArithmeticCenteredPart a p N y (zetaMoebiusResonantModes N (r ^ N))ᶜ‖ ≤
      2 * M * zetaQuarterGapError p N y b r := by
  apply (norm_centeredFourierPart_le_sum_norm_difference
    (zetaArithmeticWeightedSamples a N) (zetaQuarterKernelSamples p N y)
    (zetaMoebiusResonantModes N (r ^ N))ᶜ 2 (pow_pos hr N) (by
      intro k hk
      have hn := Finset.mem_compl.mp hk
      simpa [zetaMoebiusResonantModes, not_lt] using hn)).trans
  rw [← gap_budget_eq p N y b r hN]
  calc
    _ ≤ 2 * (b ^ N * M) * ((r ^ N)⁻¹ ^ 2 *
        ((8 / 9 : ℝ) ^ (N - 2) *
          (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
            2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
          8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k)) := by
      gcongr
      exact sum_norm_cyclicSecond_quarterKernel_le p N y hN
    _ = _ := by ring

/-- A general intermediate Dirichlet exponent gives an explicit bound
for every dominated arithmetic family outside the threshold `r^N`.
No cancellation or selected-zero hypothesis is needed. -/
theorem norm_zetaArithmeticCenteredPart_exp_compl_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) {σ r : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 5 / 4)
    (hr : 0 < r) (hN : 2 ≤ N) :
    ‖zetaArithmeticCenteredPart a p N y (zetaMoebiusResonantModes N (r ^ N))ᶜ‖ ≤
      2 * zetaMoebiusLogMajorantMass σ * zetaQuarterGapError p N y
        (Real.exp (-(5 / 4 - σ) * Real.log 2 / 4)) r := by
  apply centered_gap_bound a p N y _ _ r (Real.exp_pos _).le
    (zetaMoebiusLogMajorantMass_nonneg _) hr hN
  have h := sum_norm_zetaArithmeticWeightedSamples_le_exp a ha N hσ hσ'
  rwa [show -(5 / 4 - σ) * (N : ℝ) * Real.log 2 / 4 =
    (N : ℝ) * (-(5 / 4 - σ) * Real.log 2 / 4) by ring, Real.exp_nat_mul] at h

/-- All moving dominated families have vanishing complementary
interaction whenever the analytic exponent and symbol rate satisfy the
explicit strict inequality. This tests a continuum of choices at once. -/
theorem tendsto_zetaArithmeticCenteredPart_exp_compl (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (y : ℝ) {σ r : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 5 / 4) (hr : 0 < r)
    (hgap : Real.exp (-(5 / 4 - σ) * Real.log 2 / 4) * (8 / 9) < r ^ 2) :
    Tendsto (fun N ↦ zetaArithmeticCenteredPart (a N) p N y
      (zetaMoebiusResonantModes N (r ^ N))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦
    norm_zetaArithmeticCenteredPart_exp_compl_le (a N) (ha N) p N y hσ hσ' hr hN⟩)
  simpa only [mul_zero] using
    (tendsto_zetaQuarterGapError p y (Real.exp_pos _).le hr hgap).const_mul
      (2 * zetaMoebiusLogMajorantMass σ)

/-- Any strict margin beyond the limiting band-mass rate admits a
genuinely convergent intermediate Dirichlet exponent. The endpoint
exponent one itself is never used in an infinite absolute sum. -/
theorem exists_zetaDominatedBand_exponent {r : ℝ}
    (hgap : Real.exp (-Real.log 2 / 16) * (8 / 9) < r ^ 2) :
    ∃ σ : ℝ, 1 < σ ∧ σ ≤ 5 / 4 ∧
      Real.exp (-(5 / 4 - σ) * Real.log 2 / 4) * (8 / 9) < r ^ 2 := by
  have hc : ContinuousAt (fun σ : ℝ ↦
      Real.exp (-(5 / 4 - σ) * Real.log 2 / 4) * (8 / 9)) 1 := by fun_prop
  have hh : ∀ᶠ σ in 𝓝 (1 : ℝ),
      Real.exp (-(5 / 4 - σ) * Real.log 2 / 4) * (8 / 9) < r ^ 2 :=
    hc.tendsto.eventually_lt_const (by
      rw [show -(5 / 4 - (1 : ℝ)) * Real.log 2 / 4 = -Real.log 2 / 16 by ring]
      exact hgap)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hh
  let d := min (ε / 2) (1 / 8)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd1 : d ≤ 1 / 8 := min_le_right _ _
  refine ⟨1 + d, by linarith, by linarith, hb ?_⟩
  rw [Real.dist_eq, show 1 + d - 1 = d by ring, abs_of_pos hd]
  exact hdε

/-- The whole continuum of symbol rates beyond the limiting band-mass
threshold has negligible complementary interaction for all dominated
moving families. No fixed arithmetic family or numerical search is involved. -/
theorem tendsto_zetaArithmeticCenteredPart_band_rate_compl (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (y : ℝ) {r : ℝ} (hr : 0 < r)
    (hgap : Real.exp (-Real.log 2 / 16) * (8 / 9) < r ^ 2) :
    Tendsto (fun N ↦ zetaArithmeticCenteredPart (a N) p N y
      (zetaMoebiusResonantModes N (r ^ N))ᶜ) atTop (𝓝 0) := by
  obtain ⟨σ, hσ, hσ', hg⟩ := exists_zetaDominatedBand_exponent hgap
  exact tendsto_zetaArithmeticCenteredPart_exp_compl a ha p y hσ hσ' hr hg

/-- The genuine infinite sum is recovered from every rate in the
analytic admissible range, with both its band and frequency errors tending
to zero before any selected-zero normalization. -/
theorem tendsto_zetaArithmeticFilter_sub_band_rate (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (y : ℝ) {r : ℝ} (hr : 0 < r)
    (hgap : Real.exp (-Real.log 2 / 16) * (8 / 9) < r ^ 2) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (a N) p N y (zetaMoebiusResonantModes N (r ^ N)))
        atTop (𝓝 0) := by
  have h := (tendsto_zetaDominatedFilter_sub_band a ha p y).add
    (tendsto_zetaArithmeticCenteredPart_band_rate_compl a ha p y hr hgap)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaArithmeticBand_eq_centered_parts _ _ _ _ (zetaMoebiusResonantModes N (r ^ N))]
  ring

/-- A concrete smaller symbol threshold justified by the general band
mass estimate; it is independent of every arithmetic coefficient choice. -/
def zetaDominatedResonanceThreshold (N : ℕ) : ℝ := (14 / 15 : ℝ) ^ N

/-- The new threshold is positive at every finite scale. -/
theorem zetaDominatedResonanceThreshold_pos (N : ℕ) :
    0 < zetaDominatedResonanceThreshold N := by
  unfold zetaDominatedResonanceThreshold
  positivity

/-- The new retained symbol threshold tends to zero. -/
theorem tendsto_zetaDominatedResonanceThreshold :
    Tendsto zetaDominatedResonanceThreshold atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The retained region is contained in the previous region at every
scale; the improvement does not redefine the Fourier symbol. -/
theorem zetaDominatedResonantModes_subset (N : ℕ) :
    zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N) ⊆
      zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N) := by
  intro k hk
  have h : zetaDominatedResonanceThreshold N ≤ zetaMoebiusResonanceThreshold N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hk' : ‖cyclicDifferenceSymbol k‖ < zetaDominatedResonanceThreshold N := by
    simpa [zetaMoebiusResonantModes] using hk
  simpa [zetaMoebiusResonantModes] using hk'.trans_le h

/-- The two actual error rates for the smaller threshold are rational
and strictly below one, including the full cyclic boundary allowance. -/
theorem zetaQuarterGapError_narrow_eq (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaQuarterGapError p N y (48 / 49) (14 / 15) =
      (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) * (2400 / 2401 : ℝ) ^ N +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) * (1350 / 2401 : ℝ) ^ N := by
  norm_num [zetaQuarterGapError]

/-- An unconditional bound on the whole discarded centered interaction,
uniform in all dominated coefficient choices and all arithmetic sieves. -/
theorem norm_zetaArithmeticCenteredPart_narrow_compl_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaArithmeticCenteredPart a p N y
      (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))ᶜ‖ ≤
        2 * zetaMoebiusLogMajorantMass (9 / 8) *
          zetaQuarterGapError p N y (48 / 49) (14 / 15) := by
  exact centered_gap_bound a p N y _ _ _ (by norm_num)
    (zetaMoebiusLogMajorantMass_nonneg _) (by norm_num) hN
      (sum_norm_zetaArithmeticWeightedSamples_le a ha N)

/-- The whole discarded interaction tends to zero even before source
normalization, for every moving dominated complex coefficient family. -/
theorem tendsto_zetaArithmeticCenteredPart_narrow_compl (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticCenteredPart (a N) p N y
      (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦
    norm_zetaArithmeticCenteredPart_narrow_compl_le (a N) (ha N) p N y hN⟩)
  simpa only [mul_zero] using (tendsto_zetaQuarterGapError p y
    (by norm_num : (0 : ℝ) ≤ 48 / 49) (by norm_num : (0 : ℝ) < 14 / 15)
      (by norm_num)).const_mul (2 * zetaMoebiusLogMajorantMass (9 / 8))

/-- The true infinite series and the smaller retained interaction differ
by an explicit sum of band and frequency allowances, with no source premise. -/
theorem norm_zetaArithmeticFilter_sub_narrow_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart a p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))‖ ≤
      (1 / 2 : ℝ) ^ N * zetaMoebiusBandTailConstant p +
        2 * zetaMoebiusLogMajorantMass (9 / 8) *
          zetaQuarterGapError p N y (48 / 49) (14 / 15) := by
  have he : zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart a p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) =
      (zetaArithmeticFilter a p N (3 / 2 + I * y) - zetaArithmeticBand a p N y) +
        zetaArithmeticCenteredPart a p N y
          (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))ᶜ := by
    rw [zetaArithmeticBand_eq_centered_parts _ _ _ _
      (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_zetaDominatedFilter_sub_band_le a ha p N y)
    (norm_zetaArithmeticCenteredPart_narrow_compl_le a ha p N y hN))

/-- The actual infinite arithmetic sum is recovered from the retained
centered region with only independently vanishing band and frequency errors. -/
theorem tendsto_zetaArithmeticFilter_sub_narrow (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (a N) p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))) atTop (𝓝 0) := by
  have h := (tendsto_zetaDominatedFilter_sub_band a ha p y).add
    (tendsto_zetaArithmeticCenteredPart_narrow_compl a ha p y)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaArithmeticBand_eq_centered_parts _ _ _ _
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))]
  ring

end
end RiemannGaussian
