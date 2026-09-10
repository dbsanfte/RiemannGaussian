/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaQuarterKernelFourierBudget

/-!
# The source-scale obstruction to decoupling the resonant Fourier factors

The exact Laplace tests force the fractional absolute kernel budget to
grow beyond the selected geometric source scale. This is an independent
kernel calculation, not a consequence of assuming arithmetic decay fails.
The actual signed interaction remains available and is not bounded here.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A nonzero polynomial evaluation at any eligible smaller damping
forces source-normalized growth of the complete fractional kernel mass. -/
theorem tendsto_zetaQuarterKernel_fractionalMass_mul_pow_of_eval (p : Polynomial ℂ) (y : ℝ)
    {u τ d : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hd : 1 / 4 + τ < d) (hdu : d < u) (hp : p.eval (d : ℂ)⁻¹ ≠ 0) :
    Tendsto (fun N ↦ u ^ (N + 1) *
      fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have hbase : 1 < u * d⁻¹ := by rw [← div_eq_mul_inv, one_lt_div hd0]; exact hdu
  have hg := (tendsto_pow_atTop_atTop_of_one_lt hbase).comp (tendsto_add_atTop_nat 1)
  have hg' := Filter.Tendsto.atTop_mul_const (norm_pos_iff.mpr hp) hg
  have he := ((tendsto_pow_atTop_nhds_zero_of_lt_one hu0.le hu1).comp
    (tendsto_add_atTop_nat 1)).mul_const (zetaQuarterKernelInterpolationConstant p y / (d - 1 / 4))
  simp only [zero_mul] at he
  have hA : 0 < 2 / (d - 1 / 4 - τ) := div_pos (by norm_num) (by linarith)
  apply tendsto_atTop.2
  intro B
  filter_upwards [hg'.eventually_ge_atTop ((2 / (d - 1 / 4 - τ)) * B + 1),
    he.eventually_lt_const (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop 1] with N hB heN hN
  have h := mul_le_mul_of_nonneg_left
    (zetaQuarterKernel_laplace_le_fractionalFourierMass p N y hN hτ0 hτ1 hd)
    (pow_nonneg hu0.le (N + 1))
  have hex : u ^ (N + 1) * (d⁻¹ ^ (N + 1) * ‖p.eval (d : ℂ)⁻¹‖) =
      (u * d⁻¹) ^ (N + 1) * ‖p.eval (d : ℂ)⁻¹‖ := by rw [mul_pow]; ring
  rw [hex] at h
  dsimp only [Function.comp_def] at hB heN
  by_contra! hbad
  nlinarith [mul_pos hA (sub_pos.mpr hbad)]

/-- Any nonzero evaluation at the selected scale admits a smaller
eligible damping with nonzero evaluation. This is a continuity argument
for the whole fixed polynomial, with no coefficient search. -/
theorem exists_zetaFilter_laplace_test (p : Polynomial ℂ) {u τ : ℝ}
    (hτ0 : 0 ≤ τ) (hu : 1 / 4 + τ < u) (hp : p.eval (u : ℂ)⁻¹ ≠ 0) :
    ∃ d : ℝ, 1 / 4 + τ < d ∧ d < u ∧ p.eval (d : ℂ)⁻¹ ≠ 0 := by
  have hu0 : 0 < u := by linarith
  have hc : ContinuousAt (fun x : ℝ ↦ p.eval (x : ℂ)⁻¹) u :=
    p.continuous.continuousAt.comp (Complex.continuous_ofReal.continuousAt.inv₀
      (Complex.ofReal_ne_zero.mpr hu0.ne'))
  obtain ⟨l, r, hur, hsub⟩ := (hc.eventually_ne hp).exists_Ioo_subset
  obtain ⟨d, hld, hdu⟩ := exists_between (max_lt hur.1 hu)
  exact ⟨d, (le_max_right _ _).trans_lt hld, hdu,
    hsub ⟨(le_max_left _ _).trans_lt hld, hdu.trans hur.2⟩⟩

/-- Source-normalized absolute mass diverges for every fixed polynomial
that preserves the selected scale, whenever its fractional exponent is
below the damping gap. -/
theorem tendsto_zetaQuarterKernel_fractionalMass_mul_pow (p : Polynomial ℂ) (y : ℝ)
    {u τ : ℝ} (hu1 : u < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hu : 1 / 4 + τ < u) (hp : p.eval (u : ℂ)⁻¹ ≠ 0) :
    Tendsto (fun N ↦ u ^ (N + 1) *
      fractionalFourierMass τ (zetaQuarterKernelSamples p N y) Finset.univ) atTop atTop := by
  obtain ⟨d, hd, hdu, hpd⟩ := exists_zetaFilter_laplace_test p hτ0 hu hp
  exact tendsto_zetaQuarterKernel_fractionalMass_mul_pow_of_eval p y (by linarith)
    hu1 hτ0 hτ1 hd hdu hpd

/-- The absolute fractional kernel mass outside the shrinking resonant
region independently tends to zero. The full boundary cost is included. -/
theorem tendsto_zetaQuarterKernel_fractionalMass_compl (p : Polynomial ℂ) (y : ℝ)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    Tendsto (fun N ↦ fractionalFourierMass τ (zetaQuarterKernelSamples p N y)
      (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun N ↦ fractionalFourierMass_nonneg _ _ _) (fun N ↦
    fractionalFourierMass_le_difference (zetaQuarterKernelSamples p N y)
      (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))ᶜ 2 hτ0 hτ1
      (zetaMoebiusResonanceThreshold_pos N) (by
        intro k hk
        have hn := Finset.mem_compl.mp hk
        simpa [zetaMoebiusResonantModes, not_lt] using hn))
  simpa only [mul_zero, mul_assoc] using
    (tendsto_shrinking_gap_cyclicSecond_quarterKernel p y).const_mul 2

/-- The same independent growth is confined to the shrinking resonant
region; its complement cannot account for the absolute-budget obstruction. -/
theorem tendsto_zetaQuarterKernel_resonantFractionalMass_mul_pow (p : Polynomial ℂ) (y : ℝ)
    {u τ : ℝ} (hu1 : u < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hu : 1 / 4 + τ < u) (hp : p.eval (u : ℂ)⁻¹ ≠ 0) :
    Tendsto (fun N ↦ u ^ (N + 1) *
      fractionalFourierMass τ (zetaQuarterKernelSamples p N y)
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))) atTop atTop := by
  have hu0 : 0 ≤ u := by linarith
  have ht := tendsto_zetaQuarterKernel_fractionalMass_mul_pow p y hu1 hτ0 hτ1 hu hp
  have he := ((tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).comp
    (tendsto_add_atTop_nat 1)).mul (tendsto_zetaQuarterKernel_fractionalMass_compl p y hτ0 hτ1)
  simp only [zero_mul] at he
  apply tendsto_atTop.2
  intro B
  filter_upwards [ht.eventually_ge_atTop (B + 1),
    he.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hB heN
  have hs := congrArg (fun x : ℝ ↦ u ^ (N + 1) * x)
    (fractionalFourierMass_add_compl τ (zetaQuarterKernelSamples p N y)
      (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)))
  rw [mul_add] at hs
  dsimp only [Function.comp_def] at heN
  linarith

/-- The actual pole-jet filter preserves its selected real reciprocal
scale exactly, including the normalization of the extra pole factor. -/
theorem zetaRightHalfPoleJetFilter_eval_selected (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    (zetaRightHalfPoleJetFilter rho hrho).eval (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) = 1 := by
  have hbc : (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) ≠
      ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹ := by
    intro h
    have he := congrArg Complex.re (inv_injective h)
    norm_num at he
    linarith [NontrivialZetaZero.re_lt_one rho]
  rw [zetaRightHalfPoleJetFilter, zetaPoleJetLift_eval_self _ hbc, zetaRightHalfZeroModeFilter]
  have he : (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) = -(((rho.1.re - 3 / 2 : ℝ) : ℂ)⁻¹) := by
    rw [← inv_neg]
    congr 1
    push_cast
    ring
  rw [he]
  apply adaptiveZetaZeroModeFilter_eval_self
  rw [mem_adaptiveZetaZeroSupport, divisor_adaptiveZetaPoleRemoved_nontrivialZero]
  exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'

/-- For every hypothetical right-half zero and every exponent strictly
below `5/4-beta`, the actual source-normalized resonant absolute kernel
budget diverges. This is proved from independent kernel estimates and
filter algebra, without using the signed arithmetic source limit. -/
theorem tendsto_zetaRightHalf_resonantFractionalMass_atTop (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 5 / 4 - rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      fractionalFourierMass τ (zetaQuarterKernelSamples (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))) atTop atTop := by
  apply tendsto_zetaQuarterKernel_resonantFractionalMass_mul_pow _ _ (by linarith) hτ0
    (by linarith) (by linarith)
  rw [zetaRightHalfPoleJetFilter_eval_selected]
  exact one_ne_zero

/-- Even a moving choice of fractional exponents up to and including
one quarter cannot make the absolute kernel allowance source-bounded.
Thus approaching the endpoint with moment order does not escape this audit. -/
theorem tendsto_zetaRightHalf_resonantFractionalMass_moving_atTop (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (τ : ℕ → ℝ) (hτ0 : ∀ N, 0 ≤ τ N) (hτ1 : ∀ N, τ N ≤ 1 / 4) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      fractionalFourierMass (τ N)
        (zetaQuarterKernelSamples (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))) atTop atTop := by
  have hbase := tendsto_zetaRightHalf_resonantFractionalMass_atTop rho hrho
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith [NontrivialZetaZero.re_lt_one rho])
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [] with N
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith [NontrivialZetaZero.re_lt_one rho]) _)
  apply fractionalFourierMass_antitone_exponent _ _ (hτ0 N) (hτ1 N)
  intro k hk
  have hg : ‖cyclicDifferenceSymbol k‖ < zetaMoebiusResonanceThreshold N := by
    simpa [zetaMoebiusResonantModes] using hk
  exact hg.le.trans (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 31 / 32) (by norm_num))

/-- The arithmetic majorant multiplying the fractional kernel mass has
a fixed positive floor throughout its admissible exponent range. -/
theorem zetaMoebiusLogMajorantMass_fractional_lower {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1 / 4) :
    Real.log 2 * Real.exp (-(5 / 4 : ℝ) * Real.log 2) ≤ zetaMoebiusLogMajorantMass (5 / 4 - τ) := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hm : Real.log 2 ≤ zetaMoebiusLogMajorant 2 := by
    have h := Finset.single_le_sum (s := (2 : ℕ).divisorsAntidiagonal)
      (f := fun a : ℕ × ℕ ↦ Real.log a.2)
      (fun a _ ↦ Real.log_natCast_nonneg a.2)
      (show (1, 2) ∈ (2 : ℕ).divisorsAntidiagonal from Nat.mem_divisorsAntidiagonal.mpr (by norm_num))
    simpa only [zetaMoebiusLogMajorant, Nat.cast_ofNat] using h
  have hw : Real.exp (-(5 / 4 : ℝ) * Real.log 2) ≤ zetaPrimeExpWeight (5 / 4 - τ) 2 := by
    unfold zetaPrimeExpWeight
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hh := (summable_zetaMoebiusLogMajorant (σ := 5 / 4 - τ) (by linarith)).le_tsum 2
    (fun n _ ↦ mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
  exact (mul_le_mul hm hw (Real.exp_pos _).le (zetaMoebiusLogMajorant_nonneg 2)).trans hh

/-- The complete actual norm allowance, including its arithmetic
majorant, diverges at the selected source scale for every moving admissible
fractional exponent. Its failure is therefore not repaired by that prefactor. -/
theorem tendsto_zetaRightHalf_centeredFractionalAllowance_atTop (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (τ : ℕ → ℝ) (hτ0 : ∀ N, 0 ≤ τ N) (hτ1 : ∀ N, τ N < 1 / 4) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (2 * zetaMoebiusLogMajorantMass (5 / 4 - τ N) *
        fractionalFourierMass (τ N)
          (zetaQuarterKernelSamples (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
          (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)))) atTop atTop := by
  have ht := tendsto_zetaRightHalf_resonantFractionalMass_moving_atTop rho hrho τ hτ0
    (fun N ↦ (hτ1 N).le)
  have hc : 0 < 2 * (Real.log 2 * Real.exp (-(5 / 4 : ℝ) * Real.log 2)) := by positivity
  have hh := ht.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [] with N
  have hW := fractionalFourierMass_nonneg (τ N)
    (zetaQuarterKernelSamples (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
    (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))
  have hu : 0 ≤ (3 / 2 - rho.1.re) ^ (N + 1) :=
    pow_nonneg (by linarith [NontrivialZetaZero.re_lt_one rho]) _
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (zetaMoebiusLogMajorantMass_fractional_lower (hτ0 N) (hτ1 N))
      (by norm_num : (0 : ℝ) ≤ 2)) (mul_nonneg hu hW)
  convert h using 1
  ring

end
end RiemannGaussian
