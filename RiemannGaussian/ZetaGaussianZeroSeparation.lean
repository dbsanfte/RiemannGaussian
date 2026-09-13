/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianComplexDisplacement
import RiemannGaussian.ZetaGaussianMultiplicityDepth

/-!
# Finite Gaussian zero groups and explicit boundary separation

All selected zeros retain their distinct ordinates in one phase-family
budget. A quadratic cosine estimate controls their displacement from the
central ordinate. Consequently a boundary rectangle of depth twice the
explicit Gaussian width and vertical radius half that width contains at
most one zero, counted with multiplicity. This supplies genuine isolation
near either edge; it does not exclude a single simple zero in the rectangle
or bound the remaining signed prime tail.
-/

namespace RiemannGaussian.ZetaGaussianZeroSeparation
noncomputable section
open Complex
open ZetaGaussianScaledBandBudget GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds
open ZetaGaussianStripExplicit ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaGaussianNearCancellation ZetaGaussianDistanceRemainder
open ZetaAngularPhaseAllowance DerivativeOrderComparison
open ZetaNearOneBudgetLimit (scale)
open ZetaNearOneLocalDisc (center)
open scoped Classical

/-- The zero-damping Gaussian mass has a uniform linear dilation allowance. -/
theorem zero_damping_upper {q : ℝ} (hq : 1 ≤ q) :
    halfGaussian (gaussianScale q) 0 ≤ 225000 * q := by
  have hw := (width_bounds hq).1
  have hB : 4 * width q ^ 2 = gaussianScale q := by
    unfold width gaussianScale GaussianStripProfile.gaussianScale
    ring
  have hs := halfGaussian_scale hw 4 0
  rw [hB, zero_mul, halfGaussian_zero 4] at hs
  have hroot : Real.sqrt (Real.pi / 4) ≤ 1 := by
    have he := Real.sq_sqrt (show 0 ≤ Real.pi / 4 by positivity)
    nlinarith [Real.pi_lt_four, Real.sqrt_nonneg (Real.pi / 4)]
  have he : width q * (225000 * q) = (1 / 2 : ℝ) := by
    unfold width GaussianStripProfile.width
    field_simp
    norm_num
  apply (mul_le_mul_iff_right₀ hw).mp
  rw [he, hs]
  linarith

/-- Each zero in the scaled rectangle retains a large positive source
per unit of its actual multiplicity, despite its full imaginary displacement. -/
theorem compensated_lower {q t : ℝ} (hq : 1 ≤ q) (ρ : NontrivialZetaZero)
    (hdepth : 1 - ρ.1.re ≤ 2 * width q) (hheight : |ρ.1.im - t| ≤ width q / 2) :
    80000 * q * (analyticZetaZeroMultiplicity ρ : ℝ) ≤
      compensated (gaussianScale q) (halfWidth 9 (shift q)) (center (shift q) t) ρ := by
  obtain ⟨hw, hwu⟩ := width_bounds hq
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hB := (gaussianScale_bounds hq).1
  have hη := halfWidth_pos 9 hx
  have hshift : shift q = width q / 1000 := by
    unfold shift width GaussianStripProfile.shift
    ring
  have hscale : 4 * width q ^ 2 = gaussianScale q := by
    unfold width gaussianScale GaussianStripProfile.gaussianScale
    ring
  let z := center (shift q) t - ρ.1
  have hr : z.re = 1 + shift q - ρ.1.re := by simp [z, center]
  have hi : z.im = t - ρ.1.im := by simp [z, center]
  have hr0 : 0 < z.re := by rw [hr]; linarith [ρ.re_lt_one]
  have hru : z.re ≤ width q * (2001 / 1000) := by rw [hr, hshift]; linarith
  have hy : |z.im| ≤ width q / 2 := by simpa only [hi, abs_sub_comm] using hheight
  have hn : ‖z‖ < halfWidth 9 (shift q) := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hr0] at h
    have hηl := (geometry hq).1
    norm_num [GaussianStripProfile.width] at hwu
    linarith
  have hg := (ZetaGaussianMultiplicityDepth.scaled_tangent_lower hq (2001 / 1000)).trans
    (halfGaussian_antitone hB hru)
  have hy2 : z.im ^ 2 ≤ width q ^ 2 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg z.im) (by positivity : 0 ≤ width q / 2)).mpr hy
    rw [sq_abs] at h
    nlinarith only [h]
  have hratio : z.im ^ 2 / (4 * gaussianScale q) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [← hscale]
    nlinarith only [hy2]
  have hloss := mul_le_mul hratio (zero_damping_upper hq)
    (halfGaussian_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1 / 64)
  have hc : 1 / halfWidth 9 (shift q) ≤ 200 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 200) (geometry hq).1
    norm_num at h
    simpa only [one_div] using h
  have hs := GaussianComplexDisplacement.source_re_lower hB hη hn.le hr0.le
  have hsource : 80000 * q ≤
      (SmoothedCotangentSource.source (GaussianComplexHalfMoments.transform (gaussianScale q))
        (halfWidth 9 (shift q)) z).re := by
    nlinarith only [hg, hloss, hc, hs, hq]
  have hm := mul_le_mul_of_nonneg_right hsource
    (Nat.cast_nonneg (α := ℝ) (analyticZetaZeroMultiplicity ρ))
  have hcenter : 1 ≤ (center (shift q) t).re := by
    simpa [center] using (show 1 ≤ 1 + shift q by linarith)
  have hp : 0 ≤ nearPoisson (halfWidth 9 (shift q)) (center (shift q) t) ρ :=
    (show 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) / (2 * halfWidth 9 (shift q)) by positivity).trans
      (nearPoisson_lower hη hcenter ρ hn)
  have hreserve := mul_nonneg (factor_bounds hq).1 hp
  simp only [compensated, nearSource, nearRestrict, show ‖center (shift q) t - ρ.1‖ <
    halfWidth 9 (shift q) from hn, if_true, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  change 80000 * q * (analyticZetaZeroMultiplicity ρ : ℝ) ≤
    (analyticZetaZeroMultiplicity ρ : ℝ) * _ + factor 9 (gaussianScale q) (shift q) * _
  nlinarith only [hm, hreserve]

/-- Every eligible phase family bounds the actual total multiplicity of
the complete boundary rectangle by one. The three prime responses share
one phase kernel throughout the proof. -/
theorem family_sum_le_one {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (ha0 : a 0 ≤ 37 / 200) (ha1 : 79 / 250 ≤ a 1)
    (hW : mass a ≤ 61 / 100) (hF : frequencyCost a ω ≤ 1 / 4)
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) (hL : scale t ≤ 320000 * q)
    (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, 1 - ρ.1.re ≤ 2 * width q ∧ |ρ.1.im - t| ≤ width q / 2) :
    ∑ ρ ∈ S, analyticZetaZeroMultiplicity ρ ≤ 1 := by
  obtain ⟨hx, hxu⟩ := shift_bounds hq
  have hx' : shift q ≤ delta 9 / 4 := hxu.trans
    (by norm_num [GaussianStripProfile.shift, GaussianStripProfile.width, delta, DerivativePowerExponents.alpha])
  have hscale := ZetaGaussianBandBudget.scale_lower ht
  have hbudget := (finite_source_add_mixedWork_le_exactBudget ha hs hω0 hω1 hω hlog 9
    (by norm_num) (gaussianScale_bounds hq).1 hx hx' (M := 0) (by norm_num) t S hscale).trans
      (exactBudget_le_budget ha hs hω0 hω hlog 9 (by norm_num) (gaussianScale_bounds hq).1
        hx hx' (by linarith) hscale (by norm_num))
  have hb := budget_le (ha 0) ha0 (tsum_nonneg (tail_nonneg ha)) hW hF hq ht hL
  have hmixed := mixedWork_nonneg ha hs hp 9 (gaussianScale_bounds hq).1 hx t
  have hsource := Finset.sum_le_sum (fun ρ hρ => compensated_lower hq ρ (hS ρ hρ).1 (hS ρ hρ).2)
  rw [← Finset.mul_sum] at hsource
  have hw := mul_le_mul ha1 hsource (by positivity) (ha 1)
  by_contra! hn
  have hn' : (2 : ℝ) ≤ ∑ ρ ∈ S, (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast (show 2 ≤ ∑ ρ ∈ S, analyticZetaZeroMultiplicity ρ by omega)
  have hqm := mul_le_mul_of_nonneg_left hn' (show 0 ≤ q by linarith)
  nlinarith only [hbudget, hb, hmixed, hw, hqm, hq]

/-- The exact contact family discharges every arithmetic and phase premise
of the finite-group bound at every eligible dilation and center. -/
theorem scaled_sum_le_one {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|)
    (hL : scale t ≤ 320000 * q) (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, 1 - ρ.1.re ≤ 2 * width q ∧ |ρ.1.im - t| ≤ width q / 2) :
    ∑ ρ ∈ S, analyticZetaZeroMultiplicity ρ ≤ 1 := by
  have h0 : phaseContactExactFamily 0 = phaseContactExactCoefficients 0 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
  have h1 : phaseContactExactFamily 1 = phaseContactExactCoefficients 1 := by
    simpa [phaseContactExactFamily, phaseContactFrequency] using
      phaseContactFrequencyFamily_apply phaseContactExactCoefficients 1
  exact family_sum_le_one phaseContactExactFamily_nonneg ZetaExactPhaseAngularExclusion.exact_summable
    phaseContactExactFamily_kernel_nonneg (by norm_num) (by norm_num)
    (fun n hn => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    ZetaExactPhaseAngularExclusion.exact_log_summable
    (by rw [h0]; exact GaussianFermiProfileSurplus.exact_constant_upper)
    (by rw [h1]; exact GaussianFermiProfileSurplus.exact_first_lower)
    ZetaExactPhaseAngularExclusion.mass_bounds.2 ZetaGaussianBandExclusion.exact_frequency_cost
    hq ht hL S hS

/-- At every explicit eligible height, the full right boundary rectangle
contains at most one zero, with analytic multiplicity counted. -/
theorem right_sum_le_one {t : ℝ} (ht : 1000000 ≤ |t|) (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, 1 - ρ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |ρ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2) :
    ∑ ρ ∈ S, analyticZetaZeroMultiplicity ρ ≤ 1 :=
  scaled_sum_le_one (le_max_left _ _) ht (ZetaGaussianAllHeight.scale_le_dilation t) S hS

/-- Reflection transfers the entire finite multiplicity count to the
left boundary rectangle, with the same center and explicit dimensions. -/
theorem left_sum_le_one {t : ℝ} (ht : 1000000 ≤ |t|) (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, ρ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |ρ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2) :
    ∑ ρ ∈ S, analyticZetaZeroMultiplicity ρ ≤ 1 := by
  have hi : Function.Injective NontrivialZetaZero.conjugatePartner :=
    (show Function.Involutive NontrivialZetaZero.conjugatePartner from
      NontrivialZetaZero.conjugatePartner_conjugatePartner).injective
  have h := right_sum_le_one ht (S.image NontrivialZetaZero.conjugatePartner) (by
    intro τ hτ
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hτ
    simpa [NontrivialZetaZero.conjugatePartner_coe] using hS ρ hρ)
  simpa only [Finset.sum_image hi.injOn, analyticZetaZeroMultiplicity_conjugatePartner] using h

/-- Two actual zeros in the same right boundary rectangle coincide. -/
theorem eq_of_mem_right_rectangle {t : ℝ} (ht : 1000000 ≤ |t|) (ρ τ : NontrivialZetaZero)
    (hρ : 1 - ρ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |ρ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2)
    (hτ : 1 - τ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |τ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2) : ρ = τ := by
  by_contra hne
  have h := right_sum_le_one ht {ρ, τ} (by
    intro ξ hξ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hξ
    rcases hξ with rfl | rfl
    · exact hρ
    · exact hτ)
  rw [Finset.sum_pair hne] at h
  have := analyticZetaZeroMultiplicity_positive ρ
  have := analyticZetaZeroMultiplicity_positive τ
  omega

/-- Two actual zeros in the same left boundary rectangle coincide. -/
theorem eq_of_mem_left_rectangle {t : ℝ} (ht : 1000000 ≤ |t|) (ρ τ : NontrivialZetaZero)
    (hρ : ρ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |ρ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2)
    (hτ : τ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth t ∧
      |τ.1.im - t| ≤ ZetaGaussianAllHeight.explicitWidth t / 2) : ρ = τ := by
  have h := eq_of_mem_right_rectangle ht (NontrivialZetaZero.conjugatePartner ρ)
    (NontrivialZetaZero.conjugatePartner τ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using hρ)
    (by simpa [NontrivialZetaZero.conjugatePartner_coe] using hτ)
  simpa only [NontrivialZetaZero.conjugatePartner_conjugatePartner] using
    congrArg NontrivialZetaZero.conjugatePartner h

/-- Distinct zeros in a common right boundary layer have explicit
ordinate separation. The width is evaluated at the first zero's height. -/
theorem ordinate_separation (ρ τ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hne : ρ ≠ τ)
    (hρ : 1 - ρ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth ρ.1.im)
    (hτ : 1 - τ.1.re ≤ 2 * ZetaGaussianAllHeight.explicitWidth ρ.1.im) :
    ZetaGaussianAllHeight.explicitWidth ρ.1.im / 2 < |τ.1.im - ρ.1.im| := by
  by_contra! h
  exact hne (eq_of_mem_right_rectangle ht ρ τ
    ⟨hρ, by simpa using (half_pos (ZetaGaussianAllHeight.explicitWidth_pos ρ.1.im)).le⟩ ⟨hτ, h⟩)

/-- Every actual zero in the indicated layer is isolated from all
other nontrivial zeros by a concrete Euclidean distance, at either edge. -/
theorem distance_separation (ρ τ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hne : ρ ≠ τ)
    (hdepth : min ρ.1.re (1 - ρ.1.re) ≤ 3 / 2 * ZetaGaussianAllHeight.explicitWidth ρ.1.im) :
    ZetaGaussianAllHeight.explicitWidth ρ.1.im / 2 < ‖τ.1 - ρ.1‖ := by
  by_contra! hn
  have hw := ZetaGaussianAllHeight.explicitWidth_pos ρ.1.im
  have hr : |τ.1.re - ρ.1.re| ≤ ZetaGaussianAllHeight.explicitWidth ρ.1.im / 2 := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (τ.1 - ρ.1)).trans hn
  have hi : |τ.1.im - ρ.1.im| ≤ ZetaGaussianAllHeight.explicitWidth ρ.1.im / 2 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (τ.1 - ρ.1)).trans hn
  have hρim : |ρ.1.im - ρ.1.im| ≤ ZetaGaussianAllHeight.explicitWidth ρ.1.im / 2 := by
    simp only [sub_self, abs_zero]
    positivity
  rcases min_le_iff.mp hdepth with hleft | hright
  · exact hne (eq_of_mem_left_rectangle ht ρ τ ⟨by linarith, hρim⟩
      ⟨by linarith [(abs_le.mp hr).2], hi⟩)
  · exact hne (eq_of_mem_right_rectangle ht ρ τ ⟨by linarith, hρim⟩
      ⟨by linarith [(abs_le.mp hr).1], hi⟩)

/-- The same genuine isolation gives a strict bound for each reciprocal
zero-distance factor. It does not bound a whole growing filter product. -/
theorem inverse_distance_bound (ρ τ : NontrivialZetaZero) (ht : 1000000 ≤ |ρ.1.im|)
    (hne : ρ ≠ τ)
    (hdepth : min ρ.1.re (1 - ρ.1.re) ≤ 3 / 2 * ZetaGaussianAllHeight.explicitWidth ρ.1.im) :
    1 / ‖τ.1 - ρ.1‖ < 2 / ZetaGaussianAllHeight.explicitWidth ρ.1.im := by
  have h := one_div_lt_one_div_of_lt (half_pos (ZetaGaussianAllHeight.explicitWidth_pos ρ.1.im))
    (distance_separation ρ τ ht hne hdepth)
  simpa only [one_div_div] using h

end
end RiemannGaussian.ZetaGaussianZeroSeparation
