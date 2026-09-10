/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexSignedCurvature
import RiemannGaussian.GaussianSchwartz
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration of the signed quartic curvature

The negative square is completed before integration. The exact identity
keeps the square and its Gaussian correction together. Polynomial growth
is used only to justify integrability and the disappearance of the full
current at both ends of the real line.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

/-- A Gaussian times a measurable function of polynomial growth is
integrable, with the polynomial measured from the same Gaussian center. -/
theorem integrable_translatedGaussian_mul_of_polynomial_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {tau : ℝ} (htau : 0 < tau) (c : ℝ)
    (hf : AEStronglyMeasurable f) {C : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hbound : ∀ t, ‖f t‖ ≤ C * (1 + |t - c|) ^ n) :
    Integrable (fun t => translatedGaussian tau c t • f t) := by
  have hg := (integrable_exp_neg_mul_sq htau).comp_sub_right c
  have hp := ((centeredGaussianSchwartz ⟨tau, htau⟩).integrable_pow_mul volume n).comp_sub_right c
  simp only [centeredGaussianSchwartz_apply, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] at hp
  have hmajor := ((hg.add hp).const_mul ((2 : ℝ) ^ (n - 1))).const_mul C
  apply hmajor.mono'
  · have hc : Continuous (translatedGaussian tau c) := by unfold translatedGaussian; fun_prop
    exact hc.aestronglyMeasurable.smul hf
  · filter_upwards with t
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < translatedGaussian tau c t from Real.exp_pos _)]
    have hpow := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg (t - c)) n
    simp only [one_pow] at hpow
    calc
      _ ≤ translatedGaussian tau c t * (C * (1 + |t - c|) ^ n) :=
        mul_le_mul_of_nonneg_left (hbound t) (Real.exp_pos _).le
      _ ≤ translatedGaussian tau c t * (C * ((2 : ℝ) ^ (n - 1) *
          (1 + |t - c| ^ n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC) (Real.exp_pos _).le
      _ = _ := by simp only [translatedGaussian, Pi.add_apply]; ring

/-- The vertical quartic curvature has an exact completed-square
identity for a Gaussian. Its current derivative remains explicit. -/
theorem complexSignedCurvature_gaussian_square {f g : ℝ → ℂ} {h : ℂ}
    {t tau c : ℝ} (hf : HasDerivAt f (I * g t) t)
    (hg : HasDerivAt g (I * h) t) :
    translatedGaussian tau c t * (f t ^ 2 * starRingEnd ℂ (g t ^ 2 - f t * h)).re =
      (deriv (fun u => (translatedGaussian tau c u : ℂ) * complexQuarticCurrent f g u) t).im -
        4 * translatedGaussian tau c t *
          ((f t * starRingEnd ℂ (g t)).im - tau * (t - c) * normSq (f t) / 4) ^ 2 +
        tau ^ 2 / 4 * (t - c) ^ 2 * translatedGaussian tau c t * normSq (f t) ^ 2 := by
  have hw : HasDerivAt (translatedGaussian tau c)
      (-2 * tau * (t - c) * translatedGaussian tau c t) t := by
    convert ((((hasDerivAt_id t).sub_const c).pow 2).const_mul (-tau)).exp using 1
    · funext u
      simp only [translatedGaussian, Pi.pow_apply, id_eq]
    · simp only [translatedGaussian, Pi.pow_apply, id_eq]
      ring
  have he := complexSignedCurvature_real_weight hf hg hw
  have ht : (complexQuarticCurrent f g t).im =
      normSq (f t) * (f t * starRingEnd ℂ (g t)).im := by
    have ht : complexQuarticCurrent f g t =
        (normSq (f t) : ℂ) * (f t * starRingEnd ℂ (g t)) := by
      rw [← Complex.mul_conj]
      dsimp [complexQuarticCurrent]
      ring
    rw [ht]
    simp
  rw [ht] at he
  nlinarith [he]

end
end RiemannGaussian
