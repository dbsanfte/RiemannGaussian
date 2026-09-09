/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexSignedCurvature

/-!
# The signed current of the actual normalized eta source

The exact negative-square identity reaches the literal denominator. Its
derivative and complex phase remain explicit, together with the completion
curvature. The derived inequality is pointwise; its remainder has not been
bounded below the global reflected-zero source.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The usual arithmetic vertical parameter, with its orientation explicit. -/
def pairedEtaVerticalArgument (sigma t : ℝ) : ℂ := (sigma : ℂ) + (t : ℂ) * I

/-- The complete real smoothing denominator along an arithmetic line. -/
def suzukiEtaVerticalNormDenominator (r sigma t : ℝ) : ℝ :=
  normSq (suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t)) +
    r ^ 2 * normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t))

/-- The unnormalized quartic current of the actual infinite eta function. -/
def pairedEtaVerticalQuarticCurrent (sigma : ℝ) : ℝ → ℂ :=
  complexQuarticCurrent (fun t => pairedEtaCore (pairedEtaVerticalArgument sigma t))
    (fun t => deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))

/-- The actual varying normalized weight, before its derivative is taken. -/
def suzukiEtaNormalizedCurvatureWeight (P : ℝ → ℂ) (r sigma t : ℝ) : ℂ :=
  P t / (suzukiEtaVerticalNormDenominator r sigma t : ℂ) ^ 2

/-- A vertical holomorphic derivative retains the factor i. -/
theorem hasDerivAt_pairedEtaVertical_comp {f : ℂ → ℂ} {f' : ℂ} {sigma t : ℝ}
    (hf : HasDerivAt f f' (pairedEtaVerticalArgument sigma t)) :
    HasDerivAt (fun u => f (pairedEtaVerticalArgument sigma u)) (I * f') t := by
  have hline : HasDerivAt (fun z : ℂ => (sigma : ℂ) + z * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (sigma : ℂ)
  have h := (hf.comp (t : ℂ) hline).comp_ofReal
  simpa only [Function.comp_def, pairedEtaVerticalArgument, mul_comm] using h

private lemma eta_vertical_derivative {sigma t : ℝ}
    (hs : 0 < (pairedEtaVerticalArgument sigma t).re) :
    HasDerivAt (fun u => pairedEtaCore (pairedEtaVerticalArgument sigma u))
      (I * deriv pairedEtaCore (pairedEtaVerticalArgument sigma t)) t :=
  hasDerivAt_pairedEtaVertical_comp (analyticOnNhd_pairedEtaCore _ hs).differentiableAt.hasDerivAt

private lemma eta_vertical_second_derivative {sigma t : ℝ}
    (hs : 0 < (pairedEtaVerticalArgument sigma t).re) :
    HasDerivAt (fun u => deriv pairedEtaCore (pairedEtaVerticalArgument sigma u))
      (I * deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)) t :=
  hasDerivAt_pairedEtaVertical_comp (analyticOnNhd_pairedEtaCore _ hs).deriv.differentiableAt.hasDerivAt

/-- The true normalized weight is real differentiable wherever its
limiting numerator and denominator are not simultaneously zero. This
includes every genuine carrier pole. -/
theorem differentiableAt_suzukiEtaNormalizedCurvatureWeight {P : ℝ → ℂ} {r sigma t : ℝ}
    (hr : 0 < r) (hP : DifferentiableAt ℝ P t)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    DifferentiableAt ℝ (suzukiEtaNormalizedCurvatureWeight P r sigma) t := by
  have hf := (eta_vertical_derivative hs.1).differentiableAt
  have hg := (hasDerivAt_pairedEtaVertical_comp
    (analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hs).differentiableAt.hasDerivAt).differentiableAt
  have hd : DifferentiableAt ℝ (suzukiEtaVerticalNormDenominator r sigma) t := by
    unfold suzukiEtaVerticalNormDenominator
    simpa only [Complex.normSq_eq_norm_sq] using
      (hg.norm_sq (𝕜 := ℂ)).fun_add ((hf.norm_sq (𝕜 := ℂ)).const_mul (r ^ 2))
  have hdc := Complex.ofRealCLM.differentiableAt.comp t hd
  have hp := complexSmoothQuotient_denominator_pos hr hn
  have hz : (suzukiEtaVerticalNormDenominator r sigma t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  exact hP.div (hdc.pow 2) (pow_ne_zero 2 hz)

private lemma source_weighted_im (P : ℝ → ℂ) (r : ℝ) {sigma t : ℝ}
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain) :
    (P t * suzukiEtaSpectralSmoothSource r (pairedEtaVerticalArgument sigma t)).im =
      2 * r ^ 2 *
        ((suzukiEtaNormalizedCurvatureWeight P r sigma t *
          (pairedEtaCore (pairedEtaVerticalArgument sigma t) ^ 2 *
            starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t) ^ 2 -
              pairedEtaCore (pairedEtaVerticalArgument sigma t) *
                deriv (deriv pairedEtaCore) (pairedEtaVerticalArgument sigma t)))).re -
          normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2 *
            (suzukiEtaNormalizedCurvatureWeight P r sigma t *
              starRingEnd ℂ (deriv pairedEtaArithmeticXiRegularCorrection
                (pairedEtaVerticalArgument sigma t))).re) := by
  let s := pairedEtaVerticalArgument sigma t
  have he : P t * suzukiEtaSpectralSmoothSource r s =
      2 * I * (r : ℂ) ^ 2 *
        (suzukiEtaNormalizedCurvatureWeight P r sigma t *
            (pairedEtaCore s ^ 2 * starRingEnd ℂ
              (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s)) -
          ((normSq (pairedEtaCore s) : ℝ) : ℂ) ^ 2 *
            (suzukiEtaNormalizedCurvatureWeight P r sigma t *
              starRingEnd ℂ (deriv pairedEtaArithmeticXiRegularCorrection s))) := by
    rw [suzukiEtaSpectralSmoothSource_eq_curvature r hs]
    unfold suzukiEtaNormalizedCurvatureWeight suzukiEtaVerticalNormDenominator
    dsimp only [s]
    simp only [map_sub, map_mul, map_pow]
    rw [← mul_conj (pairedEtaCore (pairedEtaVerticalArgument sigma t))]
    ring
  change (P t * suzukiEtaSpectralSmoothSource r s).im = _
  rw [he]
  have hi (Z A : ℂ) (b : ℝ) :
      (2 * I * (r : ℂ) ^ 2 * (Z - (b : ℂ) ^ 2 * A)).im =
        2 * r ^ 2 * (Z.re - b ^ 2 * A.re) := by
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.sub_im, Complex.sub_re]
    ring
  exact hi _ _ _

/-- The complete normalized source has an exact signed current identity.
The normalization derivative, both complex weight channels, and the
completion curvature all remain. No favorable sign is assumed. -/
theorem suzukiEtaSpectralSmoothSource_weighted_im_eq_current {P : ℝ → ℂ} {r sigma t : ℝ}
    (hr : 0 < r) (hP : DifferentiableAt ℝ P t)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    (P t * suzukiEtaSpectralSmoothSource r (pairedEtaVerticalArgument sigma t)).im =
      2 * r ^ 2 *
        ((deriv (fun u => suzukiEtaNormalizedCurvatureWeight P r sigma u *
          pairedEtaVerticalQuarticCurrent sigma u) t).im -
        (deriv (suzukiEtaNormalizedCurvatureWeight P r sigma) t *
          pairedEtaVerticalQuarticCurrent sigma t).im -
        4 * (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
          starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im *
          ((suzukiEtaNormalizedCurvatureWeight P r sigma t).re *
            (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
              starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im +
          (suzukiEtaNormalizedCurvatureWeight P r sigma t).im *
            (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
              starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).re) -
        normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2 *
          (suzukiEtaNormalizedCurvatureWeight P r sigma t *
            starRingEnd ℂ (deriv pairedEtaArithmeticXiRegularCorrection
              (pairedEtaVerticalArgument sigma t))).re) := by
  rw [source_weighted_im P r hs]
  rw [complexSignedCurvature_weighted_re (eta_vertical_derivative hs.1)
    (eta_vertical_second_derivative hs.1)
    (differentiableAt_suzukiEtaNormalizedCurvatureWeight hr hP hs hn).hasDerivAt]
  rfl

/-- An unconditional pointwise signed upper bound for the complete
normalized eta source. The explicit phase defect and normalization
derivative are retained costs, not assumed small. -/
theorem suzukiEtaSpectralSmoothSource_weighted_im_le_current {P : ℝ → ℂ} {r sigma t : ℝ}
    (hr : 0 < r) (hP : DifferentiableAt ℝ P t)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hn : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0 ∨
      suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) ≠ 0) :
    (P t * suzukiEtaSpectralSmoothSource r (pairedEtaVerticalArgument sigma t)).im ≤
      2 * r ^ 2 *
        ((deriv (fun u => suzukiEtaNormalizedCurvatureWeight P r sigma u *
          pairedEtaVerticalQuarticCurrent sigma u) t).im -
        (deriv (suzukiEtaNormalizedCurvatureWeight P r sigma) t *
          pairedEtaVerticalQuarticCurrent sigma t).im +
        2 * (‖suzukiEtaNormalizedCurvatureWeight P r sigma t‖ -
          (suzukiEtaNormalizedCurvatureWeight P r sigma t).re) *
          normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
            starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))) -
        normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) ^ 2 *
          (suzukiEtaNormalizedCurvatureWeight P r sigma t *
            starRingEnd ℂ (deriv pairedEtaArithmeticXiRegularCorrection
              (pairedEtaVerticalArgument sigma t))).re) := by
  rw [source_weighted_im P r hs]
  have h := complexSignedCurvature_weighted_re_le (eta_vertical_derivative hs.1)
    (eta_vertical_second_derivative hs.1)
    (differentiableAt_suzukiEtaNormalizedCurvatureWeight hr hP hs hn).hasDerivAt
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (by positivity)

end
end RiemannGaussian
