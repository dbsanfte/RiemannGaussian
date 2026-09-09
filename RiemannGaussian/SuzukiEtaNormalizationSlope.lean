/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaSignedReflection

/-!
# Exact normalization cancellation at actual eta carrier poles

The negative square in unnormalized curvature cannot be retained alone.
At a genuine zero of the literal carrier denominator, the derivative of
the normalization cancels the whole signed quadratic interaction, for
every complex weight. This is an exact local calculation, not a sign
estimate for the complete source or for its global integral.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

private lemma normSq_vertical_derivative {f : ℝ → ℂ} {g : ℂ} {t : ℝ}
    (hf : HasDerivAt f (I * g) t) :
    HasDerivAt (fun u => normSq (f u)) (2 * (f t * starRingEnd ℂ g).im) t := by
  have he : (fun u => normSq (f u)) = fun u => (f u * starRingEnd ℂ (f u)).re := by
    funext u
    rw [mul_conj, Complex.ofReal_re]
  rw [he]
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf.fun_mul hf.star)
  convert! h using 1
  simp only [star_def, map_mul, conj_I, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.reCLM_apply]
  ring

/-- The true normalization derivative contains both eta and denominator
channels. Neither channel is held constant in the weighted identity. -/
theorem deriv_suzukiEtaVerticalNormDenominator (r : ℝ) {sigma t : ℝ}
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain) :
    deriv (suzukiEtaVerticalNormDenominator r sigma) t =
      2 * (suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) *
        starRingEnd ℂ (deriv suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t))).im +
      2 * r ^ 2 * (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
        starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im := by
  have hf := normSq_vertical_derivative (hasDerivAt_pairedEtaVertical_comp
    (analyticOnNhd_pairedEtaCore _ hs.1).differentiableAt.hasDerivAt)
  have hg := normSq_vertical_derivative (hasDerivAt_pairedEtaVertical_comp
    (analyticAt_suzukiEtaCarrierDenominator_on_completionDomain hs).differentiableAt.hasDerivAt)
  have h := (hg.fun_add (hf.const_mul (r ^ 2))).deriv
  change deriv (suzukiEtaVerticalNormDenominator r sigma) t = _ at h
  exact h.trans (by ring)

private lemma current_eq_normSq_mul (sigma t : ℝ) :
    pairedEtaVerticalQuarticCurrent sigma t =
      (normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) : ℂ) *
        (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
          starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))) := by
  unfold pairedEtaVerticalQuarticCurrent complexQuarticCurrent
  rw [← mul_conj]
  ring

/-- At an actual carrier-denominator zero the relative normalization
slope is exactly twice the imaginary completion correction. No
derivative of the vanishing denominator is discarded away from that point. -/
theorem deriv_suzukiEtaVerticalNormDenominator_at_pole (r : ℝ) {sigma t : ℝ}
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hD : suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) = 0) :
    deriv (suzukiEtaVerticalNormDenominator r sigma) t =
      2 * (pairedEtaArithmeticXiRegularCorrection (pairedEtaVerticalArgument sigma t)).im *
        suzukiEtaVerticalNormDenominator r sigma t := by
  let s := pairedEtaVerticalArgument sigma t
  have hd : deriv pairedEtaCore s = -(1 + pairedEtaArithmeticXiRegularCorrection s) * pairedEtaCore s := by
    have h := hD
    rw [suzukiEtaCarrierDenominator,
      ← (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs.1).deriv] at h
    change deriv pairedEtaCore s + (1 + pairedEtaArithmeticXiRegularCorrection s) * pairedEtaCore s = 0 at h
    linear_combination h
  have hj : (pairedEtaCore s * starRingEnd ℂ (deriv pairedEtaCore s)).im =
      (pairedEtaArithmeticXiRegularCorrection s).im * normSq (pairedEtaCore s) := by
    rw [hd, map_mul, map_neg, map_add, map_one]
    have he : pairedEtaCore s *
        (-(1 + starRingEnd ℂ (pairedEtaArithmeticXiRegularCorrection s)) * starRingEnd ℂ (pairedEtaCore s)) =
        -(1 + starRingEnd ℂ (pairedEtaArithmeticXiRegularCorrection s)) * (normSq (pairedEtaCore s) : ℂ) := by
      rw [← mul_conj]
      ring
    rw [he]
    simp
  rw [deriv_suzukiEtaVerticalNormDenominator r hs, hD, zero_mul, Complex.zero_im, mul_zero, zero_add]
  change 2 * r ^ 2 * (pairedEtaCore s * starRingEnd ℂ (deriv pairedEtaCore s)).im = _
  rw [hj]
  unfold suzukiEtaVerticalNormDenominator
  rw [hD, normSq_zero, zero_add]
  dsimp only [s]
  ring

/-- At every genuine carrier-denominator zero, differentiation of the
normalization cancels the complete signed quadratic interaction, even
for a complex weight. Thus its negative square is not a free margin. -/
theorem suzukiEtaNormalization_quadratic_cancellation_at_pole
    (K : ℝ → ℂ) {r sigma t : ℝ} (hr : 0 < r)
    (hs : pairedEtaVerticalArgument sigma t ∈ pairedEtaCompletionDomain)
    (hD : suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t) = 0)
    (hEta : pairedEtaCore (pairedEtaVerticalArgument sigma t) ≠ 0) :
    2 * (deriv (suzukiEtaVerticalNormDenominator r sigma) t /
      suzukiEtaVerticalNormDenominator r sigma t) *
        (K t * pairedEtaVerticalQuarticCurrent sigma t).im =
      4 * (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
        starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im *
        ((K t).re * (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
          starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).im +
        (K t).im * (pairedEtaCore (pairedEtaVerticalArgument sigma t) *
          starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))).re) := by
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiEtaCarrierDenominator (pairedEtaVerticalArgument sigma t)) (Or.inl hEta)
  have hd0 : suzukiEtaVerticalNormDenominator r sigma t ≠ 0 := hp.ne'
  have hd := deriv_suzukiEtaVerticalNormDenominator r hs
  rw [hD, zero_mul, Complex.zero_im, mul_zero, zero_add] at hd
  rw [hd, current_eq_normSq_mul]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  have hden : suzukiEtaVerticalNormDenominator r sigma t =
      r ^ 2 * normSq (pairedEtaCore (pairedEtaVerticalArgument sigma t)) := by
    simp only [suzukiEtaVerticalNormDenominator, hD, normSq_zero, zero_add]
  rw [hden] at hd0 ⊢
  field_simp [hr.ne', (mul_ne_zero_iff.mp hd0).2]
  ring

/-- The same complete quadratic cancellation holds at every genuine
upper pole of the original xi carrier, with all arithmetic side
conditions derived from that pole. The complex weight is arbitrary. -/
theorem suzukiXiNormalization_quadratic_cancellation_at_upper_pole
    (rho : NontrivialZetaZero) (K : ℝ → ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hupper : 0 < z.im) (hE : suzukiXiEValue z = 0) (hA : riemannXiSpectral z ≠ 0) :
    let sigma := 1/2 + z.im
    let t := -z.re
    let d := suzukiEtaVerticalNormDenominator r sigma
    let J := pairedEtaCore (pairedEtaVerticalArgument sigma t) *
      starRingEnd ℂ (deriv pairedEtaCore (pairedEtaVerticalArgument sigma t))
    2 * (deriv d t / d t) * (K t * pairedEtaVerticalQuarticCurrent sigma t).im =
      4 * J.im * ((K t).re * J.im + (K t).im * J.re) := by
  have hz : suzukiEtaVerticalSpectralPoint (1/2 + z.im) (-z.re) = z := by
    apply Complex.ext <;> simp [suzukiEtaVerticalSpectralPoint]
  have hs : pairedEtaVerticalArgument (1/2 + z.im) (-z.re) = suzukiArithmeticZetaArgument z := by
    rw [← suzukiArithmeticZetaArgument_verticalSpectralPoint, hz]
  obtain ⟨hd, hn, hD, _ha, _hb⟩ := suzukiEtaUpperPole_arithmetic_geometry rho hupper hE hA
  exact suzukiEtaNormalization_quadratic_cancellation_at_pole K hr
    (hs ▸ hd) (hs ▸ hD) (hs ▸ hn)

end
end RiemannGaussian
