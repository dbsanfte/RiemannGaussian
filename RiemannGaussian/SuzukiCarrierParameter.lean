/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaClearedDenominator
import RiemannGaussian.SuzukiEtaClearedPoleOrder

/-!
# Coupling the full eta numerator and denominator through a parameter

The affine family `a A + i A'` includes the original Suzuki denominator
at `a = 1`. Its cleared eta realization has parameter derivative exactly
`F eta`. Thus the original carrier is a parameter logarithmic derivative
of the full denominator, including its moving poles. This is distinct
from taking a spatial derivative of a chosen analytic unit.

The quotient below is only identified with the original carrier where
the original denominator is nonzero. At a pole its totalized value is
not asserted to be an analytic extension.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The affine complex-parameter family of full spectral denominators. -/
def suzukiXiAffineDenominator (a z : ℂ) : ℂ :=
  a * riemannXiSpectral z + I * deriv riemannXiSpectral z

/-- The associated quotient; its meromorphic interpretation requires
keeping the denominator divisor, including common zeros. -/
def suzukiXiAffineCarrier (a z : ℂ) : ℂ :=
  I * riemannXiSpectral z / suzukiXiAffineDenominator a z

/-- The affine family in the same cleared eta normalization as the
actual carrier. No completion or dyadic term is omitted. -/
def suzukiEtaAffineClearedDenominator (a s : ℂ) : ℂ :=
  suzukiEtaClearedCarrierDenominator s +
    (a - 1) * (pairedEtaFactor s * pairedEtaCore s)

/-- The unit member is the original entire denominator. -/
@[simp] theorem suzukiXiAffineDenominator_one (z : ℂ) :
    suzukiXiAffineDenominator 1 z = suzukiXiEValue z := by
  simp [suzukiXiAffineDenominator, suzukiXiEValue_eq]

/-- The unit quotient agrees with the literal Suzuki carrier on its
actual regular domain. -/
theorem suzukiXiAffineCarrier_one {z : ℂ} (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiAffineCarrier 1 z = suzukiXiZeroCarrier z := by
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  simp [suzukiXiAffineCarrier]

/-- Exact affine dependence, before division or taking norms. -/
theorem suzukiXiAffineDenominator_eq (a z : ℂ) :
    suzukiXiAffineDenominator a z =
      suzukiXiEValue z + (a - 1) * riemannXiSpectral z := by
  simp only [suzukiXiAffineDenominator, suzukiXiEValue_eq]
  ring

/-- The complete parameter family remains an entire spatial function. -/
theorem analyticAt_suzukiXiAffineDenominator (a z : ℂ) :
    AnalyticAt ℂ (suzukiXiAffineDenominator a) z := by
  exact (analyticAt_const.mul (analyticAt_riemannXiSpectral z)).add
    (analyticAt_const.mul (analyticAt_riemannXiSpectral z).deriv)

/-- The cleared family equals the full eta derivative and completion
expression with the constant coefficient replaced by `a`. -/
theorem suzukiEtaAffineClearedDenominator_eq (a s : ℂ) :
    suzukiEtaAffineClearedDenominator a s =
      pairedEtaFactor s * pairedEtaArithmeticDerivativeValue s +
        ((a + suzukiChebyshevMellinCompletedCorrection s) * pairedEtaFactor s -
          deriv pairedEtaFactor s) * pairedEtaCore s := by
  unfold suzukiEtaAffineClearedDenominator suzukiEtaClearedCarrierDenominator
  ring

/-- The parameter derivative is exactly the coupled arithmetic numerator. -/
theorem hasDerivAt_suzukiEtaAffineClearedDenominator (a s : ℂ) :
    HasDerivAt (fun b => suzukiEtaAffineClearedDenominator b s)
      (pairedEtaFactor s * pairedEtaCore s) a := by
  simpa [suzukiEtaAffineClearedDenominator] using
    (((hasDerivAt_id a).sub_const 1).mul_const
      (pairedEtaFactor s * pairedEtaCore s)).const_add
        (suzukiEtaClearedCarrierDenominator s)

private lemma completed_numerator {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    pairedEtaXiCompletionNumerator s * (pairedEtaFactor s * pairedEtaCore s) =
      pairedEtaFactor s ^ 2 * riemannXi s := by
  by_cases hF : pairedEtaFactor s = 0
  · simp [hF]
  · have hx := pairedEtaCompletedXi_eq_riemannXi_on_completionDomain ⟨hs, h1, hF⟩
    change pairedEtaXiCompletionNumerator s / pairedEtaFactor s * pairedEtaCore s = _ at hx
    field_simp at hx
    calc
      _ = pairedEtaFactor s * (pairedEtaXiCompletionNumerator s * pairedEtaCore s) := by ring
      _ = _ := by rw [hx]; ring

/-- Every affine member retains the full xi denominator and exactly two
dyadic factors, including at the dyadic exceptions themselves. -/
theorem completion_mul_suzukiEtaAffineClearedDenominator (a : ℂ) {s : ℂ}
    (hs : 0 < s.re) (h1 : s ≠ 1) :
    pairedEtaXiCompletionNumerator s * suzukiEtaAffineClearedDenominator a s =
      pairedEtaFactor s ^ 2 * (a * riemannXi s + deriv riemannXi s) := by
  unfold suzukiEtaAffineClearedDenominator
  rw [mul_add, mul_left_comm (pairedEtaXiCompletionNumerator s) (a - 1),
    completed_numerator hs h1, pairedEtaXiCompletionNumerator_mul_clearedCarrierDenominator hs h1]
  ring

/-- The original carrier is the parameter logarithmic derivative of
the actual cleared denominator, with all completion hypotheses explicit. -/
theorem suzukiXiZeroCarrier_eq_parameter_logDeriv {z : ℂ}
    (hz : suzukiArithmeticZetaArgument z ∈ pairedEtaCompletionDomain)
    (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiZeroCarrier z = I * logDeriv
      (fun a => suzukiEtaAffineClearedDenominator a (suzukiArithmeticZetaArgument z)) 1 := by
  rw [logDeriv_apply, (hasDerivAt_suzukiEtaAffineClearedDenominator 1 _).deriv,
    suzukiXiZeroCarrier_eq_etaCarrier_on_completionDomain hz hE]
  simp only [suzukiEtaAffineClearedDenominator, sub_self, zero_mul, add_zero]
  rw [suzukiEtaClearedCarrierDenominator_eq_factor_mul hz.2.2]
  unfold suzukiEtaCarrier
  field_simp [hz.2.2]

/-- Resolvent identity with the full complex parameter difference and
both original denominators retained. -/
theorem suzukiXiAffineCarrier_sub {a b z : ℂ}
    (ha : suzukiXiAffineDenominator a z ≠ 0)
    (hb : suzukiXiAffineDenominator b z ≠ 0) :
    suzukiXiAffineCarrier a z - suzukiXiAffineCarrier b z =
      I * (a - b) * suzukiXiAffineCarrier a z * suzukiXiAffineCarrier b z := by
  unfold suzukiXiAffineCarrier
  field_simp
  simp only [suzukiXiAffineDenominator]
  ring_nf
  simp [I_sq, sub_eq_add_neg]

/-- The full affine denominator factors through the original carrier
on the original regular domain. All new parameter poles remain visible. -/
theorem suzukiXiAffineDenominator_eq_resolvent (a : ℂ) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiAffineDenominator a z = suzukiXiEValue z *
      (1 - I * (a - 1) * suzukiXiZeroCarrier z) := by
  rw [suzukiXiAffineDenominator_eq, suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  field_simp
  ring_nf
  simp [I_sq, sub_eq_add_neg]

/-- Changing the parameter acts by an exact Möbius transform of the
original carrier, including totalized values at new parameter poles. -/
theorem suzukiXiAffineCarrier_eq_resolvent (a : ℂ) {z : ℂ}
    (hE : suzukiXiEValue z ≠ 0) :
    suzukiXiAffineCarrier a z = suzukiXiZeroCarrier z /
      (1 - I * (a - 1) * suzukiXiZeroCarrier z) := by
  rw [suzukiXiAffineCarrier, suzukiXiAffineDenominator_eq_resolvent a hE, ← div_div,
    ← suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]

/-- The genuine complex family has a denominator floor on the whole
upper safe half-plane whenever the parameter has positive real part. -/
theorem re_mul_norm_xi_le_norm_suzukiXiAffineDenominator {a z : ℂ}
    (hz : 1 / 2 ≤ z.im) :
    a.re * ‖riemannXiSpectral z‖ ≤ ‖suzukiXiAffineDenominator a z‖ := by
  have hxi := riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  have hf : suzukiXiAffineDenominator a z =
      riemannXiSpectral z * (a + I * logDeriv riemannXiSpectral z) := by
    simp only [suzukiXiAffineDenominator, logDeriv_apply]
    field_simp
  rw [hf, norm_mul, mul_comm a.re]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    a.re ≤ (a + I * logDeriv riemannXiSpectral z).re := by
      simp only [add_re, mul_re, I_re, I_im, zero_mul, one_mul]
      linarith [im_logDeriv_riemannXiSpectral_nonpos_of_half_le_im hz]
    _ ≤ _ := Complex.re_le_norm _

/-- No pole of a positive-real-part parameter occurs in the upper safe
half-plane; this is not a claim inside the zero strip. -/
theorem suzukiXiAffineDenominator_ne_zero_of_safe {a z : ℂ}
    (ha : 0 < a.re) (hz : 1 / 2 ≤ z.im) :
    suzukiXiAffineDenominator a z ≠ 0 := by
  have hxi := riemannXiSpectral_ne_zero_of_half_le_abs_im (hz.trans (le_abs_self _))
  exact norm_pos_iff.mp ((mul_pos ha (norm_pos_iff.mpr hxi)).trans_le
    (re_mul_norm_xi_le_norm_suzukiXiAffineDenominator hz))

end
end RiemannGaussian
