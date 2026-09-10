/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiGammaArithmeticReduction
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The normalized arithmetic current and its denominator drift

The derivative phase of the shifted zeta numerator is normalized by the
actual denominator. Its smooth representation through the original xi
fields includes all common zeros. The arithmetic source is its exact
coupled variation with the mass; the denominator drift is kept explicit.
-/

open Complex Filter Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- Arithmetic argument on an oriented horizontal spectral line. -/
def suzukiGammaHorizontalArgument (y x : ℝ) : ℂ :=
  suzukiArithmeticZetaArgument ((x : ℂ) + (y : ℂ) * I)

/-- The normalized arithmetic derivative phase, expressed through
globally smooth xi fields to preserve its values at common zeros. -/
def suzukiGammaNormalizedSlope (r y x : ℝ) : ℂ :=
  -I * suzukiXiHorizontalCarrier r y x -
    (1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))) *
      (suzukiXiHorizontalMass r y x : ℂ)

/-- The complete denominator drift carried by the normalized mass.
The theorem below identifies it with the literal denominator derivative. -/
def suzukiGammaNormalizationDrift (r y x : ℝ) : ℝ :=
  -2 * (suzukiGammaNormalizedSlope r y x).im - deriv (suzukiXiHorizontalMass r y) x

/-- The actual real denominator on the same oriented horizontal line. -/
def suzukiGammaHorizontalDenominator (r y x : ℝ) : ℝ :=
  suzukiGammaShiftNormDenominator r (suzukiGammaHorizontalArgument y x)

/-- The arithmetic argument stays in its genuine holomorphy domain
on every upper spectral line. -/
theorem suzukiGammaHorizontalArgument_re_pos {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    0 < (suzukiGammaHorizontalArgument y x).re := by
  rw [suzukiGammaHorizontalArgument, suzukiArithmeticZetaArgument_re]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
    mul_zero, add_zero, zero_add]
  linarith

/-- Horizontal spectral motion reverses the arithmetic imaginary
coordinate; this is the exact derivative with its orientation retained. -/
theorem hasDerivAt_suzukiGammaHorizontalArgument (y x : ℝ) :
    HasDerivAt (suzukiGammaHorizontalArgument y) (-I) x := by
  have h := ((((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)).const_mul I).const_sub (1 / 2 : ℂ)
  convert! h using 1
  simp

/-- The arithmetic derivative phase equals the literal normalized
product, including all common zeros and genuine carrier poles. -/
theorem suzukiGammaNormalizedSlope_eq_quotient (r : ℝ) {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    suzukiGammaNormalizedSlope r y x =
      suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x) *
        starRingEnd ℂ (deriv suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x)) /
          (suzukiGammaHorizontalDenominator r y x : ℂ) := by
  have hs := suzukiGammaHorizontalArgument_re_pos hy x
  unfold suzukiGammaNormalizedSlope suzukiXiHorizontalCarrier suzukiXiHorizontalMass
  rw [suzukiXiSmoothCarrier_eq_gammaShift r hs, suzukiXiNormalizedMass_eq_gammaShift r hs]
  unfold suzukiGammaShiftSmoothCarrier complexSmoothQuotient
  rw [complexSmoothQuotient_denominator]
  simp only [map_mul, normSq_I, one_mul]
  unfold suzukiGammaShiftNormalizedMass
  rw [ofReal_div]
  change -I * (I * suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x) *
    starRingEnd ℂ (suzukiGammaShiftDenominator (suzukiGammaHorizontalArgument y x)) /
      (suzukiGammaHorizontalDenominator r y x : ℂ)) -
      (1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))) *
        ((normSq (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x)) : ℂ) /
          (suzukiGammaHorizontalDenominator r y x : ℂ)) = _
  rw [← mul_conj (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x))]
  rw [suzukiGammaShiftDenominator]
  simp only [map_add, map_mul, map_one]
  ring_nf
  simp only [I_sq]
  ring

/-- The normalized derivative phase is smooth on each entire upper
line, even through repeated xi zeros and genuine carrier poles. -/
theorem contDiff_suzukiGammaNormalizedSlope {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    ContDiff ℝ ∞ (suzukiGammaNormalizedSlope r y) := by
  have hQ : ContDiff ℝ ∞ (fun x => suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact ((analyticAt_suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument_re_pos hy x)).contDiffAt.restrict_scalars ℝ).comp x
      (by
        unfold suzukiGammaHorizontalArgument suzukiArithmeticZetaArgument
        exact (contDiffAt_const.sub (contDiffAt_const.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.add contDiffAt_const))))
  unfold suzukiGammaNormalizedSlope
  exact (contDiff_const.mul (contDiff_suzukiXiHorizontalCarrier hr y)).sub
    ((contDiff_const.add (Complex.conjCLE.contDiff.comp hQ)).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_suzukiXiHorizontalMass hr y)))

/-- The true arithmetic denominator drift is also smooth across the
complete carrier divisor, through its normalized representation. -/
theorem contDiff_suzukiGammaNormalizationDrift {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) :
    ContDiff ℝ ∞ (suzukiGammaNormalizationDrift r y) := by
  unfold suzukiGammaNormalizationDrift
  exact (contDiff_const.mul (Complex.imCLM.contDiff.comp
    (contDiff_suzukiGammaNormalizedSlope hr hy))).sub
      (contDiff_infty_iff_deriv.mp (contDiff_suzukiXiHorizontalMass hr y)).2

/-- A quantitative bound on the normalized derivative phase retains
the full first Gamma correction and requires no denominator separation. -/
theorem norm_suzukiGammaNormalizedSlope_le {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    ‖suzukiGammaNormalizedSlope r y x‖ ≤ 1 / (2 * r) +
      ‖1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))‖ / r ^ 2 := by
  unfold suzukiGammaNormalizedSlope
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    suzukiXiHorizontalMass,
    abs_of_nonneg (suzukiXiNormalizedMass_nonneg r ((x : ℂ) + (y : ℂ) * I))]
  refine add_le_add (norm_suzukiXiSmoothCarrier_le hr _) ?_
  have h := mul_le_mul_of_nonneg_left
    (suzukiXiNormalizedMass_le hr ((x : ℂ) + (y : ℂ) * I))
    (norm_nonneg (1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))))
  simpa only [div_eq_mul_inv, one_mul] using h

/-- The actual normalized arithmetic source is a coupled variation
of its derivative phase and mass. All numerator and denominator zeros
are included, and the complex source is retained before projection. -/
theorem suzukiGammaShiftArithmeticSource_eq_normalized_current
    {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) (x : ℝ) :
    suzukiGammaShiftArithmeticSource r (suzukiGammaHorizontalArgument y x) =
      2 * (r : ℂ) ^ 2 *
        (suzukiGammaNormalizedSlope r y x * ((deriv (suzukiXiHorizontalMass r y) x : ℝ) : ℂ) -
          (suzukiXiHorizontalMass r y x : ℂ) * deriv (suzukiGammaNormalizedSlope r y) x) := by
  have hs := suzukiGammaHorizontalArgument_re_pos hy x
  dsimp only [suzukiGammaHorizontalArgument] at hs
  have hS := ((contDiff_suzukiXiHorizontalCarrier hr y).differentiable (by simp) x).hasDerivAt
  have hU := ((contDiff_suzukiXiHorizontalMass hr y).differentiable (by simp) x).hasDerivAt.ofReal_comp
  have hQ := ((analyticAt_suzukiGammaShiftCorrection hs).differentiableAt.hasDerivAt.comp x
    (hasDerivAt_suzukiGammaHorizontalArgument y x)).star
  have hT := ((hS.const_mul (-I)).sub ((hQ.const_add 1).mul hU)).deriv
  change deriv (suzukiGammaNormalizedSlope r y) x = _ at hT
  have he := suzukiXiSmoothCarrierSource_eq_gammaShift hr hs
  rw [suzukiGammaShiftSpectralSource_eq_add hs, suzukiGammaShiftCompletionSource_eq_mass,
    ← suzukiXiNormalizedMass_eq_gammaShift r hs,
    suzukiXiSmoothCarrierSource_eq_horizontal_mass_variation hr] at he
  rw [hT]
  simp only [star_def, map_mul, map_neg, conj_I]
  unfold suzukiGammaNormalizedSlope
  change _ = _
  dsimp only [suzukiXiHorizontalMass, suzukiXiHorizontalCarrier, suzukiGammaHorizontalArgument, Function.comp_def] at *
  linear_combination -he

private lemma normSq_horizontal_derivative {f : ℝ → ℂ} {g : ℂ} {x : ℝ}
    (hf : HasDerivAt f (-I * g) x) :
    HasDerivAt (fun u => normSq (f u)) (-2 * (f x * starRingEnd ℂ g).im) x := by
  have he : (fun u => normSq (f u)) = fun u => (f u * starRingEnd ℂ (f u)).re := by
    funext u
    rw [mul_conj, Complex.ofReal_re]
  rw [he]
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf.fun_mul hf.star)
  convert! h using 1
  simp only [star_def, map_mul, map_neg, conj_I, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.reCLM_apply]
  ring

private lemma horizontal_comp {f : ℂ → ℂ} {y x : ℝ}
    (hf : DifferentiableAt ℂ f (suzukiGammaHorizontalArgument y x)) :
    HasDerivAt (fun u => f (suzukiGammaHorizontalArgument y u))
      (-I * deriv f (suzukiGammaHorizontalArgument y x)) x := by
  convert! hf.hasDerivAt.comp x (hasDerivAt_suzukiGammaHorizontalArgument y x) using 1
  ring

/-- The full denominator derivative differentiates both actual
arithmetic channels and retains their relative complex phases. -/
theorem deriv_suzukiGammaHorizontalDenominator (r : ℝ) {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    deriv (suzukiGammaHorizontalDenominator r y) x =
      -2 * (suzukiGammaShiftDenominator (suzukiGammaHorizontalArgument y x) *
        starRingEnd ℂ (deriv suzukiGammaShiftDenominator (suzukiGammaHorizontalArgument y x))).im -
      2 * r ^ 2 * (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x) *
        starRingEnd ℂ (deriv suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x))).im := by
  have hs := suzukiGammaHorizontalArgument_re_pos hy x
  have hn := normSq_horizontal_derivative (horizontal_comp (analyticAt_suzukiGammaShiftNumerator hs).differentiableAt)
  have hd := normSq_horizontal_derivative (horizontal_comp (analyticAt_suzukiGammaShiftDenominator hs).differentiableAt)
  have h := (hd.fun_add (hn.const_mul (r ^ 2))).deriv
  change deriv (suzukiGammaHorizontalDenominator r y) x = _ at h
  exact h.trans (by ring)

/-- The globally smooth mass is the literal arithmetic numerator
norm divided by its full variable denominator, through common zeros. -/
theorem suzukiXiHorizontalMass_eq_gammaQuotient (r : ℝ) {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    suzukiXiHorizontalMass r y x = normSq (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x)) /
      suzukiGammaHorizontalDenominator r y x := by
  unfold suzukiXiHorizontalMass
  rw [suzukiXiNormalizedMass_eq_gammaShift r (suzukiGammaHorizontalArgument_re_pos hy x)]
  rfl

/-- The smooth drift is exactly the normalized derivative of the
actual denominator. The identity includes its defined value at every
common zero, justified by the minimum of the genuine nonnegative mass. -/
theorem suzukiGammaNormalizationDrift_eq_denominator
    {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) (x : ℝ) :
    suzukiGammaNormalizationDrift r y x =
      suzukiXiHorizontalMass r y x * deriv (suzukiGammaHorizontalDenominator r y) x /
        suzukiGammaHorizontalDenominator r y x := by
  by_cases hF : suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y x) = 0
  · have hU : suzukiXiHorizontalMass r y x = 0 := by
      simp [suzukiXiHorizontalMass_eq_gammaQuotient r hy x, hF]
    have hT : suzukiGammaNormalizedSlope r y x = 0 := by
      simp [suzukiGammaNormalizedSlope_eq_quotient r hy x, hF]
    have hmin : IsLocalMin (suzukiXiHorizontalMass r y) x := by
      apply Eventually.of_forall
      intro u
      rw [hU]
      exact suzukiXiNormalizedMass_nonneg r _
    simp [suzukiGammaNormalizationDrift, hT, hmin.deriv_eq_zero, hU]
  have hs := suzukiGammaHorizontalArgument_re_pos hy x
  have hn := normSq_horizontal_derivative (horizontal_comp (analyticAt_suzukiGammaShiftNumerator hs).differentiableAt)
  have hD := normSq_horizontal_derivative (horizontal_comp (analyticAt_suzukiGammaShiftDenominator hs).differentiableAt)
  have hd := (hD.fun_add (hn.const_mul (r ^ 2))).differentiableAt
  change DifferentiableAt ℝ (suzukiGammaHorizontalDenominator r y) x at hd
  have hp : 0 < suzukiGammaHorizontalDenominator r y x :=
    complexSmoothQuotient_denominator_pos hr (b := suzukiGammaShiftDenominator (suzukiGammaHorizontalArgument y x)) (Or.inl hF)
  have hm := (hn.div hd.hasDerivAt hp.ne').deriv
  change deriv (fun u => normSq (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y u)) /
      suzukiGammaHorizontalDenominator r y u) x = _ at hm
  have hfun : (fun u => normSq (suzukiGammaShiftNumerator (suzukiGammaHorizontalArgument y u)) /
      suzukiGammaHorizontalDenominator r y u) = suzukiXiHorizontalMass r y :=
    funext (fun u => (suzukiXiHorizontalMass_eq_gammaQuotient r hy u).symm)
  rw [hfun] at hm
  rw [suzukiGammaNormalizationDrift, hm, suzukiGammaNormalizedSlope_eq_quotient r hy x,
    Complex.div_ofReal_im, suzukiXiHorizontalMass_eq_gammaQuotient r hy x]
  field_simp
  ring

/-- The exact normalized arithmetic identity with an arbitrary
differentiable complex weight keeps its phase and full derivative.
Only regularity of that weight is requested; the carrier data are proved. -/
theorem suzukiGammaShiftArithmeticSource_weighted_current
    {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) {P : ℝ → ℂ} {P' : ℂ} {x : ℝ}
    (hP : HasDerivAt P P' x) :
    P x * suzukiGammaShiftArithmeticSource r (suzukiGammaHorizontalArgument y x) =
      -2 * (r : ℂ) ^ 2 * deriv (fun u => P u * (suzukiXiHorizontalMass r y u : ℂ) *
        suzukiGammaNormalizedSlope r y u) x +
      2 * (r : ℂ) ^ 2 * P' * (suzukiXiHorizontalMass r y x : ℂ) *
        suzukiGammaNormalizedSlope r y x +
      4 * (r : ℂ) ^ 2 * P x * suzukiGammaNormalizedSlope r y x *
        ((deriv (suzukiXiHorizontalMass r y) x : ℝ) : ℂ) := by
  have hU := ((contDiff_suzukiXiHorizontalMass hr y).differentiable (by simp) x).hasDerivAt.ofReal_comp
  have hT := ((contDiff_suzukiGammaNormalizedSlope hr hy).differentiable (by simp) x).hasDerivAt
  rw [suzukiGammaShiftArithmeticSource_eq_normalized_current hr hy,
    ((hP.fun_mul hU).fun_mul hT).deriv]
  ring

/-- The full reflection-weighted normalized arithmetic current. -/
def suzukiGammaReflectionCurrent (rho : NontrivialZetaZero) (r c tau y x : ℝ) : ℂ :=
  suzukiXiHorizontalReflectionHeat rho c tau y x * (suzukiXiHorizontalMass r y x : ℂ) *
    suzukiGammaNormalizedSlope r y x

/-- The full actual reflection-weighted quartic retains both the
reflection-heat derivative and the signed normalized mass variation.
All carrier poles and common zeros are permitted; only the two weight
nodes are excluded from this pointwise differentiation formula. -/
theorem suzukiGammaShiftWeightedArithmeticSource_eq_normalized_current
    (rho : NontrivialZetaZero) {r y : ℝ} (hr : 0 < r) (hy : 0 ≤ y) (c tau x : ℝ)
    (ha : (x : ℂ) + (y : ℂ) * I ≠ zetaSpectralCoordinate rho.1)
    (hb : (x : ℂ) + (y : ℂ) * I ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    suzukiGammaShiftWeightedArithmeticSource rho r c tau ((x : ℂ) + (y : ℂ) * I) =
      -2 * (r : ℂ) ^ 2 * deriv (suzukiGammaReflectionCurrent rho r c tau y) x +
      2 * (r : ℂ) ^ 2 * deriv (suzukiXiHorizontalReflectionHeat rho c tau y) x *
        (suzukiXiHorizontalMass r y x : ℂ) * suzukiGammaNormalizedSlope r y x +
      4 * (r : ℂ) ^ 2 * suzukiXiHorizontalReflectionHeat rho c tau y x *
        suzukiGammaNormalizedSlope r y x * ((deriv (suzukiXiHorizontalMass r y) x : ℝ) : ℂ) := by
  have hP := ((contDiffAt_suzukiXiHorizontalReflectionHeat rho c tau y x ha hb).differentiableAt (by simp)).hasDerivAt
  exact suzukiGammaShiftArithmeticSource_weighted_current hr hy hP

/-- The complete reflected arithmetic current has a quantitative value
bound with its actual reflection phase and first Gamma correction retained. -/
theorem norm_suzukiGammaReflectionCurrent_le (rho : NontrivialZetaZero)
    {r : ℝ} (hr : 0 < r) (c tau y x : ℝ) :
    ‖suzukiGammaReflectionCurrent rho r c tau y x‖ ≤
      ‖suzukiXiHorizontalReflectionHeat rho c tau y x‖ *
        (1 / (2 * r ^ 3) +
          ‖1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))‖ / r ^ 4) := by
  unfold suzukiGammaReflectionCurrent
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ suzukiXiHorizontalMass r y x from suzukiXiNormalizedMass_nonneg r _)]
  calc
    _ ≤ ‖suzukiXiHorizontalReflectionHeat rho c tau y x‖ * (1 / r ^ 2) *
        (1 / (2 * r) + ‖1 + starRingEnd ℂ (suzukiGammaShiftCorrection (suzukiGammaHorizontalArgument y x))‖ / r ^ 2) := by
      gcongr
      · exact suzukiXiNormalizedMass_le hr _
      · exact norm_suzukiGammaNormalizedSlope_le hr y x
    _ = _ := by ring

end
end RiemannGaussian
