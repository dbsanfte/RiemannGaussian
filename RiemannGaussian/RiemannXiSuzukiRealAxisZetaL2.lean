import RiemannGaussian.RiemannXiSuzukiRealAxisZetaTail
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Square integrability of Suzuki's real-axis zeta contribution

The carrier-weighted zeta contribution now has both a uniform compact bound
and a `C (|x|+1)^(1/4) / |x|` tail.  This file turns those estimates into an
actual `MemLp · 2` theorem.

On `|x| ≤ 1` a constant indicator is integrable.  On `|x| > 1`, squaring the
tail and using `|x|+1 ≤ 2|x|` gives an integrable multiple of
`(|x|+1)^(-3/2)`.  Measurability is proved from the analytic derivative of
zeta away from its unique pole and the fact that modifying a function on a
countable set preserves Borel measurability.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The carrier-weighted zeta component as a function on the real axis. -/
def suzukiRealAxisCarrierZetaContribution (t x : ℝ) : ℂ :=
  suzukiXiZeroCarrier (x : ℂ) *
    suzukiArithmeticZetaContribution t (x : ℂ)

/-- The globally totalized derivative of zeta is Borel measurable. -/
theorem measurable_deriv_riemannZeta :
    Measurable (deriv riemannZeta) := by
  apply (analyticOn_riemannZeta.deriv.continuousOn).measurable_of_countable_compl
  simp

/-- The globally totalized zeta function is Borel measurable. -/
theorem measurable_riemannZeta : Measurable riemannZeta := by
  apply analyticOn_riemannZeta.continuousOn.measurable_of_countable_compl
  simp

/-- The real-axis carrier-weighted zeta contribution is strongly measurable. -/
theorem aestronglyMeasurable_suzukiRealAxisCarrierZetaContribution
    (t : ℝ) :
    AEStronglyMeasurable (suzukiRealAxisCarrierZetaContribution t) := by
  apply Measurable.aestronglyMeasurable
  have hderivXi : Continuous (deriv riemannXiSpectral) := by
    have hdiffOn :=
      differentiable_riemannXiSpectral.differentiableOn.deriv isOpen_univ
    exact (differentiableOn_univ.mp hdiffOn).continuous
  have hXi : Continuous riemannXiSpectral :=
    differentiable_riemannXiSpectral.continuous
  have hofReal : Measurable (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.continuous_ofReal.measurable
  have hXiReal : Measurable
      (fun x : ℝ ↦ riemannXiSpectral (x : ℂ)) :=
    hXi.measurable.comp hofReal
  have hderivXiReal : Measurable
      (fun x : ℝ ↦ deriv riemannXiSpectral (x : ℂ)) :=
    hderivXi.measurable.comp hofReal
  have hE : Measurable (fun x : ℝ ↦
      riemannXiSpectral (x : ℂ) +
        Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ)) :=
    hXiReal.add ((measurable_const.mul measurable_const).mul hderivXiReal)
  have hESharp : Measurable (fun x : ℝ ↦
      riemannXiSpectral (x : ℂ) -
        Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ)) :=
    hXiReal.sub ((measurable_const.mul measurable_const).mul hderivXiReal)
  have hTheta : Measurable (fun x : ℝ ↦
      (riemannXiSpectral (x : ℂ) -
          Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ)) /
        (riemannXiSpectral (x : ℂ) +
          Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ))) :=
    hESharp.div hE
  have hCarrier : Measurable (fun x : ℝ ↦
      Complex.I *
        (1 +
          (riemannXiSpectral (x : ℂ) -
              Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ)) /
            (riemannXiSpectral (x : ℂ) +
              Complex.I * (1 : ℂ) * deriv riemannXiSpectral (x : ℂ))) /
        2) :=
    (measurable_const.mul (measurable_const.add hTheta)).div
      measurable_const
  have hExp : Measurable (fun x : ℝ ↦
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ))) :=
    (by fun_prop : Continuous (fun x : ℝ ↦
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)))).measurable
  have hQuotient : Measurable (fun x : ℝ ↦
      (Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) - 1) /
        (Complex.I * (x : ℂ))) :=
    (hExp.sub measurable_const).div (measurable_const.mul hofReal)
  have hArgument : Measurable (fun x : ℝ ↦
      (1 / 2 : ℂ) - Complex.I * (x : ℂ)) :=
    measurable_const.sub (measurable_const.mul hofReal)
  have hLogDeriv : Measurable (fun x : ℝ ↦
      deriv riemannZeta ((1 / 2 : ℂ) - Complex.I * (x : ℂ)) /
        riemannZeta ((1 / 2 : ℂ) - Complex.I * (x : ℂ))) :=
    (measurable_deriv_riemannZeta.comp hArgument).div
      (measurable_riemannZeta.comp hArgument)
  have hCarrierHigh : Measurable (fun x : ℝ ↦
      suzukiXiZeroCarrier (x : ℂ)) := by
    convert hCarrier using 1
    funext x
    simp only [suzukiXiZeroCarrier, suzukiXiThetaValue,
      suzukiXiESharpValue, suzukiXiEValue, analyticESharpValue,
      analyticEValue]
    simp
  have hQuotientHigh : Measurable (fun x : ℝ ↦
      suzukiArithmeticScrewQuotient t (x : ℂ)) := by
    simpa only [suzukiArithmeticScrewQuotient] using hQuotient
  have hLogDerivHigh : Measurable (fun x : ℝ ↦
      logDeriv riemannZeta
        (suzukiArithmeticZetaArgument (x : ℂ))) := by
    simpa only [suzukiArithmeticZetaArgument, logDeriv_apply] using
      hLogDeriv
  unfold suzukiRealAxisCarrierZetaContribution
    suzukiArithmeticZetaContribution
  exact hCarrierHigh.mul (hQuotientHigh.mul hLogDerivHigh)

/-- The compact-frequency constant used in the `L²` majorant. -/
def suzukiRealAxisZetaCompactConstant (t : ℝ) : ℝ :=
  (Real.exp (|t| / 2) * |t|) *
    (suzukiRealAxisZetaElementaryGrowthConstant +
      suzukiRealAxisZetaQuarterGrowthConstant * 2 ^ (1 / 4 : ℝ))

theorem suzukiRealAxisZetaCompactConstant_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisZetaCompactConstant t := by
  unfold suzukiRealAxisZetaCompactConstant
  positivity [suzukiRealAxisZetaElementaryGrowthConstant_nonneg,
    suzukiRealAxisZetaQuarterGrowthConstant_nonneg]

/-- Uniform control of the zeta component on the central interval. -/
theorem norm_suzukiRealAxisCarrierZetaContribution_le_compact
    (t : ℝ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖suzukiRealAxisCarrierZetaContribution t x‖ ≤
      suzukiRealAxisZetaCompactConstant t := by
  have hbase : |x| + 1 ≤ (2 : ℝ) := by linarith
  have hpow : (|x| + 1) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  unfold suzukiRealAxisCarrierZetaContribution
    suzukiRealAxisZetaCompactConstant
  calc
    ‖suzukiXiZeroCarrier (x : ℂ) *
        suzukiArithmeticZetaContribution t (x : ℂ)‖ ≤
      (Real.exp (|t| / 2) * |t|) *
        (suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant *
            (|x| + 1) ^ (1 / 4 : ℝ)) :=
      norm_suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal_le
        t x
    _ ≤ (Real.exp (|t| / 2) * |t|) *
        (suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant *
            2 ^ (1 / 4 : ℝ)) := by
      gcongr
      exact suzukiRealAxisZetaQuarterGrowthConstant_nonneg

/-- The elementary quarter-power tail has an integrable square beyond unit
frequency. -/
theorem sq_quarterPower_div_abs_le
    {x : ℝ} (hx : 1 ≤ |x|) :
    (((|x| + 1) ^ (1 / 4 : ℝ)) / |x|) ^ 2 ≤
      4 * (|x| + 1) ^ (-(3 / 2 : ℝ)) := by
  let a : ℝ := |x|
  let R : ℝ := |x| + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRle : R ≤ 2 * a := by
    dsimp [R, a]
    linarith
  have hRtwo : R ^ 2 ≤ 4 * a ^ 2 := by
    have hpow := pow_le_pow_left₀ hR.le hRle 2
    nlinarith
  have hquarterSq : (R ^ (1 / 4 : ℝ)) ^ 2 = R ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  change (R ^ (1 / 4 : ℝ) / a) ^ 2 ≤
    4 * R ^ (-(3 / 2 : ℝ))
  rw [div_pow, hquarterSq, Real.rpow_neg hR.le]
  rw [← div_eq_mul_inv]
  rw [div_le_div_iff₀ (sq_pos_of_pos ha)
    (Real.rpow_pos_of_pos hR (3 / 2 : ℝ))]
  calc
    R ^ (1 / 2 : ℝ) * R ^ (3 / 2 : ℝ) = R ^ 2 := by
      rw [← Real.rpow_add hR]
      norm_num [Real.rpow_natCast]
    _ ≤ 4 * a ^ 2 := hRtwo

/-- An explicit integrable majorant for the squared norm of the zeta
component. -/
def suzukiRealAxisCarrierZetaNormSqMajorant (t x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator
      (fun _ ↦ suzukiRealAxisZetaCompactConstant t ^ 2) x +
    4 * suzukiRealAxisZetaTailConstant ^ 2 *
      (1 + |x|) ^ (-(3 / 2 : ℝ))

/-- The squared-norm majorant is integrable on the whole real line. -/
theorem integrable_suzukiRealAxisCarrierZetaNormSqMajorant (t : ℝ) :
    Integrable (suzukiRealAxisCarrierZetaNormSqMajorant t) := by
  have hcompact : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun _ : ℝ ↦ suzukiRealAxisZetaCompactConstant t ^ 2)) :=
    (integrableOn_const (s := Icc (-1 : ℝ) 1)
      (by simp)).integrable_indicator
      measurableSet_Icc
  have htailBase : Integrable
      (fun x : ℝ ↦ (1 + ‖x‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (by norm_num)
  have htail : Integrable (fun x : ℝ ↦
      4 * suzukiRealAxisZetaTailConstant ^ 2 *
        (1 + |x|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      htailBase.const_mul (4 * suzukiRealAxisZetaTailConstant ^ 2)
  exact hcompact.add htail

/-- The integrable majorant dominates the genuine squared norm pointwise. -/
theorem normSq_suzukiRealAxisCarrierZetaContribution_le_majorant
    (t x : ℝ) :
    ‖suzukiRealAxisCarrierZetaContribution t x‖ ^ 2 ≤
      suzukiRealAxisCarrierZetaNormSqMajorant t x := by
  by_cases hx : |x| ≤ 1
  · have hxmem : x ∈ Icc (-1 : ℝ) 1 := (abs_le.mp hx)
    have hnorm :=
      norm_suzukiRealAxisCarrierZetaContribution_le_compact t hx
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold suzukiRealAxisCarrierZetaNormSqMajorant
    rw [Set.indicator_of_mem hxmem]
    exact hsquare.trans (le_add_of_nonneg_right (by positivity))
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hxnotmem : x ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      exact hx (abs_le.mpr hmem)
    have htail :
        ‖suzukiRealAxisCarrierZetaContribution t x‖ ≤
          suzukiRealAxisZetaTailConstant *
            (|x| + 1) ^ (1 / 4 : ℝ) / |x| := by
      unfold suzukiRealAxisCarrierZetaContribution
      exact
        norm_suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal_le_tail
          t x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htail 2
    have hquarter := sq_quarterPower_div_abs_le hxgt.le
    unfold suzukiRealAxisCarrierZetaNormSqMajorant
    rw [Set.indicator_of_notMem hxnotmem, zero_add]
    calc
      ‖suzukiRealAxisCarrierZetaContribution t x‖ ^ 2 ≤
          (suzukiRealAxisZetaTailConstant *
            (|x| + 1) ^ (1 / 4 : ℝ) / |x|) ^ 2 := hsquare
      _ = suzukiRealAxisZetaTailConstant ^ 2 *
          (((|x| + 1) ^ (1 / 4 : ℝ)) / |x|) ^ 2 := by ring
      _ ≤ suzukiRealAxisZetaTailConstant ^ 2 *
          (4 * (|x| + 1) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hquarter (sq_nonneg _)
      _ = 4 * suzukiRealAxisZetaTailConstant ^ 2 *
          (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [add_comm (1 : ℝ) |x|]
        ring

/-- The squared norm of the carrier-weighted zeta contribution is integrable. -/
theorem integrable_normSq_suzukiRealAxisCarrierZetaContribution (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisCarrierZetaContribution t x‖ ^ 2) := by
  exact (integrable_suzukiRealAxisCarrierZetaNormSqMajorant t).mono'
    ((aestronglyMeasurable_suzukiRealAxisCarrierZetaContribution t).norm.pow 2)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact normSq_suzukiRealAxisCarrierZetaContribution_le_majorant t x)

/-- The carrier-weighted arithmetic zeta contribution is an actual element of
`L²(ℝ)`, unconditionally. -/
theorem memLp_two_suzukiRealAxisCarrierZetaContribution (t : ℝ) :
    MemLp (suzukiRealAxisCarrierZetaContribution t) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_suzukiRealAxisCarrierZetaContribution t)).2
  exact integrable_normSq_suzukiRealAxisCarrierZetaContribution t

end

end RiemannGaussian
