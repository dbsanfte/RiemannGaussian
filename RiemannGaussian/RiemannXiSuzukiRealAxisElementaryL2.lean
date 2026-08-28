import RiemannGaussian.RiemannXiSuzukiRealAxisZetaL2
import RiemannGaussian.FiniteHardyBoundary

/-!
# Square integrability of Suzuki's elementary real-axis terms

This file proves the `L²(ℝ)` statements for the elementary pole pair and the
finite von Mangoldt window in Suzuki's arithmetic formula.

The common arithmetic screw quotient is first treated directly.  Its
previously proved uniform estimate controls `[-1, 1]`, while its `2 / |x|`
tail is dominated after squaring by the integrable Cauchy weight
`8 / (1 + x²)`.  Every prime term is a constant multiple of such a quotient,
so the finite prime window is square-integrable.

The two completed-zeta pole kernels are degree-zero-over-degree-one rational
boundary functions with no real poles.  Their `L²` property follows from the
project's general polynomial boundary-quotient theorem.  Finally, the xi
carrier is a measurable `L∞` multiplier of norm at most one, so multiplying
the pole and prime components by it preserves `L²`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Suzuki's xi carrier restricted to the real spectral axis. -/
def suzukiRealAxisXiZeroCarrier (x : ℝ) : ℂ :=
  suzukiXiZeroCarrier (x : ℂ)

/-- The real-axis xi carrier is Borel measurable, including at the totalized
zeros of its denominator. -/
theorem measurable_suzukiRealAxisXiZeroCarrier :
    Measurable suzukiRealAxisXiZeroCarrier := by
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
  convert hCarrier using 1
  funext x
  simp only [suzukiRealAxisXiZeroCarrier, suzukiXiZeroCarrier,
    suzukiXiThetaValue, suzukiXiESharpValue, suzukiXiEValue,
    analyticESharpValue, analyticEValue]
  simp

/-- The xi carrier is an `L∞` multiplier on the real axis. -/
theorem memLp_top_suzukiRealAxisXiZeroCarrier :
    MemLp suzukiRealAxisXiZeroCarrier ∞ := by
  apply memLp_top_of_bound
    measurable_suzukiRealAxisXiZeroCarrier.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x ↦
    norm_suzukiXiZeroCarrier_ofReal_le_one x

/-- Suzuki's arithmetic screw quotient restricted to real frequency. -/
def suzukiRealAxisScrewQuotient (t x : ℝ) : ℂ :=
  suzukiArithmeticScrewQuotient t (x : ℂ)

/-- The totalized real-axis screw quotient is Borel measurable. -/
theorem measurable_suzukiRealAxisScrewQuotient (t : ℝ) :
    Measurable (suzukiRealAxisScrewQuotient t) := by
  change Measurable
    (fun x : ℝ ↦ suzukiArithmeticScrewQuotient t (x : ℂ))
  have hofReal : Measurable (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.continuous_ofReal.measurable
  have hExp : Measurable (fun x : ℝ ↦
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ))) :=
    (by fun_prop : Continuous (fun x : ℝ ↦
      Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)))).measurable
  have hQuotient : Measurable (fun x : ℝ ↦
      (Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) - 1) /
        (Complex.I * (x : ℂ))) :=
    (hExp.sub measurable_const).div (measurable_const.mul hofReal)
  simpa only [suzukiArithmeticScrewQuotient] using hQuotient

/-- The compact-frequency bound for one real-axis screw quotient. -/
def suzukiRealAxisScrewCompactConstant (t : ℝ) : ℝ :=
  Real.exp (|t| / 2) * |t|

theorem suzukiRealAxisScrewCompactConstant_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisScrewCompactConstant t := by
  unfold suzukiRealAxisScrewCompactConstant
  positivity

/-- The real-axis screw quotient is bounded uniformly in frequency. -/
theorem norm_suzukiRealAxisScrewQuotient_le_compact (t x : ℝ) :
    ‖suzukiRealAxisScrewQuotient t x‖ ≤
      suzukiRealAxisScrewCompactConstant t := by
  exact norm_suzukiArithmeticScrewQuotient_ofReal_le t x

/-- An explicit integrable majorant for the squared norm of one screw
quotient. -/
def suzukiRealAxisScrewNormSqMajorant (t x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator
      (fun _ ↦ suzukiRealAxisScrewCompactConstant t ^ 2) x +
    8 * (1 + x ^ 2)⁻¹

/-- The screw-quotient squared-norm majorant is integrable. -/
theorem integrable_suzukiRealAxisScrewNormSqMajorant (t : ℝ) :
    Integrable (suzukiRealAxisScrewNormSqMajorant t) := by
  have hcompact : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun _ : ℝ ↦ suzukiRealAxisScrewCompactConstant t ^ 2)) :=
    (integrableOn_const (s := Icc (-1 : ℝ) 1)
      (by simp)).integrable_indicator measurableSet_Icc
  have htail : Integrable (fun x : ℝ ↦ 8 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 8
  exact hcompact.add htail

/-- The explicit majorant dominates the genuine screw-quotient squared norm
pointwise. -/
theorem normSq_suzukiRealAxisScrewQuotient_le_majorant (t x : ℝ) :
    ‖suzukiRealAxisScrewQuotient t x‖ ^ 2 ≤
      suzukiRealAxisScrewNormSqMajorant t x := by
  by_cases hx : |x| ≤ 1
  · have hxmem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    have hnorm := norm_suzukiRealAxisScrewQuotient_le_compact t x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold suzukiRealAxisScrewNormSqMajorant
    rw [Set.indicator_of_mem hxmem]
    exact hsquare.trans (le_add_of_nonneg_right (by positivity))
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hxnotmem : x ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      exact hx (abs_le.mpr hmem)
    have hnorm : ‖suzukiRealAxisScrewQuotient t x‖ ≤ 2 / |x| :=
      norm_suzukiArithmeticScrewQuotient_ofReal_le_two_div_abs t x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hinv := norm_complex_inv_ofReal_sq_le_cauchy hxgt.le
    unfold suzukiRealAxisScrewNormSqMajorant
    rw [Set.indicator_of_notMem hxnotmem, zero_add]
    calc
      ‖suzukiRealAxisScrewQuotient t x‖ ^ 2 ≤
          (2 / |x|) ^ 2 := hsquare
      _ = 4 * ‖((x : ℂ)⁻¹)‖ ^ 2 := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ 4 * (2 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 8 * (1 + x ^ 2)⁻¹ := by ring

/-- The squared norm of every real-axis screw quotient is integrable. -/
theorem integrable_normSq_suzukiRealAxisScrewQuotient (t : ℝ) :
    Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisScrewQuotient t x‖ ^ 2) := by
  exact (integrable_suzukiRealAxisScrewNormSqMajorant t).mono'
    ((measurable_suzukiRealAxisScrewQuotient t).aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact normSq_suzukiRealAxisScrewQuotient_le_majorant t x)

/-- Every real-axis arithmetic screw quotient is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisScrewQuotient (t : ℝ) :
    MemLp (suzukiRealAxisScrewQuotient t) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_suzukiRealAxisScrewQuotient t).aestronglyMeasurable).2
  exact integrable_normSq_suzukiRealAxisScrewQuotient t

/-- A finite-window prime term is exactly a fixed von Mangoldt coefficient
times a real-axis screw quotient at the shifted time `t - log n`. -/
theorem suzukiArithmeticPrimeTerm_ofReal_eq_coefficient_mul_screwQuotient
    (t : ℝ) (n : ℕ) (x : ℝ) :
    suzukiArithmeticPrimeTerm t n (x : ℂ) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        suzukiRealAxisScrewQuotient (t - Real.log n) x := by
  rfl

/-- Every fixed finite-window prime term is in `L²(ℝ)`. -/
theorem memLp_two_suzukiArithmeticPrimeTerm_ofReal (t : ℝ) (n : ℕ) :
    MemLp (fun x : ℝ ↦ suzukiArithmeticPrimeTerm t n (x : ℂ)) 2 := by
  have h :=
    (memLp_two_suzukiRealAxisScrewQuotient
      (t - Real.log n)).const_mul
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
  convert h using 1
  funext x
  exact suzukiArithmeticPrimeTerm_ofReal_eq_coefficient_mul_screwQuotient
    t n x

/-- Suzuki's complete finite prime-window contribution is in `L²(ℝ)`. -/
theorem memLp_two_suzukiArithmeticPrimeContribution_ofReal (t : ℝ) :
    MemLp
      (fun x : ℝ ↦ suzukiArithmeticPrimeContribution t (x : ℂ)) 2 := by
  unfold suzukiArithmeticPrimeContribution
  exact memLp_finsetSum (suzukiArithmeticPrimeWindow t)
    (fun n _hn ↦ memLp_two_suzukiArithmeticPrimeTerm_ofReal t n)

/-- The carrier-weighted finite prime contribution on the real axis. -/
def suzukiRealAxisCarrierPrimeContribution (t x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x *
    suzukiArithmeticPrimeContribution t (x : ℂ)

/-- The carrier-weighted finite prime contribution is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisCarrierPrimeContribution (t : ℝ) :
    MemLp (suzukiRealAxisCarrierPrimeContribution t) 2 := by
  change MemLp (fun x : ℝ ↦
    suzukiRealAxisXiZeroCarrier x *
      suzukiArithmeticPrimeContribution t (x : ℂ)) 2
  exact (memLp_two_suzukiArithmeticPrimeContribution_ofReal t).mul'
    memLp_top_suzukiRealAxisXiZeroCarrier

/-- The upper completed-zeta pole kernel is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisUpperPoleKernel :
    MemLp (fun x : ℝ ↦ (1 : ℂ) /
      (1 + 2 * Complex.I * (x : ℂ))) 2 := by
  have h := polynomialBoundaryQuotient_memLp_two
      (q := (1 : ℂ[X]))
      (P := C (2 * Complex.I) * X + C 1)
      (by
        rw [natDegree_linear]
        · norm_num
        · exact mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (by
        intro x
        simp only [eval_add, eval_C, eval_mul, eval_X, map_mul]
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre)
  convert h using 1
  funext x
  simp only [eval_one, eval_add, eval_mul, eval_C, eval_X]
  congr 1
  ring

/-- The lower completed-zeta pole kernel is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisLowerPoleKernel :
    MemLp (fun x : ℝ ↦ (1 : ℂ) /
      (1 - 2 * Complex.I * (x : ℂ))) 2 := by
  have h := polynomialBoundaryQuotient_memLp_two
      (q := (1 : ℂ[X]))
      (P := C (-2 * Complex.I) * X + C 1)
      (by
        rw [natDegree_linear]
        · norm_num
        · exact mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (by
        intro x
        simp only [eval_add, eval_C, eval_mul, eval_X, map_mul]
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre)
  convert h using 1
  funext x
  simp only [eval_one, eval_add, eval_mul, eval_C, eval_X]
  congr 1
  ring

/-- Suzuki's complete elementary pole pair is in `L²(ℝ)`. -/
theorem memLp_two_suzukiArithmeticPoleContribution_ofReal (t : ℝ) :
    MemLp
      (fun x : ℝ ↦ suzukiArithmeticPoleContribution t (x : ℂ)) 2 := by
  have hu := memLp_two_suzukiRealAxisUpperPoleKernel.const_mul
    (((4 * (Real.exp (t / 2) - 1) : ℝ) : ℂ))
  have hl := memLp_two_suzukiRealAxisLowerPoleKernel.const_mul
    (((4 * (Real.exp (-t / 2) - 1) : ℝ) : ℂ))
  have hsum := hu.add hl
  change MemLp (fun x : ℝ ↦
    ((4 * (Real.exp (t / 2) - 1) : ℝ) : ℂ) /
        (1 + 2 * Complex.I * (x : ℂ)) +
      ((4 * (Real.exp (-t / 2) - 1) : ℝ) : ℂ) /
        (1 - 2 * Complex.I * (x : ℂ))) 2
  convert hsum using 1
  funext x
  simp [div_eq_mul_inv]

/-- The carrier-weighted elementary pole contribution on the real axis. -/
def suzukiRealAxisCarrierPoleContribution (t x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x *
    suzukiArithmeticPoleContribution t (x : ℂ)

/-- The carrier-weighted pole contribution is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisCarrierPoleContribution (t : ℝ) :
    MemLp (suzukiRealAxisCarrierPoleContribution t) 2 := by
  change MemLp (fun x : ℝ ↦
    suzukiRealAxisXiZeroCarrier x *
      suzukiArithmeticPoleContribution t (x : ℂ)) 2
  exact (memLp_two_suzukiArithmeticPoleContribution_ofReal t).mul'
    memLp_top_suzukiRealAxisXiZeroCarrier

/-- The carrier-weighted pole-plus-prime block of Suzuki's arithmetic signal. -/
def suzukiRealAxisCarrierPolePrimeContribution (t x : ℝ) : ℂ :=
  suzukiRealAxisCarrierPoleContribution t x +
    suzukiRealAxisCarrierPrimeContribution t x

/-- The complete carrier-weighted pole-plus-prime block is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisCarrierPolePrimeContribution (t : ℝ) :
    MemLp (suzukiRealAxisCarrierPolePrimeContribution t) 2 := by
  exact (memLp_two_suzukiRealAxisCarrierPoleContribution t).add
    (memLp_two_suzukiRealAxisCarrierPrimeContribution t)

end

end RiemannGaussian
