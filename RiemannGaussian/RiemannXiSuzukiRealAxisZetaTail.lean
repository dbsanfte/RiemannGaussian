import RiemannGaussian.RiemannXiSuzukiRealAxisDigamma

/-!
# Real-axis decay of Suzuki's zeta contribution

This file combines the quarter-power completed-logarithmic-derivative bound
with the arithmetic screw quotient.  The quotient is identified with the
already constructed continuously extended spectral coefficient away from
zero.  It therefore has both a uniform real-axis bound and the elementary
inverse-frequency bound `2 / |x|`.

After regrouping multiplication so that the xi carrier acts on `ζ'/ζ`
before norms are taken, the zeta part of Suzuki's arithmetic signal obtains
the explicit tail

`C * (|x| + 1)^(1/4) / |x|`.

The totalized value at `x = 0` is included in every statement.  Integrability
of the squared tail and the remaining arithmetic terms are separate steps.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Away from zero, the arithmetic screw quotient is `-i` times the
continuously extended spectral screw coefficient. -/
theorem suzukiArithmeticScrewQuotient_eq_neg_I_mul_coefficient
    (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    suzukiArithmeticScrewQuotient t z =
      -Complex.I * suzukiSpectralScrewCoefficient t z := by
  rw [suzukiSpectralScrewCoefficient_of_ne_zero t hz]
  unfold suzukiArithmeticScrewQuotient spectralScrewExponential
  field_simp [hz, Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The arithmetic screw quotient is uniformly bounded on the real axis,
including its totalized zero value. -/
theorem norm_suzukiArithmeticScrewQuotient_ofReal_le
    (t x : ℝ) :
    ‖suzukiArithmeticScrewQuotient t (x : ℂ)‖ ≤
      Real.exp (|t| / 2) * |t| := by
  by_cases hx : x = 0
  · subst x
    simp [suzukiArithmeticScrewQuotient]
    positivity
  · have hxComplex : (x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hx
    rw [suzukiArithmeticScrewQuotient_eq_neg_I_mul_coefficient
      t hxComplex, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact norm_suzukiSpectralScrewCoefficient_le_strip t (by simp)

/-- The numerator of the real-axis screw quotient has norm at most two. -/
theorem norm_suzukiArithmeticScrewNumerator_ofReal_le_two
    (t x : ℝ) :
    ‖Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) - 1‖ ≤ 2 := by
  calc
    ‖Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ)) - 1‖ ≤
        ‖Complex.exp (-Complex.I * (x : ℂ) * (t : ℂ))‖ +
          ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [Complex.norm_exp]
      have hre :
          (-Complex.I * (x : ℂ) * (t : ℂ)).re = 0 := by simp
      rw [hre]
      norm_num

/-- The arithmetic screw quotient has inverse-frequency decay on the whole
real axis.  At zero both sides use Lean's totalized division and equal zero. -/
theorem norm_suzukiArithmeticScrewQuotient_ofReal_le_two_div_abs
    (t x : ℝ) :
    ‖suzukiArithmeticScrewQuotient t (x : ℂ)‖ ≤ 2 / |x| := by
  unfold suzukiArithmeticScrewQuotient
  rw [norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right
    (norm_suzukiArithmeticScrewNumerator_ofReal_le_two t x)
    (abs_nonneg x)

/-- In the zeta contribution, multiplication is regrouped so that Suzuki's
carrier cancels the completed xi logarithmic derivative before taking norms. -/
theorem suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal
    (t x : ℝ) :
    suzukiXiZeroCarrier (x : ℂ) *
        suzukiArithmeticZetaContribution t (x : ℂ) =
      suzukiArithmeticScrewQuotient t (x : ℂ) *
        (suzukiXiZeroCarrier (x : ℂ) *
          logDeriv riemannZeta
            (suzukiArithmeticZetaArgument (x : ℂ))) := by
  unfold suzukiArithmeticZetaContribution
  ring

/-- The fixed elementary part of the carrier-weighted zeta logarithmic
derivative bound. -/
def suzukiRealAxisZetaElementaryGrowthConstant : ℝ :=
  5 + ‖Complex.log Real.pi / 2‖

theorem suzukiRealAxisZetaElementaryGrowthConstant_nonneg :
    0 ≤ suzukiRealAxisZetaElementaryGrowthConstant := by
  unfold suzukiRealAxisZetaElementaryGrowthConstant
  positivity

/-- The quarter-power coefficient in the carrier-weighted zeta logarithmic
derivative bound. -/
def suzukiRealAxisZetaQuarterGrowthConstant : ℝ :=
  suzukiRealAxisQuarterDigammaGrowthConstant / 2

theorem suzukiRealAxisZetaQuarterGrowthConstant_nonneg :
    0 ≤ suzukiRealAxisZetaQuarterGrowthConstant := by
  unfold suzukiRealAxisZetaQuarterGrowthConstant
  positivity [suzukiRealAxisQuarterDigammaGrowthConstant_nonneg]

/-- A single nonnegative constant for the inverse-frequency zeta tail. -/
def suzukiRealAxisZetaTailConstant : ℝ :=
  2 * (suzukiRealAxisZetaElementaryGrowthConstant +
    suzukiRealAxisZetaQuarterGrowthConstant)

theorem suzukiRealAxisZetaTailConstant_nonneg :
    0 ≤ suzukiRealAxisZetaTailConstant := by
  unfold suzukiRealAxisZetaTailConstant
  positivity [suzukiRealAxisZetaElementaryGrowthConstant_nonneg,
    suzukiRealAxisZetaQuarterGrowthConstant_nonneg]

/-- A uniform-in-frequency estimate for the carrier-weighted zeta
contribution.  This controls compact real intervals. -/
theorem norm_suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal_le
    (t x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        suzukiArithmeticZetaContribution t (x : ℂ)‖ ≤
      (Real.exp (|t| / 2) * |t|) *
        (suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant *
            (|x| + 1) ^ (1 / 4 : ℝ)) := by
  rw [suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal,
    norm_mul]
  apply mul_le_mul
  · exact norm_suzukiArithmeticScrewQuotient_ofReal_le t x
  · simpa only [suzukiRealAxisZetaElementaryGrowthConstant,
      suzukiRealAxisZetaQuarterGrowthConstant] using
      norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le_quarterPower
        x
  · exact norm_nonneg _
  · positivity

/-- The carrier-weighted zeta contribution has explicit
`(|x|+1)^(1/4)/|x|` decay. -/
theorem norm_suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal_le_tail
    (t x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        suzukiArithmeticZetaContribution t (x : ℂ)‖ ≤
      suzukiRealAxisZetaTailConstant *
        (|x| + 1) ^ (1 / 4 : ℝ) / |x| := by
  have hpow : 1 ≤ (|x| + 1) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg x]) (by norm_num)
  have hgrowth :
      suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant *
            (|x| + 1) ^ (1 / 4 : ℝ) ≤
        (suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant) *
            (|x| + 1) ^ (1 / 4 : ℝ) := by
    have hnonneg : 0 ≤
        suzukiRealAxisZetaElementaryGrowthConstant *
          ((|x| + 1) ^ (1 / 4 : ℝ) - 1) :=
      mul_nonneg suzukiRealAxisZetaElementaryGrowthConstant_nonneg
        (sub_nonneg.mpr hpow)
    nlinarith
  rw [suzukiXiZeroCarrier_mul_suzukiArithmeticZetaContribution_ofReal,
    norm_mul]
  calc
    ‖suzukiArithmeticScrewQuotient t (x : ℂ)‖ *
        ‖suzukiXiZeroCarrier (x : ℂ) *
          logDeriv riemannZeta
            (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      (2 / |x|) *
        (suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant *
            (|x| + 1) ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul
      · exact norm_suzukiArithmeticScrewQuotient_ofReal_le_two_div_abs t x
      · simpa only [suzukiRealAxisZetaElementaryGrowthConstant,
          suzukiRealAxisZetaQuarterGrowthConstant] using
          norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le_quarterPower
            x
      · exact norm_nonneg _
      · positivity
    _ ≤ (2 / |x|) *
        ((suzukiRealAxisZetaElementaryGrowthConstant +
          suzukiRealAxisZetaQuarterGrowthConstant) *
            (|x| + 1) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = suzukiRealAxisZetaTailConstant *
        (|x| + 1) ^ (1 / 4 : ℝ) / |x| := by
      unfold suzukiRealAxisZetaTailConstant
      ring

end

end RiemannGaussian
