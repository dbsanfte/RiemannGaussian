import RiemannGaussian.RiemannXiSuzukiRealAxisElementaryL2

/-!
# Square integrability of Suzuki's real-axis digamma contribution

Suzuki's standalone digamma term contains the totalized quotient

`-(digamma (1/4 - i x/2) - digamma (1/4)) / (2 i x)`.

The quarter-power digamma estimate already gives the integrable tail after
division by `x`, but it does not control the apparent singularity at zero.
This file closes that local gap directly from the checked Euler series.  Each
digamma-difference summand is bounded by

`(|x| / 2) * (n + 1/4)^(-2)`,

and the shifted square series is summable.  Thus the numerator is globally
linear in `|x|`, which gives a uniform bound for the quotient near zero.  A
constant compact indicator and the existing quarter-power tail then form an
explicit integrable squared-norm majorant.  Finally the norm-one xi carrier
acts through the `L∞ × L² → L²` multiplier theorem.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The shifted square series controlling the digamma difference at zero
frequency. -/
def suzukiRealAxisQuarterSquareSeries (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + 1 / 4| ^ (2 : ℝ)

/-- The shifted quarter-line square series is summable. -/
theorem summable_suzukiRealAxisQuarterSquareSeries :
    Summable suzukiRealAxisQuarterSquareSeries := by
  unfold suzukiRealAxisQuarterSquareSeries
  exact (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2
    (by norm_num)

/-- Each Euler digamma-difference summand is linear in vertical height against
a summable shifted square weight. -/
theorem norm_suzukiWeilDigammaDifferenceSummand_quarter_linear_le
    (r : ℝ) (n : ℕ) :
    ‖suzukiWeilDigammaDifferenceSummand
        (1 / 4 + Complex.I * (r / 2)) (1 / 4) n‖ ≤
      (|r| / 2) * suzukiRealAxisQuarterSquareSeries n := by
  let d : ℝ := (n : ℝ) + 1 / 4
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hb : (n : ℂ) + (1 / 4 : ℂ) = (d : ℂ) := by
    dsimp [d]
    push_cast
    ring
  have ha : (n : ℂ) + (1 / 4 + Complex.I * (r / 2)) =
      (d : ℂ) + Complex.I * (r / 2) := by
    dsimp [d]
    push_cast
    ring
  have hb0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have ha0 : (d : ℂ) + Complex.I * (r / 2) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    exact hd.ne' hre
  have hAre : d ≤ ‖(d : ℂ) + Complex.I * (r / 2)‖ := by
    calc
      d = ((d : ℂ) + Complex.I * (r / 2)).re := by simp
      _ ≤ ‖(d : ℂ) + Complex.I * (r / 2)‖ := Complex.re_le_norm _
  have hquotient :
      suzukiWeilDigammaDifferenceSummand
          (1 / 4 + Complex.I * (r / 2)) (1 / 4) n =
        (Complex.I * (r / 2)) /
          ((d : ℂ) * ((d : ℂ) + Complex.I * (r / 2))) := by
    unfold suzukiWeilDigammaDifferenceSummand
    rw [hb, ha]
    rw [inv_sub_inv hb0 ha0]
    congr 1
    ring
  have htail :
      ‖suzukiWeilDigammaDifferenceSummand
          (1 / 4 + Complex.I * (r / 2)) (1 / 4) n‖ ≤
        |r| / 2 / d ^ 2 := by
    rw [hquotient, norm_div, norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hrhalf : ‖(r : ℂ) / 2‖ = |r| / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hrhalf]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd)
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hAre hd.le
  have hseries :
      suzukiRealAxisQuarterSquareSeries n = 1 / d ^ 2 := by
    unfold suzukiRealAxisQuarterSquareSeries
    have habs : |(n : ℝ) + 1 / 4| = d := by
      rw [abs_of_pos hd]
    rw [habs]
    norm_num [Real.rpow_natCast]
  rw [hseries]
  exact htail.trans_eq (by ring)

/-- The finite mass of the shifted square series. -/
def suzukiRealAxisQuarterSquareSeriesMass : ℝ :=
  ∑' n : ℕ, suzukiRealAxisQuarterSquareSeries n

theorem suzukiRealAxisQuarterSquareSeriesMass_nonneg :
    0 ≤ suzukiRealAxisQuarterSquareSeriesMass := by
  unfold suzukiRealAxisQuarterSquareSeriesMass
  exact tsum_nonneg fun n ↦ by
    unfold suzukiRealAxisQuarterSquareSeries
    positivity

/-- The quarter-line digamma difference is globally linear in vertical
height.  This is the zero-frequency estimate needed after division by `x`. -/
theorem norm_digamma_quarter_vertical_sub_le_linear (r : ℝ) :
    ‖Complex.digamma (1 / 4 + Complex.I * (r / 2)) -
        Complex.digamma (1 / 4)‖ ≤
      (|r| / 2) * suzukiRealAxisQuarterSquareSeriesMass := by
  let D : ℕ → ℂ := fun n ↦
    suzukiWeilDigammaDifferenceSummand
      (1 / 4 + Complex.I * (r / 2)) (1 / 4) n
  have ha : 0 < (1 / 4 + Complex.I * (r / 2) : ℂ).re := by
    norm_num
  have hb : 0 < (1 / 4 : ℂ).re := by norm_num
  have hDnorm : Summable (fun n ↦ ‖D n‖) := by
    simpa only [D] using
      summable_norm_suzukiWeilDigammaDifferenceSummand ha hb
  have hmajor : Summable (fun n ↦
      (|r| / 2) * suzukiRealAxisQuarterSquareSeries n) :=
    summable_suzukiRealAxisQuarterSquareSeries.mul_left _
  have hsum := hasSum_suzukiWeilDigammaDifferenceSummand ha hb
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, D n‖ ≤ ∑' n : ℕ, ‖D n‖ :=
      norm_tsum_le_tsum_norm hDnorm
    _ ≤ ∑' n : ℕ,
        (|r| / 2) * suzukiRealAxisQuarterSquareSeries n :=
      hDnorm.tsum_le_tsum
        (fun n ↦
          norm_suzukiWeilDigammaDifferenceSummand_quarter_linear_le r n)
        hmajor
    _ = (|r| / 2) * suzukiRealAxisQuarterSquareSeriesMass := by
      unfold suzukiRealAxisQuarterSquareSeriesMass
      exact summable_suzukiRealAxisQuarterSquareSeries.tsum_mul_left _

/-- The exact real-axis form of Suzuki's moving digamma parameter. -/
theorem suzukiHurwitzLerchParameter_ofReal (x : ℝ) :
    suzukiHurwitzLerchParameter (x : ℂ) =
      1 / 4 + Complex.I * ((-x : ℝ) / 2) := by
  unfold suzukiHurwitzLerchParameter
  push_cast
  ring

/-- Suzuki's standalone digamma contribution restricted to real frequency. -/
def suzukiRealAxisDigammaContribution (x : ℝ) : ℂ :=
  suzukiArithmeticDigammaContribution (x : ℂ)

/-- The totalized standalone digamma contribution is Borel measurable. -/
theorem measurable_suzukiRealAxisDigammaContribution :
    Measurable suzukiRealAxisDigammaContribution := by
  have hDigammaQuarter : Measurable (fun x : ℝ ↦
      Complex.digamma (1 / 4 + Complex.I * ((-x : ℝ) / 2))) :=
    (continuous_digamma_quarter_line.comp continuous_neg).measurable
  have hDigammaParameter : Measurable (fun x : ℝ ↦
      Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ))) := by
    convert hDigammaQuarter using 1
    funext x
    rw [suzukiHurwitzLerchParameter_ofReal]
  have hofReal : Measurable (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.continuous_ofReal.measurable
  change Measurable (fun x : ℝ ↦
    -(Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ)) -
        Complex.digamma (1 / 4)) /
      (2 * Complex.I * (x : ℂ)))
  exact (hDigammaParameter.sub measurable_const).neg.div
    ((measurable_const.mul measurable_const).mul hofReal)

/-- Linear control of the exact numerator in Suzuki's digamma quotient. -/
theorem norm_digamma_suzukiHurwitzLerchParameter_ofReal_sub_le_linear
    (x : ℝ) :
    ‖Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ)) -
        Complex.digamma (1 / 4)‖ ≤
      (|x| / 2) * suzukiRealAxisQuarterSquareSeriesMass := by
  rw [suzukiHurwitzLerchParameter_ofReal]
  simpa only [abs_neg] using
    norm_digamma_quarter_vertical_sub_le_linear (-x)

/-- Quarter-power tail control of the same exact numerator. -/
theorem norm_digamma_suzukiHurwitzLerchParameter_ofReal_sub_le_quarterPower
    (x : ℝ) :
    ‖Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ)) -
        Complex.digamma (1 / 4)‖ ≤
      2 * (|x| + 1) ^ (1 / 4 : ℝ) *
        suzukiRealAxisQuarterPSeriesMass := by
  rw [suzukiHurwitzLerchParameter_ofReal]
  simpa only [abs_neg] using
    norm_digamma_quarter_vertical_sub_le_quarterPower (-x)

/-- The uniform central-frequency bound for the standalone digamma quotient. -/
def suzukiRealAxisDigammaCompactConstant : ℝ :=
  suzukiRealAxisQuarterSquareSeriesMass / 4

theorem suzukiRealAxisDigammaCompactConstant_nonneg :
    0 ≤ suzukiRealAxisDigammaCompactConstant := by
  unfold suzukiRealAxisDigammaCompactConstant
  positivity [suzukiRealAxisQuarterSquareSeriesMass_nonneg]

/-- The linear numerator estimate cancels the real-axis denominator and
uniformly bounds the totalized digamma quotient. -/
theorem norm_suzukiRealAxisDigammaContribution_le_compact (x : ℝ) :
    ‖suzukiRealAxisDigammaContribution x‖ ≤
      suzukiRealAxisDigammaCompactConstant := by
  by_cases hx : x = 0
  · subst x
    simp [suzukiRealAxisDigammaContribution,
      suzukiArithmeticDigammaContribution, suzukiHurwitzLerchParameter,
      suzukiRealAxisDigammaCompactConstant_nonneg]
  · have hden : ‖2 * Complex.I * (x : ℂ)‖ = 2 * |x| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have hlinear :=
      norm_digamma_suzukiHurwitzLerchParameter_ofReal_sub_le_linear x
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
    unfold suzukiRealAxisDigammaContribution
      suzukiArithmeticDigammaContribution
      suzukiRealAxisDigammaCompactConstant
    rw [norm_div, norm_neg, hden]
    calc
      ‖Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ)) -
          Complex.digamma (1 / 4)‖ / (2 * |x|) ≤
        ((|x| / 2) * suzukiRealAxisQuarterSquareSeriesMass) /
          (2 * |x|) :=
        div_le_div_of_nonneg_right hlinear (by positivity)
      _ = suzukiRealAxisQuarterSquareSeriesMass / 4 := by
        field_simp [habs]
        ring

/-- The standalone digamma quotient has the same integrable quarter-power
tail shape as the zeta component. -/
theorem norm_suzukiRealAxisDigammaContribution_le_tail (x : ℝ) :
    ‖suzukiRealAxisDigammaContribution x‖ ≤
      suzukiRealAxisQuarterPSeriesMass *
        (|x| + 1) ^ (1 / 4 : ℝ) / |x| := by
  by_cases hx : x = 0
  · subst x
    simp [suzukiRealAxisDigammaContribution,
      suzukiArithmeticDigammaContribution, suzukiHurwitzLerchParameter]
  · have hden : ‖2 * Complex.I * (x : ℂ)‖ = 2 * |x| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have hquarter :=
      norm_digamma_suzukiHurwitzLerchParameter_ofReal_sub_le_quarterPower x
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
    unfold suzukiRealAxisDigammaContribution
      suzukiArithmeticDigammaContribution
    rw [norm_div, norm_neg, hden]
    calc
      ‖Complex.digamma (suzukiHurwitzLerchParameter (x : ℂ)) -
          Complex.digamma (1 / 4)‖ / (2 * |x|) ≤
        (2 * (|x| + 1) ^ (1 / 4 : ℝ) *
          suzukiRealAxisQuarterPSeriesMass) / (2 * |x|) :=
        div_le_div_of_nonneg_right hquarter (by positivity)
      _ = suzukiRealAxisQuarterPSeriesMass *
          (|x| + 1) ^ (1 / 4 : ℝ) / |x| := by
        field_simp [habs]

/-- An explicit integrable majorant for the squared standalone digamma
quotient. -/
def suzukiRealAxisDigammaNormSqMajorant (x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator
      (fun _ ↦ suzukiRealAxisDigammaCompactConstant ^ 2) x +
    4 * suzukiRealAxisQuarterPSeriesMass ^ 2 *
      (1 + |x|) ^ (-(3 / 2 : ℝ))

/-- The standalone digamma squared-norm majorant is integrable. -/
theorem integrable_suzukiRealAxisDigammaNormSqMajorant :
    Integrable suzukiRealAxisDigammaNormSqMajorant := by
  have hcompact : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun _ : ℝ ↦ suzukiRealAxisDigammaCompactConstant ^ 2)) :=
    (integrableOn_const (s := Icc (-1 : ℝ) 1)
      (by simp)).integrable_indicator measurableSet_Icc
  have htailBase : Integrable
      (fun x : ℝ ↦ (1 + ‖x‖) ^ (-(3 / 2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (by norm_num)
  have htail : Integrable (fun x : ℝ ↦
      4 * suzukiRealAxisQuarterPSeriesMass ^ 2 *
        (1 + |x|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      htailBase.const_mul (4 * suzukiRealAxisQuarterPSeriesMass ^ 2)
  exact hcompact.add htail

/-- The explicit majorant dominates the genuine digamma squared norm
pointwise. -/
theorem normSq_suzukiRealAxisDigammaContribution_le_majorant (x : ℝ) :
    ‖suzukiRealAxisDigammaContribution x‖ ^ 2 ≤
      suzukiRealAxisDigammaNormSqMajorant x := by
  by_cases hx : |x| ≤ 1
  · have hxmem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    have hnorm := norm_suzukiRealAxisDigammaContribution_le_compact x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold suzukiRealAxisDigammaNormSqMajorant
    rw [Set.indicator_of_mem hxmem]
    exact hsquare.trans (le_add_of_nonneg_right (by positivity))
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hxnotmem : x ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      exact hx (abs_le.mpr hmem)
    have htail := norm_suzukiRealAxisDigammaContribution_le_tail x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htail 2
    have hquarter := sq_quarterPower_div_abs_le hxgt.le
    unfold suzukiRealAxisDigammaNormSqMajorant
    rw [Set.indicator_of_notMem hxnotmem, zero_add]
    calc
      ‖suzukiRealAxisDigammaContribution x‖ ^ 2 ≤
          (suzukiRealAxisQuarterPSeriesMass *
            (|x| + 1) ^ (1 / 4 : ℝ) / |x|) ^ 2 := hsquare
      _ = suzukiRealAxisQuarterPSeriesMass ^ 2 *
          (((|x| + 1) ^ (1 / 4 : ℝ)) / |x|) ^ 2 := by ring
      _ ≤ suzukiRealAxisQuarterPSeriesMass ^ 2 *
          (4 * (|x| + 1) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hquarter (sq_nonneg _)
      _ = 4 * suzukiRealAxisQuarterPSeriesMass ^ 2 *
          (1 + |x|) ^ (-(3 / 2 : ℝ)) := by
        rw [add_comm (1 : ℝ) |x|]
        ring

/-- The squared norm of the standalone real-axis digamma contribution is
integrable. -/
theorem integrable_normSq_suzukiRealAxisDigammaContribution :
    Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisDigammaContribution x‖ ^ 2) := by
  exact integrable_suzukiRealAxisDigammaNormSqMajorant.mono'
    (measurable_suzukiRealAxisDigammaContribution.aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact normSq_suzukiRealAxisDigammaContribution_le_majorant x)

/-- Suzuki's standalone real-axis digamma contribution is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisDigammaContribution :
    MemLp suzukiRealAxisDigammaContribution 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    measurable_suzukiRealAxisDigammaContribution.aestronglyMeasurable).2
  exact integrable_normSq_suzukiRealAxisDigammaContribution

/-- The carrier-weighted standalone digamma contribution on the real axis. -/
def suzukiRealAxisCarrierDigammaContribution (x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x * suzukiRealAxisDigammaContribution x

/-- The carrier-weighted standalone digamma contribution is in `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisCarrierDigammaContribution :
    MemLp suzukiRealAxisCarrierDigammaContribution 2 := by
  exact memLp_two_suzukiRealAxisDigammaContribution.mul'
    memLp_top_suzukiRealAxisXiZeroCarrier

end

end RiemannGaussian
