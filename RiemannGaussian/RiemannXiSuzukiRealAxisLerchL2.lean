import RiemannGaussian.RiemannXiSuzukiRealAxisDigammaL2

/-!
# Square integrability of Suzuki's real-axis Hurwitz--Lerch contribution

For fixed positive screw time, put `q = exp (-2t)`.  Then `0 ≤ q < 1`, and
Suzuki's Hurwitz--Lerch difference is a convergent series of differences of
the terms `q^n / (n + a)`.  On the real spectral axis each such difference is
exactly `-q^n` times the Euler digamma-difference summand already controlled
in the preceding file.

This gives two complementary estimates.  The shifted-square estimate is
linear in `|x|` and therefore cancels the quotient denominator at zero.  The
uniform common-half-plane estimate is geometrically summable independently
of `x`, and therefore gives a `C_t / |x|` tail.  These bounds yield an explicit
integrable squared-norm majorant made from a compact indicator and the Cauchy
weight `(1 + x²)⁻¹`.  The xi carrier again acts as a norm-one `L∞` multiplier.

The positivity assumption on `t` is explicit throughout: the defining
Hurwitz--Lerch series is not assigned a value at the divergent nome `q = 1`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The positive-time nome in Suzuki's Hurwitz--Lerch term. -/
def suzukiRealAxisLerchQ (t : ℝ) : ℝ :=
  Real.exp (-2 * t)

theorem suzukiRealAxisLerchQ_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisLerchQ t := by
  unfold suzukiRealAxisLerchQ
  positivity

theorem suzukiRealAxisLerchQ_lt_one {t : ℝ} (ht : 0 < t) :
    suzukiRealAxisLerchQ t < 1 := by
  unfold suzukiRealAxisLerchQ
  rw [Real.exp_lt_one_iff]
  linarith

/-- Every real-axis moving parameter belongs to the common Lerch domain. -/
theorem suzukiHurwitzLerchParameter_ofReal_mem_commonDomain (x : ℝ) :
    suzukiHurwitzLerchParameter (x : ℂ) ∈
      suzukiHurwitzLerchCommonDomain := by
  change (1 / 8 : ℝ) < (suzukiHurwitzLerchParameter (x : ℂ)).re
  rw [suzukiHurwitzLerchParameter_re]
  norm_num

/-- The fixed quarter parameter belongs to the common Lerch domain. -/
theorem one_fourth_mem_suzukiHurwitzLerchCommonDomain :
    (1 / 4 : ℂ) ∈ suzukiHurwitzLerchCommonDomain := by
  norm_num [suzukiHurwitzLerchCommonDomain]

/-- The shifted square weight is uniformly at most sixteen. -/
theorem suzukiRealAxisQuarterSquareSeries_le_sixteen (n : ℕ) :
    suzukiRealAxisQuarterSquareSeries n ≤ 16 := by
  let d : ℝ := (n : ℝ) + 1 / 4
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hquarter : (1 / 4 : ℝ) ≤ d := by
    dsimp [d]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  unfold suzukiRealAxisQuarterSquareSeries
  have habs : |(n : ℝ) + 1 / 4| = d := by
    rw [abs_of_pos hd]
  rw [habs]
  norm_num [Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (sq_pos_of_pos hd)]
  nlinarith [sq_nonneg (d - 1 / 4)]

/-- The geometrically damped shifted-square weight. -/
def suzukiRealAxisLerchLinearSeries (t : ℝ) (n : ℕ) : ℝ :=
  suzukiRealAxisLerchQ t ^ n * suzukiRealAxisQuarterSquareSeries n

/-- The damped shifted-square series is summable at positive time. -/
theorem summable_suzukiRealAxisLerchLinearSeries
    {t : ℝ} (ht : 0 < t) :
    Summable (suzukiRealAxisLerchLinearSeries t) := by
  have hgeo := summable_geometric_of_lt_one
    (suzukiRealAxisLerchQ_nonneg t) (suzukiRealAxisLerchQ_lt_one ht)
  apply (hgeo.mul_left 16).of_nonneg_of_le
  · intro n
    unfold suzukiRealAxisLerchLinearSeries
    exact mul_nonneg
      (pow_nonneg (suzukiRealAxisLerchQ_nonneg t) n) (by
        unfold suzukiRealAxisQuarterSquareSeries
        positivity)
  · intro n
    unfold suzukiRealAxisLerchLinearSeries
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (suzukiRealAxisQuarterSquareSeries_le_sixteen n)
      (pow_nonneg (suzukiRealAxisLerchQ_nonneg t) n)

/-- The finite mass controlling the Lerch difference linearly at zero. -/
def suzukiRealAxisLerchLinearMass (t : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiRealAxisLerchLinearSeries t n

theorem suzukiRealAxisLerchLinearMass_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisLerchLinearMass t := by
  unfold suzukiRealAxisLerchLinearMass
  exact tsum_nonneg fun n ↦ by
    unfold suzukiRealAxisLerchLinearSeries
    exact mul_nonneg
      (pow_nonneg (suzukiRealAxisLerchQ_nonneg t) n) (by
        unfold suzukiRealAxisQuarterSquareSeries
        positivity)

/-- The finite geometric mass controlling the Lerch difference uniformly in
frequency. -/
def suzukiRealAxisLerchGeometricMass (t : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiRealAxisLerchQ t ^ n

theorem suzukiRealAxisLerchGeometricMass_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisLerchGeometricMass t := by
  unfold suzukiRealAxisLerchGeometricMass
  exact tsum_nonneg fun n ↦
    pow_nonneg (suzukiRealAxisLerchQ_nonneg t) n

/-- One term of the real-axis Hurwitz--Lerch difference. -/
def suzukiRealAxisLerchDifferenceSummand
    (t x : ℝ) (n : ℕ) : ℂ :=
  suzukiHurwitzLerchOneSummand (suzukiRealAxisLerchQ t)
      (suzukiHurwitzLerchParameter (x : ℂ)) n -
    suzukiHurwitzLerchOneSummand (suzukiRealAxisLerchQ t) (1 / 4) n

/-- A Lerch-difference summand is exactly a geometrically damped negative
Euler digamma-difference summand. -/
theorem suzukiRealAxisLerchDifferenceSummand_eq
    (t x : ℝ) (n : ℕ) :
    suzukiRealAxisLerchDifferenceSummand t x n =
      -((suzukiRealAxisLerchQ t : ℂ) ^ n *
        suzukiWeilDigammaDifferenceSummand
          (suzukiHurwitzLerchParameter (x : ℂ)) (1 / 4) n) := by
  unfold suzukiRealAxisLerchDifferenceSummand
    suzukiHurwitzLerchOneSummand
    suzukiWeilDigammaDifferenceSummand
  ring

/-- Linear-in-frequency control of one Lerch-difference summand. -/
theorem norm_suzukiRealAxisLerchDifferenceSummand_le_linear
    (t x : ℝ) (n : ℕ) :
    ‖suzukiRealAxisLerchDifferenceSummand t x n‖ ≤
      (|x| / 2) * suzukiRealAxisLerchLinearSeries t n := by
  have hdigamma :
      ‖suzukiWeilDigammaDifferenceSummand
          (suzukiHurwitzLerchParameter (x : ℂ)) (1 / 4) n‖ ≤
        (|x| / 2) * suzukiRealAxisQuarterSquareSeries n := by
    rw [suzukiHurwitzLerchParameter_ofReal]
    simpa only [abs_neg] using
      norm_suzukiWeilDigammaDifferenceSummand_quarter_linear_le (-x) n
  rw [suzukiRealAxisLerchDifferenceSummand_eq, norm_neg, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (suzukiRealAxisLerchQ_nonneg t)]
  unfold suzukiRealAxisLerchLinearSeries
  calc
    suzukiRealAxisLerchQ t ^ n *
        ‖suzukiWeilDigammaDifferenceSummand
          (suzukiHurwitzLerchParameter (x : ℂ)) (1 / 4) n‖ ≤
      suzukiRealAxisLerchQ t ^ n *
        ((|x| / 2) * suzukiRealAxisQuarterSquareSeries n) :=
      mul_le_mul_of_nonneg_left hdigamma
        (pow_nonneg (suzukiRealAxisLerchQ_nonneg t) n)
    _ = (|x| / 2) *
        (suzukiRealAxisLerchQ t ^ n *
          suzukiRealAxisQuarterSquareSeries n) := by ring

/-- Uniform geometric control of one Lerch-difference summand. -/
theorem norm_suzukiRealAxisLerchDifferenceSummand_le_geometric
    (t x : ℝ) (n : ℕ) :
    ‖suzukiRealAxisLerchDifferenceSummand t x n‖ ≤
      16 * suzukiRealAxisLerchQ t ^ n := by
  unfold suzukiRealAxisLerchDifferenceSummand suzukiRealAxisLerchQ
  calc
    ‖suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
          (suzukiHurwitzLerchParameter (x : ℂ)) n -
        suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
          (1 / 4) n‖ ≤
      ‖suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
          (suzukiHurwitzLerchParameter (x : ℂ)) n‖ +
        ‖suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
          (1 / 4) n‖ := norm_sub_le _ _
    _ ≤ 8 * Real.exp (-2 * t) ^ n +
        8 * Real.exp (-2 * t) ^ n := by
      exact add_le_add
        (norm_suzukiHurwitzLerchOneSummand_le
          (Real.exp_pos _).le
          (suzukiHurwitzLerchParameter_ofReal_mem_commonDomain x) n)
        (norm_suzukiHurwitzLerchOneSummand_le
          (Real.exp_pos _).le
          one_fourth_mem_suzukiHurwitzLerchCommonDomain n)
    _ = 16 * Real.exp (-2 * t) ^ n := by ring

/-- The real-axis difference series sums to Suzuki's literal
Hurwitz--Lerch difference. -/
theorem hasSum_suzukiRealAxisLerchDifferenceSummand
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasSum (suzukiRealAxisLerchDifferenceSummand t x)
      (suzukiArithmeticLerchDifference t (x : ℂ)) := by
  change HasSum (fun n : ℕ ↦
    suzukiHurwitzLerchOneSummand (suzukiRealAxisLerchQ t)
        (suzukiHurwitzLerchParameter (x : ℂ)) n -
      suzukiHurwitzLerchOneSummand (suzukiRealAxisLerchQ t)
        (1 / 4) n)
    (suzukiArithmeticLerchDifference t (x : ℂ))
  have hmoving := summable_suzukiHurwitzLerchOneSummand
    (suzukiRealAxisLerchQ t) (suzukiRealAxisLerchQ_nonneg t)
    (suzukiRealAxisLerchQ_lt_one ht)
    (suzukiHurwitzLerchParameter_ofReal_mem_commonDomain x)
  have hfixed := summable_suzukiHurwitzLerchOneSummand
    (suzukiRealAxisLerchQ t) (suzukiRealAxisLerchQ_nonneg t)
    (suzukiRealAxisLerchQ_lt_one ht)
    one_fourth_mem_suzukiHurwitzLerchCommonDomain
  simpa [suzukiRealAxisLerchDifferenceSummand, suzukiRealAxisLerchQ,
    suzukiArithmeticLerchDifference, suzukiArithmeticLerchTail,
    suzukiHurwitzLerchOne] using hmoving.hasSum.sub hfixed.hasSum

/-- The complete Lerch difference is linear in frequency at the origin. -/
theorem norm_suzukiArithmeticLerchDifference_ofReal_le_linear
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ ≤
      (|x| / 2) * suzukiRealAxisLerchLinearMass t := by
  have hsum := hasSum_suzukiRealAxisLerchDifferenceSummand ht x
  have hnorm : Summable (fun n ↦
      ‖suzukiRealAxisLerchDifferenceSummand t x n‖) :=
    hsum.summable.norm
  have hmajor : Summable (fun n ↦
      (|x| / 2) * suzukiRealAxisLerchLinearSeries t n) :=
    (summable_suzukiRealAxisLerchLinearSeries ht).mul_left _
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, suzukiRealAxisLerchDifferenceSummand t x n‖ ≤
        ∑' n : ℕ, ‖suzukiRealAxisLerchDifferenceSummand t x n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        (|x| / 2) * suzukiRealAxisLerchLinearSeries t n :=
      hnorm.tsum_le_tsum
        (fun n ↦
          norm_suzukiRealAxisLerchDifferenceSummand_le_linear t x n)
        hmajor
    _ = (|x| / 2) * suzukiRealAxisLerchLinearMass t := by
      unfold suzukiRealAxisLerchLinearMass
      exact (summable_suzukiRealAxisLerchLinearSeries ht).tsum_mul_left _

/-- The complete Lerch difference is uniformly bounded by a geometric mass. -/
theorem norm_suzukiArithmeticLerchDifference_ofReal_le_geometric
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ ≤
      16 * suzukiRealAxisLerchGeometricMass t := by
  have hsum := hasSum_suzukiRealAxisLerchDifferenceSummand ht x
  have hnorm : Summable (fun n ↦
      ‖suzukiRealAxisLerchDifferenceSummand t x n‖) :=
    hsum.summable.norm
  have hgeo := summable_geometric_of_lt_one
    (suzukiRealAxisLerchQ_nonneg t) (suzukiRealAxisLerchQ_lt_one ht)
  have hmajor : Summable (fun n ↦
      16 * suzukiRealAxisLerchQ t ^ n) := hgeo.mul_left 16
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, suzukiRealAxisLerchDifferenceSummand t x n‖ ≤
        ∑' n : ℕ, ‖suzukiRealAxisLerchDifferenceSummand t x n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, 16 * suzukiRealAxisLerchQ t ^ n :=
      hnorm.tsum_le_tsum
        (fun n ↦
          norm_suzukiRealAxisLerchDifferenceSummand_le_geometric t x n)
        hmajor
    _ = 16 * suzukiRealAxisLerchGeometricMass t := by
      unfold suzukiRealAxisLerchGeometricMass
      exact hgeo.tsum_mul_left _

/-- Suzuki's Hurwitz--Lerch contribution restricted to real frequency. -/
def suzukiRealAxisLerchContribution (t x : ℝ) : ℂ :=
  suzukiArithmeticLerchContribution t (x : ℂ)

/-- At positive time, the totalized real-axis Lerch contribution is Borel
measurable. -/
theorem measurable_suzukiRealAxisLerchContribution
    {t : ℝ} (ht : 0 < t) :
    Measurable (suzukiRealAxisLerchContribution t) := by
  have hMoving : Continuous (fun x : ℝ ↦
      suzukiHurwitzLerchOne (Real.exp (-2 * t))
        (suzukiHurwitzLerchParameter (x : ℂ))) :=
    (analyticOnNhd_suzukiHurwitzLerchOne
      (Real.exp (-2 * t)) (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)).continuousOn.comp_continuous
      (by unfold suzukiHurwitzLerchParameter; fun_prop)
      suzukiHurwitzLerchParameter_ofReal_mem_commonDomain
  have hDifference : Continuous (fun x : ℝ ↦
      suzukiArithmeticLerchDifference t (x : ℂ)) := by
    unfold suzukiArithmeticLerchDifference suzukiArithmeticLerchTail
    exact hMoving.sub continuous_const
  have hofReal : Measurable (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.continuous_ofReal.measurable
  change Measurable (fun x : ℝ ↦
    -((Real.exp (-t / 2) : ℝ) : ℂ) *
      suzukiArithmeticLerchDifference t (x : ℂ) /
        (2 * Complex.I * (x : ℂ)))
  exact (measurable_const.mul hDifference.measurable).div
    ((measurable_const.mul measurable_const).mul hofReal)

/-- The compact-frequency bound for the Lerch quotient. -/
def suzukiRealAxisLerchCompactConstant (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * suzukiRealAxisLerchLinearMass t / 4

theorem suzukiRealAxisLerchCompactConstant_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisLerchCompactConstant t := by
  unfold suzukiRealAxisLerchCompactConstant
  positivity [suzukiRealAxisLerchLinearMass_nonneg t]

/-- The inverse-frequency tail constant for the Lerch quotient. -/
def suzukiRealAxisLerchTailConstant (t : ℝ) : ℝ :=
  8 * Real.exp (-t / 2) * suzukiRealAxisLerchGeometricMass t

theorem suzukiRealAxisLerchTailConstant_nonneg (t : ℝ) :
    0 ≤ suzukiRealAxisLerchTailConstant t := by
  unfold suzukiRealAxisLerchTailConstant
  positivity [suzukiRealAxisLerchGeometricMass_nonneg t]

/-- Linear cancellation of the Lerch difference uniformly bounds its
totalized quotient near zero. -/
theorem norm_suzukiRealAxisLerchContribution_le_compact
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖suzukiRealAxisLerchContribution t x‖ ≤
      suzukiRealAxisLerchCompactConstant t := by
  by_cases hx : x = 0
  · subst x
    simp [suzukiRealAxisLerchContribution,
      suzukiArithmeticLerchContribution, suzukiArithmeticLerchDifference,
      suzukiArithmeticLerchTail, suzukiHurwitzLerchParameter,
      suzukiRealAxisLerchCompactConstant_nonneg]
  · have hden : ‖2 * Complex.I * (x : ℂ)‖ = 2 * |x| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have hlinear :=
      norm_suzukiArithmeticLerchDifference_ofReal_le_linear ht x
    have hmul : Real.exp (-t / 2) *
        ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ ≤
      Real.exp (-t / 2) *
        ((|x| / 2) * suzukiRealAxisLerchLinearMass t) :=
      mul_le_mul_of_nonneg_left hlinear (Real.exp_pos _).le
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
    unfold suzukiRealAxisLerchContribution
      suzukiArithmeticLerchContribution
      suzukiRealAxisLerchCompactConstant
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hden]
    calc
      Real.exp (-t / 2) *
          ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ /
            (2 * |x|) ≤
        (Real.exp (-t / 2) *
          ((|x| / 2) * suzukiRealAxisLerchLinearMass t)) /
            (2 * |x|) :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ = Real.exp (-t / 2) *
          suzukiRealAxisLerchLinearMass t / 4 := by
        field_simp [habs]
        ring

/-- The positive-time Lerch quotient has an inverse-frequency tail. -/
theorem norm_suzukiRealAxisLerchContribution_le_tail
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖suzukiRealAxisLerchContribution t x‖ ≤
      suzukiRealAxisLerchTailConstant t / |x| := by
  by_cases hx : x = 0
  · subst x
    simp [suzukiRealAxisLerchContribution,
      suzukiArithmeticLerchContribution, suzukiArithmeticLerchDifference,
      suzukiArithmeticLerchTail, suzukiHurwitzLerchParameter]
  · have hden : ‖2 * Complex.I * (x : ℂ)‖ = 2 * |x| := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have hgeometric :=
      norm_suzukiArithmeticLerchDifference_ofReal_le_geometric ht x
    have hmul : Real.exp (-t / 2) *
        ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ ≤
      Real.exp (-t / 2) *
        (16 * suzukiRealAxisLerchGeometricMass t) :=
      mul_le_mul_of_nonneg_left hgeometric (Real.exp_pos _).le
    have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
    unfold suzukiRealAxisLerchContribution
      suzukiArithmeticLerchContribution suzukiRealAxisLerchTailConstant
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hden]
    calc
      Real.exp (-t / 2) *
          ‖suzukiArithmeticLerchDifference t (x : ℂ)‖ /
            (2 * |x|) ≤
        (Real.exp (-t / 2) *
          (16 * suzukiRealAxisLerchGeometricMass t)) /
            (2 * |x|) :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ = (8 * Real.exp (-t / 2) *
          suzukiRealAxisLerchGeometricMass t) / |x| := by
        field_simp [habs]
        ring

/-- An explicit integrable majorant for the squared Lerch quotient. -/
def suzukiRealAxisLerchNormSqMajorant (t x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator
      (fun _ ↦ suzukiRealAxisLerchCompactConstant t ^ 2) x +
    2 * suzukiRealAxisLerchTailConstant t ^ 2 * (1 + x ^ 2)⁻¹

/-- The Lerch squared-norm majorant is integrable. -/
theorem integrable_suzukiRealAxisLerchNormSqMajorant (t : ℝ) :
    Integrable (suzukiRealAxisLerchNormSqMajorant t) := by
  have hcompact : Integrable
      ((Icc (-1 : ℝ) 1).indicator
        (fun _ : ℝ ↦ suzukiRealAxisLerchCompactConstant t ^ 2)) :=
    (integrableOn_const (s := Icc (-1 : ℝ) 1)
      (by simp)).integrable_indicator measurableSet_Icc
  have htail : Integrable (fun x : ℝ ↦
      2 * suzukiRealAxisLerchTailConstant t ^ 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul
      (2 * suzukiRealAxisLerchTailConstant t ^ 2)
  exact hcompact.add htail

/-- The explicit majorant dominates the genuine Lerch squared norm
pointwise. -/
theorem normSq_suzukiRealAxisLerchContribution_le_majorant
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖suzukiRealAxisLerchContribution t x‖ ^ 2 ≤
      suzukiRealAxisLerchNormSqMajorant t x := by
  by_cases hx : |x| ≤ 1
  · have hxmem : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
    have hnorm := norm_suzukiRealAxisLerchContribution_le_compact ht x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold suzukiRealAxisLerchNormSqMajorant
    rw [Set.indicator_of_mem hxmem]
    exact hsquare.trans (le_add_of_nonneg_right (by positivity))
  · have hxgt : 1 < |x| := lt_of_not_ge hx
    have hxnotmem : x ∉ Icc (-1 : ℝ) 1 := by
      intro hmem
      exact hx (abs_le.mpr hmem)
    have htail := norm_suzukiRealAxisLerchContribution_le_tail ht x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htail 2
    have hinv := norm_complex_inv_ofReal_sq_le_cauchy hxgt.le
    unfold suzukiRealAxisLerchNormSqMajorant
    rw [Set.indicator_of_notMem hxnotmem, zero_add]
    calc
      ‖suzukiRealAxisLerchContribution t x‖ ^ 2 ≤
          (suzukiRealAxisLerchTailConstant t / |x|) ^ 2 := hsquare
      _ = suzukiRealAxisLerchTailConstant t ^ 2 *
          ‖((x : ℂ)⁻¹)‖ ^ 2 := by
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ suzukiRealAxisLerchTailConstant t ^ 2 *
          (2 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = 2 * suzukiRealAxisLerchTailConstant t ^ 2 *
          (1 + x ^ 2)⁻¹ := by ring

/-- The squared norm of the positive-time real-axis Lerch contribution is
integrable. -/
theorem integrable_normSq_suzukiRealAxisLerchContribution
    {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisLerchContribution t x‖ ^ 2) := by
  exact (integrable_suzukiRealAxisLerchNormSqMajorant t).mono'
    ((measurable_suzukiRealAxisLerchContribution ht).aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact normSq_suzukiRealAxisLerchContribution_le_majorant ht x)

/-- Suzuki's positive-time real-axis Hurwitz--Lerch contribution belongs to
`L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisLerchContribution
    {t : ℝ} (ht : 0 < t) :
    MemLp (suzukiRealAxisLerchContribution t) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_suzukiRealAxisLerchContribution ht).aestronglyMeasurable).2
  exact integrable_normSq_suzukiRealAxisLerchContribution ht

/-- The carrier-weighted positive-time Lerch contribution on the real axis. -/
def suzukiRealAxisCarrierLerchContribution (t x : ℝ) : ℂ :=
  suzukiRealAxisXiZeroCarrier x * suzukiRealAxisLerchContribution t x

/-- The carrier-weighted positive-time Lerch contribution belongs to
`L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisCarrierLerchContribution
    {t : ℝ} (ht : 0 < t) :
    MemLp (suzukiRealAxisCarrierLerchContribution t) 2 := by
  exact (memLp_two_suzukiRealAxisLerchContribution ht).mul'
    memLp_top_suzukiRealAxisXiZeroCarrier

end

end RiemannGaussian
