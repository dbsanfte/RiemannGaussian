import RiemannGaussian.RiemannXiSuzukiHolomorphic

/-!
# The Hurwitz--Lerch term in Suzuki's arithmetic formula

For positive screw time, Suzuki's arithmetic expression for `P_t(z)` contains

`Phi(exp(-2t), 1, 1/4 - i z/2) - Phi(exp(-2t), 1, 1/4)`.

This file constructs that expression directly from its defining series.  The
fixed right half-plane `Re a > 1/8` contains both parameters whenever
`Im z > 1/2`.  Every denominator there has norm at least `1/8`, so the series
is uniformly dominated by eight times a convergent geometric series.
Consequently the sum is holomorphic in the parameter, and Suzuki's composed
difference is holomorphic throughout the safe spectral half-plane.

The hypothesis `t > 0` is essential for this series representation: at
`t = 0` the geometric nome is one and the two individual `s = 1` series do
not converge.  The removable zero-time value must therefore be handled by a
separate limiting theorem rather than by silently assigning divergent sums.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- A common right half-plane containing both Hurwitz--Lerch parameters used
in Suzuki's arithmetic formula above the xi zero strip. -/
def suzukiHurwitzLerchCommonDomain : Set ℂ :=
  {a | (1 / 8 : ℝ) < a.re}

/-- One term of the `Phi(q, 1, a)` defining series. -/
def suzukiHurwitzLerchOneSummand
    (q : ℝ) (a : ℂ) (n : ℕ) : ℂ :=
  (q : ℂ) ^ n / ((n : ℂ) + a)

/-- The defining series for `Phi(q, 1, a)`.  Convergence is proved below for
`0 <= q < 1` on the common right half-plane. -/
def suzukiHurwitzLerchOne (q : ℝ) (a : ℂ) : ℂ :=
  ∑' n : ℕ, suzukiHurwitzLerchOneSummand q a n

/-- The real part lower bound gives a uniform denominator bound on the common
right half-plane. -/
theorem one_eighth_le_norm_nat_add_of_mem_suzukiHurwitzLerchCommonDomain
    {a : ℂ} (ha : a ∈ suzukiHurwitzLerchCommonDomain) (n : ℕ) :
    (1 / 8 : ℝ) ≤ ‖(n : ℂ) + a‖ := by
  calc
    (1 / 8 : ℝ) ≤ (n : ℝ) + a.re := by
      change (1 / 8 : ℝ) < a.re at ha
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    _ = ((n : ℂ) + a).re := by simp
    _ ≤ ‖(n : ℂ) + a‖ := Complex.re_le_norm _

/-- Each Hurwitz--Lerch summand is bounded by an explicit geometric
majorant uniformly over the common right half-plane. -/
theorem norm_suzukiHurwitzLerchOneSummand_le
    {q : ℝ} (hq : 0 ≤ q)
    {a : ℂ} (ha : a ∈ suzukiHurwitzLerchCommonDomain) (n : ℕ) :
    ‖suzukiHurwitzLerchOneSummand q a n‖ ≤ 8 * q ^ n := by
  have hden : (1 / 8 : ℝ) ≤ ‖(n : ℂ) + a‖ :=
    one_eighth_le_norm_nat_add_of_mem_suzukiHurwitzLerchCommonDomain ha n
  have hdenPos : 0 < ‖(n : ℂ) + a‖ :=
    (by norm_num : (0 : ℝ) < 1 / 8).trans_le hden
  rw [suzukiHurwitzLerchOneSummand, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  rw [div_le_iff₀ hdenPos]
  have hpow : 0 ≤ q ^ n := pow_nonneg hq n
  have hmul := mul_le_mul_of_nonneg_left hden hpow
  nlinarith

/-- The defining `Phi(q, 1, a)` series is absolutely summable for
`0 <= q < 1` throughout the common right half-plane. -/
theorem summable_suzukiHurwitzLerchOneSummand
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    {a : ℂ} (ha : a ∈ suzukiHurwitzLerchCommonDomain) :
    Summable (suzukiHurwitzLerchOneSummand q a) := by
  apply
    ((summable_geometric_of_lt_one hq0 hq1).mul_left 8).of_norm_bounded
  exact norm_suzukiHurwitzLerchOneSummand_le hq0 ha

/-- The defining series converges uniformly on the entire common right
half-plane. -/
theorem hasSumUniformlyOn_suzukiHurwitzLerchOneSummand
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSumUniformlyOn
      (fun n : ℕ ↦
        fun a : ℂ ↦ suzukiHurwitzLerchOneSummand q a n)
      (suzukiHurwitzLerchOne q) suzukiHurwitzLerchCommonDomain := by
  change HasSumUniformlyOn
    (fun n : ℕ ↦
      fun a : ℂ ↦ suzukiHurwitzLerchOneSummand q a n)
    (fun a : ℂ ↦ ∑' n : ℕ,
      suzukiHurwitzLerchOneSummand q a n)
    suzukiHurwitzLerchCommonDomain
  exact HasSumUniformlyOn.of_norm_le_summable
    ((summable_geometric_of_lt_one hq0 hq1).mul_left 8)
    (fun n a ha ↦ norm_suzukiHurwitzLerchOneSummand_le hq0 ha n)

/-- Every individual Hurwitz--Lerch summand is holomorphic in its parameter
on the common right half-plane. -/
theorem differentiableOn_suzukiHurwitzLerchOneSummand
    (q : ℝ) (n : ℕ) :
    DifferentiableOn ℂ
      (fun a ↦ suzukiHurwitzLerchOneSummand q a n)
      suzukiHurwitzLerchCommonDomain := by
  intro a ha
  apply DifferentiableAt.differentiableWithinAt
  have hdenNorm :=
    one_eighth_le_norm_nat_add_of_mem_suzukiHurwitzLerchCommonDomain ha n
  have hden : (n : ℂ) + a ≠ 0 := by
    apply Complex.normSq_pos.mp
    rw [Complex.normSq_eq_norm_sq]
    positivity
  unfold suzukiHurwitzLerchOneSummand
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hden

/-- The complete defining series is holomorphic in its parameter on the
common right half-plane. -/
theorem differentiableOn_suzukiHurwitzLerchOne
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    DifferentiableOn ℂ (suzukiHurwitzLerchOne q)
      suzukiHurwitzLerchCommonDomain := by
  unfold suzukiHurwitzLerchOne
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one hq0 hq1).mul_left 8)
    (differentiableOn_suzukiHurwitzLerchOneSummand q)
    (Complex.isOpen_re_gt (1 / 8))
  exact fun n a ha ↦ norm_suzukiHurwitzLerchOneSummand_le hq0 ha n

/-- Analytic form of the preceding holomorphy theorem. -/
theorem analyticOnNhd_suzukiHurwitzLerchOne
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    AnalyticOnNhd ℂ (suzukiHurwitzLerchOne q)
      suzukiHurwitzLerchCommonDomain :=
  (differentiableOn_suzukiHurwitzLerchOne q hq0 hq1).analyticOnNhd
    (Complex.isOpen_re_gt (1 / 8))

/-- The moving Hurwitz--Lerch parameter `1/4 - i z/2` in Suzuki's formula. -/
def suzukiHurwitzLerchParameter (z : ℂ) : ℂ :=
  1 / 4 - Complex.I * z / 2

/-- Real part of Suzuki's moving Hurwitz--Lerch parameter. -/
theorem suzukiHurwitzLerchParameter_re (z : ℂ) :
    (suzukiHurwitzLerchParameter z).re = 1 / 4 + z.im / 2 := by
  simp [suzukiHurwitzLerchParameter]
  ring

/-- Above the spectral zero strip, the moving parameter remains in the common
right half-plane. -/
theorem mapsTo_suzukiHurwitzLerchParameter :
    MapsTo suzukiHurwitzLerchParameter suzukiXiSafeUpperHalfPlane
      suzukiHurwitzLerchCommonDomain := by
  intro z hz
  change (1 / 8 : ℝ) < (suzukiHurwitzLerchParameter z).re
  rw [suzukiHurwitzLerchParameter_re]
  change (1 / 2 : ℝ) < z.im at hz
  linarith

/-- The moving Hurwitz--Lerch value in Suzuki's arithmetic formula. -/
def suzukiArithmeticLerchTail (t : ℝ) (z : ℂ) : ℂ :=
  suzukiHurwitzLerchOne (Real.exp (-2 * t))
    (suzukiHurwitzLerchParameter z)

/-- For positive time, the moving Hurwitz--Lerch value is holomorphic on the
safe spectral half-plane. -/
theorem analyticOnNhd_suzukiArithmeticLerchTail
    {t : ℝ} (ht : 0 < t) :
    AnalyticOnNhd ℂ (suzukiArithmeticLerchTail t)
      suzukiXiSafeUpperHalfPlane := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hparam : AnalyticOnNhd ℂ suzukiHurwitzLerchParameter
      suzukiXiSafeUpperHalfPlane := by
    apply (show DifferentiableOn ℂ suzukiHurwitzLerchParameter
        suzukiXiSafeUpperHalfPlane by
      intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      unfold suzukiHurwitzLerchParameter
      fun_prop).analyticOnNhd
    exact isOpen_suzukiXiSafeUpperHalfPlane
  have hcomp :=
    (analyticOnNhd_suzukiHurwitzLerchOne
      (Real.exp (-2 * t)) hq0 hq1).comp
        hparam mapsTo_suzukiHurwitzLerchParameter
  change AnalyticOnNhd ℂ
    (fun z ↦ suzukiHurwitzLerchOne (Real.exp (-2 * t))
      (suzukiHurwitzLerchParameter z))
    suzukiXiSafeUpperHalfPlane
  exact hcomp

/-- The exact Hurwitz--Lerch difference appearing in Suzuki's formula. -/
def suzukiArithmeticLerchDifference (t : ℝ) (z : ℂ) : ℂ :=
  suzukiArithmeticLerchTail t z -
    suzukiHurwitzLerchOne (Real.exp (-2 * t)) (1 / 4)

/-- Suzuki's Hurwitz--Lerch difference is holomorphic on the safe spectral
half-plane for every positive time. -/
theorem analyticOnNhd_suzukiArithmeticLerchDifference
    {t : ℝ} (ht : 0 < t) :
    AnalyticOnNhd ℂ (suzukiArithmeticLerchDifference t)
      suzukiXiSafeUpperHalfPlane := by
  unfold suzukiArithmeticLerchDifference
  exact (analyticOnNhd_suzukiArithmeticLerchTail ht).sub
    analyticOnNhd_const

end

end RiemannGaussian
