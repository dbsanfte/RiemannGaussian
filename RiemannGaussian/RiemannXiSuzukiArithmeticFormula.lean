import RiemannGaussian.RiemannXiSuzukiArithmeticLerch
import RiemannGaussian.GaussianDigammaGrowth
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Suzuki's positive-time arithmetic `P_t`

This file formalizes every term on the arithmetic side of Suzuki's equation
(1.6) for positive screw time:

* the two elementary completed-zeta pole contributions;
* the logarithmic derivative of zeta at `1/2 - i z`;
* the finite von Mangoldt sum over `1 <= n <= exp(t)`;
* the digamma difference at `1/4 - i z/2`; and
* the Hurwitz--Lerch difference constructed from its convergent series.

All denominators are proved nonzero on `Im z > 1/2`.  The zeta argument then
has real part greater than one, the gamma/Lerch argument has positive real
part, and every component is holomorphic.  Their sum is therefore a literal
holomorphic arithmetic function for every `t > 0`.

No equality with the spectral zero sum is asserted here.  That equality is
Suzuki's specialized Weil explicit-formula theorem and remains the next
formal obligation.  Likewise, the `t = 0` value is not obtained by evaluating
the divergent nome-one Lerch series; it requires a separate removable-limit
argument.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- A point above the spectral-xi zero strip is nonzero. -/
theorem ne_zero_of_mem_suzukiXiSafeUpperHalfPlane
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    z ≠ 0 := by
  intro h
  subst z
  norm_num [suzukiXiSafeUpperHalfPlane] at hz

/-- The upper completed-zeta pole denominator is nonzero on the safe
half-plane. -/
theorem one_add_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    1 + 2 * Complex.I * z ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  change (1 / 2 : ℝ) < z.im at hz
  linarith

/-- The lower completed-zeta pole denominator is nonzero on the safe
half-plane. -/
theorem one_sub_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    1 - 2 * Complex.I * z ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  change (1 / 2 : ℝ) < z.im at hz
  linarith

/-- The zeta argument `1/2 - i z` in Suzuki's arithmetic formula. -/
def suzukiArithmeticZetaArgument (z : ℂ) : ℂ :=
  1 / 2 - Complex.I * z

/-- Real part of the zeta argument in spectral coordinates. -/
theorem suzukiArithmeticZetaArgument_re (z : ℂ) :
    (suzukiArithmeticZetaArgument z).re = 1 / 2 + z.im := by
  simp [suzukiArithmeticZetaArgument]

/-- The Euler-product half-plane for the zeta logarithmic derivative. -/
def suzukiArithmeticZetaDomain : Set ℂ :=
  {s | (1 : ℝ) < s.re}

/-- A safe spectral point maps into the Euler-product half-plane. -/
theorem mapsTo_suzukiArithmeticZetaArgument :
    MapsTo suzukiArithmeticZetaArgument suzukiXiSafeUpperHalfPlane
      suzukiArithmeticZetaDomain := by
  intro z hz
  change (1 : ℝ) < (suzukiArithmeticZetaArgument z).re
  rw [suzukiArithmeticZetaArgument_re]
  change (1 / 2 : ℝ) < z.im at hz
  linarith

/-- The zeta logarithmic derivative is holomorphic where `Re s > 1`. -/
theorem analyticOnNhd_logDeriv_riemannZeta_re_gt_one :
    AnalyticOnNhd ℂ (logDeriv riemannZeta)
      suzukiArithmeticZetaDomain := by
  have hzeta : AnalyticOnNhd ℂ riemannZeta
      suzukiArithmeticZetaDomain := by
    apply analyticOn_riemannZeta.mono
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    subst s
    norm_num [suzukiArithmeticZetaDomain] at hs
  rw [show logDeriv riemannZeta =
      fun s ↦ deriv riemannZeta s / riemannZeta s by rfl]
  exact hzeta.deriv.div hzeta fun s hs ↦
    riemannZeta_ne_zero_of_one_lt_re hs

/-- The composed zeta logarithmic derivative is holomorphic throughout the
safe spectral half-plane. -/
theorem analyticOnNhd_suzukiArithmeticZetaLogDerivative :
    AnalyticOnNhd ℂ
      (fun z ↦ logDeriv riemannZeta (suzukiArithmeticZetaArgument z))
      suzukiXiSafeUpperHalfPlane := by
  have harg : AnalyticOnNhd ℂ suzukiArithmeticZetaArgument
      suzukiXiSafeUpperHalfPlane := by
    apply (show DifferentiableOn ℂ suzukiArithmeticZetaArgument
        suzukiXiSafeUpperHalfPlane by
      intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      unfold suzukiArithmeticZetaArgument
      fun_prop).analyticOnNhd
    exact isOpen_suzukiXiSafeUpperHalfPlane
  exact analyticOnNhd_logDeriv_riemannZeta_re_gt_one.comp
    harg mapsTo_suzukiArithmeticZetaArgument

/-- The two elementary completed-zeta pole contributions in Suzuki's
arithmetic formula. -/
def suzukiArithmeticPoleContribution (t : ℝ) (z : ℂ) : ℂ :=
  ((4 * (Real.exp (t / 2) - 1) : ℝ) : ℂ) /
      (1 + 2 * Complex.I * z) +
    ((4 * (Real.exp (-t / 2) - 1) : ℝ) : ℂ) /
      (1 - 2 * Complex.I * z)

/-- The elementary pole contribution is holomorphic on the safe
half-plane. -/
theorem analyticOnNhd_suzukiArithmeticPoleContribution (t : ℝ) :
    AnalyticOnNhd ℂ (suzukiArithmeticPoleContribution t)
      suzukiXiSafeUpperHalfPlane := by
  apply (show DifferentiableOn ℂ (suzukiArithmeticPoleContribution t)
      suzukiXiSafeUpperHalfPlane by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold suzukiArithmeticPoleContribution
    apply DifferentiableAt.add
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact
          one_add_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact
          one_sub_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz).analyticOnNhd
  exact isOpen_suzukiXiSafeUpperHalfPlane

/-- The continuously safe quotient `(exp(-i z t) - 1)/(i z)` on the spectral
half-plane.  The removable value at zero is irrelevant here because zero lies
outside the domain. -/
def suzukiArithmeticScrewQuotient (t : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
    (Complex.I * z)

/-- The arithmetic screw quotient is holomorphic on the safe half-plane. -/
theorem analyticOnNhd_suzukiArithmeticScrewQuotient (t : ℝ) :
    AnalyticOnNhd ℂ (suzukiArithmeticScrewQuotient t)
      suzukiXiSafeUpperHalfPlane := by
  apply (show DifferentiableOn ℂ (suzukiArithmeticScrewQuotient t)
      suzukiXiSafeUpperHalfPlane by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold suzukiArithmeticScrewQuotient
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero Complex.I_ne_zero
        (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)).analyticOnNhd
  exact isOpen_suzukiXiSafeUpperHalfPlane

/-- The zeta logarithmic-derivative contribution in Suzuki's formula. -/
def suzukiArithmeticZetaContribution (t : ℝ) (z : ℂ) : ℂ :=
  suzukiArithmeticScrewQuotient t z *
    logDeriv riemannZeta (suzukiArithmeticZetaArgument z)

/-- The zeta contribution is holomorphic on the safe half-plane. -/
theorem analyticOnNhd_suzukiArithmeticZetaContribution (t : ℝ) :
    AnalyticOnNhd ℂ (suzukiArithmeticZetaContribution t)
      suzukiXiSafeUpperHalfPlane := by
  exact (analyticOnNhd_suzukiArithmeticScrewQuotient t).mul
    analyticOnNhd_suzukiArithmeticZetaLogDerivative

/-- One von Mangoldt term in the finite arithmetic prime window. -/
def suzukiArithmeticPrimeTerm (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    ((Complex.exp
        (-Complex.I * z * ((t - Real.log n : ℝ) : ℂ)) - 1) /
      (Complex.I * z))

/-- Every fixed prime term is holomorphic on the safe half-plane. -/
theorem analyticOnNhd_suzukiArithmeticPrimeTerm
    (t : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (suzukiArithmeticPrimeTerm t n)
      suzukiXiSafeUpperHalfPlane := by
  apply (show DifferentiableOn ℂ (suzukiArithmeticPrimeTerm t n)
      suzukiXiSafeUpperHalfPlane by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold suzukiArithmeticPrimeTerm
    apply DifferentiableAt.mul
    · fun_prop
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact mul_ne_zero Complex.I_ne_zero
          (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)).analyticOnNhd
  exact isOpen_suzukiXiSafeUpperHalfPlane

/-- The exact finite index window `1 <= n <= exp(t)` in Suzuki's prime sum. -/
def suzukiArithmeticPrimeWindow (t : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊Real.exp t⌋₊

/-- Membership in the finite Lean window is exactly Suzuki's real cutoff. -/
theorem mem_suzukiArithmeticPrimeWindow_iff
    {t : ℝ} {n : ℕ} :
    n ∈ suzukiArithmeticPrimeWindow t ↔
      1 ≤ n ∧ (n : ℝ) ≤ Real.exp t := by
  simp only [suzukiArithmeticPrimeWindow, Finset.mem_Icc]
  rw [Nat.le_floor_iff (Real.exp_nonneg t)]

/-- The complete finite von Mangoldt contribution. -/
def suzukiArithmeticPrimeContribution (t : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ suzukiArithmeticPrimeWindow t,
    suzukiArithmeticPrimeTerm t n z

/-- The finite von Mangoldt contribution is holomorphic on the safe
half-plane. -/
theorem analyticOnNhd_suzukiArithmeticPrimeContribution (t : ℝ) :
    AnalyticOnNhd ℂ (suzukiArithmeticPrimeContribution t)
      suzukiXiSafeUpperHalfPlane := by
  apply (show DifferentiableOn ℂ (suzukiArithmeticPrimeContribution t)
      suzukiXiSafeUpperHalfPlane by
    unfold suzukiArithmeticPrimeContribution
    exact DifferentiableOn.fun_sum fun n _hn ↦
      (analyticOnNhd_suzukiArithmeticPrimeTerm t n).differentiableOn).analyticOnNhd
  exact isOpen_suzukiXiSafeUpperHalfPlane

/-- The digamma difference contribution in Suzuki's formula. -/
def suzukiArithmeticDigammaContribution (z : ℂ) : ℂ :=
  -(Complex.digamma (suzukiHurwitzLerchParameter z) -
      Complex.digamma (1 / 4)) /
    (2 * Complex.I * z)

/-- The moving gamma/Lerch parameter stays in the positive-real-part
half-plane. -/
theorem mapsTo_suzukiHurwitzLerchParameter_re_pos :
    MapsTo suzukiHurwitzLerchParameter suzukiXiSafeUpperHalfPlane
      {a : ℂ | 0 < a.re} := by
  intro z hz
  have h := mapsTo_suzukiHurwitzLerchParameter hz
  change (0 : ℝ) < (suzukiHurwitzLerchParameter z).re
  change (1 / 8 : ℝ) < (suzukiHurwitzLerchParameter z).re at h
  linarith

/-- The composed digamma term is holomorphic on the safe spectral
half-plane. -/
theorem analyticOnNhd_suzukiArithmeticDigammaComposed :
    AnalyticOnNhd ℂ
      (fun z ↦ Complex.digamma (suzukiHurwitzLerchParameter z))
      suzukiXiSafeUpperHalfPlane := by
  have hparam : AnalyticOnNhd ℂ suzukiHurwitzLerchParameter
      suzukiXiSafeUpperHalfPlane := by
    apply (show DifferentiableOn ℂ suzukiHurwitzLerchParameter
        suzukiXiSafeUpperHalfPlane by
      intro z _hz
      apply DifferentiableAt.differentiableWithinAt
      unfold suzukiHurwitzLerchParameter
      fun_prop).analyticOnNhd
    exact isOpen_suzukiXiSafeUpperHalfPlane
  exact analyticOnNhd_digamma_re_pos.comp hparam
    mapsTo_suzukiHurwitzLerchParameter_re_pos

/-- The complete digamma contribution is holomorphic on the safe
half-plane. -/
theorem analyticOnNhd_suzukiArithmeticDigammaContribution :
    AnalyticOnNhd ℂ suzukiArithmeticDigammaContribution
      suzukiXiSafeUpperHalfPlane := by
  have hnum : AnalyticOnNhd ℂ
      (fun z ↦ -(Complex.digamma (suzukiHurwitzLerchParameter z) -
        Complex.digamma (1 / 4))) suzukiXiSafeUpperHalfPlane :=
    (analyticOnNhd_suzukiArithmeticDigammaComposed.sub
      analyticOnNhd_const).neg
  have hden : AnalyticOnNhd ℂ (fun z : ℂ ↦ 2 * Complex.I * z)
      suzukiXiSafeUpperHalfPlane :=
    (analyticOnNhd_const.mul analyticOnNhd_const).mul analyticOnNhd_id
  unfold suzukiArithmeticDigammaContribution
  exact hnum.div hden fun z hz ↦
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)

/-- The Hurwitz--Lerch contribution in Suzuki's arithmetic formula. -/
def suzukiArithmeticLerchContribution (t : ℝ) (z : ℂ) : ℂ :=
  -((Real.exp (-t / 2) : ℝ) : ℂ) *
    suzukiArithmeticLerchDifference t z /
      (2 * Complex.I * z)

/-- For positive time, the complete Hurwitz--Lerch contribution is
holomorphic on the safe half-plane. -/
theorem analyticOnNhd_suzukiArithmeticLerchContribution
    {t : ℝ} (ht : 0 < t) :
    AnalyticOnNhd ℂ (suzukiArithmeticLerchContribution t)
      suzukiXiSafeUpperHalfPlane := by
  have hnum : AnalyticOnNhd ℂ
      (fun z ↦ -((Real.exp (-t / 2) : ℝ) : ℂ) *
        suzukiArithmeticLerchDifference t z)
      suzukiXiSafeUpperHalfPlane :=
    analyticOnNhd_const.mul
      (analyticOnNhd_suzukiArithmeticLerchDifference ht)
  have hden : AnalyticOnNhd ℂ (fun z : ℂ ↦ 2 * Complex.I * z)
      suzukiXiSafeUpperHalfPlane :=
    (analyticOnNhd_const.mul analyticOnNhd_const).mul analyticOnNhd_id
  unfold suzukiArithmeticLerchContribution
  exact hnum.div hden fun z hz ↦
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)

/-- Suzuki's complete arithmetic expression (1.6).  The definition is total,
but its direct Lerch-series interpretation and the holomorphy theorem below
require positive time. -/
def riemannXiSuzukiArithmeticPPositive (t : ℝ) (z : ℂ) : ℂ :=
  suzukiArithmeticPoleContribution t z +
    suzukiArithmeticZetaContribution t z +
      suzukiArithmeticPrimeContribution t z +
        suzukiArithmeticDigammaContribution z +
          suzukiArithmeticLerchContribution t z

/-- For every positive screw time, Suzuki's entire arithmetic expression is
holomorphic above the spectral-xi zero strip. -/
theorem analyticOnNhd_riemannXiSuzukiArithmeticPPositive
    {t : ℝ} (ht : 0 < t) :
    AnalyticOnNhd ℂ (riemannXiSuzukiArithmeticPPositive t)
      suzukiXiSafeUpperHalfPlane := by
  exact (((analyticOnNhd_suzukiArithmeticPoleContribution t).add
    (analyticOnNhd_suzukiArithmeticZetaContribution t)).add
      (analyticOnNhd_suzukiArithmeticPrimeContribution t)).add
        analyticOnNhd_suzukiArithmeticDigammaContribution |>.add
          (analyticOnNhd_suzukiArithmeticLerchContribution ht)

end

end RiemannGaussian
