import RiemannGaussian.RiemannXiSuzukiWeilArithmetic
import RiemannGaussian.GaussianDigammaGauss

/-!
# The Archimedean term in Suzuki's specialized Weil formula

This file evaluates the last local term on the right-hand side of Suzuki's
specialized Weil explicit formula.  The calculation is organized through the
geometric expansion of the Archimedean kernel into lower-half-plane spectral
modes.  Gauss's complex digamma series, already proved in Lean from Euler's
Gamma approximants, supplies the undamped part; the absolutely convergent
Hurwitz--Lerch series supplies the positive-time tail.

No global Weil distribution identity is assumed in this file.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval LSeries.notation Topology lp

namespace RiemannGaussian

noncomputable section

/-- One term of the convergent complex series for a digamma difference. -/
def suzukiWeilDigammaDifferenceSummand
    (a b : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + b)⁻¹ - ((n : ℂ) + a)⁻¹

/-- The complex digamma-difference series is absolutely summable throughout
the product of two right half-planes. -/
theorem summable_norm_suzukiWeilDigammaDifferenceSummand
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun n ↦ ‖suzukiWeilDigammaDifferenceSummand a b n‖) := by
  let c : ℝ := min 1 (min a.re b.re)
  have hc : 0 < c := by
    exact lt_min one_pos (lt_min ha hb)
  have hcOne : c ≤ 1 := min_le_left _ _
  have hcA : c ≤ a.re :=
    (min_le_right (1 : ℝ) (min a.re b.re)).trans (min_le_left _ _)
  have hcB : c ≤ b.re :=
    (min_le_right (1 : ℝ) (min a.re b.re)).trans (min_le_right _ _)
  have hdenA (n : ℕ) :
      c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + a‖ := by
    calc
      c * ((n : ℝ) + 1) = c * n + c := by ring
      _ ≤ (n : ℝ) + a.re := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hcn : c * (n : ℝ) ≤ 1 * n :=
          mul_le_mul_of_nonneg_right hcOne hn
        linarith
      _ = ((n : ℂ) + a).re := by simp
      _ ≤ ‖(n : ℂ) + a‖ := Complex.re_le_norm _
  have hdenB (n : ℕ) :
      c * ((n : ℝ) + 1) ≤ ‖(n : ℂ) + b‖ := by
    calc
      c * ((n : ℝ) + 1) = c * n + c := by ring
      _ ≤ (n : ℝ) + b.re := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hcn : c * (n : ℝ) ≤ 1 * n :=
          mul_le_mul_of_nonneg_right hcOne hn
        linarith
      _ = ((n : ℂ) + b).re := by simp
      _ ≤ ‖(n : ℂ) + b‖ := Complex.re_le_norm _
  have hbase : Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have hp : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hp
  apply (hbase.mul_left (‖a - b‖ / c ^ 2)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro n
  have hnPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcNPos : 0 < c * ((n : ℝ) + 1) := mul_pos hc hnPos
  have hA0 : (n : ℂ) + a ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt (hcNPos.trans_le (hdenA n)))
  have hB0 : (n : ℂ) + b ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt (hcNPos.trans_le (hdenB n)))
  have hterm :
      suzukiWeilDigammaDifferenceSummand a b n =
        (a - b) / (((n : ℂ) + b) * ((n : ℂ) + a)) := by
    unfold suzukiWeilDigammaDifferenceSummand
    field_simp [hA0, hB0]
    ring
  have hprod :
      (c * ((n : ℝ) + 1)) ^ 2 ≤
        ‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖ := by
    calc
      (c * ((n : ℝ) + 1)) ^ 2 =
          (c * ((n : ℝ) + 1)) *
            (c * ((n : ℝ) + 1)) := by ring
      _ ≤ ‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖ :=
        mul_le_mul (hdenB n) (hdenA n) hcNPos.le (norm_nonneg _)
  rw [hterm, norm_div, norm_mul]
  calc
    ‖a - b‖ / (‖(n : ℂ) + b‖ * ‖(n : ℂ) + a‖) ≤
        ‖a - b‖ / (c * ((n : ℝ) + 1)) ^ 2 := by
      exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hcNPos)
        hprod
    _ = (‖a - b‖ / c ^ 2) *
        (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hc]

/-- Gauss's Euler series gives the full complex digamma difference on the
right half-plane. -/
theorem hasSum_suzukiWeilDigammaDifferenceSummand
    {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    HasSum (suzukiWeilDigammaDifferenceSummand a b)
      (Complex.digamma a - Complex.digamma b) := by
  have hdiff := (Complex.digamma_tendsto_euler ha).sub
    (Complex.digamma_tendsto_euler hb)
  have hshift : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range (n + 1),
        suzukiWeilDigammaDifferenceSummand a b j)
      atTop (nhds (Complex.digamma a - Complex.digamma b)) := by
    apply hdiff.congr'
    filter_upwards with n
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [suzukiWeilDigammaDifferenceSummand, add_comm]
  have hpartial : Tendsto
      (fun n : ℕ ↦ ∑ j ∈ Finset.range n,
        suzukiWeilDigammaDifferenceSummand a b j)
      atTop (nhds (Complex.digamma a - Complex.digamma b)) := by
    exact (tendsto_add_atTop_iff_nat 1).mp
      (by simpa [Nat.add_comm] using hshift)
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_suzukiWeilDigammaDifferenceSummand ha hb)).2 hpartial

/-! ## Archimedean spectral modes -/

/-- The positive real shift `n + 1/4` underlying the Archimedean geometric
kernel. -/
def suzukiWeilArchimedeanShift (n : ℕ) : ℂ :=
  (n : ℂ) + 1 / 4

/-- The lower-half-plane spectral frequency associated with the `n`th
Archimedean kernel mode. -/
def suzukiWeilArchimedeanFrequency (n : ℕ) : ℂ :=
  -2 * Complex.I * suzukiWeilArchimedeanShift n

/-- One transformed Archimedean mode. -/
def suzukiWeilArchimedeanModeTerm
    (t : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  suzukiSpectralScrewCoefficient t
      (suzukiWeilArchimedeanFrequency n) /
    (z - suzukiWeilArchimedeanFrequency n)

@[simp] theorem suzukiWeilArchimedeanShift_re (n : ℕ) :
    (suzukiWeilArchimedeanShift n).re = (n : ℝ) + 1 / 4 := by
  simp [suzukiWeilArchimedeanShift]

@[simp] theorem suzukiWeilArchimedeanShift_im (n : ℕ) :
    (suzukiWeilArchimedeanShift n).im = 0 := by
  simp [suzukiWeilArchimedeanShift]

@[simp] theorem suzukiWeilArchimedeanFrequency_im (n : ℕ) :
    (suzukiWeilArchimedeanFrequency n).im =
      -2 * ((n : ℝ) + 1 / 4) := by
  simp [suzukiWeilArchimedeanFrequency]

theorem suzukiWeilArchimedeanShift_ne_zero (n : ℕ) :
    suzukiWeilArchimedeanShift n ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem suzukiWeilArchimedeanFrequency_ne_zero (n : ℕ) :
    suzukiWeilArchimedeanFrequency n ≠ 0 := by
  unfold suzukiWeilArchimedeanFrequency
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (suzukiWeilArchimedeanShift_ne_zero n)

/-- Every Archimedean mode lies strictly below every safe evaluation point. -/
theorem suzukiWeilArchimedeanFrequency_im_lt
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    (suzukiWeilArchimedeanFrequency n).im < z.im := by
  rw [suzukiWeilArchimedeanFrequency_im]
  change (1 / 2 : ℝ) < z.im at hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The time exponential of an Archimedean mode is its geometric Lerch
factor. -/
theorem exp_neg_I_mul_suzukiWeilArchimedeanFrequency
    (t : ℝ) (n : ℕ) :
    Complex.exp
        (-Complex.I * suzukiWeilArchimedeanFrequency n * (t : ℂ)) =
      (Real.exp (-t / 2) : ℂ) *
        (Real.exp (-2 * t) : ℂ) ^ n := by
  have hexponent :
      -Complex.I * suzukiWeilArchimedeanFrequency n * (t : ℂ) =
        ((-t / 2 : ℝ) : ℂ) +
          (n : ℂ) * ((-2 * t : ℝ) : ℂ) := by
    unfold suzukiWeilArchimedeanFrequency suzukiWeilArchimedeanShift
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexponent, Complex.exp_add, Complex.ofReal_exp,
    Complex.exp_nat_mul, Complex.ofReal_exp]

/-- The integral of one Archimedean kernel mode is the corresponding Suzuki
coefficient divided by its Cauchy gap. -/
theorem integral_suzukiWeilArchimedeanMode
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z
      (suzukiWeilArchimedeanFrequency n) x) =
      suzukiWeilArchimedeanModeTerm t z n := by
  exact integral_suzukiWeilFourierIntegrand ht
    (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)
    (suzukiWeilArchimedeanFrequency_im_lt hz n)

/-- Pointwise partial fractions split one transformed mode into its damped
Hurwitz--Lerch difference and undamped digamma-difference summand. -/
theorem suzukiWeilArchimedeanModeTerm_eq
    (t : ℝ) {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    suzukiWeilArchimedeanModeTerm t z n =
      (((Real.exp (-t / 2) : ℝ) : ℂ) *
          (suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
              (suzukiHurwitzLerchParameter z) n -
            suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
              (1 / 4) n) +
        suzukiWeilDigammaDifferenceSummand
          (suzukiHurwitzLerchParameter z) (1 / 4) n) /
        (2 * Complex.I * z) := by
  have hz0 := ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz
  have hiz : 2 * Complex.I * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hz0
  have hpRe : 0 < (suzukiHurwitzLerchParameter z).re := by
    have hp := mapsTo_suzukiHurwitzLerchParameter_re_pos hz
    exact hp
  have hnp :
      (n : ℂ) + suzukiHurwitzLerchParameter z ≠ 0 := by
    rw [add_comm]
    exact Complex.add_natCast_ne_zero_of_re_pos hpRe n
  have hnq : (n : ℂ) + 1 / 4 ≠ 0 := by
    rw [add_comm]
    exact Complex.add_natCast_ne_zero_of_re_pos (by norm_num) n
  have hnq' : 1 + (n : ℂ) * 4 ≠ 0 := by
    convert mul_ne_zero hnq (by norm_num : (4 : ℂ) ≠ 0) using 1
    ring
  have hgap : z - suzukiWeilArchimedeanFrequency n ≠ 0 := by
    intro h
    have hlt := suzukiWeilArchimedeanFrequency_im_lt hz n
    exact (ne_of_lt hlt)
      (congrArg Complex.im (sub_eq_zero.mp h)).symm
  have hfrequency :
      suzukiWeilArchimedeanFrequency n =
        -2 * Complex.I * ((n : ℂ) + 1 / 4) := by
    rfl
  have hgapEq :
      z - suzukiWeilArchimedeanFrequency n =
        2 * Complex.I *
          ((n : ℂ) + suzukiHurwitzLerchParameter z) := by
    unfold suzukiWeilArchimedeanFrequency suzukiWeilArchimedeanShift
      suzukiHurwitzLerchParameter
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold suzukiWeilArchimedeanModeTerm
  rw [suzukiSpectralScrewCoefficient_of_ne_zero t
    (suzukiWeilArchimedeanFrequency_ne_zero n)]
  unfold spectralScrewExponential
  rw [exp_neg_I_mul_suzukiWeilArchimedeanFrequency]
  rw [hgapEq, hfrequency]
  unfold suzukiHurwitzLerchOneSummand
    suzukiWeilDigammaDifferenceSummand
  field_simp [hiz, hnp, hnq, hgap, Complex.I_ne_zero]
  unfold suzukiHurwitzLerchParameter
  ring_nf
  rw [Complex.I_sq]
  push_cast
  field_simp [hnq']
  ring

/-- The complete series of transformed Archimedean modes sums to the exact
damped Lerch difference plus the undamped complex digamma difference. -/
theorem hasSum_suzukiWeilArchimedeanModeTerm
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    HasSum (suzukiWeilArchimedeanModeTerm t z)
      ((((Real.exp (-t / 2) : ℝ) : ℂ) *
          suzukiArithmeticLerchDifference t z +
        (Complex.digamma (suzukiHurwitzLerchParameter z) -
          Complex.digamma (1 / 4))) /
        (2 * Complex.I * z)) := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpCommon := mapsTo_suzukiHurwitzLerchParameter hz
  have hfixedCommon :
      (1 / 4 : ℂ) ∈ suzukiHurwitzLerchCommonDomain := by
    norm_num [suzukiHurwitzLerchCommonDomain]
  have hmoving :=
    (summable_suzukiHurwitzLerchOneSummand
      (Real.exp (-2 * t)) hq0 hq1 hpCommon).hasSum
  have hfixed :=
    (summable_suzukiHurwitzLerchOneSummand
      (Real.exp (-2 * t)) hq0 hq1 hfixedCommon).hasSum
  have hlerch : HasSum
      (fun n : ℕ ↦
        suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
            (suzukiHurwitzLerchParameter z) n -
          suzukiHurwitzLerchOneSummand (Real.exp (-2 * t))
            (1 / 4) n)
      (suzukiArithmeticLerchDifference t z) := by
    simpa [suzukiArithmeticLerchDifference,
      suzukiArithmeticLerchTail, suzukiHurwitzLerchOne] using
      hmoving.sub hfixed
  have hpRe : 0 < (suzukiHurwitzLerchParameter z).re :=
    mapsTo_suzukiHurwitzLerchParameter_re_pos hz
  have hdigamma := hasSum_suzukiWeilDigammaDifferenceSummand
    hpRe (by norm_num : (0 : ℝ) < (1 / 4 : ℂ).re)
  have hcombined :=
    (hlerch.mul_left (((Real.exp (-t / 2) : ℝ) : ℂ))).add hdigamma
  have hdiv := hcombined.div_const (2 * Complex.I * z)
  exact HasSum.congr_fun hdiv fun n ↦
    suzukiWeilArchimedeanModeTerm_eq t hz n

/-- The summed Archimedean modes have exactly the opposite sign from the
digamma and Lerch terms in Suzuki's arithmetic `P_t`, as required by the
minus sign in Weil's formula. -/
theorem tsum_suzukiWeilArchimedeanModeTerm_eq_arithmetic
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∑' n : ℕ, suzukiWeilArchimedeanModeTerm t z n) =
      -(suzukiArithmeticDigammaContribution z +
        suzukiArithmeticLerchContribution t z) := by
  rw [(hasSum_suzukiWeilArchimedeanModeTerm ht hz).tsum_eq]
  unfold suzukiArithmeticDigammaContribution
    suzukiArithmeticLerchContribution
  ring

/-! ## The geometric Archimedean kernel -/

/-- The positive-half-line kernel in the Archimedean term of Weil's explicit
formula, written in its geometric-series normalization. -/
def suzukiWeilArchimedeanKernel (x : ℝ) : ℝ :=
  Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

/-- Suzuki's test multiplied by the Archimedean kernel.  Its integral is
taken with respect to `volume.restrict (Ioi 0)`, so the totalized value at the
removable endpoint does not enter. -/
def suzukiWeilArchimedeanIntegrand
    (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  suzukiWeilTest t z x * (suzukiWeilArchimedeanKernel x : ℂ)

/-- The exact nonnegative norm of one Archimedean geometric mode. -/
def suzukiWeilArchimedeanModeBound
    (t : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) : ℝ :=
  ‖suzukiWeilTest t z x‖ * Real.exp (-x / 2) *
    Real.exp (-2 * x) ^ n

/-- The explicit geometric majorant is not merely a bound: it is exactly
the norm of the corresponding Archimedean Fourier mode. -/
theorem norm_suzukiWeilFourierIntegrand_archimedeanFrequency
    (t : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    ‖suzukiWeilFourierIntegrand t z
        (suzukiWeilArchimedeanFrequency n) x‖ =
      suzukiWeilArchimedeanModeBound t z n x := by
  unfold suzukiWeilFourierIntegrand suzukiWeilArchimedeanModeBound
  rw [norm_mul,
    exp_neg_I_mul_suzukiWeilArchimedeanFrequency,
    norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  ring_nf

/-- Suzuki's piecewise test is measurable on the real line. -/
theorem measurable_suzukiWeilTest (t : ℝ) (z : ℂ) :
    Measurable (suzukiWeilTest t z) := by
  unfold suzukiWeilTest
  apply Measurable.ite measurableSet_Iio
  · fun_prop
  · apply Measurable.ite measurableSet_Iic <;> fun_prop

/-- The totalized real Archimedean kernel is measurable. -/
theorem measurable_suzukiWeilArchimedeanKernel :
    Measurable suzukiWeilArchimedeanKernel := by
  unfold suzukiWeilArchimedeanKernel
  fun_prop

/-- The product defining the Archimedean integrand is strongly measurable. -/
theorem stronglyMeasurable_suzukiWeilArchimedeanIntegrand
    (t : ℝ) (z : ℂ) :
    StronglyMeasurable (suzukiWeilArchimedeanIntegrand t z) := by
  unfold suzukiWeilArchimedeanIntegrand
  exact (measurable_suzukiWeilTest t z).stronglyMeasurable.mul
    (Complex.continuous_ofReal.measurable.comp
      measurable_suzukiWeilArchimedeanKernel).stronglyMeasurable

/-- On the compact middle branch, cancellation at zero makes Suzuki's test
at most linear in the spatial variable. -/
theorem norm_suzukiWeilTest_middle_le
    {t x : ℝ} (hx0 : 0 ≤ x) (hxt : x ≤ t)
    {z : ℂ} (hz : z ≠ 0) :
    ‖suzukiWeilTest t z x‖ ≤
      x * Real.exp (‖z‖ * t) := by
  rw [suzukiWeilTest_of_nonneg_of_le z hx0 hxt, norm_div]
  let w : ℂ := Complex.I * z * (x : ℂ)
  have hExp : ‖Complex.exp w - 1‖ ≤
      ‖w‖ * Real.exp ‖w‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
  have hnum : ‖1 - Complex.exp w‖ ≤
      ‖w‖ * Real.exp ‖w‖ := by
    rw [show 1 - Complex.exp w = -(Complex.exp w - 1) by ring_nf,
      norm_neg]
    exact hExp
  have hw : ‖w‖ = ‖z‖ * x := by
    unfold w
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hden : ‖Complex.I * z‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hden, show 1 - Complex.exp (Complex.I * z * (x : ℂ)) =
      1 - Complex.exp w by rfl]
  calc
    ‖1 - Complex.exp w‖ / ‖z‖ ≤
        (‖w‖ * Real.exp ‖w‖) / ‖z‖ := by
      exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = x * Real.exp ‖w‖ := by
      rw [hw]
      field_simp [norm_ne_zero_iff.mpr hz]
    _ ≤ x * Real.exp (‖z‖ * t) := by
      apply mul_le_mul_of_nonneg_left _ hx0
      exact Real.exp_le_exp.mpr
        (by rw [hw]; exact mul_le_mul_of_nonneg_left hxt (norm_nonneg z))

/-- Multiplication by `x` removes the Archimedean kernel's endpoint pole,
uniformly on every positive compact interval. -/
theorem mul_suzukiWeilArchimedeanKernel_le
    {t x : ℝ} (hx : 0 < x) (hxt : x ≤ t) :
    x * suzukiWeilArchimedeanKernel x ≤
      Real.exp (3 * t / 2) / 2 := by
  have hdPos : 0 < 1 - Real.exp (-2 * x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden :
      2 * x * Real.exp (-2 * x) ≤
        1 - Real.exp (-2 * x) := by
    have hExp := Real.add_one_le_exp (2 * x)
    have hmul := mul_le_mul_of_nonneg_right hExp
      (Real.exp_pos (-2 * x)).le
    have hcancel :
        Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [hcancel] at hmul
    nlinarith [Real.exp_pos (-2 * x)]
  have hexp :
      Real.exp (-x / 2) ≤ Real.exp (3 * t / 2 - 2 * x) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have heq :
      (Real.exp (3 * t / 2) / 2) *
          (2 * x * Real.exp (-2 * x)) =
        x * Real.exp (3 * t / 2 - 2 * x) := by
    rw [show Real.exp (3 * t / 2 - 2 * x) =
        Real.exp (3 * t / 2) * Real.exp (-2 * x) by
      rw [← Real.exp_add]
      ring_nf]
    ring_nf
  unfold suzukiWeilArchimedeanKernel
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hdPos).2
  calc
    x * Real.exp (-x / 2) ≤
        x * Real.exp (3 * t / 2 - 2 * x) :=
      mul_le_mul_of_nonneg_left hexp hx.le
    _ = (Real.exp (3 * t / 2) / 2) *
        (2 * x * Real.exp (-2 * x)) := heq.symm
    _ ≤ (Real.exp (3 * t / 2) / 2) *
        (1 - Real.exp (-2 * x)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)

/-- The Archimedean kernel is strictly positive away from its endpoint. -/
theorem suzukiWeilArchimedeanKernel_pos
    {x : ℝ} (hx : 0 < x) :
    0 < suzukiWeilArchimedeanKernel x := by
  unfold suzukiWeilArchimedeanKernel
  apply div_pos (Real.exp_pos _)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

/-- At every positive point, the geometric mode norms sum exactly to the
norm of the complete Archimedean integrand. -/
theorem hasSum_suzukiWeilArchimedeanModeBound
    (t : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ suzukiWeilArchimedeanModeBound t z n x)
      ‖suzukiWeilArchimedeanIntegrand t z x‖ := by
  have hq : ‖Real.exp (-2 * x)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := hasSum_geometric_of_norm_lt_one hq
  have hmul := hgeo.mul_left
    (‖suzukiWeilTest t z x‖ * Real.exp (-x / 2))
  have hkPos := suzukiWeilArchimedeanKernel_pos hx
  have hlimit :
      ‖suzukiWeilArchimedeanIntegrand t z x‖ =
        (‖suzukiWeilTest t z x‖ * Real.exp (-x / 2)) *
          (1 - Real.exp (-2 * x))⁻¹ := by
    rw [suzukiWeilArchimedeanIntegrand, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hkPos]
    unfold suzukiWeilArchimedeanKernel
    rw [div_eq_mul_inv]
    ring_nf
  rw [hlimit]
  simpa [suzukiWeilArchimedeanModeBound] using hmul

/-- The complete Archimedean integrand is uniformly bounded on its compact
middle branch, including arbitrarily close to zero. -/
theorem norm_suzukiWeilArchimedeanIntegrand_middle_le
    {t : ℝ} {z : ℂ} (hz : z ≠ 0)
    {x : ℝ} (hx : x ∈ Ioc 0 t) :
    ‖suzukiWeilArchimedeanIntegrand t z x‖ ≤
      Real.exp (‖z‖ * t) * (Real.exp (3 * t / 2) / 2) := by
  have hkPos := suzukiWeilArchimedeanKernel_pos hx.1
  rw [suzukiWeilArchimedeanIntegrand, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hkPos]
  calc
    ‖suzukiWeilTest t z x‖ * suzukiWeilArchimedeanKernel x ≤
        (x * Real.exp (‖z‖ * t)) *
          suzukiWeilArchimedeanKernel x :=
      mul_le_mul_of_nonneg_right
        (norm_suzukiWeilTest_middle_le hx.1.le hx.2 hz) hkPos.le
    _ = Real.exp (‖z‖ * t) *
        (x * suzukiWeilArchimedeanKernel x) := by ring_nf
    _ ≤ Real.exp (‖z‖ * t) *
        (Real.exp (3 * t / 2) / 2) :=
      mul_le_mul_of_nonneg_left
        (mul_suzukiWeilArchimedeanKernel_le hx.1 hx.2)
        (Real.exp_pos _).le

/-- The endpoint cancellation makes the complete Archimedean integrand
integrable on every compact positive middle branch. -/
theorem integrableOn_suzukiWeilArchimedeanIntegrand_middle
    {t : ℝ} {z : ℂ} (hz : z ≠ 0) :
    IntegrableOn (suzukiWeilArchimedeanIntegrand t z) (Ioc 0 t) := by
  let C : ℝ :=
    Real.exp (‖z‖ * t) * (Real.exp (3 * t / 2) / 2)
  have hC : Integrable (fun _ : ℝ ↦ C)
      (volume.restrict (Ioc 0 t)) := by
    exact integrableOn_const measure_Ioc_lt_top.ne
  apply hC.mono'
    (stronglyMeasurable_suzukiWeilArchimedeanIntegrand t z).aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun x hx ↦ by
    exact norm_suzukiWeilArchimedeanIntegrand_middle_le hz hx

/-- Past a positive cutoff, the geometric Archimedean kernel is dominated
by its zeroth exponential mode times a fixed geometric factor. -/
theorem suzukiWeilArchimedeanKernel_le_tail
    {t x : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    suzukiWeilArchimedeanKernel x ≤
      (1 / (1 - Real.exp (-2 * t))) * Real.exp (-x / 2) := by
  have hdt : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden :
      1 - Real.exp (-2 * t) ≤ 1 - Real.exp (-2 * x) := by
    exact sub_le_sub_left
      (Real.exp_le_exp.mpr (by linarith)) 1
  unfold suzukiWeilArchimedeanKernel
  calc
    Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) ≤
        Real.exp (-x / 2) / (1 - Real.exp (-2 * t)) := by
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdt hden
    _ = (1 / (1 - Real.exp (-2 * t))) *
        Real.exp (-x / 2) := by ring_nf

/-- The complete Archimedean integrand on the infinite tail is dominated
by an integrable zeroth Fourier mode. -/
theorem norm_suzukiWeilArchimedeanIntegrand_tail_le
    {t : ℝ} (ht : 0 < t) {z : ℂ} {x : ℝ} (htx : t ≤ x) :
    ‖suzukiWeilArchimedeanIntegrand t z x‖ ≤
      (1 / (1 - Real.exp (-2 * t))) *
        ‖suzukiWeilFourierIntegrand t z
          (suzukiWeilArchimedeanFrequency 0) x‖ := by
  have hx : 0 < x := ht.trans_le htx
  have hkPos := suzukiWeilArchimedeanKernel_pos hx
  have hmode :
      Complex.exp
          (-Complex.I * suzukiWeilArchimedeanFrequency 0 * (x : ℂ)) =
        (Real.exp (-x / 2) : ℂ) := by
    simpa using
      exp_neg_I_mul_suzukiWeilArchimedeanFrequency x 0
  rw [suzukiWeilArchimedeanIntegrand, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hkPos]
  calc
    ‖suzukiWeilTest t z x‖ * suzukiWeilArchimedeanKernel x ≤
        ‖suzukiWeilTest t z x‖ *
          ((1 / (1 - Real.exp (-2 * t))) * Real.exp (-x / 2)) :=
      mul_le_mul_of_nonneg_left
        (suzukiWeilArchimedeanKernel_le_tail ht htx) (norm_nonneg _)
    _ = (1 / (1 - Real.exp (-2 * t))) *
        (‖suzukiWeilTest t z x‖ * Real.exp (-x / 2)) := by ring_nf
    _ = (1 / (1 - Real.exp (-2 * t))) *
        ‖suzukiWeilFourierIntegrand t z
          (suzukiWeilArchimedeanFrequency 0) x‖ := by
      congr 1
      unfold suzukiWeilFourierIntegrand
      rw [norm_mul, hmode, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The complete Archimedean integrand is integrable on the infinite tail. -/
theorem integrableOn_suzukiWeilArchimedeanIntegrand_tail
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    IntegrableOn (suzukiWeilArchimedeanIntegrand t z) (Ioi t) := by
  let C : ℝ := 1 / (1 - Real.exp (-2 * t))
  have hmode : Integrable
      (suzukiWeilFourierIntegrand t z
        (suzukiWeilArchimedeanFrequency 0)) :=
    integrable_suzukiWeilFourierIntegrand ht.le
      (suzukiWeilArchimedeanFrequency_im_lt hz 0)
  have hmajor : Integrable
      (fun x : ℝ ↦ C *
        ‖suzukiWeilFourierIntegrand t z
          (suzukiWeilArchimedeanFrequency 0) x‖)
      (volume.restrict (Ioi t)) := by
    exact (hmode.norm.const_mul C).integrableOn
  apply hmajor.mono'
    (stronglyMeasurable_suzukiWeilArchimedeanIntegrand t z).aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun x hx ↦ by
    exact norm_suzukiWeilArchimedeanIntegrand_tail_le ht hx.le

/-- Suzuki's complete Archimedean kernel term is absolutely integrable on
the whole positive half-line. -/
theorem integrableOn_suzukiWeilArchimedeanIntegrand
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    IntegrableOn (suzukiWeilArchimedeanIntegrand t z) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi ht.le]
  exact (integrableOn_suzukiWeilArchimedeanIntegrand_middle
    (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)).union
      (integrableOn_suzukiWeilArchimedeanIntegrand_tail ht hz)

/-- Restricting one Archimedean Fourier mode to the positive half-line does
not alter its integral, since Suzuki's test vanishes on the complement. -/
theorem integral_Ioi_suzukiWeilArchimedeanMode
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, suzukiWeilFourierIntegrand t z
      (suzukiWeilArchimedeanFrequency n) x) =
      suzukiWeilArchimedeanModeTerm t z n := by
  have hintegrable :=
    integrable_suzukiWeilFourierIntegrand ht.le
      (suzukiWeilArchimedeanFrequency_im_lt hz n)
  have hzero :
      (∫ x : ℝ in (Ioi (0 : ℝ))ᶜ,
        suzukiWeilFourierIntegrand t z
          (suzukiWeilArchimedeanFrequency n) x) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [compl_Ioi] at hx
    change x ≤ 0 at hx
    rcases eq_or_lt_of_le hx with hxeq | hxlt
    · subst x
      simp [suzukiWeilFourierIntegrand, suzukiWeilTest_zero ht.le]
    · exact suzukiWeilFourierIntegrand_of_neg t z
        (suzukiWeilArchimedeanFrequency n) hxlt
  have hadd := integral_add_compl
    (s := Ioi (0 : ℝ)) measurableSet_Ioi hintegrable
  rw [hzero, add_zero] at hadd
  exact hadd.trans (integral_suzukiWeilArchimedeanMode ht.le hz n)

/-- The geometric kernel is the sum of its lower-half-plane exponential
modes at every positive point. -/
theorem hasSum_suzukiWeilArchimedeanExponential
    {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ ↦ Complex.exp
        (-Complex.I * suzukiWeilArchimedeanFrequency n * (x : ℂ)))
      (suzukiWeilArchimedeanKernel x : ℂ) := by
  have hq : ‖(Real.exp (-2 * x) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := hasSum_geometric_of_norm_lt_one hq
  have hmul := hgeo.mul_left ((Real.exp (-x / 2) : ℝ) : ℂ)
  have hkernel : HasSum
      (fun n : ℕ ↦ ((Real.exp (-x / 2) : ℝ) : ℂ) *
        ((Real.exp (-2 * x) : ℝ) : ℂ) ^ n)
      (suzukiWeilArchimedeanKernel x : ℂ) := by
    simpa [suzukiWeilArchimedeanKernel, div_eq_mul_inv] using hmul
  exact HasSum.congr_fun hkernel fun n ↦
    exp_neg_I_mul_suzukiWeilArchimedeanFrequency x n

/-- After multiplication by Suzuki's test, the geometric modes sum
pointwise to the complete Archimedean integrand. -/
theorem hasSum_suzukiWeilArchimedeanIntegrand
    (t : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ ↦ suzukiWeilFourierIntegrand t z
        (suzukiWeilArchimedeanFrequency n) x)
      (suzukiWeilArchimedeanIntegrand t z x) := by
  have hmul :=
    (hasSum_suzukiWeilArchimedeanExponential hx).mul_left
      (suzukiWeilTest t z x)
  exact HasSum.congr_fun hmul fun n ↦ by
    rfl

/-- Dominated convergence exchanges the Archimedean geometric mode sum
with integration over the positive half-line. -/
theorem hasSum_integral_Ioi_suzukiWeilArchimedeanMode
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    HasSum
      (fun n : ℕ ↦ ∫ x : ℝ in Ioi 0,
        suzukiWeilFourierIntegrand t z
          (suzukiWeilArchimedeanFrequency n) x)
      (∫ x : ℝ in Ioi 0, suzukiWeilArchimedeanIntegrand t z x) := by
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (suzukiWeilArchimedeanModeBound t z)
  · intro n
    exact (integrable_suzukiWeilFourierIntegrand ht.le
      (suzukiWeilArchimedeanFrequency_im_lt hz n)).integrableOn.aestronglyMeasurable
  · intro n
    exact Eventually.of_forall fun x ↦
      (norm_suzukiWeilFourierIntegrand_archimedeanFrequency
        t z n x).le
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun x hx ↦
      (hasSum_suzukiWeilArchimedeanModeBound t z hx).summable
  · have hnorm :=
      (integrableOn_suzukiWeilArchimedeanIntegrand ht hz).norm
    apply hnorm.congr
    change ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖suzukiWeilArchimedeanIntegrand t z x‖ =
        ∑' n : ℕ, suzukiWeilArchimedeanModeBound t z n x
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun x hx ↦
      (hasSum_suzukiWeilArchimedeanModeBound t z hx).tsum_eq.symm
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun x hx ↦
      hasSum_suzukiWeilArchimedeanIntegrand t z hx

/-- The single Archimedean kernel integral equals the rigorously summed
series of transformed lower-half-plane modes. -/
theorem integral_Ioi_suzukiWeilArchimedeanIntegrand_eq_tsum
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ in Ioi 0, suzukiWeilArchimedeanIntegrand t z x) =
      ∑' n : ℕ, suzukiWeilArchimedeanModeTerm t z n := by
  have hIntegral :=
    hasSum_integral_Ioi_suzukiWeilArchimedeanMode ht hz
  have hModes : HasSum (suzukiWeilArchimedeanModeTerm t z)
      (∫ x : ℝ in Ioi 0,
        suzukiWeilArchimedeanIntegrand t z x) :=
    HasSum.congr_fun hIntegral fun n ↦
      (integral_Ioi_suzukiWeilArchimedeanMode ht hz n).symm
  exact hModes.tsum_eq.symm

/-- With Weil's minus sign, the complete Archimedean integral is exactly
Suzuki's digamma plus Hurwitz--Lerch arithmetic contribution. -/
theorem neg_integral_Ioi_suzukiWeilArchimedeanIntegrand_eq_arithmetic
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    -(∫ x : ℝ in Ioi 0, suzukiWeilArchimedeanIntegrand t z x) =
      suzukiArithmeticDigammaContribution z +
        suzukiArithmeticLerchContribution t z := by
  rw [integral_Ioi_suzukiWeilArchimedeanIntegrand_eq_tsum ht hz,
    tsum_suzukiWeilArchimedeanModeTerm_eq_arithmetic ht hz]
  ring_nf

/-- Every local term on the arithmetic side of Suzuki's specialized Weil
formula has now been evaluated from its literal integral or prime sum.  The
complete signed right-hand side is exactly the previously constructed
arithmetic function `P_t`.  No global zero-distribution identity is used. -/
theorem suzukiWeilLocalRHS_eq_riemannXiSuzukiArithmeticPPositive
    {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) -
      (∫ x : ℝ in Ioi 0, suzukiWeilArchimedeanIntegrand t z x) =
        riemannXiSuzukiArithmeticPPositive t z := by
  rw [elementary_integral_sub_primeSample_tsums_eq_arithmetic ht.le hz]
  calc
    suzukiArithmeticPoleContribution t z +
          suzukiArithmeticZetaContribution t z +
            suzukiArithmeticPrimeContribution t z -
        (∫ x : ℝ in Ioi 0,
          suzukiWeilArchimedeanIntegrand t z x) =
      suzukiArithmeticPoleContribution t z +
          suzukiArithmeticZetaContribution t z +
            suzukiArithmeticPrimeContribution t z +
        (-(∫ x : ℝ in Ioi 0,
          suzukiWeilArchimedeanIntegrand t z x)) := by ring
    _ = suzukiArithmeticPoleContribution t z +
          suzukiArithmeticZetaContribution t z +
            suzukiArithmeticPrimeContribution t z +
        (suzukiArithmeticDigammaContribution z +
          suzukiArithmeticLerchContribution t z) := by
      rw [neg_integral_Ioi_suzukiWeilArchimedeanIntegrand_eq_arithmetic
        ht hz]
    _ = riemannXiSuzukiArithmeticPPositive t z := by
      unfold riemannXiSuzukiArithmeticPPositive
      ring

end

end RiemannGaussian
