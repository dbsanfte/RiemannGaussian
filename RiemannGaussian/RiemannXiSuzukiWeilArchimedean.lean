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

end

end RiemannGaussian
