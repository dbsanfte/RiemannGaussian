import RiemannGaussian.RiemannXiSuzukiPointwiseTailNormalization
import RiemannGaussian.RiemannXiSuzukiWeilArchimedean
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The first audited Suzuki transport tail

This file fixes the transport base at the first prime event `log 2` and
freezes that event.  It proves both pieces of base data required by the
source-exact cumulative-surplus criterion:

* cutoff one is an exact event cut at `log 2`; and
* the corresponding frozen slope is strictly negative.

The slope estimate is analytic rather than floating-point.  Three explicit
positive Euler-series terms compare `digamma (1/4)` with the known value at
`1/2`; the positive Lerch slope is bounded by a geometric tail; and all
remaining constants are controlled by checked rational inequalities.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## Exact first event cell -/

/-- At the first prime location, cutoff one includes exactly the event at
`log 2` and leaves every later event in the future. -/
theorem suzukiPrimeEventCut_logTwo_one :
    ScrewEventCut suzukiPrimeLocation (Real.log 2) 1 := by
  constructor
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    rfl
  · intro k
    unfold suzukiPrimeLocation
    apply Real.log_le_log
    · norm_num
    · norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith

/-! ## Elementary constants at `log 2` -/

private theorem exp_logTwo_half_sq :
    Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_neg_logTwo_half_sq :
    Real.exp (-Real.log 2 / 2) ^ 2 = 1 / 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have hneg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show (2 : ℝ) * (-Real.log 2 / 2) = -Real.log 2 by ring,
    hneg]

private theorem exp_logTwo_half_le_ten_sevenths :
    Real.exp (Real.log 2 / 2) ≤ 10 / 7 := by
  have hpos := (Real.exp_pos (Real.log 2 / 2)).le
  have hsq := exp_logTwo_half_sq
  nlinarith

private theorem seven_tenths_le_exp_neg_logTwo_half :
    7 / 10 ≤ Real.exp (-Real.log 2 / 2) := by
  have hpos := (Real.exp_pos (-Real.log 2 / 2)).le
  have hsq := exp_neg_logTwo_half_sq
  nlinarith

private theorem exp_neg_logTwo_half_le_five_sevenths :
    Real.exp (-Real.log 2 / 2) ≤ 5 / 7 := by
  have hpos := (Real.exp_pos (-Real.log 2 / 2)).le
  have hsq := exp_neg_logTwo_half_sq
  nlinarith

private theorem logTwo_gt_693_thousandths :
    (693 / 1000 : ℝ) < Real.log 2 := by
  exact (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
    Real.log_two_gt_d9

private theorem one_lt_log_pi : (1 : ℝ) < Real.log Real.pi := by
  exact (Real.lt_log_iff_exp_lt Real.pi_pos).2
    (Real.exp_one_lt_three.trans Real.pi_gt_three)

/-! ## A finite Euler bound for the quarter-point digamma -/

/-- The first three positive Euler-difference terms give a concrete upper
bound for the quarter-point digamma in terms of its known half-point value. -/
theorem re_digamma_quarter_le_half_bound :
    (Complex.digamma (1 / 4)).re ≤
      -2 * Real.log 2 - Real.eulerMascheroniConstant - 98 / 45 := by
  let f : ℕ → ℝ := fun n =>
    (suzukiWeilDigammaDifferenceSummand (1 / 2) (1 / 4) n).re
  have hsum : HasSum f
      ((Complex.digamma (1 / 2) - Complex.digamma (1 / 4)).re) := by
    exact Complex.hasSum_re
      (hasSum_suzukiWeilDigammaDifferenceSummand
        (a := (1 / 2 : ℂ)) (b := (1 / 4 : ℂ))
        (by norm_num) (by norm_num))
  have hterm (n : ℕ) :
      f n =
        1 / ((n : ℝ) + 1 / 4) -
          1 / ((n : ℝ) + 1 / 2) := by
    unfold f suzukiWeilDigammaDifferenceSummand
    norm_num [Complex.inv_re, Complex.normSq_apply]
  have hnonnegative (n : ℕ) : 0 ≤ f n := by
    rw [hterm]
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  have hpartial : (98 / 45 : ℝ) ≤ ∑' n : ℕ, f n := by
    calc
      (98 / 45 : ℝ) = ∑ n ∈ Finset.range 3, f n := by
        simp_rw [hterm]
        norm_num
      _ ≤ ∑' n : ℕ, f n :=
        hsum.summable.sum_le_tsum (Finset.range 3)
          (fun n _hn => hnonnegative n)
  rw [hsum.tsum_eq, Complex.digamma_one_half] at hpartial
  norm_num [Complex.log_re] at hpartial
  linarith

/-! ## A geometric bound for the first Lerch slope -/

private theorem exp_neg_two_logTwo :
    Real.exp (-2 * Real.log 2) = (1 / 4 : ℝ) := by
  rw [show -2 * Real.log 2 = -Real.log 2 + -Real.log 2 by ring,
    Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem suzukiPointwiseLerchGapSlopeSummand_logTwo_eq
    (n : ℕ) :
    suzukiPointwiseLerchGapSlopeSummand (Real.log 2) n =
      2 * Real.exp (-Real.log 2 / 2) * (1 / 4 : ℝ) ^ n /
        ((n : ℝ) + 1 / 4) := by
  unfold suzukiPointwiseLerchGapSlopeSummand
  rw [suzukiPointwiseLerchMode_eq_geometric,
    exp_neg_two_logTwo]
  ring

/-- At the first prime time, the complete positive Lerch-slope series has an
explicit rational upper bound. -/
theorem suzukiPointwiseLerchGapSlope_logTwo_le :
    suzukiPointwiseLerchGapSlope (Real.log 2) ≤ 130 / 21 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsummable := summable_suzukiPointwiseLerchGapSlopeSummand hlog
  have hsplit : suzukiPointwiseLerchGapSlope (Real.log 2) =
      suzukiPointwiseLerchGapSlopeSummand (Real.log 2) 0 +
        ∑' n : ℕ,
          suzukiPointwiseLerchGapSlopeSummand (Real.log 2) (n + 1) := by
    unfold suzukiPointwiseLerchGapSlope
    simpa using (hsummable.sum_add_tsum_nat_add 1).symm
  have hzero :
      suzukiPointwiseLerchGapSlopeSummand (Real.log 2) 0 ≤ 40 / 7 := by
    rw [suzukiPointwiseLerchGapSlopeSummand_logTwo_eq]
    norm_num
    nlinarith [exp_neg_logTwo_half_le_five_sevenths]
  have htailTerm (n : ℕ) :
      suzukiPointwiseLerchGapSlopeSummand (Real.log 2) (n + 1) ≤
        (5 / 14 : ℝ) * (1 / 4 : ℝ) ^ n := by
    rw [suzukiPointwiseLerchGapSlopeSummand_logTwo_eq]
    let r : ℝ := Real.exp (-Real.log 2 / 2)
    let q : ℝ := 1 / 4
    let a : ℝ := (((n + 1 : ℕ) : ℝ) + 1 / 4)
    have hr : r ≤ 5 / 7 :=
      exp_neg_logTwo_half_le_five_sevenths
    have hq : 0 ≤ q ^ (n + 1) := by positivity
    have ha : 1 ≤ a := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      dsimp only [a]
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    have haPos : 0 < a := zero_lt_one.trans_le ha
    have hnum : 0 ≤ 2 * r * q ^ (n + 1) := by positivity
    calc
      2 * r * q ^ (n + 1) / a ≤ 2 * r * q ^ (n + 1) := by
        rw [div_le_iff₀ haPos]
        have hmul := mul_le_mul_of_nonneg_left ha hnum
        simpa using hmul
      _ ≤ 2 * (5 / 7 : ℝ) * q ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (by norm_num)) hq
      _ = (5 / 14 : ℝ) * q ^ n := by
        rw [pow_succ]
        dsimp only [q]
        ring
  have hmajor : HasSum
      (fun n : ℕ => (5 / 14 : ℝ) * (1 / 4 : ℝ) ^ n)
      (10 / 21 : ℝ) := by
    have hgeo :=
      (hasSum_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (5 / 14 : ℝ)
    have hvalue :
        (5 / 14 : ℝ) * (1 - 1 / 4)⁻¹ = 10 / 21 := by
      norm_num
    rw [hvalue] at hgeo
    exact hgeo
  have htailSummable : Summable (fun n : ℕ =>
      suzukiPointwiseLerchGapSlopeSummand (Real.log 2) (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsummable
  have htail :
      (∑' n : ℕ,
        suzukiPointwiseLerchGapSlopeSummand (Real.log 2) (n + 1)) ≤
          10 / 21 := by
    rw [← hmajor.tsum_eq]
    exact htailSummable.tsum_le_tsum htailTerm hmajor.summable
  rw [hsplit]
  linarith

/-! ## The first frozen slope -/

private theorem sqrt_two_le_ten_sevenths :
    Real.sqrt 2 ≤ 10 / 7 := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

private theorem first_suzukiPrimeWeight_lower_bound :
    (483 / 1000 : ℝ) ≤ Real.log 2 / Real.sqrt 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [le_div_iff₀ hsqrtPos]
  have hsqrt := sqrt_two_le_ten_sevenths
  have hlog := logTwo_gt_693_thousandths
  nlinarith

private theorem screwPrefixMass_suzukiPrimeWeight_one :
    screwPrefixMass suzukiPrimeWeight 1 =
      Real.log 2 / Real.sqrt 2 := by
  simp [screwPrefixMass, suzukiPrimeWeight,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- Freezing the first von Mangoldt event at `log 2` leaves a strictly
negative reset slope.  Every constant in this estimate is checked exactly;
no floating-point certificate enters the proof. -/
theorem suzukiPointwiseFrozenBaseSlope_logTwo_one_neg :
    suzukiPointwiseFrozenBaseSlope (Real.log 2) 1 < 0 := by
  have helementary :
      2 * Real.exp (Real.log 2 / 2) -
          2 * Real.exp (-Real.log 2 / 2) ≤ 51 / 35 := by
    nlinarith [exp_logTwo_half_le_ten_sevenths,
      seven_tenths_le_exp_neg_logTwo_half]
  have hdigamma :
      ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 <
        -Real.log 2 - 331 / 180 := by
    have hquarter := re_digamma_quarter_le_half_bound
    have heuler := Real.one_half_lt_eulerMascheroniConstant
    have hpi := one_lt_log_pi
    linarith
  have hlerch :
      1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) ≤
        65 / 42 := by
    nlinarith [suzukiPointwiseLerchGapSlope_logTwo_le]
  have hweight := first_suzukiPrimeWeight_lower_bound
  have hlog := logTwo_gt_693_thousandths
  unfold suzukiPointwiseFrozenBaseSlope
  rw [screwPrefixMass_suzukiPrimeWeight_one]
  unfold suzukiPointwiseArchimedeanSlope
  nlinarith

/-- Nonpositivity form of the audited first-tail slope, suitable for direct
use by the cumulative-surplus criterion. -/
theorem suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive :
    suzukiPointwiseFrozenBaseSlope (Real.log 2) 1 ≤ 0 :=
  suzukiPointwiseFrozenBaseSlope_logTwo_one_neg.le

/-! ## Assumption-free entry to the arithmetic tail frontier -/

/-- On the canonical tail beginning at the first prime event, nonnegativity
of the literal arithmetic Suzuki function is equivalent to the cumulative
transport-surplus inequalities.  Unlike the general criterion, this theorem
has no event-cut, normalization, or frozen-slope hypothesis: all three have
been discharged for `base = log 2` and `start = 1` above. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_cumulativeTransportSurplus :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ cutoff : ℕ,
        -suzukiPointwiseFrozenBaseValue (Real.log 2) 1 ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 n := by
  exact riemannXiSuzukiPsiNonnegative_on_tail_iff_cumulativeTransportSurplus
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive
    suzukiPrimeEventCut_logTwo_one

end

end RiemannGaussian
