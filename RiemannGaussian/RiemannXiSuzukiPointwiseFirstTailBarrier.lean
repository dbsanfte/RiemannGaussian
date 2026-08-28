import RiemannGaussian.RiemannXiSuzukiPointwiseFirstTailReserve
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The initial barrier of the first Suzuki transport tail

The assumption-free first-tail criterion still contains one non-arithmetic
positive cutoff.  Cutoff one transports only the synthetic mass that resets
the negative slope at `log 2`; the first future von Mangoldt atom enters at
cutoff two.

This file proves that the synthetic cell cannot consume the initial positive
reserve.  It first sharpens the exact base-value and slope estimates, then
uses quantitative lower and upper curvature bounds to control the complete
cell integral.  The resulting terminal criterion begins at cutoff two, where
every remaining prefix contains a genuine future arithmetic event.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## A reusable telescoping majorant -/

private theorem hasSum_scaled_reciprocalDifference
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    HasSum
      (fun k : ℕ => c *
        (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1)))
      (c / a) := by
  let g : ℕ → ℝ := fun k => c *
    (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1))
  have hnonnegative (k : ℕ) : 0 ≤ g k := by
    unfold g
    apply mul_nonneg hc
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonnegative (c / a)).2
  have hpartial (n : ℕ) :
      (∑ k ∈ Finset.range n, g k) =
        c * (1 / a - 1 / ((n : ℝ) + a)) := by
    change (∑ k ∈ Finset.range n, c *
      (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + a + 1))) = _
    rw [← Finset.mul_sum]
    have hrewrite :
        (fun k : ℕ =>
          (1 : ℝ) / ((k : ℝ) + a) -
            1 / ((k : ℝ) + a + 1)) =
          fun k : ℕ =>
            (1 : ℝ) / ((k : ℝ) + a) -
              1 / (((k + 1 : ℕ) : ℝ) + a) := by
      funext k
      norm_num only [Nat.cast_add, Nat.cast_one]
      congr 2
      ring_nf
    rw [hrewrite, Finset.sum_range_sub']
    norm_num
  have hdenominator : Tendsto (fun n : ℕ => (n : ℝ) + a)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop a
      tendsto_natCast_atTop_atTop
  have hinverse : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + a))
      atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hdenominator
    exact h.congr'
      (Filter.Eventually.of_forall (fun n => by simp [one_div]))
  have hlimit : Tendsto
      (fun n : ℕ => c * (1 / a - 1 / ((n : ℝ) + a)))
      atTop (nhds (c / a)) := by
    convert (tendsto_const_nhds.sub hinverse).const_mul c using 1
    congr 1
    field_simp [ha.ne']
    ring_nf
  exact hlimit.congr'
    (Filter.Eventually.of_forall (fun n => (hpartial n).symm))

/-! ## Sharpened constant bounds -/

/-- A checked upper bound for Euler's constant, obtained from the decreasing
upper sequence at index `200` and exact logarithm bounds. -/
theorem eulerMascheroniConstant_lt_29_over_50 :
    Real.eulerMascheroniConstant < 29 / 50 := by
  calc
    Real.eulerMascheroniConstant < Real.eulerMascheroniSeq' 200 :=
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 200
    _ < 29 / 50 := by
      rw [Real.eulerMascheroniSeq']
      set_option maxRecDepth 10000 in
        norm_num
      have hlog : Real.log (200 : ℝ) =
          3 * Real.log 2 + 2 * Real.log 5 := by
        rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num,
          Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow]
        norm_num
      rw [hlog]
      nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

private theorem hasSum_quarterDigammaStrongTailMajorant :
    HasSum
      (fun k : ℕ => (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 8) - 1 / ((k : ℝ) + 9)))
      (1 / 32 : ℝ) := by
  have h := hasSum_scaled_reciprocalDifference
    (a := (8 : ℝ)) (c := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have h' : HasSum
      (fun k : ℕ => (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 8) - 1 / ((k : ℝ) + 9)))
      ((1 / 4 : ℝ) / 8) := by
    apply h.congr
    intro k
    congr 3
    ring_nf
  norm_num at h' ⊢
  exact h'

/-- A sharper complete lower bound for the quarter-point digamma. -/
theorem re_digamma_quarter_gt_strong_lower_bound :
    (-2117 / 500 : ℝ) < (Complex.digamma (1 / 4)).re := by
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
  have htailTerm (k : ℕ) :
      f (k + 9) ≤ (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 8) - 1 / ((k : ℝ) + 9)) := by
    rw [hterm]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    let x : ℝ := k
    have hx : 0 ≤ x := Nat.cast_nonneg k
    have hleft :
        1 / (x + 9 + 1 / 4) - 1 / (x + 9 + 1 / 2) =
          (1 / 4 : ℝ) /
            ((x + 9 + 1 / 4) * (x + 9 + 1 / 2)) := by
      field_simp
      ring_nf
    have hright :
        (1 / 4 : ℝ) * (1 / (x + 8) - 1 / (x + 9)) =
          (1 / 4 : ℝ) / ((x + 8) * (x + 9)) := by
      field_simp
      ring_nf
    change 1 / (x + 9 + 1 / 4) - 1 / (x + 9 + 1 / 2) ≤
      (1 / 4 : ℝ) * (1 / (x + 8) - 1 / (x + 9))
    rw [hleft, hright]
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · nlinarith
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range 9, f n) +
          ∑' k : ℕ, f (k + 9) := by
    simpa using (hsum.summable.sum_add_tsum_nat_add 9).symm
  have hfinite : (∑ n ∈ Finset.range 9, f n) =
      ∑ n ∈ Finset.range 9,
        (1 / ((n : ℝ) + 1 / 4) -
          1 / ((n : ℝ) + 1 / 2)) := by
    apply Finset.sum_congr rfl
    intro n _hn
    exact hterm n
  have htailSummable : Summable (fun k : ℕ => f (k + 9)) :=
    (summable_nat_add_iff 9).mpr hsum.summable
  have htail : (∑' k : ℕ, f (k + 9)) ≤ 1 / 32 := by
    rw [← hasSum_quarterDigammaStrongTailMajorant.tsum_eq]
    exact htailSummable.tsum_le_tsum htailTerm
      hasSum_quarterDigammaStrongTailMajorant.summable
  have hdifference : (∑' n : ℕ, f n) ≤ 22671 / 10000 := by
    rw [hsplit, hfinite]
    have hfiniteBound :
        (∑ n ∈ Finset.range 9,
          (1 / ((n : ℝ) + 1 / 4) -
            1 / ((n : ℝ) + 1 / 2))) + 1 / 32 ≤
          (22671 / 10000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  rw [hsum.tsum_eq, Complex.digamma_one_half] at hdifference
  norm_num [Complex.log_re] at hdifference
  nlinarith [Real.log_two_lt_d9,
    eulerMascheroniConstant_lt_29_over_50]

private theorem log_pi_lt_229_over_200 :
    Real.log Real.pi < 229 / 200 := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 229 / 200) 8
  have hpiExp : Real.pi < Real.exp (229 / 200) := by
    calc
      Real.pi < 3.141593 := Real.pi_lt_d6
      _ < ∑ i ∈ Finset.range 8,
          (229 / 200 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (229 / 200) := hexponential
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpiExp

private theorem exp_logTwo_half_sq_barrier :
    Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 by ring_nf,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_neg_logTwo_half_sq_barrier :
    Real.exp (-Real.log 2 / 2) ^ 2 = 1 / 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have hneg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show (2 : ℝ) * (-Real.log 2 / 2) = -Real.log 2 by ring_nf,
    hneg]

private theorem exp_logTwo_half_lower_barrier :
    (707 / 500 : ℝ) ≤ Real.exp (Real.log 2 / 2) := by
  have hnonnegative := (Real.exp_pos (Real.log 2 / 2)).le
  nlinarith [exp_logTwo_half_sq_barrier]

private theorem exp_neg_logTwo_half_lower_barrier :
    (707 / 1000 : ℝ) ≤ Real.exp (-Real.log 2 / 2) := by
  have hnonnegative := (Real.exp_pos (-Real.log 2 / 2)).le
  nlinarith [exp_neg_logTwo_half_sq_barrier]

private theorem exp_neg_logTwo_half_upper_barrier :
    Real.exp (-Real.log 2 / 2) ≤ 884 / 1250 := by
  have hnonnegative := (Real.exp_pos (-Real.log 2 / 2)).le
  nlinarith [exp_neg_logTwo_half_sq_barrier]

private theorem exp_neg_two_logTwo_barrier :
    Real.exp (-2 * Real.log 2) = (1 / 4 : ℝ) := by
  rw [show -2 * Real.log 2 = -Real.log 2 + -Real.log 2 by ring_nf,
    Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-! ## A complete lower bound for the Lerch value -/

private theorem lerchGapSummand_logTwo_strong_lower_bound (n : ℕ) :
    (1 - (884 / 1250 : ℝ) * (1 / 4 : ℝ) ^ n) /
        ((n : ℝ) + 1 / 4) ^ 2 ≤
      suzukiPointwiseLerchGapSummand (Real.log 2) n := by
  rw [suzukiPointwiseLerchGapSummand_eq,
    suzukiPointwiseLerchMode_eq_geometric,
    exp_neg_two_logTwo_barrier]
  apply div_le_div_of_nonneg_right
  · have hpow : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      exp_neg_logTwo_half_upper_barrier hpow
    linarith
  · positivity

private theorem hasSum_lerchGapStrongTailFloor :
    HasSum
      (fun k : ℕ => (999 / 1000 : ℝ) *
        (1 / ((k : ℝ) + 81 / 4) -
          1 / ((k : ℝ) + 81 / 4 + 1)))
      ((999 / 1000 : ℝ) / (81 / 4)) :=
  hasSum_scaled_reciprocalDifference
    (a := (81 / 4 : ℝ)) (c := (999 / 1000 : ℝ))
    (by norm_num) (by norm_num)

private theorem lerchGapStrongTailFloor_le (k : ℕ) :
    (999 / 1000 : ℝ) *
        (1 / ((k : ℝ) + 81 / 4) -
          1 / ((k : ℝ) + 81 / 4 + 1)) ≤
      (1 - (884 / 1250 : ℝ) * (1 / 4 : ℝ) ^ (k + 20)) /
        (((k + 20 : ℕ) : ℝ) + 1 / 4) ^ 2 := by
  let x : ℝ := (k : ℝ) + 81 / 4
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hpow : (1 / 4 : ℝ) ^ (k + 20) ≤ (1 / 4 : ℝ) ^ 20 := by
    rw [pow_add]
    have hk : (1 / 4 : ℝ) ^ k ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have htwenty : 0 ≤ (1 / 4 : ℝ) ^ 20 := by positivity
    nlinarith
  have hnumerator : (999 / 1000 : ℝ) ≤
      1 - (884 / 1250 : ℝ) * (1 / 4 : ℝ) ^ (k + 20) := by
    have hscaled := mul_le_mul_of_nonneg_left hpow
      (by norm_num : (0 : ℝ) ≤ 884 / 1250)
    norm_num at hscaled
    linarith
  have hcast : (((k + 20 : ℕ) : ℝ) + 1 / 4) = x := by
    dsimp only [x]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  rw [hcast]
  have htelescoping :
      (999 / 1000 : ℝ) * (1 / x - 1 / (x + 1)) =
        (999 / 1000 : ℝ) / (x * (x + 1)) := by
    field_simp [hx.ne', (by positivity : x + 1 ≠ 0)]
    ring_nf
  rw [htelescoping]
  calc
    (999 / 1000 : ℝ) / (x * (x + 1)) ≤
        (999 / 1000 : ℝ) / x ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num)
      · positivity
      · nlinarith
    _ ≤ (1 - (884 / 1250 : ℝ) * (1 / 4 : ℝ) ^ (k + 20)) /
        x ^ 2 :=
      div_le_div_of_nonneg_right hnumerator (sq_nonneg x)

/-- The complete positive Lerch contribution at `log 2` exceeds `1.437`.
The proof uses twenty explicit terms and a proved telescoping lower bound for
the entire remaining infinite tail. -/
theorem quarter_mul_lerchGap_logTwo_gt_1437_over_1000 :
    (1437 / 1000 : ℝ) <
      1 / 4 *
        (∑' n : ℕ,
          suzukiPointwiseLerchGapSummand (Real.log 2) n) := by
  let lower : ℕ → ℝ := fun n =>
    (1 - (884 / 1250 : ℝ) * (1 / 4 : ℝ) ^ n) /
      ((n : ℝ) + 1 / 4) ^ 2
  let tailFloor : ℕ → ℝ := fun k => (999 / 1000 : ℝ) *
    (1 / ((k : ℝ) + 81 / 4) -
      1 / ((k : ℝ) + 81 / 4 + 1))
  have hnumeric : (1437 / 1000 : ℝ) <
      1 / 4 *
        ((∑ n ∈ Finset.range 20, lower n) +
          (999 / 1000 : ℝ) / (81 / 4)) := by
    dsimp only [lower]
    norm_num [Finset.sum_range_succ]
  have hfinite :
      (∑ n ∈ Finset.range 20, lower n) ≤
        ∑ n ∈ Finset.range 20,
          suzukiPointwiseLerchGapSummand (Real.log 2) n := by
    apply Finset.sum_le_sum
    intro n _hn
    exact lerchGapSummand_logTwo_strong_lower_bound n
  have hactualSummable :=
    summable_suzukiPointwiseLerchGapSummand
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hsplit :
      (∑' n : ℕ,
        suzukiPointwiseLerchGapSummand (Real.log 2) n) =
        (∑ n ∈ Finset.range 20,
          suzukiPointwiseLerchGapSummand (Real.log 2) n) +
          ∑' k : ℕ,
            suzukiPointwiseLerchGapSummand (Real.log 2) (k + 20) := by
    simpa using (hactualSummable.sum_add_tsum_nat_add 20).symm
  have htailFloorSum :
      (∑' k : ℕ, tailFloor k) =
        (999 / 1000 : ℝ) / (81 / 4) := by
    exact hasSum_lerchGapStrongTailFloor.tsum_eq
  have htail : (∑' k : ℕ, tailFloor k) ≤
      ∑' k : ℕ,
        suzukiPointwiseLerchGapSummand (Real.log 2) (k + 20) := by
    have hfloorSummable : Summable tailFloor :=
      hasSum_lerchGapStrongTailFloor.summable
    have hshiftedSummable : Summable (fun k : ℕ =>
        suzukiPointwiseLerchGapSummand (Real.log 2) (k + 20)) :=
      (summable_nat_add_iff 20).mpr hactualSummable
    apply hfloorSummable.tsum_le_tsum
    · intro k
      exact (lerchGapStrongTailFloor_le k).trans
        (lerchGapSummand_logTwo_strong_lower_bound (k + 20))
    · exact hshiftedSummable
  rw [htailFloorSum] at htail
  rw [hsplit]
  have hsumCompare :
      (∑ n ∈ Finset.range 20, lower n) +
          (999 / 1000 : ℝ) / (81 / 4) ≤
        (∑ n ∈ Finset.range 20,
          suzukiPointwiseLerchGapSummand (Real.log 2) n) +
          ∑' k : ℕ,
            suzukiPointwiseLerchGapSummand (Real.log 2) (k + 20) :=
    add_le_add hfinite htail
  exact hnumeric.trans_le
    (mul_le_mul_of_nonneg_left hsumCompare (by norm_num))

/-! ## Quantitative first-tail value and slope -/

private theorem seven_over_125_lt_suzukiPointwiseArchimedean_logTwo :
    (7 / 125 : ℝ) < suzukiPointwiseArchimedean (Real.log 2) := by
  have helementary : (121 / 250 : ℝ) ≤
      4 * (Real.exp (Real.log 2 / 2) +
        Real.exp (-Real.log 2 / 2) - 2) := by
    have hpNonnegative := (Real.exp_pos (Real.log 2 / 2)).le
    have hrNonnegative := (Real.exp_pos (-Real.log 2 / 2)).le
    have hp : (707 / 500 : ℝ) ≤ Real.exp (Real.log 2 / 2) :=
      exp_logTwo_half_lower_barrier
    have hr : (707 / 1000 : ℝ) ≤ Real.exp (-Real.log 2 / 2) :=
      exp_neg_logTwo_half_lower_barrier
    nlinarith
  have hcoefficient : (-5379 / 1000 : ℝ) <
      (Complex.digamma (1 / 4)).re - Real.log Real.pi := by
    nlinarith [re_digamma_quarter_gt_strong_lower_bound,
      log_pi_lt_229_over_200]
  have hhalfPos : 0 < Real.log 2 / 2 := by positivity
  have hhalfUpper : Real.log 2 / 2 < 173287 / 500000 := by
    nlinarith [Real.log_two_lt_d9]
  have hlinear : (-373 / 200 : ℝ) <
      Real.log 2 / 2 *
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) := by
    calc
      (-373 / 200 : ℝ) <
          (173287 / 500000 : ℝ) * (-5379 / 1000 : ℝ) := by
        norm_num
      _ < Real.log 2 / 2 * (-5379 / 1000 : ℝ) :=
        mul_lt_mul_of_neg_right hhalfUpper (by norm_num)
      _ < Real.log 2 / 2 *
          ((Complex.digamma (1 / 4)).re - Real.log Real.pi) :=
        mul_lt_mul_of_pos_left hcoefficient hhalfPos
  rw [suzukiPointwiseArchimedean_eq_series
    (Real.log_pos (by norm_num)).le]
  unfold suzukiPointwiseArchimedeanSeries
  nlinarith [quarter_mul_lerchGap_logTwo_gt_1437_over_1000]

/-- The exact frozen base reserve is in fact greater than `7 / 125`. -/
theorem seven_over_125_lt_suzukiPointwiseFrozenBaseValue_logTwo_one :
    (7 / 125 : ℝ) <
      suzukiPointwiseFrozenBaseValue (Real.log 2) 1 := by
  unfold suzukiPointwiseFrozenBaseValue frozenScrewHingeModel
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show screwAffineKick (suzukiPrimeWeight 0)
      (suzukiPrimeLocation 0) (Real.log 2) = 0 by
    simp [screwAffineKick, suzukiPrimeLocation]]
  simpa using seven_over_125_lt_suzukiPointwiseArchimedean_logTwo

private theorem quarter_mul_lerchGapSlope_logTwo_gt_371_over_250 :
    (371 / 250 : ℝ) <
      1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) := by
  have hsummable := summable_suzukiPointwiseLerchGapSlopeSummand
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hfinite : (371 / 250 : ℝ) <
      1 / 4 *
        (∑ n ∈ Finset.range 2,
          suzukiPointwiseLerchGapSlopeSummand (Real.log 2) n) := by
    have hr := exp_neg_logTwo_half_lower_barrier
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    unfold suzukiPointwiseLerchGapSlopeSummand
    rw [suzukiPointwiseLerchMode_eq_geometric,
      suzukiPointwiseLerchMode_eq_geometric,
      exp_neg_two_logTwo_barrier]
    norm_num
    nlinarith
  have htoTsum :
      (∑ n ∈ Finset.range 2,
        suzukiPointwiseLerchGapSlopeSummand (Real.log 2) n) ≤
          ∑' n : ℕ,
            suzukiPointwiseLerchGapSlopeSummand (Real.log 2) n :=
    hsummable.sum_le_tsum (Finset.range 2) (fun n _hn => by
      unfold suzukiPointwiseLerchGapSlopeSummand
      positivity)
  unfold suzukiPointwiseLerchGapSlope
  nlinarith

private theorem screwPrefixMass_suzukiPrimeWeight_one_barrier :
    screwPrefixMass suzukiPrimeWeight 1 =
      Real.log 2 / Real.sqrt 2 := by
  simp [screwPrefixMass, suzukiPrimeWeight,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

private theorem suzukiPrimeWeight_zero_lt_491_over_1000 :
    Real.log 2 / Real.sqrt 2 < 491 / 1000 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtNonnegative : 0 ≤ Real.sqrt 2 := hsqrtPos.le
  have hsqrtSquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith
  rw [div_lt_iff₀ hsqrtPos]
  nlinarith [Real.log_two_lt_d9]

/-- The first frozen slope has magnitude strictly less than `3 / 10`. -/
theorem neg_three_tenths_lt_suzukiPointwiseFrozenBaseSlope_logTwo_one :
    (-3 / 10 : ℝ) <
      suzukiPointwiseFrozenBaseSlope (Real.log 2) 1 := by
  have helementary : (353 / 250 : ℝ) ≤
      2 * Real.exp (Real.log 2 / 2) -
        2 * Real.exp (-Real.log 2 / 2) := by
    nlinarith [exp_logTwo_half_lower_barrier,
      exp_neg_logTwo_half_upper_barrier]
  have hcoefficient : (-5379 / 2000 : ℝ) <
      ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 := by
    nlinarith [re_digamma_quarter_gt_strong_lower_bound,
      log_pi_lt_229_over_200]
  unfold suzukiPointwiseFrozenBaseSlope
  rw [screwPrefixMass_suzukiPrimeWeight_one_barrier]
  unfold suzukiPointwiseArchimedeanSlope
  nlinarith [quarter_mul_lerchGapSlope_logTwo_gt_371_over_250,
    suzukiPrimeWeight_zero_lt_491_over_1000]

/-! ## Quantitative curvature bounds -/

/-- Suzuki's smooth curvature is uniformly at least `7 / 6` beyond the
canonical first-event base. -/
theorem seven_sixths_le_suzukiSmoothCurvature_of_logTwo_le
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (7 / 6 : ℝ) ≤ suzukiSmoothCurvature t := by
  have htpos : 0 < t :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  have hpositiveHalf :
      Real.exp (Real.log 2 / 2) ≤ Real.exp (t / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnegativeHalf :
      Real.exp (-t / 2) ≤ Real.exp (-Real.log 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnegativeTwo :
      Real.exp (-2 * t) ≤ (1 / 4 : ℝ) := by
    rw [← exp_neg_two_logTwo_barrier]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hdenominator :
      (3 / 4 : ℝ) ≤ 1 - Real.exp (-2 * t) := by
    linarith
  have hdenominatorPos : 0 < 1 - Real.exp (-2 * t) :=
    one_sub_exp_neg_two_mul_pos htpos
  have hnumeratorIdentity :
      Real.exp (-(5 * t) / 2) =
        Real.exp (-t / 2) * Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hnumerator :
      Real.exp (-(5 * t) / 2) ≤ (221 / 1250 : ℝ) := by
    rw [hnumeratorIdentity]
    have hproduct := mul_le_mul hnegativeHalf hnegativeTwo
      (Real.exp_pos (-2 * t)).le
      (Real.exp_pos (-Real.log 2 / 2)).le
    nlinarith [hproduct, exp_neg_logTwo_half_upper_barrier]
  have hmissing : suzukiMissingCurvature t ≤ (59 / 250 : ℝ) := by
    unfold suzukiMissingCurvature
    rw [div_le_iff₀ hdenominatorPos]
    nlinarith
  unfold suzukiSmoothCurvature
  nlinarith [exp_logTwo_half_lower_barrier,
    hpositiveHalf]

/-! ## The synthetic zero-slope cell -/

/-- The mass point that cancels the first frozen slope lies less than
`9 / 35` to the right of `log 2`. -/
theorem suzukiFirstTailResetMassPoint_sub_logTwo_lt_nine_over_35 :
    suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1 -
      Real.log 2 < (9 / 35 : ℝ) := by
  let r := suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1
  have hbasePoint : Real.log 2 ≤ r := by
    dsimp only [r]
    exact base_le_suzukiResetTransportMassPoint
      (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1
  have hcontinuous :
      ContinuousOn suzukiSmoothCurvature
        (Set.uIcc (Real.log 2) r) := by
    apply continuousOn_suzukiSmoothCurvature_Ioi.mono
    intro s hs
    rw [Set.uIcc_of_le hbasePoint] at hs
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hs.1
  have hcurvatureIntegrable :
      IntervalIntegrable suzukiSmoothCurvature volume
        (Real.log 2) r :=
    hcontinuous.intervalIntegrable
  have hconstantIntegrable :
      IntervalIntegrable (fun _ : ℝ => (7 / 6 : ℝ)) volume
        (Real.log 2) r :=
    (continuous_const : Continuous (fun _ : ℝ => (7 / 6 : ℝ))).intervalIntegrable
      _ _
  have hlowerIntegral :
      (∫ _s in Real.log 2..r, (7 / 6 : ℝ)) ≤
        ∫ s in Real.log 2..r, suzukiSmoothCurvature s := by
    apply intervalIntegral.integral_mono_on hbasePoint
      hconstantIntegrable hcurvatureIntegrable
    intro s hs
    exact seven_sixths_le_suzukiSmoothCurvature_of_logTwo_le hs.1
  have hmass := suzukiResetTransportMassPoint_one_mass_eq_neg_slope
    (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
  change (∫ s in Real.log 2..r, suzukiSmoothCurvature s) =
      -suzukiPointwiseFrozenBaseSlope (Real.log 2) 1 at hmass
  rw [intervalIntegral.integral_const] at hlowerIntegral
  norm_num only [smul_eq_mul] at hlowerIntegral
  rw [hmass] at hlowerIntegral
  nlinarith [
    neg_three_tenths_lt_suzukiPointwiseFrozenBaseSlope_logTwo_one]

/-- The synthetic first-tail mass point occurs before time one. -/
theorem suzukiFirstTailResetMassPoint_lt_one :
    suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1 < 1 := by
  nlinarith [suzukiFirstTailResetMassPoint_sub_logTwo_lt_nine_over_35,
    Real.log_two_lt_d9]

private theorem exp_one_half_lt_five_thirds :
    Real.exp (1 / 2 : ℝ) < 5 / 3 := by
  have hsquare : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hpositive := Real.exp_pos (1 / 2 : ℝ)
  nlinarith [Real.exp_one_lt_d9]

/-- Before time one the exact Suzuki curvature is less than `5 / 3`. -/
theorem suzukiSmoothCurvature_lt_five_thirds_of_pos_of_lt_one
    {t : ℝ} (htpos : 0 < t) (htone : t < 1) :
    suzukiSmoothCurvature t < (5 / 3 : ℝ) := by
  calc
    suzukiSmoothCurvature t < Real.exp (t / 2) :=
      suzukiSmoothCurvature_lt_pureExponential htpos
    _ < Real.exp (1 / 2) := Real.exp_lt_exp.mpr (by linarith)
    _ < 5 / 3 := exp_one_half_lt_five_thirds

/-- The complete loss incurred while cancelling the synthetic initial slope
is strictly smaller than the checked base reserve `7 / 125`. -/
theorem suzukiFirstTailSyntheticCellLoss_lt_seven_over_125 :
    (∫ s in Real.log 2..
        suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1,
        (s - Real.log 2) * suzukiSmoothCurvature s) <
      (7 / 125 : ℝ) := by
  let r := suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1
  have hbasePoint : Real.log 2 ≤ r := by
    dsimp only [r]
    exact base_le_suzukiResetTransportMassPoint
      (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1
  have hpointOne : r < 1 := by
    dsimp only [r]
    exact suzukiFirstTailResetMassPoint_lt_one
  have hcurvatureContinuous :
      ContinuousOn suzukiSmoothCurvature
        (Set.uIcc (Real.log 2) r) := by
    apply continuousOn_suzukiSmoothCurvature_Ioi.mono
    intro s hs
    rw [Set.uIcc_of_le hbasePoint] at hs
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hs.1
  have hlossIntegrable :
      IntervalIntegrable
        (fun s : ℝ => (s - Real.log 2) * suzukiSmoothCurvature s)
        volume (Real.log 2) r :=
    ((continuousOn_id.sub continuousOn_const).mul
      hcurvatureContinuous).intervalIntegrable
  have hupperContinuous : Continuous
      (fun s : ℝ => (s - Real.log 2) * (5 / 3 : ℝ)) := by
    fun_prop
  have hupperIntegrable :
      IntervalIntegrable
        (fun s : ℝ => (s - Real.log 2) * (5 / 3 : ℝ))
        volume (Real.log 2) r :=
    hupperContinuous.intervalIntegrable _ _
  have hintegralUpper :
      (∫ s in Real.log 2..r,
          (s - Real.log 2) * suzukiSmoothCurvature s) ≤
        ∫ s in Real.log 2..r,
          (s - Real.log 2) * (5 / 3 : ℝ) := by
    apply intervalIntegral.integral_mono_on hbasePoint
      hlossIntegrable hupperIntegrable
    intro s hs
    have hdistanceNonnegative : 0 ≤ s - Real.log 2 := by
      linarith [hs.1]
    apply mul_le_mul_of_nonneg_left _ hdistanceNonnegative
    exact (suzukiSmoothCurvature_lt_five_thirds_of_pos_of_lt_one
      ((Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hs.1)
      (hs.2.trans_lt hpointOne)).le
  have hupperIdentity :
      (∫ s in Real.log 2..r,
          (s - Real.log 2) * (5 / 3 : ℝ)) =
        (5 / 6 : ℝ) * (r - Real.log 2) ^ 2 := by
    have hfunction :
        (fun s : ℝ => (s - Real.log 2) * (5 / 3 : ℝ)) =
          fun s : ℝ => (5 / 3 : ℝ) * s -
            (5 / 3 : ℝ) * Real.log 2 := by
      funext s
      ring_nf
    have hlinearIntegrable :
        IntervalIntegrable (fun s : ℝ => (5 / 3 : ℝ) * s)
          volume (Real.log 2) r := by
      have hcontinuous : Continuous
          (fun s : ℝ => (5 / 3 : ℝ) * s) := by
        fun_prop
      exact hcontinuous.intervalIntegrable _ _
    have hconstantIntegrable :
        IntervalIntegrable
          (fun _s : ℝ => (5 / 3 : ℝ) * Real.log 2)
          volume (Real.log 2) r := by
      have hcontinuous : Continuous
          (fun _s : ℝ => (5 / 3 : ℝ) * Real.log 2) := by
        fun_prop
      exact hcontinuous.intervalIntegrable _ _
    rw [hfunction, intervalIntegral.integral_sub hlinearIntegrable
      hconstantIntegrable, intervalIntegral.integral_const_mul,
      integral_id, intervalIntegral.integral_const]
    norm_num only [smul_eq_mul]
    ring_nf
  rw [hupperIdentity] at hintegralUpper
  have hdistance : r - Real.log 2 < (9 / 35 : ℝ) := by
    dsimp only [r]
    exact suzukiFirstTailResetMassPoint_sub_logTwo_lt_nine_over_35
  have hdistanceNonnegative : 0 ≤ r - Real.log 2 := sub_nonneg.mpr hbasePoint
  have hdistanceSquare :
      (r - Real.log 2) ^ 2 < (9 / 35 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hdistanceNonnegative (by norm_num)).2 hdistance
  exact hintegralUpper.trans_lt (by nlinarith)

/-- The first nontrivial canonical transport gap is strictly positive.  This
discharges the synthetic zero-slope cell rather than assuming its barrier. -/
theorem suzukiFirstTailSyntheticGap_pos :
    0 < curvatureTransportGap
      (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
      (Real.log 2) suzukiSmoothCurvature
      (suzukiResetLocation (Real.log 2) 1)
      (suzukiResetWeight
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
      (suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1) 1 := by
  let r := suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 1
  have hnegativeIntegral :
      (∫ s in Real.log 2..r,
          (Real.log 2 - s) * suzukiSmoothCurvature s) =
        -(∫ s in Real.log 2..r,
          (s - Real.log 2) * suzukiSmoothCurvature s) := by
    calc
      (∫ s in Real.log 2..r,
          (Real.log 2 - s) * suzukiSmoothCurvature s) =
          ∫ s in Real.log 2..r,
            -((s - Real.log 2) * suzukiSmoothCurvature s) := by
              apply intervalIntegral.integral_congr
              intro s _hs
              ring_nf
      _ = -(∫ s in Real.log 2..r,
          (s - Real.log 2) * suzukiSmoothCurvature s) :=
        intervalIntegral.integral_neg
  rw [suzukiResetTransportGap_one]
  change 0 < suzukiPointwiseFrozenBaseValue (Real.log 2) 1 +
    ∫ s in Real.log 2..r,
      (Real.log 2 - s) * suzukiSmoothCurvature s
  rw [hnegativeIntegral]
  nlinarith [seven_over_125_lt_suzukiPointwiseFrozenBaseValue_logTwo_one,
    suzukiFirstTailSyntheticCellLoss_lt_seven_over_125]

/-- Cutoff one satisfies the strict cumulative transport-surplus inequality. -/
theorem neg_suzukiPointwiseFrozenBaseValue_logTwo_one_lt_cumulativeSurplus_one :
    -suzukiPointwiseFrozenBaseValue (Real.log 2) 1 <
      ∑ n ∈ Finset.range 1,
        suzukiResetTransportCellSurplus (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 n := by
  have hgap := suzukiFirstTailSyntheticGap_pos
  rw [suzukiResetTransportGap_eq_baseValue_add_sum] at hgap
  linarith

/-- The exact canonical tail-positivity criterion now starts at cutoff two.
Every prefix still present there contains at least one future arithmetic
von-Mangoldt event; cutoff zero and the synthetic cutoff one are proved. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_cumulativeTransportSurplus :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ cutoff : ℕ, 2 ≤ cutoff →
        -suzukiPointwiseFrozenBaseValue (Real.log 2) 1 ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 n := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_positiveCutoff_cumulativeTransportSurplus]
  constructor
  · intro hall cutoff hcutoff
    exact hall cutoff (by omega)
  · intro hlarge cutoff hpositive
    by_cases hone : cutoff = 1
    · subst cutoff
      exact
        neg_suzukiPointwiseFrozenBaseValue_logTwo_one_lt_cumulativeSurplus_one.le
    · exact hlarge cutoff (by omega)

end

end RiemannGaussian
