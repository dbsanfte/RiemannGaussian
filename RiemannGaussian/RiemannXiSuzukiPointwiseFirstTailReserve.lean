import RiemannGaussian.RiemannXiSuzukiPointwiseFirstTail

/-!
# Positive reserve at the first Suzuki transport tail

The canonical first tail begins at `log 2` after freezing the first von
Mangoldt event.  Its cumulative-surplus criterion includes cutoff zero,
which simply asks for nonnegativity of the frozen base value.  This file
proves the stronger strict inequality for that literal value.

The estimate is exact.  A telescoping rational series bounds the complete
Euler difference between the quarter- and half-point digamma values.  A
finite lower sum of nonnegative order-two Lerch-gap terms, with a rational
bound on `exp (-log 2 / 2)`, supplies the positive part.  No floating-point
evaluation or external certificate is trusted by the proof.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped BigOperators Topology

/-! ## A complete lower bound for the quarter-point digamma -/

private theorem hasSum_quarterDigammaTailMajorant :
    HasSum
      (fun k : ℕ => (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 4) - 1 / ((k : ℝ) + 5)))
      (1 / 16 : ℝ) := by
  let g : ℕ → ℝ := fun k => (1 / 4 : ℝ) *
    (1 / ((k : ℝ) + 4) - 1 / ((k : ℝ) + 5))
  have hnonnegative (k : ℕ) : 0 ≤ g k := by
    unfold g
    apply mul_nonneg (by norm_num)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonnegative (1 / 16)).2
  have hpartial (n : ℕ) :
      (∑ k ∈ Finset.range n, g k) =
        (1 / 4 : ℝ) * (1 / 4 - 1 / ((n : ℝ) + 4)) := by
    change (∑ k ∈ Finset.range n,
      (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 4) - 1 / ((k : ℝ) + 5))) = _
    rw [← Finset.mul_sum]
    have hrewrite :
        (fun k : ℕ =>
          (1 : ℝ) / ((k : ℝ) + 4) - 1 / ((k : ℝ) + 5)) =
          fun k : ℕ =>
            (1 : ℝ) / ((k : ℝ) + 4) -
              1 / (((k + 1 : ℕ) : ℝ) + 4) := by
      funext k
      norm_num only [Nat.cast_add, Nat.cast_one]
      congr 2
      ring
    rw [hrewrite, Finset.sum_range_sub']
    norm_num
  have hdenominator : Tendsto (fun n : ℕ => (n : ℝ) + 4)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 4
      tendsto_natCast_atTop_atTop
  have hinverse : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4))
      atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hdenominator
    exact h.congr'
      (Filter.Eventually.of_forall (fun n => by
        simp [one_div]))
  have hlimit : Tendsto
      (fun n : ℕ => (1 / 4 : ℝ) *
        (1 / 4 - 1 / ((n : ℝ) + 4)))
      atTop (nhds (1 / 16)) := by
    convert (tendsto_const_nhds.sub hinverse).const_mul (1 / 4 : ℝ)
      using 1
    norm_num
  exact hlimit.congr'
    (Filter.Eventually.of_forall (fun n => (hpartial n).symm))

/-- A rational lower bound for the real quarter-point digamma.  Unlike the
finite upper bound used for the frozen slope, this controls the complete
positive Euler-difference series by a telescoping tail. -/
theorem re_digamma_quarter_gt_lower_bound :
    (-433 / 100 : ℝ) < (Complex.digamma (1 / 4)).re := by
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
      f (k + 5) ≤ (1 / 4 : ℝ) *
        (1 / ((k : ℝ) + 4) - 1 / ((k : ℝ) + 5)) := by
    rw [hterm]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    let x : ℝ := k
    have hx : 0 ≤ x := Nat.cast_nonneg k
    have hleft :
        1 / (x + 5 + 1 / 4) - 1 / (x + 5 + 1 / 2) =
          (1 / 4 : ℝ) /
            ((x + 5 + 1 / 4) * (x + 5 + 1 / 2)) := by
      field_simp
      ring
    have hright :
        (1 / 4 : ℝ) * (1 / (x + 4) - 1 / (x + 5)) =
          (1 / 4 : ℝ) / ((x + 4) * (x + 5)) := by
      field_simp
      ring
    change 1 / (x + 5 + 1 / 4) - 1 / (x + 5 + 1 / 2) ≤
      (1 / 4 : ℝ) * (1 / (x + 4) - 1 / (x + 5))
    rw [hleft, hright]
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · nlinarith
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range 5, f n) +
          ∑' k : ℕ, f (k + 5) := by
    simpa using (hsum.summable.sum_add_tsum_nat_add 5).symm
  have hfinite : (∑ n ∈ Finset.range 5, f n) =
      (2 + 2 / 15 + 2 / 45 + 2 / 91 + 2 / 153 : ℝ) := by
    simp_rw [hterm]
    norm_num
  have htailSummable : Summable (fun k : ℕ => f (k + 5)) :=
    (summable_nat_add_iff 5).mpr hsum.summable
  have htail : (∑' k : ℕ, f (k + 5)) ≤ 1 / 16 := by
    rw [← hasSum_quarterDigammaTailMajorant.tsum_eq]
    exact htailSummable.tsum_le_tsum htailTerm
      hasSum_quarterDigammaTailMajorant.summable
  have hdifference : (∑' n : ℕ, f n) ≤ 569 / 250 := by
    rw [hsplit, hfinite]
    linarith
  rw [hsum.tsum_eq, Complex.digamma_one_half] at hdifference
  norm_num [Complex.log_re] at hdifference
  nlinarith [Real.log_two_lt_d9,
    Real.eulerMascheroniConstant_lt_two_thirds]

/-! ## Positive terms at the first tail base -/

private theorem exp_logTwo_half_sq_reserve :
    Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_neg_logTwo_half_sq_reserve :
    Real.exp (-Real.log 2 / 2) ^ 2 = 1 / 2 := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have hneg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show (2 : ℝ) * (-Real.log 2 / 2) = -Real.log 2 by ring,
    hneg]

private theorem elementary_logTwo_lower_bound :
    (121 / 250 : ℝ) ≤
      4 * (Real.exp (Real.log 2 / 2) +
        Real.exp (-Real.log 2 / 2) - 2) := by
  have hpNonnegative := (Real.exp_pos (Real.log 2 / 2)).le
  have hrNonnegative := (Real.exp_pos (-Real.log 2 / 2)).le
  have hpSquare := exp_logTwo_half_sq_reserve
  have hrSquare := exp_neg_logTwo_half_sq_reserve
  have hp : (707 / 500 : ℝ) ≤ Real.exp (Real.log 2 / 2) := by
    nlinarith
  have hr : (707 / 1000 : ℝ) ≤ Real.exp (-Real.log 2 / 2) := by
    nlinarith
  nlinarith

private theorem exp_neg_logTwo_half_le_177_over_250 :
    Real.exp (-Real.log 2 / 2) ≤ 177 / 250 := by
  have hrNonnegative := (Real.exp_pos (-Real.log 2 / 2)).le
  have hrSquare := exp_neg_logTwo_half_sq_reserve
  nlinarith

private theorem exp_neg_two_logTwo_reserve :
    Real.exp (-2 * Real.log 2) = (1 / 4 : ℝ) := by
  rw [show -2 * Real.log 2 = -Real.log 2 + -Real.log 2 by ring,
    Real.exp_add, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private theorem lerchGapSummand_logTwo_lower_bound (n : ℕ) :
    (1 - (177 / 250 : ℝ) * (1 / 4 : ℝ) ^ n) /
        ((n : ℝ) + 1 / 4) ^ 2 ≤
      suzukiPointwiseLerchGapSummand (Real.log 2) n := by
  rw [suzukiPointwiseLerchGapSummand_eq,
    suzukiPointwiseLerchMode_eq_geometric,
    exp_neg_two_logTwo_reserve]
  apply div_le_div_of_nonneg_right
  · have hpow : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      exp_neg_logTwo_half_le_177_over_250 hpow
    linarith
  · positivity

/-- Eighteen nonnegative terms already give a strict rational lower bound
for the complete order-two Lerch gap at the first prime time. -/
theorem quarter_mul_lerchGap_logTwo_gt :
    (711 / 500 : ℝ) <
      1 / 4 *
        (∑' n : ℕ,
          suzukiPointwiseLerchGapSummand (Real.log 2) n) := by
  let lower : ℕ → ℝ := fun n =>
    (1 - (177 / 250 : ℝ) * (1 / 4 : ℝ) ^ n) /
      ((n : ℝ) + 1 / 4) ^ 2
  have hfinite : (711 / 125 : ℝ) <
      ∑ n ∈ Finset.range 18, lower n := by
    dsimp only [lower]
    norm_num [Finset.sum_range_succ]
  have hcompare :
      (∑ n ∈ Finset.range 18, lower n) ≤
        ∑ n ∈ Finset.range 18,
          suzukiPointwiseLerchGapSummand (Real.log 2) n := by
    apply Finset.sum_le_sum
    intro n _hn
    exact lerchGapSummand_logTwo_lower_bound n
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hinfinite :
      (∑ n ∈ Finset.range 18,
        suzukiPointwiseLerchGapSummand (Real.log 2) n) ≤
          ∑' n : ℕ,
            suzukiPointwiseLerchGapSummand (Real.log 2) n :=
    (summable_suzukiPointwiseLerchGapSummand hlog).sum_le_tsum
      (Finset.range 18)
      (fun n _hn => suzukiPointwiseLerchGapSummand_nonnegative hlog n)
  have htotal : (711 / 125 : ℝ) <
      ∑' n : ℕ,
        suzukiPointwiseLerchGapSummand (Real.log 2) n :=
    hfinite.trans_le (hcompare.trans hinfinite)
  have hscaled := mul_lt_mul_of_pos_left htotal
    (by norm_num : (0 : ℝ) < 1 / 4)
  norm_num at hscaled ⊢
  exact hscaled

private theorem log_pi_lt_23_over_20 :
    Real.log Real.pi < 23 / 20 := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 20) 6
  have hpiExp : Real.pi < Real.exp (23 / 20) := by
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ < ∑ i ∈ Finset.range 6,
          (23 / 20 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (23 / 20) := hexponential
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpiExp

private theorem linear_logTwo_lower_bound :
    (-951 / 500 : ℝ) <
      Real.log 2 / 2 *
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) := by
  have hcoefficient : (-137 / 25 : ℝ) <
      (Complex.digamma (1 / 4)).re - Real.log Real.pi := by
    nlinarith [re_digamma_quarter_gt_lower_bound,
      log_pi_lt_23_over_20]
  have hhalfPos : 0 < Real.log 2 / 2 := by
    positivity
  have hhalfUpper : Real.log 2 / 2 < 347 / 1000 := by
    nlinarith [Real.log_two_lt_d9]
  calc
    (-951 / 500 : ℝ) <
        (347 / 1000 : ℝ) * (-137 / 25 : ℝ) := by norm_num
    _ < Real.log 2 / 2 * (-137 / 25 : ℝ) :=
      mul_lt_mul_of_neg_right hhalfUpper (by norm_num)
    _ < Real.log 2 / 2 *
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) :=
      mul_lt_mul_of_pos_left hcoefficient hhalfPos

/-! ## Literal reserve and the reduced frontier -/

private theorem suzukiPointwiseFrozenBaseValue_logTwo_one_eq :
    suzukiPointwiseFrozenBaseValue (Real.log 2) 1 =
      suzukiPointwiseArchimedean (Real.log 2) := by
  unfold suzukiPointwiseFrozenBaseValue frozenScrewHingeModel
  simp [screwAffineKick, suzukiPrimeLocation]

/-- The literal frozen value at the canonical first-event base exceeds the
explicit rational reserve `1 / 250`. -/
theorem one_div_250_lt_suzukiPointwiseFrozenBaseValue_logTwo_one :
    (1 / 250 : ℝ) <
      suzukiPointwiseFrozenBaseValue (Real.log 2) 1 := by
  rw [suzukiPointwiseFrozenBaseValue_logTwo_one_eq,
    suzukiPointwiseArchimedean_eq_series
      (Real.log_pos (by norm_num)).le]
  unfold suzukiPointwiseArchimedeanSeries
  nlinarith [elementary_logTwo_lower_bound,
    linear_logTwo_lower_bound, quarter_mul_lerchGap_logTwo_gt]

/-- Positivity form of the explicit first-tail reserve. -/
theorem suzukiPointwiseFrozenBaseValue_logTwo_one_pos :
    0 < suzukiPointwiseFrozenBaseValue (Real.log 2) 1 :=
  (by norm_num : (0 : ℝ) < 1 / 250).trans
    one_div_250_lt_suzukiPointwiseFrozenBaseValue_logTwo_one

/-- With the positive initial reserve checked, the canonical tail criterion
only needs the genuinely arithmetic positive cutoffs. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_positiveCutoff_cumulativeTransportSurplus :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ cutoff : ℕ, 0 < cutoff →
        -suzukiPointwiseFrozenBaseValue (Real.log 2) 1 ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus (Real.log 2)
              (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
              (le_refl (Real.log 2))
              suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 n := by
  rw [riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_cumulativeTransportSurplus]
  constructor
  · intro hall cutoff _hcutoff
    exact hall cutoff
  · intro hpositive cutoff
    by_cases hcutoff : cutoff = 0
    · subst cutoff
      simpa using
        (neg_nonpos.mpr
          suzukiPointwiseFrozenBaseValue_logTwo_one_pos.le)
    · exact hpositive cutoff (Nat.pos_of_ne_zero hcutoff)

end

end RiemannGaussian
