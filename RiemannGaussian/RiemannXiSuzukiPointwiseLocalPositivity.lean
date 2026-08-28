import RiemannGaussian.RiemannXiSuzukiPointwiseArithmetic
import RiemannGaussian.GaussianScrewBridge

/-!
# Unconditional local positivity of Suzuki's arithmetic pointwise function

Suzuki proved that his pointwise arithmetic `Psi` is positive on a nonzero
interval at the origin.  The published direct proof uses numerical root
isolation.  Here we instead give a symbolic proof suited to kernel checking.

The order-two Hurwitz--Lerch difference is a sum of nonnegative terms.  On a
fixed finite block, the elementary inequality

`(2/3) u <= 1 - exp (-2u)` for `0 < u <= 1`

turns that block into a positive multiple of a shifted harmonic sum.  Since
the harmonic sums are unbounded, one finite block dominates the fixed
digamma/`log pi` coefficient.  Shrinking time after choosing the block makes
the inequality valid uniformly and also keeps the von-Mangoldt window below
the first prime.

No numerical approximation or hypothesis about zeta zeros enters the proof.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped BigOperators Topology

/-! ## The positive Hurwitz--Lerch gap -/

/-- One summand of the positive order-two Hurwitz--Lerch gap in Suzuki's
pointwise formula. -/
def suzukiPointwiseLerchGapSummand (t : ℝ) (n : ℕ) : ℝ :=
  suzukiHurwitzLerchTwoSummand 1 n -
    Real.exp (-t / 2) *
      suzukiHurwitzLerchTwoSummand (Real.exp (-2 * t)) n

/-- A gap summand has the elementary exponential form
`(1 - exp (-2 (n + 1/4) t)) / (n + 1/4)^2`. -/
theorem suzukiPointwiseLerchGapSummand_eq
    (t : ℝ) (n : ℕ) :
    suzukiPointwiseLerchGapSummand t n =
      (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) /
        ((n : ℝ) + 1 / 4) ^ 2 := by
  have hexp :
      Real.exp (-t / 2) * (Real.exp (-2 * t)) ^ n =
        Real.exp (-2 * ((n : ℝ) + 1 / 4) * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  unfold suzukiPointwiseLerchGapSummand
    suzukiHurwitzLerchTwoSummand
  rw [one_pow]
  calc
    1 / ((n : ℝ) + 1 / 4) ^ 2 -
        Real.exp (-t / 2) *
          ((Real.exp (-2 * t)) ^ n / ((n : ℝ) + 1 / 4) ^ 2) =
      (1 - Real.exp (-t / 2) * (Real.exp (-2 * t)) ^ n) /
        ((n : ℝ) + 1 / 4) ^ 2 := by ring
    _ = (1 - Real.exp (-2 * ((n : ℝ) + 1 / 4) * t)) /
        ((n : ℝ) + 1 / 4) ^ 2 := by rw [hexp]

/-- Every Lerch-gap summand is nonnegative at nonnegative time. -/
theorem suzukiPointwiseLerchGapSummand_nonnegative
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ suzukiPointwiseLerchGapSummand t n := by
  rw [suzukiPointwiseLerchGapSummand_eq]
  have ha : 0 ≤ (n : ℝ) + 1 / 4 := by positivity
  have harg : -2 * ((n : ℝ) + 1 / 4) * t ≤ 0 := by
    nlinarith
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr harg))
    (sq_nonneg _)

/-- The positive-time Lerch gap is summable. -/
theorem summable_suzukiPointwiseLerchGapSummand
    {t : ℝ} (ht : 0 ≤ t) :
    Summable (suzukiPointwiseLerchGapSummand t) := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  exact (summable_suzukiHurwitzLerchTwoSummand zero_le_one le_rfl).sub
    ((summable_suzukiHurwitzLerchTwoSummand hq0 hq1).mul_left
      (Real.exp (-t / 2)))

/-- Suzuki's complete order-two Hurwitz--Lerch difference is the sum of the
nonnegative gap summands. -/
theorem suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiHurwitzLerchTwo 1 -
        Real.exp (-t / 2) *
          suzukiHurwitzLerchTwo (Real.exp (-2 * t)) =
      ∑' n : ℕ, suzukiPointwiseLerchGapSummand t n := by
  have hq0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hOne :=
    summable_suzukiHurwitzLerchTwoSummand zero_le_one le_rfl
  have hMoving :=
    (summable_suzukiHurwitzLerchTwoSummand hq0 hq1).mul_left
      (Real.exp (-t / 2))
  unfold suzukiHurwitzLerchTwo
  rw [← tsum_mul_left, ← hOne.tsum_sub hMoving]
  apply tsum_congr
  intro n
  rfl

/-- On a block where `(n + 1/4)t <= 1`, one Lerch-gap summand dominates a
shifted harmonic term. -/
theorem two_thirds_mul_time_div_le_suzukiPointwiseLerchGapSummand
    {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hsmall : ((n : ℝ) + 1 / 4) * t ≤ 1) :
    (2 / 3 : ℝ) * t / ((n : ℝ) + 1 / 4) ≤
      suzukiPointwiseLerchGapSummand t n := by
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hat : 0 < a * t := mul_pos ha ht
  have hbase := two_thirds_mul_le_one_sub_exp_neg_two_mul
    hat (by simpa [a] using hsmall)
  rw [suzukiPointwiseLerchGapSummand_eq]
  change (2 / 3 : ℝ) * t / a ≤
    (1 - Real.exp (-2 * a * t)) / a ^ 2
  have hrewrite :
      (2 / 3 : ℝ) * t / a =
        ((2 / 3 : ℝ) * (a * t)) / a ^ 2 := by
    field_simp [ha.ne']
  rw [hrewrite]
  calc
    ((2 / 3 : ℝ) * (a * t)) / a ^ 2 ≤
        (1 - Real.exp (-2 * (a * t))) / a ^ 2 :=
      div_le_div_of_nonneg_right hbase (sq_nonneg a)
    _ = (1 - Real.exp (-2 * a * t)) / a ^ 2 := by
      rw [show -2 * (a * t) = -2 * a * t by ring]

/-! ## Prime-free initial interval -/

/-- Before the first prime event, the finite von-Mangoldt contribution in
Suzuki's literal source formula vanishes. -/
theorem suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two
    {t : ℝ} (ht : 0 ≤ t) (htwo : t < Real.log 2) :
    suzukiPointwisePrimeContribution t = 0 := by
  have hexpOne : (1 : ℝ) ≤ Real.exp t := by
    simpa using Real.exp_le_exp.mpr ht
  have hexpTwo : Real.exp t < 2 := by
    calc
      Real.exp t < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr htwo
      _ = 2 := Real.exp_log (by norm_num)
  have hfloorOne : 1 ≤ ⌊Real.exp t⌋₊ :=
    (Nat.le_floor_iff (Real.exp_nonneg t)).2 (by
      exact_mod_cast hexpOne)
  have hfloorTwo : ⌊Real.exp t⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_nonneg t)).2 hexpTwo
  have hfloor : ⌊Real.exp t⌋₊ = 1 := by omega
  rw [suzukiPointwisePrimeContribution_eq_sum_range ht, hfloor]
  simp

/-- The elementary hyperbolic-cosine part of Suzuki's Archimedean term is
nonnegative. -/
theorem suzukiPointwiseElementary_nonnegative (t : ℝ) :
    0 ≤ 4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) := by
  have hproduct : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hamgm : (2 : ℝ) ≤ Real.exp (t / 2) + Real.exp (-t / 2) := by
    have h := two_mul_le_add_of_sq_le_mul
      (Real.exp_pos (t / 2)).le (Real.exp_pos (-t / 2)).le
      (show (1 : ℝ) ^ 2 ≤
        Real.exp (t / 2) * Real.exp (-t / 2) by
          rw [hproduct]
          norm_num)
    norm_num at h ⊢
    exact h
  positivity

/-! ## Symbolic local positivity -/

/-- Suzuki's actual arithmetic pointwise function is unconditionally
strictly positive throughout some nonzero interval to the right of the
origin.  The interval is selected symbolically from harmonic divergence; no
floating-point or unproved zero information is used. -/
theorem exists_pos_on_riemannXiSuzukiPsi :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → 0 < riemannXiSuzukiPsi t := by
  let D : ℝ := (Complex.digamma (1 / 4)).re - Real.log Real.pi
  obtain ⟨N, hN⟩ :=
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
      (3 * |D| + 1)).exists
  let S : ℝ := ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1 / 4)
  have hHarmonicLe :
      (∑ n ∈ Finset.range N, (1 / (n + 1) : ℝ)) ≤ S := by
    unfold S
    apply Finset.sum_le_sum
    intro n hn
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  have hS : 3 * |D| < S := by
    have hlarge : 3 * |D| + 1 < S := hN.trans_le hHarmonicLe
    linarith
  let δ : ℝ := min (Real.log 2) (1 / ((N : ℝ) + 1))
  have hδ : 0 < δ := lt_min
    (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have htlog : t < Real.log 2 := htδ.trans_le (min_le_left _ _)
  have htN : t < 1 / ((N : ℝ) + 1) :=
    htδ.trans_le (min_le_right _ _)
  have htNmul : t * ((N : ℝ) + 1) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at htN
    simpa [mul_comm] using htN
  have hgapFinite :
      (2 / 3 : ℝ) * t * S ≤
        suzukiHurwitzLerchTwo 1 -
          Real.exp (-t / 2) *
            suzukiHurwitzLerchTwo (Real.exp (-2 * t)) := by
    rw [suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap ht.le]
    have hsum :
        (∑ n ∈ Finset.range N,
          (2 / 3 : ℝ) * t / ((n : ℝ) + 1 / 4)) ≤
            ∑ n ∈ Finset.range N,
              suzukiPointwiseLerchGapSummand t n := by
      apply Finset.sum_le_sum
      intro n hn
      apply two_thirds_mul_time_div_le_suzukiPointwiseLerchGapSummand ht
      have hnN : (n : ℝ) + 1 / 4 ≤ (N : ℝ) + 1 := by
        have hnLt : n < N := Finset.mem_range.mp hn
        have hnCast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnLt.le
        linarith
      calc
        ((n : ℝ) + 1 / 4) * t ≤ ((N : ℝ) + 1) * t := by
          exact mul_le_mul_of_nonneg_right hnN ht.le
        _ = t * ((N : ℝ) + 1) := by ring
        _ ≤ 1 := htNmul.le
    have hfiniteToInfinite :
        (∑ n ∈ Finset.range N,
          suzukiPointwiseLerchGapSummand t n) ≤
            ∑' n : ℕ, suzukiPointwiseLerchGapSummand t n :=
      (summable_suzukiPointwiseLerchGapSummand ht.le).sum_le_tsum
        (Finset.range N)
        (fun n hn => suzukiPointwiseLerchGapSummand_nonnegative ht.le n)
    have hfactor :
        (∑ n ∈ Finset.range N,
          (2 / 3 : ℝ) * t / ((n : ℝ) + 1 / 4)) =
            (2 / 3 : ℝ) * t * S := by
      unfold S
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [← hfactor]
    exact hsum.trans hfiniteToInfinite
  have hgapStrict :
      t / 2 * |D| <
        1 / 4 *
          (suzukiHurwitzLerchTwo 1 -
            Real.exp (-t / 2) *
              suzukiHurwitzLerchTwo (Real.exp (-2 * t))) := by
    have hmul : t * (3 * |D|) < t * S :=
      mul_lt_mul_of_pos_left hS ht
    have hscaled := mul_le_mul_of_nonneg_left hgapFinite
      (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    nlinarith
  have hlinear : -(t / 2 * |D|) ≤ t / 2 * D := by
    have hD := neg_abs_le D
    nlinarith
  have hpositiveCore :
      0 < t / 2 * D +
        1 / 4 *
          (suzukiHurwitzLerchTwo 1 -
            Real.exp (-t / 2) *
              suzukiHurwitzLerchTwo (Real.exp (-2 * t))) := by
    linarith
  have helementary := suzukiPointwiseElementary_nonnegative t
  have hprime :=
    suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two ht.le htlog
  rw [riemannXiSuzukiPsi, abs_of_pos ht]
  unfold riemannXiSuzukiPsiNonnegative
  rw [hprime, sub_zero]
  unfold suzukiPointwiseArchimedean
  change 0 <
    4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
      t / 2 * D +
        1 / 4 *
          (suzukiHurwitzLerchTwo 1 -
            Real.exp (-t / 2) *
              suzukiHurwitzLerchTwo (Real.exp (-2 * t)))
  linarith

/-- Evenness upgrades the right-hand interval to an unconditional punctured
neighborhood of the origin. -/
theorem exists_pos_on_abs_riemannXiSuzukiPsi :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < |t| → |t| < δ → 0 < riemannXiSuzukiPsi t := by
  obtain ⟨δ, hδ, hpositive⟩ := exists_pos_on_riemannXiSuzukiPsi
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  simpa [riemannXiSuzukiPsi] using hpositive |t| ht htδ

end

end RiemannGaussian
