/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiBilinearWork

/-!
# Retaining the full arithmetic mass logarithm in Suzuki work

The bilinear lower bound loses a positive nonlinear reserve whose total is
not known to be finite. Here the implicit canonical center is eliminated
while retaining that nonlinear information: use the logarithm of the exact
finite prime mass with its source-exact constant correction. The difference
from the original work is a positive Lerch correction with a proved summable
majorant. Thus the replacement is uniformly accurate on every late finite
band, independently of its length.

The cumulative lower bound needed for RH is still open. This file controls
the actual replacement error; it does not establish the arithmetic floor.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped BigOperators Topology

/-- Exact finite arithmetic work retaining the logarithm of the corrected
old prime mass, without an implicit canonical center. -/
def suzukiFirstTailMassLogWork (count : ℕ) : ℝ :=
  suzukiPrimeWeight (count + 1) *
    (suzukiPrimeLocation (count + 1) -
      2 * Real.log ((screwPrefixMass suzukiPrimeWeight (count + 1) -
        suzukiArchimedeanSlopeConstant) / 2))

/-- The exact positive correction between the actual work and its mass
logarithm expression. Only the retained Lerch tail enters this correction. -/
def suzukiFirstTailMassLogWorkError (count : ℕ) : ℝ :=
  2 * suzukiPrimeWeight (count + 1) *
    Real.log (1 + suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) /
      (2 * Real.exp (suzukiFirstTailChebyshevCenter count / 2)))

/-- The corrected finite mass equals the leading positive exponential and
the full positive slope tail at its original canonical center. -/
theorem suzukiFirstTailCorrectedMass_eq_exp_add_tail (count : ℕ) :
    screwPrefixMass suzukiPrimeWeight (count + 1) - suzukiArchimedeanSlopeConstant =
      2 * Real.exp (suzukiFirstTailChebyshevCenter count / 2) +
        suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) := by
  have hr : 0 < suzukiFirstTailChebyshevCenter count :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
      (log_two_le_suzukiFirstTailChebyshevCenter count)
  have hm := suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass count
  rw [suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail hr] at hm
  rw [screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
  simp only [Nat.add_assoc] at *
  linarith

/-- The argument of the arithmetic logarithm is strictly positive, with
nonvanishing discharged from the actual slope-matching equation. -/
theorem suzukiFirstTailCorrectedMass_pos (count : ℕ) :
    0 < screwPrefixMass suzukiPrimeWeight (count + 1) - suzukiArchimedeanSlopeConstant := by
  rw [suzukiFirstTailCorrectedMass_eq_exp_add_tail]
  exact add_pos_of_pos_of_nonneg (by positivity)
    (suzukiArchimedeanPositiveSlopeTail_nonneg _)

/-- Exact replacement of the implicit canonical center by the finite
arithmetic mass logarithm, retaining the entire correction. -/
theorem suzukiFirstTailTransportLinearWork_eq_massLog_add_error (count : ℕ) :
    suzukiFirstTailTransportLinearWork count =
      suzukiFirstTailMassLogWork count + suzukiFirstTailMassLogWorkError count := by
  let r := suzukiFirstTailChebyshevCenter count
  have ht := suzukiArchimedeanPositiveSlopeTail_nonneg r
  have hp : 0 < 1 + suzukiArchimedeanPositiveSlopeTail r / (2 * Real.exp (r / 2)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
  have hf : (screwPrefixMass suzukiPrimeWeight (count + 1) -
      suzukiArchimedeanSlopeConstant) / 2 =
        Real.exp (r / 2) *
          (1 + suzukiArchimedeanPositiveSlopeTail r / (2 * Real.exp (r / 2))) := by
    rw [suzukiFirstTailCorrectedMass_eq_exp_add_tail]
    dsimp [r]
    field_simp [(Real.exp_pos _).ne']
  unfold suzukiFirstTailTransportLinearWork suzukiFirstTailMassLogWork
    suzukiFirstTailMassLogWorkError
  rw [hf, Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
  dsimp [r]
  ring

/-- The arithmetic mass-log work is a one-sided approximation to the actual
work, and the positive error is bounded by the literal normalized Lerch tail. -/
theorem suzukiFirstTailMassLogWorkError_bounds (count : ℕ) :
    0 ≤ suzukiFirstTailMassLogWorkError count ∧
      suzukiFirstTailMassLogWorkError count ≤ suzukiPrimeWeight (count + 1) *
        suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) /
          Real.exp (suzukiFirstTailChebyshevCenter count / 2) := by
  let r := suzukiFirstTailChebyshevCenter count
  let q := suzukiArchimedeanPositiveSlopeTail r / (2 * Real.exp (r / 2))
  have ht := suzukiArchimedeanPositiveSlopeTail_nonneg r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hl : Real.log (1 + q) ≤ q := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + q)
    linarith
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) (suzukiPrimeWeight_nonnegative _))
      (Real.log_nonneg (by linarith : 1 ≤ 1 + q))
  · have h := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (suzukiPrimeWeight_nonnegative (count + 1)))
    unfold suzukiFirstTailMassLogWorkError
    dsimp [q, r] at h
    exact h.trans_eq (by ring)

/-- The positive Lerch slope tail has an explicit exponential bound beyond
the first arithmetic endpoint. -/
theorem suzukiArchimedeanPositiveSlopeTail_le_exp {r : ℝ} (hr : Real.log 2 ≤ r) :
    suzukiArchimedeanPositiveSlopeTail r ≤ (8 / 15 : ℝ) * Real.exp (-5 * r / 2) := by
  have hr0 : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hr
  let q := Real.exp (-2 * r)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq4 : q ≤ (1 / 4 : ℝ) := by
    calc
      q ≤ Real.exp (-(Real.log 2 + Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 4 := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hq1 : q < 1 := by linarith
  have hterm (n : ℕ) : suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4 ≤
      (2 / 5 : ℝ) * Real.exp (-5 * r / 2) * q ^ n := by
    have he : Real.exp (-2 * (((n + 1 : ℕ) : ℝ) + 1 / 4) * r) =
        Real.exp (-5 * r / 2) * q ^ n := by
      dsimp only [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    unfold suzukiPointwiseLerchGapSlopeSummand
    rw [he]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 / 4)).2
    have hn := Nat.cast_nonneg (α := ℝ) n
    have hepos : 0 ≤ Real.exp (-5 * r / 2) * q ^ n := by positivity
    push_cast
    nlinarith
  have hs := (summable_suzukiArchimedeanPositiveSlopeTail hr0).tsum_le_tsum hterm
    ((summable_geometric_of_lt_one hq0 hq1).mul_left ((2 / 5 : ℝ) * Real.exp (-5 * r / 2)))
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at hs
  change suzukiArchimedeanPositiveSlopeTail r ≤ _ at hs
  have he := Real.exp_pos (-5 * r / 2)
  have hd : 0 < 1 - q := by linarith
  have hb : (2 / 5 : ℝ) * Real.exp (-5 * r / 2) * (1 - q)⁻¹ ≤
      (8 / 15 : ℝ) * Real.exp (-5 * r / 2) := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hq4)]
  exact hs.trans hb

/-- The exact replacement error decays exponentially at the actual canonical
center, before the center is bounded in terms of the integer cutoff. -/
theorem suzukiFirstTailMassLogWorkError_le_exp (count : ℕ) :
    suzukiFirstTailMassLogWorkError count ≤
      (8 / 15 : ℝ) * suzukiPrimeWeight (count + 1) *
        Real.exp (-3 * suzukiFirstTailChebyshevCenter count) := by
  let r := suzukiFirstTailChebyshevCenter count
  have ht := suzukiArchimedeanPositiveSlopeTail_le_exp
    (log_two_le_suzukiFirstTailChebyshevCenter count)
  have he : Real.exp (-5 * r / 2) / Real.exp (r / 2) = Real.exp (-3 * r) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ suzukiPrimeWeight (count + 1) * suzukiArchimedeanPositiveSlopeTail r /
        Real.exp (r / 2) := (suzukiFirstTailMassLogWorkError_bounds count).2
    _ ≤ suzukiPrimeWeight (count + 1) * ((8 / 15 : ℝ) * Real.exp (-5 * r / 2)) /
        Real.exp (r / 2) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (suzukiPrimeWeight_nonnegative _)) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, mul_div_assoc, mul_div_assoc, he]; ring

/-- An unconditional inverse-square envelope for the full mass-log replacement
error. In particular, it is summable independently of every zero hypothesis. -/
theorem suzukiFirstTailMassLogWorkError_le_inv_sq (count : ℕ) :
    suzukiFirstTailMassLogWorkError count ≤
      2 * Real.exp 6 / (count + 1 : ℝ) ^ 2 := by
  let x : ℝ := count + 1
  let r := suzukiFirstTailChebyshevCenter count
  have hx : 0 < x := by dsimp [x]; positivity
  have hn : 0 < ((count + 3 : ℕ) : ℝ) := by positivity
  have hw : suzukiPrimeWeight (count + 1) ≤ 3 * x := by
    have hs : (1 : ℝ) ≤ Real.sqrt ((count + 3 : ℕ) : ℝ) :=
      Real.one_le_sqrt.mpr (by norm_cast; omega)
    have hl := (ArithmeticFunction.vonMangoldt_le_log (n := count + 3)).trans
      (Real.log_le_self hn.le)
    have hm : ArithmeticFunction.vonMangoldt (count + 3) /
        Real.sqrt ((count + 3 : ℕ) : ℝ) ≤ ((count + 3 : ℕ) : ℝ) := by
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).2
      exact hl.trans (by nlinarith)
    unfold suzukiPrimeWeight
    simp only [Nat.add_assoc, Nat.reduceAdd]
    refine hm.trans ?_
    dsimp [x]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) count]
  have hr : Real.log x - 2 ≤ r := by
    have hlog : Real.log x ≤ Real.log ((count + 2 : ℕ) : ℝ) :=
      Real.log_le_log hx (by dsimp [x]; push_cast; linarith)
    linarith [log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count]
  have he : Real.exp (-3 * r) ≤ Real.exp 6 / x ^ 3 := by
    calc
      Real.exp (-3 * r) ≤ Real.exp (6 - 3 * Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_sub, show 3 * Real.log x = Real.log (x ^ 3) by
          rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  calc
    _ ≤ (8 / 15 : ℝ) * suzukiPrimeWeight (count + 1) * Real.exp (-3 * r) :=
      suzukiFirstTailMassLogWorkError_le_exp count
    _ ≤ (8 / 15 : ℝ) * (3 * x) * (Real.exp 6 / x ^ 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num)) he
        (Real.exp_pos _).le (by positivity)
    _ = (8 / 5 : ℝ) * Real.exp 6 / x ^ 2 := by field_simp; ring
    _ ≤ _ := by
      change (8 / 5 : ℝ) * Real.exp 6 / x ^ 2 ≤ 2 * Real.exp 6 / x ^ 2
      exact div_le_div_of_nonneg_right (by nlinarith [Real.exp_pos (6 : ℝ)]) (sq_nonneg x)

/-- The exact positive error between the original work and the arithmetic
mass-log work has finite total. -/
theorem summable_suzukiFirstTailMassLogWorkError :
    Summable suzukiFirstTailMassLogWorkError := by
  have hm : Summable (fun n : ℕ => 2 * Real.exp 6 / (n + 1 : ℝ) ^ 2) := by
    have h := ((summable_nat_add_iff 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num))).mul_left (2 * Real.exp 6)
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h
  exact hm.of_nonneg_of_le (fun n => (suzukiFirstTailMassLogWorkError_bounds n).1)
    suzukiFirstTailMassLogWorkError_le_inv_sq

/-- The exact ratio of the corrected old prime mass to the continuous mass
scale at the next integer. It involves only finite arithmetic data. -/
def suzukiFirstTailCorrectedMassRatio (count : ℕ) : ℝ :=
  (screwPrefixMass suzukiPrimeWeight (count + 1) - suzukiArchimedeanSlopeConstant) /
    (2 * Real.sqrt ((count + 3 : ℕ) : ℝ))

/-- The finite corrected mass ratio is strictly positive at every prefix. -/
theorem suzukiFirstTailCorrectedMassRatio_pos (count : ℕ) :
    0 < suzukiFirstTailCorrectedMassRatio count :=
  div_pos (suzukiFirstTailCorrectedMass_pos count) (by positivity)

/-- Exact nonlinear reserve retained by the mass logarithm beyond the bilinear
lower bound. Summability of this reserve is not asserted. -/
def suzukiFirstTailMassLogReserve (count : ℕ) : ℝ :=
  2 * suzukiPrimeWeight (count + 1) *
    (suzukiFirstTailCorrectedMassRatio count - 1 - Real.log (suzukiFirstTailCorrectedMassRatio count))

/-- The retained finite arithmetic reserve has a proved nonnegative sign. -/
theorem suzukiFirstTailMassLogReserve_nonneg (count : ℕ) :
    0 ≤ suzukiFirstTailMassLogReserve count := by
  have hl := Real.log_le_sub_one_of_pos (suzukiFirstTailCorrectedMassRatio_pos count)
  exact mul_nonneg (mul_nonneg (by norm_num) (suzukiPrimeWeight_nonnegative _)) (by linarith)

/-- The mass-log expression retains the entire finite nonlinear reserve
discarded by the simpler bilinear lower bound. -/
theorem suzukiFirstTailMassLogWork_eq_bilinear_add_reserve (count : ℕ) :
    suzukiFirstTailMassLogWork count =
      suzukiFirstTailBilinearWork count + suzukiFirstTailMassLogReserve count := by
  let b : ℝ := ((count + 3 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hm := suzukiFirstTailCorrectedMass_pos count
  have hlog : Real.log (suzukiFirstTailCorrectedMassRatio count) =
      Real.log ((screwPrefixMass suzukiPrimeWeight (count + 1) -
        suzukiArchimedeanSlopeConstant) / 2) - Real.log b / 2 := by
    unfold suzukiFirstTailCorrectedMassRatio
    rw [← div_div, Real.log_div (by positivity) (Real.sqrt_pos.mpr hb).ne', Real.log_sqrt hb.le]
  unfold suzukiFirstTailMassLogWork suzukiFirstTailMassLogReserve suzukiFirstTailBilinearWork
  rw [hlog]
  unfold suzukiFirstTailCorrectedMassRatio suzukiPrimeLocation
  simp only [Nat.add_assoc, Nat.reduceAdd]
  dsimp [b]
  ring

/-- The retained work is the signed logarithm of the exact finite mass ratio,
weighted by the actual next prime-power atom. -/
theorem suzukiFirstTailMassLogWork_eq_neg_two_mul_log_ratio (count : ℕ) :
    suzukiFirstTailMassLogWork count = -2 * suzukiPrimeWeight (count + 1) *
      Real.log (suzukiFirstTailCorrectedMassRatio count) := by
  rw [suzukiFirstTailMassLogWork_eq_bilinear_add_reserve]
  unfold suzukiFirstTailBilinearWork suzukiFirstTailMassLogReserve suzukiFirstTailCorrectedMassRatio
  ring

/-- The original convexity reserve consists of the retained finite arithmetic
reserve plus the now summably controlled Lerch correction. -/
theorem suzukiFirstTailWorkConvexReserve_eq_massLogReserve_add_error (count : ℕ) :
    suzukiFirstTailWorkConvexReserve count =
      suzukiFirstTailMassLogReserve count + suzukiFirstTailMassLogWorkError count := by
  have h₁ := suzukiFirstTailTransportLinearWork_eq_massLog_add_error count
  have h₂ := suzukiFirstTailTransportLinearWork_eq_bilinear_add_reserve count
  rw [suzukiFirstTailMassLogWork_eq_bilinear_add_reserve] at h₁
  linarith

/-- Exact finite-band accounting for the unchanged signed work and its
finite arithmetic replacement. -/
theorem suzuki_signed_work_block_eq_massLog_add_error (start count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) =
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) +
        ∑ n ∈ Finset.range count, suzukiFirstTailMassLogWorkError (start + n) := by
  simp_rw [suzukiFirstTailTransportLinearWork_eq_massLog_add_error]
  exact Finset.sum_add_distrib

private theorem error_le_reciprocal_difference (count : ℕ) :
    suzukiFirstTailMassLogWorkError count ≤ 4 * Real.exp 6 *
      (1 / (count + 1 : ℝ) - 1 / (count + 2 : ℝ)) := by
  let x : ℝ := count + 1
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) count]
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have he : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
  have hi : 1 / x ^ 2 ≤ 2 * (1 / x - 1 / (x + 1)) := by
    rw [he, mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)).2
    nlinarith
  have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * Real.exp 6)
  refine (suzukiFirstTailMassLogWorkError_le_inv_sq count).trans ?_
  convert h using 1 <;> dsimp [x] <;> ring

/-- A telescoping upper bound for the entire error in every finite band,
including the terminal reciprocal rather than silently dropping it. -/
theorem suzukiFirstTailMassLogWorkError_block_le_reciprocal_difference (start count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWorkError (start + n)) ≤
      4 * Real.exp 6 * (1 / (start + 1 : ℝ) - 1 / ((start + count : ℕ) + 1 : ℝ)) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ]
    have he := error_le_reciprocal_difference (start + count)
    have hid : ((start + (count + 1) : ℕ) : ℝ) + 1 = ((start + count : ℕ) : ℝ) + 2 := by
      push_cast
      ring
    rw [hid]
    linarith

/-- Uniform signed error bounds, independent of band length, for the exact
finite arithmetic mass-log replacement of the original work. -/
theorem suzuki_signed_work_block_massLog_error_bounds (start count : ℕ) :
    0 ≤ (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) -
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) ∧
    (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) -
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) ≤
        4 * Real.exp 6 / (start + 1 : ℝ) := by
  rw [suzuki_signed_work_block_eq_massLog_add_error, add_sub_cancel_left]
  constructor
  · exact Finset.sum_nonneg (fun _ _ => (suzukiFirstTailMassLogWorkError_bounds _).1)
  · have h := suzukiFirstTailMassLogWorkError_block_le_reciprocal_difference start count
    have hp : 0 ≤ 4 * Real.exp 6 / ((start + count : ℕ) + 1 : ℝ) := by positivity
    rw [mul_sub, mul_one_div, mul_one_div] at h
    linarith

/-- The cumulative difference has an actual finite limit, given by the sum
of the original positive Lerch correction. -/
theorem suzuki_signed_work_sub_massLog_tendsto :
    Tendsto (fun count : ℕ =>
      (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) -
        ∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork n)
      atTop (𝓝 (∑' n : ℕ, suzukiFirstTailMassLogWorkError n)) := by
  have ht := summable_suzukiFirstTailMassLogWorkError.hasSum.tendsto_sum_nat
  apply ht.congr'
  filter_upwards [] with count
  have he := suzuki_signed_work_block_eq_massLog_add_error 0 count
  simp only [Nat.zero_add] at he
  linarith

/-- The finite-band canonical gap change is exactly mass-log work plus the
positive Lerch error minus the original transport cost. -/
theorem suzukiFirstTailCanonicalGap_add_eq_massLog_add_error_sub_cost (start count : ℕ) :
    suzukiFirstTailCanonicalGap (start + count) = suzukiFirstTailCanonicalGap start +
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) +
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWorkError (start + n)) -
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n) := by
  rw [suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost,
    suzuki_signed_work_block_eq_massLog_add_error]
  ring

/-- Signed finite-band gap bounds retaining the two different error sources:
the original cost tail below and an explicit reciprocal upper error. -/
theorem suzukiFirstTailCanonicalGap_block_massLog_error_bounds (start count : ℕ) :
    -(∑' n : ℕ, suzukiFirstTailTransportCellCost (start + n)) ≤
      suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
        (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) ∧
    suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
      (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n)) ≤
        4 * Real.exp 6 / (start + 1 : ℝ) := by
  have he := suzuki_signed_work_block_massLog_error_bounds start count
  rw [suzuki_signed_work_block_eq_massLog_add_error, add_sub_cancel_left] at he
  have hc := suzukiFirstTailTransportCellCost_block_le_tail start count
  have hc0 : 0 ≤ ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n) :=
    Finset.sum_nonneg (fun _ _ => (suzukiFirstTailTransportCellCost_bounds _).1)
  rw [suzukiFirstTailCanonicalGap_add_eq_massLog_add_error_sub_cost]
  constructor <;> linarith

/-- The finite arithmetic mass-log sum approximates every sufficiently late
canonical gap change with any positive accuracy, uniformly in band length. -/
theorem suzukiFirstTailCanonicalGap_block_massLog_error_uniformly_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      |suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
        (∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork (start + n))| < ε := by
  have ht : Tendsto (fun start : ℕ => 4 * Real.exp 6 / (start + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hc := suzukiFirstTailTransportCellCost_tail_tendsto_zero.eventually (gt_mem_nhds hε)
  filter_upwards [ht.eventually (gt_mem_nhds hε), hc] with start he hc
  intro count
  have hb := suzukiFirstTailCanonicalGap_block_massLog_error_bounds start count
  apply abs_lt.mpr
  constructor <;> linarith

/-- A finite eventual floor for the arithmetic mass-log sum is exactly as
strong as a finite eventual floor for the original signed work. The bounded
positive replacement error is absorbed into the arbitrary floor constant. -/
theorem suzuki_signed_work_eventually_bounded_below_iff_massLog :
    (∃ B : ℝ, ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) ↔
    (∃ B : ℝ, ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork n) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + 4 * Real.exp 6, ?_⟩
    filter_upwards [hB] with count hc
    have he := (suzuki_signed_work_block_massLog_error_bounds 0 count).2
    simp only [Nat.cast_zero, zero_add, div_one] at he
    linarith
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    filter_upwards [hB] with count hc
    have he := (suzuki_signed_work_block_massLog_error_bounds 0 count).1
    simp only [Nat.zero_add] at he
    linarith

/-- The unchanged RH implication now accepts a floor for a wholly finite
arithmetic mass-log sum, with no uncontrolled approximation remainder. -/
theorem riemannHypothesis_of_suzuki_massLog_work_eventually_bounded_below
    (B : ℝ) (hB : ∀ᶠ count : ℕ in atTop, -B ≤
      ∑ n ∈ Finset.range count, suzukiFirstTailMassLogWork n) : RiemannHypothesis := by
  obtain ⟨C, hC⟩ := suzuki_signed_work_eventually_bounded_below_iff_massLog.mpr ⟨B, hB⟩
  exact riemannHypothesis_of_suzuki_signed_work_eventually_bounded_below C hC

end
end RiemannGaussian
