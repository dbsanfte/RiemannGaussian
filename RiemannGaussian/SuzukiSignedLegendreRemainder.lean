/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiMassShiftBudget

/-!
# A signed comparison with the exact finite mass potential

The leading Archimedean exponential and the full corrected arithmetic mass
are compared before either is bounded separately. Their Legendre terms
cancel exactly. The only remaining error is a positive Lerch value tail
minus a nonnegative convexity correction.

This controls the actual canonical gap by a finite prime mass--moment
expression with a vanishing one-sided error. It does not establish the
independent lower bound on that expression required for RH.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped BigOperators Topology

/-- The exact constant left in the Archimedean value after its leading
exponential and linear slope have been removed. -/
def suzukiArchimedeanIntercept : ℝ := suzukiHurwitzLerchTwo 1 / 4 - 8

/-- The full decaying value tail, with the cancelling zeroth Lerch mode
removed but every subsequent mode retained. -/
def suzukiArchimedeanValueTail (r : ℝ) : ℝ :=
  Real.exp (-r / 2) * (suzukiHurwitzLerchTwo (Real.exp (-2 * r)) - 16) / 4

/-- The zeroth mode cancels the decaying exponential exactly in the value,
just as it does in the already proved slope identity. -/
theorem suzukiPointwiseArchimedean_eq_exp_add_linear_sub_valueTail (r : ℝ) :
    suzukiPointwiseArchimedean r = 4 * Real.exp (r / 2) +
      suzukiArchimedeanSlopeConstant * r + suzukiArchimedeanIntercept -
      suzukiArchimedeanValueTail r := by
  unfold suzukiPointwiseArchimedean suzukiArchimedeanSlopeConstant
    suzukiArchimedeanIntercept suzukiArchimedeanValueTail
  ring

private theorem value_tail_series {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : ℕ ↦ Real.exp (-2 * ((n + 1 : ℕ) + 1 / 4 : ℝ) * r) /
      (4 * ((n + 1 : ℕ) + 1 / 4 : ℝ) ^ 2)) (suzukiArchimedeanValueTail r) := by
  let q := Real.exp (-2 * r)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs := summable_suzukiHurwitzLerchTwoSummand hq0 hq1
  have ht := ((summable_nat_add_iff 1).mpr hs).hasSum
  have he := hs.sum_add_tsum_nat_add 1
  have hzero : suzukiHurwitzLerchTwoSummand q 0 = 16 := by
    norm_num [suzukiHurwitzLerchTwoSummand]
  rw [Finset.sum_range_one, hzero] at he
  have hsum : (∑' n : ℕ, suzukiHurwitzLerchTwoSummand q (n + 1)) =
      suzukiHurwitzLerchTwo q - 16 := by
    change 16 + _ = suzukiHurwitzLerchTwo q at he
    linarith
  rw [hsum] at ht
  have hb := ht.mul_left (Real.exp (-r / 2) / 4)
  have hvalue : Real.exp (-r / 2) / 4 * (suzukiHurwitzLerchTwo q - 16) =
      suzukiArchimedeanValueTail r := by
    unfold suzukiArchimedeanValueTail
    dsimp [q]
    ring
  rw [hvalue] at hb
  apply hb.congr_fun
  intro n
  have hexp : Real.exp (-r / 2) * q ^ (n + 1) =
        Real.exp (-2 * ((n + 1 : ℕ) + 1 / 4 : ℝ) * r) := by
      dsimp only [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
  unfold suzukiHurwitzLerchTwoSummand
  rw [← hexp]
  field_simp

/-- The whole value tail is nonnegative and no larger than two fifths of
the exact positive slope tail. -/
theorem suzukiArchimedeanValueTail_bounds {r : ℝ} (hr : 0 < r) :
    0 ≤ suzukiArchimedeanValueTail r ∧
      suzukiArchimedeanValueTail r ≤ (2 / 5 : ℝ) * suzukiArchimedeanPositiveSlopeTail r := by
  have hs := value_tail_series hr
  constructor
  · rw [← hs.tsum_eq]
    exact tsum_nonneg (fun _ ↦ by positivity)
  · have ht := ((summable_suzukiArchimedeanPositiveSlopeTail hr).mul_left (2 / 5 : ℝ))
    have hb := hs.summable.tsum_le_tsum (g := fun n : ℕ ↦
      (2 / 5 : ℝ) * (suzukiPointwiseLerchGapSlopeSummand r (n + 1) / 4)) ?_ ht
    · rw [hs.tsum_eq, tsum_mul_left] at hb
      exact hb
    · intro n
      unfold suzukiPointwiseLerchGapSlopeSummand
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have he := (Real.exp_pos (-2 * ((n + 1 : ℕ) + 1 / 4 : ℝ) * r)).le
      have hp : (0 : ℝ) < ((n + 1 : ℕ) + 1 / 4 : ℝ) := by positivity
      apply (div_le_iff₀ (by positivity : 0 < 4 * ((n + 1 : ℕ) + 1 / 4 : ℝ) ^ 2)).mpr
      field_simp
      push_cast at *
      nlinarith

/-- Retaining the first positive tail mode gives a matching lower bound;
the complete geometric tail gives the displayed upper bound. -/
theorem suzukiArchimedeanValueTail_exp_bounds {r : ℝ} (hr : Real.log 2 ≤ r) :
    (4 / 25 : ℝ) * Real.exp (-5 * r / 2) ≤ suzukiArchimedeanValueTail r ∧
      suzukiArchimedeanValueTail r ≤ (16 / 75 : ℝ) * Real.exp (-5 * r / 2) := by
  have hr0 : 0 < r := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hr
  constructor
  · have hs := value_tail_series hr0
    have h := hs.summable.sum_le_tsum (Finset.range 1) (fun _ _ ↦ by positivity)
    rw [hs.tsum_eq, Finset.sum_range_one] at h
    norm_num at h
    rw [show -5 * r / 2 = -(5 / 2 * r) by ring]
    linarith
  · have h := (suzukiArchimedeanValueTail_bounds hr0).2.trans
      (mul_le_mul_of_nonneg_left (suzukiArchimedeanPositiveSlopeTail_le_exp hr) (by norm_num))
    exact h.trans_eq (by ring)

/-- The finite arithmetic potential uses the complete old prime mass and
first moment, the exact slope constant, and a single endpoint logarithm. -/
def suzukiMassLegendrePotential (count : ℕ) : ℝ :=
  screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) -
    2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
      (Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2) - 1) +
    suzukiArchimedeanIntercept

/-- The nonlinear correction retained when the exponential's center is
replaced by the logarithm of the same corrected finite mass. -/
def suzukiMassLegendreConvexCorrection (count : ℕ) : ℝ :=
  2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
    Real.log (1 + suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) /
      (2 * Real.exp (suzukiFirstTailChebyshevCenter count / 2))) -
    2 * suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count)

/-- Before any estimate, the potential minus the original canonical gap is
exactly the full positive value tail minus its convexity correction. -/
theorem suzukiMassLegendrePotential_sub_gap_eq (count : ℕ) :
    suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count =
      suzukiArchimedeanValueTail (suzukiFirstTailChebyshevCenter count) -
        suzukiMassLegendreConvexCorrection count := by
  let r := suzukiFirstTailChebyshevCenter count
  let T := suzukiArchimedeanPositiveSlopeTail r
  have hT : 0 ≤ T := suzukiArchimedeanPositiveSlopeTail_nonneg r
  have hm := suzukiFirstTailCorrectedMass_eq_exp_add_tail count
  change suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant = 2 * Real.exp (r / 2) + T at hm
  have hlog : Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2) =
      r / 2 + Real.log (1 + T / (2 * Real.exp (r / 2))) := by
    have hf : (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2 =
        Real.exp (r / 2) * (1 + T / (2 * Real.exp (r / 2))) := by rw [hm]; field_simp
    rw [hf, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have hg := suzukiFirstTailResetTransportGap_succ_eq_literalLegendreDefect count
  change suzukiFirstTailCanonicalGap count = suzukiPointwiseArchimedean r -
    r * suzukiOldPrimeMass count +
      screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) at hg
  rw [suzukiPointwiseArchimedean_eq_exp_add_linear_sub_valueTail] at hg
  unfold suzukiMassLegendrePotential suzukiMassLegendreConvexCorrection
  change _ - _ = suzukiArchimedeanValueTail r -
    (2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
      Real.log (1 + T / (2 * Real.exp (r / 2))) - 2 * T)
  rw [hg, hlog]
  nlinarith

/-- The retained convexity correction is nonnegative and quadratic in the
same small slope tail; it is not estimated by the full prime mass. -/
theorem suzukiMassLegendreConvexCorrection_bounds (count : ℕ) :
    0 ≤ suzukiMassLegendreConvexCorrection count ∧
      suzukiMassLegendreConvexCorrection count ≤
        suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count) ^ 2 /
          Real.exp (suzukiFirstTailChebyshevCenter count / 2) := by
  let E := Real.exp (suzukiFirstTailChebyshevCenter count / 2)
  let T := suzukiArchimedeanPositiveSlopeTail (suzukiFirstTailChebyshevCenter count)
  let q := 1 + T / (2 * E)
  have hE : 0 < E := Real.exp_pos _
  have hT : 0 ≤ T := suzukiArchimedeanPositiveSlopeTail_nonneg _
  have hq : 0 < q := by dsimp [q]; positivity
  have hmass : suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant = 2 * E + T :=
    suzukiFirstTailCorrectedMass_eq_exp_add_tail count
  have hEq : 2 * E * q = 2 * E + T := by dsimp [q]; field_simp
  have he : suzukiMassLegendreConvexCorrection count =
      2 * (2 * E + T) * Real.log q - 2 * T := by
    unfold suzukiMassLegendreConvexCorrection
    rw [hmass]
  constructor
  · have hl := mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log hq.le)
      (by positivity : 0 ≤ 4 * E)
    rw [he]
    nlinarith
  · have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq)
      (by positivity : 0 ≤ 2 * (2 * E + T))
    rw [he]
    apply (le_div_iff₀ hE).mpr
    nlinarith

private theorem slope_tail_sq_div_exp_le {r : ℝ} (hr : Real.log 2 ≤ r) :
    suzukiArchimedeanPositiveSlopeTail r ^ 2 / Real.exp (r / 2) ≤
      (8 / 225 : ℝ) * Real.exp (-5 * r / 2) := by
  have hT := suzukiArchimedeanPositiveSlopeTail_nonneg r
  have hbound := suzukiArchimedeanPositiveSlopeTail_le_exp hr
  have hsmall : Real.exp (-3 * r) ≤ (1 / 8 : ℝ) := by
    calc
      _ ≤ Real.exp (-(Real.log 2 + Real.log 2 + Real.log 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
        norm_num
  have heq : Real.exp (-5 * r / 2) ^ 2 / Real.exp (r / 2) =
      Real.exp (-5 * r / 2) * Real.exp (-3 * r) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    norm_num
    ring
  calc
    _ ≤ ((8 / 15 : ℝ) * Real.exp (-5 * r / 2)) ^ 2 / Real.exp (r / 2) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hT hbound 2) (Real.exp_pos _).le
    _ = (64 / 225 : ℝ) * (Real.exp (-5 * r / 2) ^ 2 / Real.exp (r / 2)) := by ring
    _ = (64 / 225 : ℝ) * (Real.exp (-5 * r / 2) * Real.exp (-3 * r)) := by rw [heq]
    _ ≤ (64 / 225 : ℝ) * (Real.exp (-5 * r / 2) * (1 / 8)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le) (by norm_num)
    _ = _ := by ring

/-- The original gap lies immediately below the finite arithmetic potential.
The complete signed error has an exponential bound after cancellation of the
leading mass and transport terms. -/
theorem suzukiMassLegendrePotential_sub_gap_bounds (count : ℕ) :
    0 ≤ suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count ∧
      suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count ≤
        (16 / 75 : ℝ) * Real.exp (-5 * suzukiFirstTailChebyshevCenter count / 2) := by
  have hr := log_two_le_suzukiFirstTailChebyshevCenter count
  have hV := suzukiArchimedeanValueTail_exp_bounds hr
  have hR := suzukiMassLegendreConvexCorrection_bounds count
  have hsmall := hR.2.trans (slope_tail_sq_div_exp_le hr)
  have he := (Real.exp_pos (-5 * suzukiFirstTailChebyshevCenter count / 2)).le
  rw [suzukiMassLegendrePotential_sub_gap_eq]
  constructor <;> linarith

/-- The source-exact comparison error is bounded by an explicit inverse
five-halves power at every original integer cutoff. -/
theorem suzukiMassLegendrePotential_sub_gap_le_inv_five_halves (count : ℕ) :
    suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count ≤
      (16 / 75 : ℝ) * Real.exp 5 / (count + 2 : ℝ) ^ (5 / 2 : ℝ) := by
  have hr := log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
  have hn : (0 : ℝ) < count + 2 := by positivity
  have he : Real.exp (-5 * suzukiFirstTailChebyshevCenter count / 2) ≤
      Real.exp 5 / (count + 2 : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      _ ≤ Real.exp (5 - Real.log (count + 2 : ℝ) * (5 / 2)) :=
        Real.exp_le_exp.mpr (by push_cast at hr; linarith)
      _ = _ := by rw [Real.exp_sub, Real.rpow_def_of_pos hn]
  exact (suzukiMassLegendrePotential_sub_gap_bounds count).2.trans
    ((mul_le_mul_of_nonneg_left he (by norm_num)).trans_eq (by ring))

/-- On every finite band, the signed comparison error is controlled by one
inverse-five-halves allowance at the starting cutoff, regardless of length. -/
theorem suzukiCanonicalGap_block_massLegendre_error_le (start count : ℕ) :
    |(suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start) -
      (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start)| ≤
        (16 / 75 : ℝ) * Real.exp 5 / (start + 2 : ℝ) ^ (5 / 2 : ℝ) := by
  have hs := suzukiMassLegendrePotential_sub_gap_bounds start
  have ht := suzukiMassLegendrePotential_sub_gap_bounds (start + count)
  have hsb := suzukiMassLegendrePotential_sub_gap_le_inv_five_halves start
  have htb := suzukiMassLegendrePotential_sub_gap_le_inv_five_halves (start + count)
  have hden : (start + 2 : ℝ) ^ (5 / 2 : ℝ) ≤
      ((start + count : ℕ) + 2 : ℝ) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) count]) (by norm_num)
  have hmono := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ (16 / 75 : ℝ) * Real.exp 5) (by positivity) hden
  rw [abs_le]
  constructor <;> linarith

/-- The quadrature cost of integrating the mass logarithm across one actual
prime atom. Both endpoint masses and the old-mass logarithm are retained. -/
def suzukiMassLogQuadratureCost (count : ℕ) : ℝ :=
  2 * (suzukiOldPrimeMass (count + 1) - suzukiArchimedeanSlopeConstant) *
      (Real.log ((suzukiOldPrimeMass (count + 1) - suzukiArchimedeanSlopeConstant) / 2) - 1) -
    2 * (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) *
      (Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2) - 1) -
    2 * suzukiPrimeWeight (count + 1) *
      Real.log ((suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) / 2)

/-- Exact summation of the nonlinear mass logarithm into the arithmetic
endpoint potential, with the complete quadrature cost kept signed. -/
theorem suzukiFirstTailMassLogWork_eq_massLegendre_increment_add_cost (count : ℕ) :
    suzukiFirstTailMassLogWork count =
      suzukiMassLegendrePotential (count + 1) - suzukiMassLegendrePotential count +
        suzukiMassLogQuadratureCost count := by
  unfold suzukiFirstTailMassLogWork suzukiMassLegendrePotential suzukiMassLogQuadratureCost
  rw [screwPrefixMoment_succ]
  ring

/-- The quadrature cost is nonnegative and bounded by twice the squared
new atom divided by its own positive corrected old mass. -/
theorem suzukiMassLogQuadratureCost_bounds (count : ℕ) :
    0 ≤ suzukiMassLogQuadratureCost count ∧
      suzukiMassLogQuadratureCost count ≤
        2 * suzukiPrimeWeight (count + 1) ^ 2 /
          (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) := by
  let m := suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant
  let a := suzukiPrimeWeight (count + 1)
  have hm : 0 < m := suzukiFirstTailCorrectedMass_pos count
  have ha : 0 ≤ a := suzukiPrimeWeight_nonnegative _
  have hma : 0 < m + a := by positivity
  have hmass : suzukiOldPrimeMass (count + 1) - suzukiArchimedeanSlopeConstant = m + a := by
    rw [suzukiOldPrimeMass_succ]
    dsimp [m, a]
    ring
  let q := 1 + a / m
  have hq : 0 < q := by dsimp [q]; positivity
  have heq : m * q = m + a := by dsimp [q]; field_simp
  have hlog : Real.log ((m + a) / 2) = Real.log (m / 2) + Real.log q := by
    rw [show (m + a) / 2 = (m / 2) * q by nlinarith,
      Real.log_mul (by positivity) hq.ne']
  have he : suzukiMassLogQuadratureCost count = 2 * (m + a) * Real.log q - 2 * a := by
    unfold suzukiMassLogQuadratureCost
    rw [hmass]
    change 2 * (m + a) * (Real.log ((m + a) / 2) - 1) -
      2 * m * (Real.log (m / 2) - 1) - 2 * a * Real.log (m / 2) = _
    rw [hlog]
    ring
  constructor
  · have hl := mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log hq.le)
      (by positivity : 0 ≤ 2 * m)
    rw [he]
    nlinarith
  · have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq)
      (by positivity : 0 ≤ 2 * (m + a))
    rw [he]
    change _ ≤ 2 * a ^ 2 / m
    apply (le_div_iff₀ hm).mpr
    nlinarith

/-- The original recurrence transports the signed sum of the quadrature,
Lerch, and canonical-cell costs exactly into the new endpoint error. -/
theorem suzukiCanonicalGap_succ_eq_massLegendre_increment_add_signed_cost (count : ℕ) :
    suzukiFirstTailCanonicalGap (count + 1) - suzukiFirstTailCanonicalGap count =
      suzukiMassLegendrePotential (count + 1) - suzukiMassLegendrePotential count +
        (suzukiMassLogQuadratureCost count + suzukiFirstTailMassLogWorkError count -
          suzukiFirstTailTransportCellCost count) := by
  rw [suzukiFirstTailCanonicalGap_succ,
    suzukiFirstTailTransportLinearWork_eq_massLog_add_error,
    suzukiFirstTailMassLogWork_eq_massLegendre_increment_add_cost]
  ring

/-- Summing whole signed cells preserves cancellation of their leading
positive quadrature cost against the negative canonical transport cost. -/
theorem sum_suzuki_signed_cost_eq_gap_sub_massLegendre (start count : ℕ) :
    (∑ j ∈ Finset.range count,
      (suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
        suzukiFirstTailTransportCellCost (start + j))) =
      (suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start) -
        (suzukiMassLegendrePotential (start + count) - suzukiMassLegendrePotential start) := by
  have he (j : ℕ) :
      suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
        suzukiFirstTailTransportCellCost (start + j) =
      (suzukiFirstTailCanonicalGap (start + (j + 1)) - suzukiMassLegendrePotential (start + (j + 1))) -
        (suzukiFirstTailCanonicalGap (start + j) - suzukiMassLegendrePotential (start + j)) := by
    have h := suzukiCanonicalGap_succ_eq_massLegendre_increment_add_signed_cost (start + j)
    simp only [Nat.add_assoc] at h
    linarith
  simp_rw [he]
  rw [Finset.sum_range_sub (fun j ↦
    suzukiFirstTailCanonicalGap (start + j) - suzukiMassLegendrePotential (start + j)) count]
  simp only [Nat.add_zero]
  ring

/-- The complete signed cost combination has an inverse-five-halves band
bound, obtained before taking absolute values of its separate components. -/
theorem abs_sum_suzuki_signed_cost_le_inv_five_halves (start count : ℕ) :
    |∑ j ∈ Finset.range count,
      (suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
        suzukiFirstTailTransportCellCost (start + j))| ≤
      (16 / 75 : ℝ) * Real.exp 5 / (start + 2 : ℝ) ^ (5 / 2 : ℝ) := by
  rw [sum_suzuki_signed_cost_eq_gap_sub_massLegendre]
  exact suzukiCanonicalGap_block_massLegendre_error_le start count

private theorem error_allowance_tendsto_zero :
    Tendsto (fun start : ℕ ↦
      (16 / 75 : ℝ) * Real.exp 5 / (start + 2 : ℝ) ^ (5 / 2 : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun start : ℕ ↦ (start : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp hx)

/-- The exact finite arithmetic potential converges to the original gap
in absolute difference, without a normalization or an arithmetic hypothesis. -/
theorem suzukiMassLegendrePotential_sub_gap_tendsto_zero :
    Tendsto (fun count : ℕ ↦ suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count)
      atTop (𝓝 0) := by
  exact squeeze_zero (fun count ↦ (suzukiMassLegendrePotential_sub_gap_bounds count).1)
    suzukiMassLegendrePotential_sub_gap_le_inv_five_halves error_allowance_tendsto_zero

/-- Whole signed cost blocks become uniformly small with their length left
arbitrary. The leading separate quadrature and transport bounds are not added. -/
theorem sum_suzuki_signed_cost_uniformly_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      |∑ j ∈ Finset.range count,
        (suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
          suzukiFirstTailTransportCellCost (start + j))| < ε := by
  filter_upwards [error_allowance_tendsto_zero.eventually (gt_mem_nhds hε)] with start hstart
  intro count
  exact (abs_sum_suzuki_signed_cost_le_inv_five_halves start count).trans_lt hstart

private def archimedeanLegendreError (r : ℝ) : ℝ :=
  suzukiArchimedeanIntercept - suzukiPointwiseArchimedean r +
    r * suzukiPointwiseArchimedeanSlope r -
    2 * (suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant) *
      (Real.log ((suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant) / 2) - 1)

private theorem corrected_slope_pos {r : ℝ} (hr : 0 < r) :
    0 < suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant := by
  rw [suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail hr]
  have hT := suzukiArchimedeanPositiveSlopeTail_nonneg r
  have hE := Real.exp_pos (r / 2)
  linarith

private theorem hasDerivAt_archimedeanLegendreError {r : ℝ} (hr : 0 < r) :
    HasDerivAt archimedeanLegendreError
      ((r - 2 * Real.log ((suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant) / 2)) *
        suzukiSmoothCurvature r) r := by
  have hA := hasDerivAt_suzukiPointwiseArchimedean hr
  have hS := hasDerivAt_suzukiPointwiseArchimedeanSlope hr
  have hm := hS.sub_const suzukiArchimedeanSlopeConstant
  have hp := corrected_slope_pos hr
  have hlog := (hm.div_const 2).log (div_ne_zero hp.ne' (by norm_num))
  have hphi := (hm.const_mul 2).mul (hlog.sub_const 1)
  have h := (((hasDerivAt_const r suzukiArchimedeanIntercept).sub hA).add
    ((hasDerivAt_id r).mul hS)).sub hphi
  apply h.congr_deriv
  simp only [id_eq]
  field_simp
  ring

private theorem archimedeanLegendreError_antitone :
    AntitoneOn archimedeanLegendreError (Set.Ici (Real.log 2)) := by
  have hpos (r : ℝ) (hr : r ∈ Set.Ici (Real.log 2)) : 0 < r :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hr
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    (fun r hr ↦ (hasDerivAt_archimedeanLegendreError (hpos r hr)).continuousAt.continuousWithinAt)
    (fun r hr ↦ (hasDerivAt_archimedeanLegendreError
      (hpos r (interior_subset hr))).differentiableAt.differentiableWithinAt)
  intro r hr
  have hrI := interior_subset hr
  have hr0 := hpos r hrI
  rw [(hasDerivAt_archimedeanLegendreError hr0).deriv]
  have hmass : 2 * Real.exp (r / 2) ≤
      suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant := by
    rw [suzukiPointwiseArchimedeanSlope_eq_exp_add_constant_add_positiveTail hr0]
    linarith [suzukiArchimedeanPositiveSlopeTail_nonneg r]
  have hlog := Real.log_le_log (Real.exp_pos (r / 2))
    (show Real.exp (r / 2) ≤
      (suzukiPointwiseArchimedeanSlope r - suzukiArchimedeanSlopeConstant) / 2 by linarith)
  rw [Real.log_exp] at hlog
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
    (suzukiSmoothCurvature_pos_of_log_two_le hrI).le

private theorem error_eq_at_center (count : ℕ) :
    suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count =
      archimedeanLegendreError (suzukiFirstTailChebyshevCenter count) := by
  have hm : suzukiPointwiseArchimedeanSlope (suzukiFirstTailChebyshevCenter count) =
      suzukiOldPrimeMass count := by
    rw [suzukiOldPrimeMass, screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass]
    simpa only [Nat.add_assoc] using
      suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass count
  have hg := suzukiFirstTailResetTransportGap_succ_eq_literalLegendreDefect count
  change suzukiFirstTailCanonicalGap count =
    suzukiPointwiseArchimedean (suzukiFirstTailChebyshevCenter count) -
      suzukiFirstTailChebyshevCenter count * suzukiOldPrimeMass count +
        screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) at hg
  rw [hg]
  unfold archimedeanLegendreError suzukiMassLegendrePotential
  rw [hm]
  ring

/-- The one-sided comparison error decreases along the actual arithmetic
mass schedule. This retains the sign of the net cost at every step. -/
theorem antitone_suzukiMassLegendrePotential_sub_gap :
    Antitone (fun count : ℕ ↦ suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count) := by
  apply antitone_nat_of_succ_le
  intro count
  rw [error_eq_at_center, error_eq_at_center]
  exact archimedeanLegendreError_antitone
    (log_two_le_suzukiFirstTailChebyshevCenter count)
    (log_two_le_suzukiFirstTailChebyshevCenter (count + 1))
    (suzukiFirstTailChebyshevCenter_le_succ count)

/-- The full signed cost combination is nonnegative and has the sharp
vanishing band allowance. Its positive and negative components cancel before
the bound is taken, and the remaining sign is retained. -/
theorem sum_suzuki_signed_cost_bounds (start count : ℕ) :
    0 ≤ (∑ j ∈ Finset.range count,
      (suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
        suzukiFirstTailTransportCellCost (start + j))) ∧
    (∑ j ∈ Finset.range count,
      (suzukiMassLogQuadratureCost (start + j) + suzukiFirstTailMassLogWorkError (start + j) -
        suzukiFirstTailTransportCellCost (start + j))) ≤
      (16 / 75 : ℝ) * Real.exp 5 / (start + 2 : ℝ) ^ (5 / 2 : ℝ) := by
  constructor
  · rw [sum_suzuki_signed_cost_eq_gap_sub_massLegendre]
    have h := antitone_suzukiMassLegendrePotential_sub_gap (Nat.le_add_right start count)
    linarith
  · exact (le_abs_self _).trans (abs_sum_suzuki_signed_cost_le_inv_five_halves start count)

end
end RiemannGaussian
