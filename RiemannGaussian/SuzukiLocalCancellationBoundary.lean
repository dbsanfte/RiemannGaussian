/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiArithmeticCancellation
import RiemannGaussian.SuzukiActualCutoff
import RiemannGaussian.SuzukiLocalCancellation

/-!
# The unconditional boundary condition for local Suzuki cancellation

The existing prime number theorem controls the actual weighted mass and the
canonical gap. Exact endpoint comparison transfers that cancellation to the
literal logarithmic-average signal, including its real-cutoff interpolation.
This removes the density mode in the local recurrence; it gives no
subexponential one-sided bound.
-/

namespace RiemannGaussian
noncomputable section
open Filter
open scoped Topology

private theorem endpoint_atTop :
    Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)

/-- PNT makes the corrected mass ratio at the literal integer endpoint tend to one. -/
theorem suzukiLocalActualEndpointMassRatio_tendsto_one :
    Tendsto suzukiActualEndpointMassRatio atTop (𝓝 1) := by
  have hm := suzukiWeightedMass_div_sqrt_tendsto_two.comp endpoint_atTop
  have hc : Tendsto (fun n : ℕ => suzukiArchimedeanSlopeConstant /
      Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp endpoint_atTop)
  have hh := (hm.sub hc).div_const 2
  norm_num only [sub_zero, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards with n
  have he : suzukiOldPrimeMass n = suzukiChebyshevWeightedMass ((n + 2 : ℕ) : ℝ) := by
    simpa [suzukiOldPrimeMass, Nat.add_assoc] using
      screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass (n + 1)
  change (suzukiChebyshevWeightedMass _ / _ - _ / _) / 2 = _
  rw [suzukiActualEndpointMassRatio, he]
  ring

private theorem entropy_tendsto_zero :
    Tendsto (fun n => suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio n))
      atTop (𝓝 0) := by
  have hm := suzukiLocalActualEndpointMassRatio_tendsto_one
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hm
  have hh := ((hm.mul hl).sub hm).add_const 1
  simpa [suzukiChebyshevRelativeEntropy] using hh

private theorem potential_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => suzukiMassLegendrePotential n /
      Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have he := suzukiMassLegendrePotential_sub_gap_tendsto_zero.div_atTop
    (Real.tendsto_sqrt_atTop.comp endpoint_atTop)
  have hh := he.add suzukiCanonicalGap_div_sqrt_tendsto_zero
  norm_num only [add_zero] at hh
  apply hh.congr'
  filter_upwards with n
  simp only [Function.comp_def]
  ring

/-- The literal logarithmic average is smaller than square-root scale at integer endpoints. -/
theorem suzukiLocalLogAverage_nat_add_two_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => suzukiChebyshevLogAverageError ((n + 2 : ℕ) : ℝ) /
      Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log ((n + 2 : ℕ) : ℝ) /
      Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
        endpoint_atTop
  have hc : Tendsto (fun n : ℕ => suzukiArchimedeanIntercept /
      Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp endpoint_atTop)
  have hh := (((hl.const_mul suzukiArchimedeanSlopeConstant).add hc).sub
    (entropy_tendsto_zero.const_mul 4)).sub potential_div_sqrt_tendsto_zero
  norm_num only [mul_zero, add_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards with n
  have he := suzukiMassLegendrePotential_eq_actualEndpoint_sub_entropy n
  have hs : Real.sqrt ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith only [he]

/-- A uniform finite allowance controls both signs of interpolation inside every cutoff cell. -/
theorem abs_suzukiLocalLogAverage_sub_floor_le {x : ℝ} (hx : 1 ≤ x) :
    |suzukiChebyshevLogAverageError x -
      suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ)| ≤ 16 := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNr : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN
  have hNp : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by linarith
  have hxp : 0 < x := by linarith
  have hNx := Nat.floor_le hxp.le
  have hxN := Nat.lt_floor_add_one x
  have hsN : 1 ≤ Real.sqrt (⌊x⌋₊ : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hNr
  have hdiff : Real.sqrt x - Real.sqrt (⌊x⌋₊ : ℝ) ≤ 1 := by
    nlinarith [Real.sq_sqrt hxp.le, Real.sq_sqrt hNp.le,
      Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - Real.sqrt (⌊x⌋₊ : ℝ) - 1)]
  have hm : 0 ≤ suzukiChebyshevWeightedMass (⌊x⌋₊ : ℝ) := by
    have he := suzukiChebyshevMassAbel_eq hNr
    change _ = suzukiChebyshevWeightedMass (⌊x⌋₊ : ℝ) at he
    rw [← he]
    apply Finset.sum_nonneg
    intro n _
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      ArithmeticFunction.vonMangoldt_nonneg
  have hl : 0 ≤ Real.log (x / (⌊x⌋₊ : ℝ)) :=
    Real.log_nonneg ((one_le_div hNp).mpr hNx)
  have hhi := suzukiChebyshevLogAverageError_le_floor_add_inv_sqrt hx
  have hh : 12 / Real.sqrt (⌊x⌋₊ : ℝ) ≤ 12 := by
    exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have he := suzukiChebyshevLogAverageError_cell_eq hx
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hl hm]

/-- PNT cancellation holds for the literal logarithmic average at all real cutoffs. -/
theorem suzukiLocalLogAverage_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => suzukiChebyshevLogAverageError x / Real.sqrt x)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => suzukiChebyshevLogAverageError (n : ℝ) /
      Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).mp suzukiLocalLogAverage_nat_add_two_div_sqrt_tendsto_zero
  have hf := (hn.comp (tendsto_nat_floor_atTop (α := ℝ))).abs
  have hc : Tendsto (fun x : ℝ => (16 : ℝ) / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hh := hf.add hc
  simp only [abs_zero, add_zero] at hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hh
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxp : 0 < x := by linarith
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNp : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsN : 0 < Real.sqrt (⌊x⌋₊ : ℝ) := Real.sqrt_pos.mpr hNp
  have hsle := Real.sqrt_le_sqrt (Nat.floor_le hxp.le)
  have hb := abs_suzukiLocalLogAverage_sub_floor_le hx
  have ha : |suzukiChebyshevLogAverageError x| ≤
      |suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ)| + 16 := by
    have := abs_add_le (suzukiChebyshevLogAverageError x -
      suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ))
      (suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ))
    simp only [sub_add_cancel] at this
    linarith
  simp only [Real.norm_eq_abs, Function.comp_def, abs_div,
    abs_of_pos hs, abs_of_pos hsN]
  calc
    _ ≤ (|suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ)| + 16) / Real.sqrt x :=
      div_le_div_of_nonneg_right ha hs.le
    _ = |suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ)| / Real.sqrt x +
        16 / Real.sqrt x := add_div _ _ _
    _ ≤ |suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ)| / Real.sqrt (⌊x⌋₊ : ℝ) +
        16 / Real.sqrt x := by
      exact add_le_add
        (div_le_div_of_nonneg_left (abs_nonneg (suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ))) hsN hsle)
        le_rfl

/-- The actual signal has no surviving density mode: `S(t) / exp(t/2) → 0`. -/
theorem suzukiLocalSignal_div_exp_tendsto_zero :
    Tendsto (fun t : ℝ => suzukiChebyshevLogAverageLaplaceSignal t / Real.exp (t / 2))
      atTop (𝓝 0) := by
  have hh := (suzukiLocalLogAverage_div_sqrt_tendsto_zero.comp Real.tendsto_exp_atTop).neg
  simpa only [Function.comp_def, neg_zero, suzukiChebyshevLogAverageLaplaceSignal,
    neg_div, Real.exp_half] using hh

private theorem shifted_signal_div_exp (r : ℝ) :
    Tendsto (fun t : ℝ => suzukiChebyshevLogAverageLaplaceSignal (t + r) /
      Real.exp (t / 2)) atTop (𝓝 0) := by
  have hh := (suzukiLocalSignal_div_exp_tendsto_zero.comp
    (tendsto_atTop_add_const_right atTop r tendsto_id)).mul_const (Real.exp (r / 2))
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards with t
  change suzukiChebyshevLogAverageLaplaceSignal (t + r) /
    Real.exp ((t + r) / 2) * Real.exp (r / 2) = _
  rw [add_div, Real.exp_add]
  field_simp

/-- The full second difference satisfies the unconditional PNT boundary. -/
theorem suzukiLocalSecondDifference_div_exp_tendsto_zero :
    Tendsto (fun t : ℝ => suzukiLocalSecondDifference t / Real.exp (t / 2))
      atTop (𝓝 0) := by
  have hh := ((shifted_signal_div_exp (2 * Real.log 2)).sub
    ((shifted_signal_div_exp (Real.log 2)).const_mul 2)).add
      suzukiLocalSignal_div_exp_tendsto_zero
  simp only [mul_zero, sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards with t
  unfold suzukiLocalSecondDifference
  ring

/-- The boundary term in the exact backward recurrence vanishes on every lattice. -/
theorem suzukiLocalSecondDifference_lattice_boundary (t : ℝ) :
    Tendsto (fun n : ℕ => (Real.sqrt 2)⁻¹ ^ n *
      suzukiLocalSecondDifference (t + n * Real.log 2)) atTop (𝓝 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Tendsto (fun n : ℕ => t + n * Real.log 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.atTop_mul_const hlog)
  have hh := (suzukiLocalSecondDifference_div_exp_tendsto_zero.comp ht).const_mul
    (Real.exp (t / 2))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards with n
  have he : Real.exp ((t + n * Real.log 2) / 2) =
      Real.exp (t / 2) * Real.sqrt 2 ^ n := by
    rw [show (t + n * Real.log 2) / 2 = t / 2 + n * (Real.log 2 / 2) by ring,
      Real.exp_add, Real.exp_nat_mul, Real.exp_half (Real.log 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change Real.exp (t / 2) * (suzukiLocalSecondDifference _ / _) = _
  rw [he, inv_pow]
  field_simp

/-- Density cancellation and PNT give `G(exp t) = o(exp(t/2))`, with no power saving asserted. -/
theorem suzukiLocalPrimeComparison_div_exp_tendsto_zero :
    Tendsto (fun t : ℝ => suzukiLocalPrimeComparison t / Real.exp (t / 2))
      atTop (𝓝 0) := by
  have h3 := shifted_signal_div_exp (3 * Real.log 2)
  have h2 := (shifted_signal_div_exp (2 * Real.log 2)).const_mul (2 + Real.sqrt 2)
  have h1 := (shifted_signal_div_exp (Real.log 2)).const_mul (1 + 2 * Real.sqrt 2)
  have h0 := suzukiLocalSignal_div_exp_tendsto_zero.const_mul (Real.sqrt 2)
  have hh := ((h3.sub h2).add h1).sub h0
  simp only [mul_zero, sub_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [suzukiLocalPrimeComparison_eq_four_shifts ht]
  ring

/-- The exact real-base prime comparison is unconditionally sub-square-root. -/
theorem suzukiLocalArithmeticComparison_div_sqrt_tendsto_zero :
    Tendsto (fun X : ℝ => suzukiLocalArithmeticComparison X / Real.sqrt X)
      atTop (𝓝 0) := by
  have hh := suzukiLocalPrimeComparison_div_exp_tendsto_zero.comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  change suzukiLocalPrimeComparison (Real.log X) / Real.exp (Real.log X / 2) = _
  rw [← suzukiLocalArithmeticComparison_exp, Real.exp_half, Real.exp_log hX]

end
end RiemannGaussian
