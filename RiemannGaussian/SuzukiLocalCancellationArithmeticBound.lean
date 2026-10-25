/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationPrimitiveBound
import RiemannGaussian.SuzukiLocalCancellationPrimePowers
import RiemannGaussian.SuzukiLocalCancellationExplicitBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An explicit inherited bound for the signed ordinary-prime sum

The seven-eighths baseline transfers to exponent three-eighths for the
actual local arithmetic filter. This does not supply the all-positive-
exponent lower bound required by the local Suzuki RH criterion.
-/

namespace RiemannGaussian
noncomputable section

private theorem local_primitive_envelope_on_window {t s : ℝ} (ht : 0 ≤ t)
    (hs : s ∈ Set.Icc t (t + 3 * Real.log 2)) :
    |RosserSchoenfeldPrimePrimitive.value s -
      (Real.exp s - 1 - Real.log (2 * Real.pi) * s)| ≤
      ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) *
        Real.exp ((7 / 8 : ℝ) * (t + 3 * Real.log 2)) := by
  apply (suzukiLocalPrimePrimitive_error_le_seven_eighths (ht.trans hs.1)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (by norm_num))

private theorem local_scaled_primitive_envelope_le (t : ℝ) :
    24 * (((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) *
      Real.exp ((7 / 8 : ℝ) * (t + 3 * Real.log 2))) * Real.exp (-t / 2) ≤
      (192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24)) * Real.exp ((3 / 8 : ℝ) * t) := by
  have he : Real.exp ((7 / 8 : ℝ) * (3 * Real.log 2)) ≤ 8 := by
    calc
      _ ≤ Real.exp (3 * Real.log 2) := Real.exp_le_exp.mpr (by
        nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
      _ = 8 := by
        rw [show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring,
          Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  calc
    _ = (24 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) *
      Real.exp ((3 / 8 : ℝ) * t)) * Real.exp ((7 / 8 : ℝ) * (3 * Real.log 2)) := by
      have hex : Real.exp ((7 / 8 : ℝ) * (t + 3 * Real.log 2)) *
          Real.exp (-t / 2) = Real.exp ((3 / 8 : ℝ) * t) *
          Real.exp ((7 / 8 : ℝ) * (3 * Real.log 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      linear_combination (24 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24)) * hex
    _ ≤ (24 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) *
      Real.exp ((3 / 8 : ℝ) * t)) * 8 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- Applying the proved twice-Abel estimate to the existing primitive
envelope gives an explicit global three-eighths bound in logarithmic time. -/
theorem abs_suzukiLocalPrimeComparison_le_three_eighths {t : ℝ} (ht : 0 ≤ t) :
    |suzukiLocalPrimeComparison t| ≤
      (192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24)) * Real.exp ((3 / 8 : ℝ) * t) := by
  exact (abs_suzukiLocalPrimeComparison_le_of_primitive_envelope
    (by positivity) (fun s hs => local_primitive_envelope_on_window ht hs)).trans
      (local_scaled_primitive_envelope_le t)

/-- The complete real-cutoff comparison, with its inherited exponent and
an explicit constant. Every real base at least one is covered. -/
theorem abs_suzukiLocalArithmeticComparison_le_three_eighths {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalArithmeticComparison X| ≤
      (192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24)) * X ^ (3 / 8 : ℝ) := by
  have hpos : 0 < X := zero_lt_one.trans_le hX
  have he := suzukiLocalArithmeticComparison_exp (Real.log X)
  rw [Real.exp_log hpos] at he
  rw [he, Real.rpow_def_of_pos hpos]
  simpa only [mul_comm] using abs_suzukiLocalPrimeComparison_le_three_eighths
    (Real.log_nonneg hX)

/-- The same explicit exponent for the signed ordinary-prime sum, paying
the full proper-prime-power deletion cost in the constant. -/
theorem abs_suzukiLocalOrdinaryArithmeticComparison_le_three_eighths
    {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalOrdinaryArithmeticComparison X| ≤
      (192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) +
        54 * ((Real.sqrt 2 + 1) * Real.log 2)) * X ^ (3 / 8 : ℝ) := by
  have hp := abs_suzukiLocalArithmeticComparison_sub_ordinary_le hX
  have hg := abs_suzukiLocalArithmeticComparison_le_three_eighths hX
  have hb : |suzukiLocalOrdinaryArithmeticComparison X| ≤
      |suzukiLocalArithmeticComparison X| +
        |suzukiLocalArithmeticComparison X - suzukiLocalOrdinaryArithmeticComparison X| := by
    convert abs_sub (suzukiLocalArithmeticComparison X)
      (suzukiLocalArithmeticComparison X - suzukiLocalOrdinaryArithmeticComparison X) using 1
    congr 1
    ring
  have hx : 1 ≤ X ^ (3 / 8 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hc : 0 ≤ 54 * ((Real.sqrt 2 + 1) * Real.log 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hx hc]

/-- An unconditional one-sided estimate for the actual ordinary-prime
sum. Exponent three-eighths is the inherited baseline, not target (T). -/
theorem suzukiLocalOrdinaryArithmeticComparison_lower_bound_three_eighths
    {X : ℝ} (hX : 1 ≤ X) :
    -(192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) +
        54 * ((Real.sqrt 2 + 1) * Real.log 2)) * X ^ (3 / 8 : ℝ) ≤
      suzukiLocalOrdinaryArithmeticComparison X := by
  have hb := (abs_le.mp (abs_suzukiLocalOrdinaryArithmeticComparison_le_three_eighths hX)).1
  simpa only [neg_mul] using hb

private theorem local_arithmetic_constant_le_two_hundred :
    192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) +
      54 * ((Real.sqrt 2 + 1) * Real.log 2) ≤ 200 := by
  have hp : Real.pi ^ 2 ≤ (63 / 20 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hl : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hprod : (Real.sqrt 2 + 1) * Real.log 2 ≤ (5 / 2 : ℝ) * (7 / 10) :=
    mul_le_mul (by linarith) hl (Real.log_nonneg (by norm_num)) (by norm_num)
  nlinarith

/-- A simple numerical constant for the complete signed ordinary-prime
comparison, at every real cutoff at least one. -/
theorem abs_suzukiLocalOrdinaryArithmeticComparison_le_two_hundred
    {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalOrdinaryArithmeticComparison X| ≤ 200 * X ^ (3 / 8 : ℝ) := by
  exact (abs_suzukiLocalOrdinaryArithmeticComparison_le_three_eighths hX).trans
    (mul_le_mul_of_nonneg_right local_arithmetic_constant_le_two_hundred (by positivity))

/-- A concrete one-sided ordinary-prime bound inherited from the existing
seven-eighths theorem. The all-exponent target remains a separate premise. -/
theorem suzukiLocalOrdinaryArithmeticComparison_lower_bound_two_hundred
    {X : ℝ} (hX : 1 ≤ X) :
    -200 * X ^ (3 / 8 : ℝ) ≤ suzukiLocalOrdinaryArithmeticComparison X := by
  have hb := (abs_le.mp (abs_suzukiLocalOrdinaryArithmeticComparison_le_two_hundred hX)).1
  simpa only [neg_mul] using hb

end
end RiemannGaussian
