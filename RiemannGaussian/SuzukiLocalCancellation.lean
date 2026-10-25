/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiPositivityRH

/-!
# Source-exact local cancellation of the Suzuki signal

The second forward difference cancels all old prime history, leaving a
triangular packet of the actual von Mangoldt weights. A further difference
cancels the exponential density. These are exact identities, with no
arithmetic bound on the remaining signed packet asserted.
-/

namespace RiemannGaussian
noncomputable section
open scoped BigOperators

/-- A triangular packet of width `2*h`, including its zero endpoints. -/
def suzukiLocalTriangle (h v : ℝ) : ℝ := max 0 (h - |v - h|)

/-- The second difference of a positive hinge is exactly the triangle. -/
theorem suzukiLocalTriangle_eq_hinge_difference {h : ℝ} (hh : 0 ≤ h) (t v : ℝ) :
    max 0 (t + 2 * h - v) - 2 * max 0 (t + h - v) + max 0 (t - v) =
      suzukiLocalTriangle h (v - t) := by
  unfold suzukiLocalTriangle
  rcases le_total v t with hv | hv
  · rw [max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith), abs_of_nonpos (by linarith),
      max_eq_left (by linarith)]
    ring
  · rcases le_total v (t + h) with hvh | hvh
    · rw [max_eq_right (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith), abs_of_nonpos (by linarith),
        max_eq_right (by linarith)]
      ring
    · rcases le_total v (t + 2 * h) with hv2 | hv2
      · rw [max_eq_right (by linarith), max_eq_left (by linarith),
          max_eq_left (by linarith), abs_of_nonneg (by linarith),
          max_eq_right (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_left (by linarith),
          max_eq_left (by linarith), abs_of_nonneg (by linarith),
          max_eq_left (by linarith)]
        ring

/-- The triangular atom vanishes before its left endpoint. -/
theorem suzukiLocalTriangle_eq_zero_of_nonpos {h v : ℝ} (hh : 0 ≤ h) (hv : v ≤ 0) :
    suzukiLocalTriangle h v = 0 := by
  unfold suzukiLocalTriangle
  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]

/-- The triangular atom vanishes at and after its right endpoint. -/
theorem suzukiLocalTriangle_eq_zero_of_two_mul_le {h v : ℝ} (hh : 0 ≤ h)
    (hv : 2 * h ≤ v) : suzukiLocalTriangle h v = 0 := by
  unfold suzukiLocalTriangle
  rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]

/-- The literal prime prefix can be enlarged by zero hinges, retaining every
von Mangoldt coefficient and the exact real cutoff. -/
theorem suzukiPointwisePrimeContribution_eq_sum_hinges {s T : ℝ} (hsT : s ≤ T) :
    suzukiPointwisePrimeContribution s =
      ∑ n ∈ suzukiArithmeticPrimeWindow T,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * max 0 (s - Real.log n) := by
  classical
  have hsub : suzukiArithmeticPrimeWindow s ⊆ suzukiArithmeticPrimeWindow T := by
    intro n hn
    rw [mem_suzukiArithmeticPrimeWindow_iff] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Real.exp_le_exp.mpr hsT)⟩
  calc
    _ = ∑ n ∈ suzukiArithmeticPrimeWindow s,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * max 0 (s - Real.log n) := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn1, hnexp⟩ := mem_suzukiArithmeticPrimeWindow_iff.mp hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog := (Real.log_le_iff_le_exp hnpos).mpr hnexp
      simp only [suzukiPointwisePrimeTerm, max_eq_right (sub_nonneg.mpr hlog)]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro n hnT hns
      obtain ⟨hn1, _⟩ := mem_suzukiArithmeticPrimeWindow_iff.mp hnT
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnexp : Real.exp s < n := by
        by_contra h
        exact hns (mem_suzukiArithmeticPrimeWindow_iff.mpr ⟨hn1, le_of_not_gt h⟩)
      have hlog := (Real.lt_log_iff_exp_lt hnpos).mpr hnexp
      rw [max_eq_left (by linarith), mul_zero]

/-- The finite local packet at logarithmic base `t`; all prime powers remain. -/
def suzukiLocalPrimePacket (t : ℝ) : ℝ :=
  ∑ n ∈ suzukiArithmeticPrimeWindow (t + 2 * Real.log 2),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      suzukiLocalTriangle (Real.log 2) (Real.log n - t)

/-- The second difference of the complete literal Suzuki signal. -/
def suzukiLocalSecondDifference (t : ℝ) : ℝ :=
  suzukiChebyshevLogAverageLaplaceSignal (t + 2 * Real.log 2) -
    2 * suzukiChebyshevLogAverageLaplaceSignal (t + Real.log 2) +
      suzukiChebyshevLogAverageLaplaceSignal t

/-- The fixed signed comparison of two overlapping, source-exact packets. -/
def suzukiLocalPrimeComparison (t : ℝ) : ℝ :=
  Real.sqrt 2 * suzukiLocalPrimePacket t - suzukiLocalPrimePacket (t + Real.log 2)

/-- Every old prime hinge cancels in the literal second difference. -/
theorem suzukiLocalPrimePacket_eq_prime_second_difference (t : ℝ) :
    suzukiLocalPrimePacket t =
      suzukiPointwisePrimeContribution (t + 2 * Real.log 2) -
        2 * suzukiPointwisePrimeContribution (t + Real.log 2) +
          suzukiPointwisePrimeContribution t := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [suzukiPointwisePrimeContribution_eq_sum_hinges (le_refl _),
    suzukiPointwisePrimeContribution_eq_sum_hinges
      (show t + Real.log 2 ≤ t + 2 * Real.log 2 by linarith),
    suzukiPointwisePrimeContribution_eq_sum_hinges
      (show t ≤ t + 2 * Real.log 2 by linarith)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  unfold suzukiLocalPrimePacket
  apply Finset.sum_congr rfl
  intro n _
  linear_combination -(ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
    suzukiLocalTriangle_eq_hinge_difference hh t (Real.log n)

/-- Enlarging the finite packet cutoff introduces only zero terms. -/
theorem suzukiLocalPrimePacket_eq_sum_of_le {t T : ℝ}
    (hT : t + 2 * Real.log 2 ≤ T) :
    suzukiLocalPrimePacket t =
      ∑ n ∈ suzukiArithmeticPrimeWindow T,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          suzukiLocalTriangle (Real.log 2) (Real.log n - t) := by
  classical
  unfold suzukiLocalPrimePacket
  apply Finset.sum_subset
  · intro n hn
    rw [mem_suzukiArithmeticPrimeWindow_iff] at hn ⊢
    exact ⟨hn.1, hn.2.trans (Real.exp_le_exp.mpr hT)⟩
  · intro n hnT hnt
    obtain ⟨hn1, _⟩ := mem_suzukiArithmeticPrimeWindow_iff.mp hnT
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnexp : Real.exp (t + 2 * Real.log 2) < n := by
      by_contra h
      exact hnt (mem_suzukiArithmeticPrimeWindow_iff.mpr ⟨hn1, le_of_not_gt h⟩)
    have hlog := (Real.lt_log_iff_exp_lt hnpos).mpr hnexp
    rw [suzukiLocalTriangle_eq_zero_of_two_mul_le
      (Real.log_nonneg (by norm_num)) (by linarith), mul_zero]

/-- The single fixed signed kernel retaining both overlapping packets. -/
def suzukiLocalSignedKernel (v : ℝ) : ℝ :=
  Real.sqrt 2 * suzukiLocalTriangle (Real.log 2) v -
    suzukiLocalTriangle (Real.log 2) (v - Real.log 2)

/-- The signed packet is one finite sum of the actual von Mangoldt weights
against its fixed signed kernel, retaining all overlaps and endpoints. -/
theorem suzukiLocalPrimeComparison_eq_sum_signed_kernel (t : ℝ) :
    suzukiLocalPrimeComparison t =
      ∑ n ∈ suzukiArithmeticPrimeWindow (t + 3 * Real.log 2),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          suzukiLocalSignedKernel (Real.log n - t) := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold suzukiLocalPrimeComparison
  rw [suzukiLocalPrimePacket_eq_sum_of_le (show t + 2 * Real.log 2 ≤
    t + 3 * Real.log 2 by linarith),
    suzukiLocalPrimePacket_eq_sum_of_le (show t + Real.log 2 + 2 * Real.log 2 ≤
      t + 3 * Real.log 2 by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [show Real.log n - (t + Real.log 2) = Real.log n - t - Real.log 2 by ring]
  unfold suzukiLocalSignedKernel
  ring

/-- The arithmetic packet `A(X)` at a real multiplicative base, with its
literal `log(n/X)` atom and exact finite cutoff. -/
def suzukiLocalArithmeticPacket (X : ℝ) : ℝ :=
  ∑ n ∈ suzukiArithmeticPrimeWindow (Real.log X + 2 * Real.log 2),
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      suzukiLocalTriangle (Real.log 2) (Real.log ((n : ℝ) / X))

/-- The exact real-base prime comparison `G(X) = sqrt(2)*A(X)-A(2X)`. -/
def suzukiLocalArithmeticComparison (X : ℝ) : ℝ :=
  Real.sqrt 2 * suzukiLocalArithmeticPacket X - suzukiLocalArithmeticPacket (2 * X)

/-- Positive real multiplicative bases agree exactly with logarithmic time. -/
theorem suzukiLocalArithmeticPacket_eq_log_packet {X : ℝ} (hX : 0 < X) :
    suzukiLocalArithmeticPacket X = suzukiLocalPrimePacket (Real.log X) := by
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, _⟩ := mem_suzukiArithmeticPrimeWindow_iff.mp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.log_div hnpos.ne' hX.ne']

/-- The arithmetic comparison at `exp t` is the exact time comparison. -/
theorem suzukiLocalArithmeticComparison_exp (t : ℝ) :
    suzukiLocalArithmeticComparison (Real.exp t) = suzukiLocalPrimeComparison t := by
  rw [suzukiLocalArithmeticComparison,
    suzukiLocalArithmeticPacket_eq_log_packet (Real.exp_pos t),
    suzukiLocalArithmeticPacket_eq_log_packet (mul_pos (by norm_num) (Real.exp_pos t)),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos t).ne', Real.log_exp]
  rw [add_comm (Real.log 2) t]
  rfl

/-- The real arithmetic packet cutoff is exactly `n ≤ 4X`. -/
theorem mem_suzukiLocalArithmeticPacket_window_iff {X : ℝ} (hX : 0 < X) (n : ℕ) :
    n ∈ suzukiArithmeticPrimeWindow (Real.log X + 2 * Real.log 2) ↔
      1 ≤ n ∧ (n : ℝ) ≤ 4 * X := by
  rw [mem_suzukiArithmeticPrimeWindow_iff, Real.exp_add, Real.exp_log hX,
    show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [show X * (2 * 2) = 4 * X by ring]

private theorem local_exp_shift (t : ℝ) :
    Real.exp ((t + Real.log 2) / 2) = Real.sqrt 2 * Real.exp (t / 2) := by
  rw [add_div, Real.exp_add, Real.exp_half (Real.log 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

private theorem local_exp_two_shifts (t : ℝ) :
    Real.exp ((t + 2 * Real.log 2) / 2) = 2 * Real.exp (t / 2) := by
  rw [show (t + 2 * Real.log 2) / 2 = t / 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The literal signal's second difference is the density minus the actual
finite triangular prime packet, with no historical or boundary remainder. -/
theorem suzukiLocalSecondDifference_eq_main_sub_packet {t : ℝ} (ht : 0 ≤ t) :
    suzukiLocalSecondDifference t =
      4 * (Real.sqrt 2 - 1) ^ 2 * Real.exp (t / 2) - suzukiLocalPrimePacket t := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [suzukiLocalSecondDifference,
    suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime (by linarith),
    suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime (by linarith),
    suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht,
    suzukiLocalPrimePacket_eq_prime_second_difference, local_exp_shift,
    local_exp_two_shifts]
  linear_combination -4 * Real.exp (t / 2) *
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- The final shift cancels the complete exponential density exactly. -/
theorem suzukiLocalPrimeComparison_eq_shift_second_difference {t : ℝ} (ht : 0 ≤ t) :
    suzukiLocalPrimeComparison t =
      suzukiLocalSecondDifference (t + Real.log 2) -
        Real.sqrt 2 * suzukiLocalSecondDifference t := by
  have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [suzukiLocalSecondDifference_eq_main_sub_packet (by linarith),
    suzukiLocalSecondDifference_eq_main_sub_packet ht, local_exp_shift,
    suzukiLocalPrimeComparison]
  ring

/-- The exact four-shift filter of the original Suzuki signal, in increasing
shift order with coefficients `-sqrt 2, 1+2*sqrt 2, -(2+sqrt 2), 1`. -/
theorem suzukiLocalPrimeComparison_eq_four_shifts {t : ℝ} (ht : 0 ≤ t) :
    suzukiLocalPrimeComparison t =
      -(Real.sqrt 2) * suzukiChebyshevLogAverageLaplaceSignal t +
        (1 + 2 * Real.sqrt 2) *
          suzukiChebyshevLogAverageLaplaceSignal (t + Real.log 2) -
        (2 + Real.sqrt 2) *
          suzukiChebyshevLogAverageLaplaceSignal (t + 2 * Real.log 2) +
        suzukiChebyshevLogAverageLaplaceSignal (t + 3 * Real.log 2) := by
  rw [suzukiLocalPrimeComparison_eq_shift_second_difference ht]
  unfold suzukiLocalSecondDifference
  rw [show t + Real.log 2 + 2 * Real.log 2 = t + 3 * Real.log 2 by ring,
    show t + Real.log 2 + Real.log 2 = t + 2 * Real.log 2 by ring]
  ring

end
end RiemannGaussian
