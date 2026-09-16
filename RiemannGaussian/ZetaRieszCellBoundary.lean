/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCells

/-!
# Signed corrections at the actual divisor breakpoints

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCellBoundary
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeCells

/-- The convex hinge remainder of one actual divisor breakpoint. -/
def hingeRemainder (a x y : ℝ) : ℝ :=
  max 0 (a - y) - max 0 (a - x) + (y - x) * (if x < a then 1 else 0)

/-- Each crossed hinge has a nonnegative overshoot before its Mobius sign. -/
theorem hingeRemainder_nonneg (a x y : ℝ) : 0 ≤ hingeRemainder a x y := by
  unfold hingeRemainder
  by_cases hx : x < a
  · rw [if_pos hx, max_eq_right (by linarith : 0 ≤ a - x), mul_one]
    have h := le_max_right 0 (a - y)
    linarith
  · rw [if_neg hx, max_eq_left (by linarith : a - x ≤ 0), mul_zero, sub_zero, add_zero]
    exact le_max_left _ _

/-- No boundary remainder occurs without a change in the active hinge. -/
theorem hingeRemainder_eq_zero {a x y : ℝ} (h : (x < a ↔ y < a)) :
    hingeRemainder a x y = 0 := by
  unfold hingeRemainder
  by_cases hx : x < a
  · have hy := h.mp hx
    rw [if_pos hx, max_eq_right (by linarith : 0 ≤ a - x),
      max_eq_right (by linarith : 0 ≤ a - y), mul_one]
    ring
  · have hy : ¬ y < a := fun hy => hx (h.mpr hy)
    rw [if_neg hx, max_eq_left (by linarith : a - x ≤ 0),
      max_eq_left (by linarith : a - y ≤ 0)]
    ring

/-- A crossed divisor pays at most its actual prime-logarithm displacement. -/
theorem hingeRemainder_le_gap (a x y : ℝ) : hingeRemainder a x y ≤ |y - x| := by
  unfold hingeRemainder
  by_cases hx : x < a <;> by_cases hy : y < a
  · rw [if_pos hx, max_eq_right (by linarith : 0 ≤ a - x),
      max_eq_right (by linarith : 0 ≤ a - y), mul_one]
    have := abs_nonneg (y - x)
    linarith
  · rw [if_pos hx, max_eq_right (by linarith : 0 ≤ a - x),
      max_eq_left (by linarith : a - y ≤ 0), mul_one, abs_of_nonneg (by linarith : 0 ≤ y - x)]
    linarith
  · rw [if_neg hx, max_eq_left (by linarith : a - x ≤ 0),
      max_eq_right (by linarith : 0 ≤ a - y), mul_zero, abs_of_nonpos (by linarith : y - x ≤ 0)]
    linarith
  · rw [if_neg hx, max_eq_left (by linarith : a - x ≤ 0),
      max_eq_left (by linarith : a - y ≤ 0), mul_zero]
    have := abs_nonneg (y - x)
    linarith

/-- Only actual cofactor divisors whose breakpoint was crossed are eligible. -/
def crossedDivisors (L : ℝ) (n : ℕ) (x y : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d => ¬ (x < L - Real.log d ↔ y < L - Real.log d))

/-- Keep the signs of all actual crossed divisor overshoots. -/
def boundaryCorrection (L : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    hingeRemainder (L - Real.log d) x y

/-- The boundary correction is supported on the literal short divisor
window, not on the complete divisor mass. -/
theorem boundaryCorrection_eq_crossed (L : ℝ) (n : ℕ) (x y : ℝ) :
    boundaryCorrection L n x y =
      ∑ d ∈ crossedDivisors L n x y, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        hingeRemainder (L - Real.log d) x y := by
  unfold boundaryCorrection crossedDivisors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : x < L - Real.log d ↔ y < L - Real.log d
  · simp only [h, not_true_eq_false, if_false, hingeRemainder_eq_zero h, mul_zero]
  · rw [if_pos h]

/-- A local absolute relaxation charges only crossed divisors and the
actual gap; the stronger preceding identity retains their Mobius signs. -/
theorem abs_boundaryCorrection_le (L : ℝ) (n : ℕ) (x y : ℝ) :
    |boundaryCorrection L n x y| ≤
      |y - x| * ∑ d ∈ crossedDivisors L n x y, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [boundaryCorrection_eq_crossed, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul, abs_of_nonneg (hingeRemainder_nonneg _ _ _), mul_comm |y - x|]
  exact mul_le_mul_of_nonneg_left (hingeRemainder_le_gap _ _ _) (abs_nonneg _)

/-- The signed cell slope is the complete active-hinge indicator sum. -/
theorem cellSlope_eq_indicator (L : ℝ) (n : ℕ) (x : ℝ) :
    cellSlope L n x = ∑ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (if x < L - Real.log d then 1 else 0) := by
  unfold cellSlope activeDivisors
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have h : Real.log d < L - x ↔ x < L - Real.log d := by constructor <;> intro h <;> linarith
  simp only [h, mul_ite, mul_one, mul_zero]

/-- The correction is the exact first-order remainder, with no absolute
value applied to its signed crossed-divisor sum. -/
theorem boundaryCorrection_eq_difference (L : ℝ) (n : ℕ) (x y : ℝ) :
    boundaryCorrection L n x y = VaughanLogAverage.riesz (L - y) n -
      VaughanLogAverage.riesz (L - x) n + (y - x) * cellSlope L n x := by
  have ht (d : ℕ) : ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      hingeRemainder (L - Real.log d) x y =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * max 0 (L - y - Real.log d) -
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * max 0 (L - x - Real.log d) +
      (y - x) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (if x < L - Real.log d then 1 else 0)) := by
    unfold hingeRemainder
    rw [show L - Real.log d - y = L - y - Real.log d by ring,
      show L - Real.log d - x = L - x - Real.log d by ring]
    ring
  unfold boundaryCorrection
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← cellSlope_eq_indicator]
  rfl

/-- Every target profile consists of two exact signed cell moments and
the signed overshoots of only the crossed divisor breakpoints. -/
theorem targetProfile_eq_affine_sub_boundary (L : ℝ) (n : ℕ) (x y : ℝ) :
    targetProfile L n y = targetProfile L n x + (y - x) * cellSlope L n x -
      boundaryCorrection L n x y := by
  rw [boundaryCorrection_eq_difference]
  unfold targetProfile
  ring

/-- A common divisor cell removes the boundary correction exactly. -/
theorem boundaryCorrection_eq_zero_of_cell (L : ℝ) (n : ℕ) (x y : ℝ)
    (hcell : activeDivisors L n y = activeDivisors L n x) :
    boundaryCorrection L n x y = 0 := by
  have h := targetProfile_eq_affine_sub_boundary L n x y
  rw [targetProfile_eq_affine L n x y hcell] at h
  linarith

/-- The full complex prime moments retain the original support mask,
filter, cofactor, logarithmic displacement and arbitrary prior weights. -/
def primePacketMoment (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n k : ℕ) : ℂ :=
  ∑ q ∈ Q, eta q * bandAmplitude L P N t (q * n) * ((Real.log q - x : ℝ) : ℂ) ^ k

/-- The entire boundary packet keeps its signed cofactor overshoots and
complex prime phases coupled. -/
def primePacketBoundary (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ q ∈ Q, eta q * bandAmplitude L P N t (q * n) *
    (boundaryCorrection L n x (Real.log q) : ℂ)

/-- At arbitrary target and prime widths, the entire packet is exactly
two coupled complex prime moments minus the crossed-divisor correction. -/
theorem prime_packet_eq_moment_pair (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n) :
    (∑ q ∈ Q, eta q * bandWeight L P N t (q * n)) =
      (targetProfile L n x : ℂ) * primePacketMoment L x P N t Q eta n 0 +
      (cellSlope L n x : ℂ) * primePacketMoment L x P N t Q eta n 1 -
      primePacketBoundary L x P N t Q eta n := by
  unfold primePacketMoment primePacketBoundary
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [bandWeight_eq_amplitude_mul_riesz, riesz_prime_eq_target L (hQ q hq).1 (hQ q hq).2,
    targetProfile_eq_affine_sub_boundary L n x (Real.log q)]
  push_cast
  ring

/-- Only the signed boundary packet is relaxed; its error pays the
literal crossed-divisor mass, preserving both main complex moments. -/
theorem norm_primePacketBoundary_le (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n : ℕ) :
    ‖primePacketBoundary L x P N t Q eta n‖ ≤
      ∑ q ∈ Q, ‖eta q‖ * ‖bandAmplitude L P N t (q * n)‖ *
        (|Real.log q - x| * ∑ d ∈ crossedDivisors L n x (Real.log q),
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) := by
  unfold primePacketBoundary
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_boundaryCorrection_le L n x (Real.log q)) (by positivity)

end
end RiemannGaussian.ZetaRieszCellBoundary
