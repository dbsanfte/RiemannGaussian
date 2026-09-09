/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Tactic

/-!
# Exact secant bounds for the phase contact equations

The structural optimizer problem is a polynomial contact system in four
cosines, four positive contact masses, and an efficiency parameter. To
certify a root by contraction, this module keeps exact divided differences
of the Chebyshev polynomials and bounds their variation on `[-1,1]`.

The intentionally loose bound `6^n` is sufficient for a small root-isolation
ball. These are analytic ingredients for the existence proof; no optimizer
or root is assumed or declared to have been constructed here.
-/

namespace RiemannGaussian

noncomputable section

/-- The actual Chebyshev polynomial evaluated at a phase cosine. -/
def phaseChebyshevValue (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

/-- Evaluating the polynomial at a cosine gives the original harmonic
phase used by the positive-kernel optimization problem. -/
theorem phaseChebyshevValue_cos (n : ℕ) (t : ℝ) :
    phaseChebyshevValue n (Real.cos t) = Real.cos ((n : ℝ) * t) := by
  simp [phaseChebyshevValue]

private theorem phaseChebyshevValue_zero (x : ℝ) : phaseChebyshevValue 0 x = 1 := by
  simp [phaseChebyshevValue]

private theorem phaseChebyshevValue_one (x : ℝ) : phaseChebyshevValue 1 x = x := by
  simp [phaseChebyshevValue]

private theorem phaseChebyshevValue_add_two (n : ℕ) (x : ℝ) :
    phaseChebyshevValue (n + 2) x =
      2 * x * phaseChebyshevValue (n + 1) x - phaseChebyshevValue n x := by
  simp [phaseChebyshevValue, Polynomial.Chebyshev.T_add_two]

/-- A polynomial divided difference, defined at coincident inputs too,
without dividing by `x-y`. -/
def phaseChebyshevSecant (x y : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * phaseChebyshevValue (n + 1) x +
      2 * y * phaseChebyshevSecant x y (n + 1) - phaseChebyshevSecant x y n

/-- The secant polynomial retains the exact difference, including when
the two cosine arguments coincide. -/
theorem phaseChebyshev_sub_eq_mul_secant (n : ℕ) (x y : ℝ) :
    phaseChebyshevValue n x - phaseChebyshevValue n y =
      (x - y) * phaseChebyshevSecant x y n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [phaseChebyshevValue_zero, phaseChebyshevSecant]
  | one => simp [phaseChebyshevValue_one, phaseChebyshevSecant]
  | more n ih0 ih1 =>
    rw [phaseChebyshevValue_add_two, phaseChebyshevValue_add_two, phaseChebyshevSecant]
    linear_combination 2 * y * ih1 - ih0

/-- A uniform coefficient-growth allowance for the evaluated Chebyshev
polynomials throughout the entire cosine interval. -/
theorem abs_phaseChebyshevValue_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |phaseChebyshevValue n x| ≤ (6 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [phaseChebyshevValue_zero]
  | one => simpa [phaseChebyshevValue_one] using hx.trans (by norm_num : (1 : ℝ) ≤ 6)
  | more n ih0 ih1 =>
    rw [phaseChebyshevValue_add_two]
    have h := abs_sub (2 * x * phaseChebyshevValue (n + 1) x) (phaseChebyshevValue n x)
    simp only [abs_mul, abs_two] at h
    have hp : |x| * |phaseChebyshevValue (n + 1) x| ≤ (6 : ℝ) ^ (n + 1) := by
      exact (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans (by simpa using ih1)
    rw [pow_succ] at hp
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) n]

/-- Uniform control of the exact divided difference on the cosine square. -/
theorem abs_phaseChebyshevSecant_le (n : ℕ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |phaseChebyshevSecant x y n| ≤ (6 : ℝ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [phaseChebyshevSecant]
  | one => norm_num [phaseChebyshevSecant]
  | more n ih0 ih1 =>
    rw [phaseChebyshevSecant]
    have h := abs_sub
      (2 * phaseChebyshevValue (n + 1) x + 2 * y * phaseChebyshevSecant x y (n + 1))
      (phaseChebyshevSecant x y n)
    have h' := abs_add_le (2 * phaseChebyshevValue (n + 1) x)
      (2 * y * phaseChebyshevSecant x y (n + 1))
    simp only [abs_mul, abs_two] at h'
    have ht := abs_phaseChebyshevValue_le (n + 1) hx
    have hp : |y| * |phaseChebyshevSecant x y (n + 1)| ≤ (6 : ℝ) ^ (n + 1) := by
      exact (mul_le_mul_of_nonneg_right hy (abs_nonneg _)).trans (by simpa using ih1)
    rw [pow_succ] at ht hp
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) n]

/-- The exact secant identity gives a uniform Lipschitz bound for every
Chebyshev value used by the contact system. -/
theorem abs_phaseChebyshevValue_sub_le (n : ℕ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |phaseChebyshevValue n x - phaseChebyshevValue n y| ≤ (6 : ℝ) ^ n * |x - y| := by
  rw [phaseChebyshev_sub_eq_mul_secant, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_phaseChebyshevSecant_le n hx hy) (abs_nonneg _)

/-- A quantitative bound on the secant's deviation from its diagonal
value. This controls the error of the contact system's linearization without
discarding the exact difference identity. -/
theorem abs_phaseChebyshevSecant_sub_diagonal_le (n : ℕ) {x y c : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hc : |c| ≤ 1) :
    |phaseChebyshevSecant x y n - phaseChebyshevSecant c c n| ≤
      (6 : ℝ) ^ n * (|x - c| + |y - c|) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [phaseChebyshevSecant]; positivity
  | one => simp [phaseChebyshevSecant]; positivity
  | more n ih0 ih1 =>
    have he : phaseChebyshevSecant x y (n + 2) - phaseChebyshevSecant c c (n + 2) =
        2 * (phaseChebyshevValue (n + 1) x - phaseChebyshevValue (n + 1) c) +
        2 * y * (phaseChebyshevSecant x y (n + 1) - phaseChebyshevSecant c c (n + 1)) +
        2 * (y - c) * phaseChebyshevSecant c c (n + 1) -
        (phaseChebyshevSecant x y n - phaseChebyshevSecant c c n) := by
      simp only [phaseChebyshevSecant]
      ring
    rw [he]
    have ht := abs_phaseChebyshevValue_sub_le (n + 1) hx hc
    have hd := abs_phaseChebyshevSecant_le (n + 1) hc hc
    have hyprod : |y| * |phaseChebyshevSecant x y (n + 1) -
        phaseChebyshevSecant c c (n + 1)| ≤
        (6 : ℝ) ^ (n + 1) * (|x - c| + |y - c|) :=
      (mul_le_mul_of_nonneg_right hy (abs_nonneg _)).trans (by simpa using ih1)
    have hcprod := mul_le_mul_of_nonneg_left hd (abs_nonneg (y - c))
    have htri : ∀ a b c d : ℝ, |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
      intro a b c d
      calc
        _ ≤ |a + b + c| + |d| := abs_sub _ _
        _ ≤ (|a + b| + |c|) + |d| := by linarith [abs_add_le (a + b) c]
        _ ≤ _ := by linarith [abs_add_le a b]
    have hbound := htri
      (2 * (phaseChebyshevValue (n + 1) x - phaseChebyshevValue (n + 1) c))
      (2 * y * (phaseChebyshevSecant x y (n + 1) - phaseChebyshevSecant c c (n + 1)))
      (2 * (y - c) * phaseChebyshevSecant c c (n + 1))
      (phaseChebyshevSecant x y n - phaseChebyshevSecant c c n)
    simp only [abs_mul, abs_two] at hbound
    rw [pow_succ] at ht hcprod hyprod
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    have hpos := mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) n)
      (add_nonneg (abs_nonneg (x - c)) (abs_nonneg (y - c)))
    nlinarith only [hbound, ht, hcprod, hyprod, ih0, hpos]

end

end RiemannGaussian
