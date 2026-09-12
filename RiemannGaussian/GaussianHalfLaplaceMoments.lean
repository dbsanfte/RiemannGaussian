/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Signed recurrence for every damped half-Gaussian moment

Polynomial moments of the Gaussian exist at every real damping. Integration
by parts retains the endpoint in the first recurrence and gives the exact
three-term recurrence at all higher orders. This permits polynomial cosine
enclosures to be integrated without taking absolute values of their terms.
-/

namespace RiemannGaussian.GaussianHalfLaplaceMoments
noncomputable section
open Filter MeasureTheory Set Topology
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds

/-- The entire damped Gaussian monomial, before integration. -/
def atom (n : ℕ) (x t : ℝ) : ℝ := t ^ n * (window 1 t * Real.exp (-x * t))

/-- The actual half-line moment, including every polynomial order. -/
def moment (n : ℕ) (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), atom n x t

private theorem norm_atom_le (n : ℕ) (x t : ℝ) :
    ‖atom n x t‖ ≤ Real.exp (x ^ 2 / 2) *
      (|t| ^ n * Real.exp (-(1 / 2) * t ^ 2)) := by
  have he : window 1 t * Real.exp (-x * t) ≤
      Real.exp (x ^ 2 / 2) * Real.exp (-(1 / 2) * t ^ 2) := by
    unfold window
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (t + x)]
  calc
    _ = |t| ^ n * (window 1 t * Real.exp (-x * t)) := by
      simp [atom, norm_mul, Real.norm_eq_abs, window]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg t) n)]

/-- Every polynomial moment is absolutely integrable, also at negative damping. -/
theorem integrable_atom (n : ℕ) (x : ℝ) : Integrable (atom n x) := by
  have hg : Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-(1 / 2) * t ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ) < 1 / 2) (show (-1 : ℝ) < (n : ℝ) by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
  have hb : Integrable (fun t : ℝ ↦ Real.exp (x ^ 2 / 2) *
      (|t| ^ n * Real.exp (-(1 / 2) * t ^ 2))) := by
    simpa [norm_mul, Real.norm_eq_abs, abs_pow, Real.exp_pos] using
      hg.norm.const_mul (Real.exp (x ^ 2 / 2))
  apply hb.mono' (by unfold atom window; fun_prop)
  exact Eventually.of_forall (norm_atom_le n x)

/-- Every damped polynomial Gaussian has zero boundary value at positive infinity. -/
theorem tendsto_atom (n : ℕ) (x : ℝ) : Tendsto (atom n x) atTop (𝓝 0) := by
  have hf : (atTop : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  have hg := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ) < 1 / 2) (n : ℝ)).mono_left hf
  have hb : Tendsto (fun t : ℝ ↦ Real.exp (x ^ 2 / 2) *
      (|t| ^ n * Real.exp (-(1 / 2) * t ^ 2))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using hg.const_mul (Real.exp (x ^ 2 / 2))
  exact squeeze_zero_norm (norm_atom_le n x) hb

/-- Order zero is precisely the original half-Gaussian transform. -/
theorem moment_zero (x : ℝ) : moment 0 x = halfGaussian 1 x := by
  simp [moment, atom, halfGaussian]

private theorem hasDerivAt_atom_zero (x t : ℝ) :
    HasDerivAt (atom 0 x) (-2 * atom 1 x t - x * atom 0 x t) t := by
  have h := ((((hasDerivAt_id t).pow 2).neg).exp).mul
    (((hasDerivAt_id t).const_mul (-x)).exp)
  convert! h using 1
  · ext u
    simp [atom, window]
  · simp [atom, window]
    ring

/-- The first recurrence keeps the nonzero Euler endpoint exactly. -/
theorem moment_one (x : ℝ) : 2 * moment 1 x + x * moment 0 x = 1 := by
  have hi := ((integrable_atom 1 x).const_mul (-2)).sub ((integrable_atom 0 x).const_mul x)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun t _ ↦ hasDerivAt_atom_zero x t) hi.integrableOn (tendsto_atom 0 x)
  rw [integral_sub ((integrable_atom 1 x).const_mul (-2)).integrableOn
    ((integrable_atom 0 x).const_mul x).integrableOn,
    integral_const_mul, integral_const_mul] at h
  rw [show atom 0 x 0 = 1 by simp [atom, window]] at h
  rw [zero_sub] at h
  change -2 * moment 1 x - x * moment 0 x = -1 at h
  linarith

private theorem hasDerivAt_atom_succ (n : ℕ) (x t : ℝ) :
    HasDerivAt (atom (n + 1) x)
      (((n + 1 : ℕ) : ℝ) * atom n x t - x * atom (n + 1) x t -
        2 * atom (n + 2) x t) t := by
  have h := ((hasDerivAt_id t).pow (n + 1)).mul (hasDerivAt_atom_zero x t)
  convert! h using 1
  · ext u
    simp [atom]
  · simp only [atom, pow_zero, pow_one, one_mul, Pi.pow_apply, id_eq, Nat.add_sub_cancel]
    rw [pow_succ, show t ^ (n + 2) = t ^ n * t ^ 2 by ring]
    ring

/-- All higher orders satisfy the exact signed three-term recurrence. -/
theorem moment_recurrence (n : ℕ) (x : ℝ) :
    2 * moment (n + 2) x + x * moment (n + 1) x = ((n + 1 : ℕ) : ℝ) * moment n x := by
  have hfirst : Integrable (fun t : ℝ ↦ ((n + 1 : ℕ) : ℝ) * atom n x t -
      x * atom (n + 1) x t) := ((integrable_atom n x).const_mul _).sub
    ((integrable_atom (n + 1) x).const_mul x)
  have hi := hfirst.sub ((integrable_atom (n + 2) x).const_mul 2)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun t _ ↦ hasDerivAt_atom_succ n x t) hi.integrableOn (tendsto_atom (n + 1) x)
  rw [integral_sub hfirst.integrableOn
    ((integrable_atom (n + 2) x).const_mul 2).integrableOn,
    integral_sub ((integrable_atom n x).const_mul ((n + 1 : ℕ) : ℝ)).integrableOn
      ((integrable_atom (n + 1) x).const_mul x).integrableOn,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  rw [show atom (n + 1) x 0 = 0 by simp [atom], sub_zero] at h
  change ((n + 1 : ℕ) : ℝ) * moment n x - x * moment (n + 1) x - 2 * moment (n + 2) x = 0 at h
  linarith

/-- The first moment is an affine expression in the original transform. -/
theorem moment_one_eq (x : ℝ) : moment 1 x = (1 - x * moment 0 x) / 2 := by
  linarith [moment_one x]

/-- The recurrence can be evaluated without estimating any signed coefficient. -/
theorem moment_succ_succ (n : ℕ) (x : ℝ) :
    moment (n + 2) x = (((n + 1 : ℕ) : ℝ) * moment n x - x * moment (n + 1) x) / 2 := by
  linarith [moment_recurrence n x]

/-- Every finite signed polynomial integrates term by term against the same Gaussian. -/
theorem integral_sum_atoms (S : Finset ℕ) (k : ℕ → ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), ∑ n ∈ S, c n * atom (k n) x t) = ∑ n ∈ S, c n * moment (k n) x := by
  rw [integral_finsetSum S (fun n _ ↦ ((integrable_atom (k n) x).const_mul (c n)).integrableOn)]
  simp only [integral_const_mul, moment]

end
end RiemannGaussian.GaussianHalfLaplaceMoments
