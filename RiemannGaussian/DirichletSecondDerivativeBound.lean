/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.LogarithmicSecondDerivativeTest
import RiemannGaussian.FiniteAbelVariation
import RiemannGaussian.ZetaFiniteDifferencing

/-!
# Second-derivative cancellation for the complete Dirichlet terms

The actual real damping is positive and decreasing when the real exponent
is nonnegative. Exact Abel summation transports the full logarithmic
second-derivative estimate through that damping with only its initial
value as cost. The terminal theorem bounds literal `zetaPrimeFeature`
terms on a positive dyadic block, without excluding resonances.

These are ordinary Dirichlet coefficients equal to one. Additional prime,
sieve or moment weights still require their own variation or correlation
estimates; their cancellation is not inferred from a smooth phase.
-/

namespace RiemannGaussian.DirichletSecondDerivativeBound
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase
open scoped Classical

/-- The actual radial Dirichlet factor decreases throughout the positive
axis for every nonnegative real exponent. -/
theorem damping_antitoneOn {σ : ℝ} (hσ : 0 ≤ σ) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-σ * Real.log x)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (Real.log_le_log hx hxy) (neg_nonpos.mpr hσ))

/-- The complete damping preserves the second-derivative cancellation
bound on every actual dyadic block, including the empty block. -/
theorem damped_bound {σ t X a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X) (htX : t ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N,
      (Real.exp (-σ * Real.log (a + n)) : ℂ) * rotation (phase t (a + n))‖ ≤
        ((4 * N * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
          2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi)) *
            Real.exp (-σ * Real.log a) := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ Real.exp (-σ * Real.log (a + n)) :=
      fun _ _ ↦ (Real.exp_pos _).le
    have hm : AntitoneOn (fun n : ℕ ↦ Real.exp (-σ * Real.log (a + n)))
        (Set.Icc 0 N) := by
      intro i _ j _ hij
      apply damping_antitoneOn hσ
      · change 0 < a + (i : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) i]
      · change 0 < a + (j : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      · have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ Finset.range (n + 1), rotation (phase t (a + k))‖ ≤
          (4 * (N + 1 : ℕ) * Real.sqrt (t / (4 * X ^ 2)) / (2 * Real.pi) +
            2 / Real.sqrt (t / (4 * X ^ 2))) * (3 + 2 * Real.pi) := by
      have hb' : a + (n + 1 : ℕ) ≤ 2 * X := by
        have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
        push_cast at hb ⊢
        linarith
      apply (LogarithmicSecondDerivativeTest.square_root_bound ht hX ha (n + 1) hb' htX).trans
      gcongr
    simpa only [Nat.cast_zero, add_zero, Nat.succ_eq_add_one] using
      FiniteAbelVariation.decreasing_bound (fun n ↦ Real.exp (-σ * Real.log (a + n)))
        (fun n ↦ rotation (phase t (a + n))) N hw hm hp

/-- The literal finite Dirichlet sum inherits the proved bound for its
full complex terms, with every original cutoff and radial factor retained. -/
theorem feature_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ))
    (hb : (a : ℝ) + N ≤ 2 * X) (htX : s.im ≤ 4 * X ^ 2) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      ((4 * N * Real.sqrt (s.im / (4 * X ^ 2)) / (2 * Real.pi) +
        2 / Real.sqrt (s.im / (4 * X ^ 2))) * (3 + 2 * Real.pi)) *
          zetaPrimeExpWeight s.re a := by
  simpa only [ZetaFiniteDifferencing.feature_polar, zetaPrimeExpWeight, Nat.cast_add,
    PhaseIncrementInverse.rotation] using damped_bound hσ ht hX ha N hb htX

end
end RiemannGaussian.DirichletSecondDerivativeBound
