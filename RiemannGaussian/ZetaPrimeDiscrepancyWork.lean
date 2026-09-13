/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeKernelSecondDifference
import Mathlib.Analysis.PSeries

/-!+# Prime jumps and signed Chebyshev discrepancy work

The actual integer Chebyshev discrepancy retains the ordinary-prime jumps,
their correlation with the preceding error, and every finite block boundary.
The weighted square identity keeps the full complex test. Its diagonal has
an independent geometric bound for the original factorial kernel divided
by the integer coordinate, uniformly over all finite index sets and heights.

The remaining weighted squared-error flux is signed. Positivity only gives
the separate monotone real-weight estimate proved below; it does not apply
automatically to the oscillatory zero detector or prove its required floor.
-/

namespace RiemannGaussian.PrimeDiscrepancyWork
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The actual ordinary-prime jump, with proper prime powers excluded. -/
def jump (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- The integer samples of the same `x - theta(x)` in the signed carrier. -/
def error (n : ℕ) : ℝ := n - Chebyshev.theta n

/-- Every prime jump is nonnegative. -/
theorem jump_nonneg (n : ℕ) : 0 ≤ jump n := by
  unfold jump
  split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl

/-- The full ordinary-prime jump is bounded by the integer logarithm. -/
theorem jump_le_log (n : ℕ) : jump n ≤ Real.log n := by
  unfold jump
  split_ifs <;> first | exact le_rfl | exact Real.log_natCast_nonneg _

/-- The finite prefix of actual jumps is exactly the Chebyshev function. -/
theorem theta_eq_sum (N : ℕ) :
    Chebyshev.theta N = ∑ j ∈ Finset.range N, jump (j + 1) := by
  induction N with
  | zero => simp [Chebyshev.theta]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    rw [Finset.sum_Ioc_succ_top (by omega : 0 ≤ N)]
    rfl

/-- The exact drift and prime jump at each integer, including prime endpoints. -/
theorem error_succ (n : ℕ) : error (n + 1) = error n + 1 - jump (n + 1) := by
  unfold error
  rw [theta_eq_sum (n + 1), theta_eq_sum n, Finset.sum_range_succ]
  push_cast
  ring

/-- A complete block retains its initial discrepancy and every intervening prime. -/
theorem error_block (a L : ℕ) :
    error (a + L) = error a + L - ∑ j ∈ Finset.range L, jump (a + j + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ, error_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- The signed correlation with the pre-jump error equals its exact square
increment and the squared forcing. No absolute value is taken. -/
theorem square_increment (n : ℕ) :
    2 * (jump (n + 1) - 1) * error n =
      (jump (n + 1) - 1) ^ 2 - (error (n + 1) ^ 2 - error n ^ 2) := by
  rw [error_succ]
  ring

/-- Prime/pre-jump-error work keeps every earlier-prime interaction.
Its triangular support is by position, not by an arithmetic product cutoff. -/
theorem prime_work_eq_ordered_pairs (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ S, w n * (jump (n + 1) : ℂ) * (error n : ℂ)) =
      (∑ n ∈ S, w n * (jump (n + 1) : ℂ) * (n : ℂ)) -
        ∑ n ∈ S, ∑ j ∈ Finset.range n,
          w n * (jump (n + 1) : ℂ) * (jump (j + 1) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [error, theta_eq_sum, ofReal_sub, ofReal_natCast, ofReal_sum, mul_sub,
    Finset.mul_sum]

/-- The complete complex-weighted work law telescopes with both boundary
energies and every weight increment, including all changes of phase. -/
theorem weighted_work (a L : ℕ) (w : ℕ → ℂ) :
    2 * (∑ j ∈ Finset.range L,
      w j * ((jump (a + j + 1) - 1 : ℝ) : ℂ) * (error (a + j) : ℂ)) =
      (∑ j ∈ Finset.range L, w j * (((jump (a + j + 1) - 1) ^ 2 : ℝ) : ℂ)) -
        w L * ((error (a + L) ^ 2 : ℝ) : ℂ) + w 0 * ((error a ^ 2 : ℝ) : ℂ) +
          ∑ j ∈ Finset.range L,
            (w (j + 1) - w j) * ((error (a + j + 1) ^ 2 : ℝ) : ℂ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ, mul_add]
    rw [ih]
    have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (square_increment (a + L))
    push_cast at h
    rw [show a + (L + 1) = a + L + 1 by omega]
    push_cast
    linear_combination w L * h

/-- Nonnegative decreasing real tests give an independent one-sided work
bound, with the initial block energy charged explicitly. The phase-bearing
factorial tests require their signed weight-variation term instead. -/
theorem monotone_work_le (a L : ℕ) (w : ℕ → ℝ)
    (hw : 0 ≤ w L) (hdec : ∀ j < L, w (j + 1) ≤ w j) :
    2 * (∑ j ∈ Finset.range L, w j * (jump (a + j + 1) - 1) * error (a + j)) ≤
      (∑ j ∈ Finset.range L, w j * (jump (a + j + 1) - 1) ^ 2) +
        w 0 * error a ^ 2 := by
  have h := congrArg Complex.re (weighted_work a L (fun j ↦ (w j : ℂ)))
  simp only [← ofReal_mul, ← ofReal_sub, ← ofReal_sum,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ofReal_re, add_re] at h
  have hv : (∑ j ∈ Finset.range L,
      (w (j + 1) - w j) * error (a + j + 1) ^ 2) ≤ 0 :=
    Finset.sum_nonpos fun j hj ↦ mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hdec j (Finset.mem_range.mp hj))) (sq_nonneg _)
  nlinarith [mul_nonneg hw (sq_nonneg (error (a + L)))]

/-- The squared local forcing has an elementary logarithmic envelope;
no estimate for the accumulated Chebyshev error is used. -/
theorem forcing_square_le (n : ℕ) : (jump n - 1) ^ 2 ≤ 1 + (Real.log n) ^ 2 := by
  nlinarith [jump_nonneg n, jump_le_log n, Real.log_natCast_nonneg n]

private theorem diagonal_majorant (n : ℕ) :
    (jump (n + 1) - 1) ^ 2 * Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ)) ≤
      129 * ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) := by
  have hl := Real.log_natCast_nonneg (n + 1)
  have h := logMoment_exp_envelope 2 hl (by norm_num : (0 : ℝ) < 1 / 8) (5 / 4)
  norm_num only [Nat.factorial, Nat.cast_ofNat, inv_div, one_div, inv_one, mul_one,
    show (5 / 4 - 1 / 8 : ℝ) = 9 / 8 by norm_num] at h
  have he : Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ)) ≤
      Real.exp (-(9 / 8 : ℝ) * Real.log (n + 1 : ℕ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_right (forcing_square_le (n + 1))
    (Real.exp_pos (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ))).le
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
  have hr : Real.log ((n + 1 : ℕ) : ℝ) * (-(9 / 8 : ℝ)) =
      -(9 / 8 : ℝ) * Real.log (n + 1 : ℕ) := by ring
  rw [hr]
  nlinarith

/-- The full diagonal majorant converges, including both prime jumps and
the unit drift at nonprimes. This supplies a genuine finite mass. -/
theorem summable_diagonal_mass : Summable (fun n : ℕ ↦
    (jump (n + 1) - 1) ^ 2 * Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ))) := by
  have hs : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num))
  exact (hs.mul_left 129).of_nonneg_of_le (fun _ ↦ by positivity) diagonal_majorant

/-- The finite mass of the actual squared local forcing at the tilted exponent. -/
def diagonalMass : ℝ := ∑' n : ℕ,
  (jump (n + 1) - 1) ^ 2 * Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ))

/-- The diagonal mass is nonnegative. -/
theorem diagonalMass_nonneg : 0 ≤ diagonalMass := tsum_nonneg (fun _ ↦ by positivity)

/-- The full factorial kernel at its original real part, with one exact
coordinate divisor. Every complex coefficient and prime phase remains. -/
def test (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (n : ℕ) : ℂ :=
  zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ)) (n + 1 : ℕ) / (n + 1 : ℕ)

/-- A fixed exponential tilt bounds the exact test, uniformly in height. -/
theorem norm_test_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (n : ℕ) :
    ‖test p N y n‖ ≤ (4 / 5 : ℝ) ^ N *
      Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ)) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k := by
  have he : test p N y n =
      zetaPrimeFilterKernel p N (3 / 2 + I * (y : ℂ) + 1) (n + 1 : ℕ) := by
    simpa only [test, pow_one, ofReal_natCast, Nat.cast_one] using
      zetaPrimeFilterKernel_div_pow p N 1 (3 / 2 + I * (y : ℂ))
        (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  rw [he]
  have h := norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * (y : ℂ) + 1)
    (x := (n + 1 : ℕ)) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
    (by norm_num : (0 : ℝ) < 5 / 4)
  norm_num at h ⊢
  exact h

/-- The actual diagonal of a finite prime-discrepancy work block.
The index set may move or be disconnected; no sign-selected work is bounded. -/
def diagonal (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, test p N y n * (((jump (n + 1) - 1) ^ 2 : ℝ) : ℂ)

/-- The complete diagonal has an independent geometric estimate, uniform
over every finite index set and ordinate, with the original fixed filter. -/
theorem norm_diagonal_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (S : Finset ℕ) :
    ‖diagonal p N y S‖ ≤ (4 / 5 : ℝ) ^ N *
      (∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k) * diagonalMass := by
  let C := (4 / 5 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, C * ((jump (n + 1) - 1) ^ 2 *
        Real.exp (-(5 / 4 : ℝ) * Real.log (n + 1 : ℕ))) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_right (norm_test_le p N y n) (sq_nonneg _)).trans_eq
        (by dsimp [C]; ring)
    _ ≤ C * diagonalMass := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (summable_diagonal_mass.sum_le_tsum S (fun _ _ ↦ by positivity)) hC

/-- Every moving finite diagonal tends to zero even at the fixed-zero
normalization. No hypothetical zero, prime-error bound or height limit is used. -/
theorem tendsto_scaled_diagonal (p : Polynomial ℂ) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (S : ℕ → Finset ℕ) (y : ℕ → ℝ) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) * diagonal p N (y N) (S N)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ ↦ (4 / 5 : ℝ) ^ N *
      (∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k) * diagonalMass) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by norm_num : (4 / 5 : ℝ) < 1)).mul_const
        (∑ k ∈ p.support, ‖p.coeff k‖ * (4 / 5 : ℝ) ^ k)).mul_const diagonalMass
  apply squeeze_zero_norm (fun N ↦ ?_) hlim
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hu hu1)).trans
    (norm_diagonal_le p N (y N) (S N))

/-- The actual centered forcing paired with its preceding Chebyshev error,
tested by the unchanged full factorial kernel with its coordinate divisor. -/
def work (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (a L : ℕ) : ℂ :=
  ∑ j ∈ Finset.range L, test p N y (a + j) *
    ((jump (a + j + 1) - 1 : ℝ) : ℂ) * (error (a + j) : ℂ)

/-- The exact signed squared-error flux: both boundary energies and all
complex test increments. Its real part has no asserted sign. -/
def flux (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (a L : ℕ) : ℂ :=
  test p N y (a + L) * ((error (a + L) ^ 2 : ℝ) : ℂ) -
    test p N y a * ((error a ^ 2 : ℝ) : ℂ) -
      ∑ j ∈ Finset.range L, (test p N y (a + j + 1) - test p N y (a + j)) *
        ((error (a + j + 1) ^ 2 : ℝ) : ℂ)

/-- The exact work/flux identity for the actual arithmetic block.
The entire finite diagonal is retained before using its independent bound. -/
theorem work_add_flux_eq_diagonal (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (a L : ℕ) :
    2 * work p N y a L + flux p N y a L =
      diagonal p N y ((Finset.range L).image (fun j ↦ a + j)) := by
  have h := weighted_work a L (fun j ↦ test p N y (a + j))
  rw [diagonal, Finset.sum_image (by intro i _ j _ h; dsimp only at h; omega)]
  dsimp [work, flux] at h ⊢
  simp only [Nat.add_assoc] at h ⊢
  linear_combination h

/-- Along arbitrary moving complete blocks, work is minus half the signed
energy flux up to an independently vanishing source-scale error. This
eliminates the local forcing diagonal; it does not bound the retained flux
or the original linear Chebyshev carrier. -/
theorem tendsto_scaled_work_add_flux (p : Polynomial ℂ) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (a L : ℕ → ℕ) (y : ℕ → ℝ) :
    Tendsto (fun N ↦ (u : ℂ) ^ (N + 1) *
      (2 * work p N (y N) (a N) (L N) + flux p N (y N) (a N) (L N))) atTop (𝓝 0) := by
  simpa only [work_add_flux_eq_diagonal] using
    tendsto_scaled_diagonal p hu hu1
      (fun N ↦ (Finset.range (L N)).image (fun j ↦ a N + j)) y

end
end RiemannGaussian.PrimeDiscrepancyWork
