/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompletedCofactor

/-!
# Physical prime-prefix budgets retaining both prime logarithms

Chebyshev's actual prime-logarithm bound pays each prime factor. The
physical inverse length and damped floor remain in an explicit allowance
for arbitrary dominated prime-pair marks, including subband masks.
No hypothetical zero is needed for this independent prefix estimate.
-/

namespace RiemannGaussian.ZetaRieszSemiprimePrefix
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor

/-- Every selected prime prefix retains the logarithmic Chebyshev mass. -/
theorem sum_prime_log_mass_subset_le (S : Finset ℕ) (A : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ A) :
    (∑ a ∈ S, Real.log a / Real.sqrt a) ≤ 3 * Real.sqrt A := by
  apply le_trans _ (sum_prime_log_inv_sqrt_le A)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    simp only [zetaSquarePrimesThrough, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(hS a ha).1.pos, (hS a ha).2⟩, (hS a ha).1⟩
  · intro a _ _
    exact div_nonneg (Real.log_natCast_nonneg a) (Real.sqrt_nonneg _)

/-- The full product logarithm is paid by its prime logarithm and a
small-cofactor cost. This preserves the useful log(p) prime-density mark. -/
theorem log_product_le_prime_log {a p A : ℕ} (ha : 0 < a) (haA : a ≤ A) (hp : p.Prime) :
    Real.log ((a * p : ℕ) : ℝ) ≤ (1 + Real.log A / Real.log 2) * Real.log p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpa : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have ha' : Real.log a ≤ Real.log A := Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast haA)
  have hcost : 0 ≤ Real.log A / Real.log 2 := div_nonneg (Real.log_natCast_nonneg A) hlog2.le
  have h := mul_le_mul_of_nonneg_left hpa hcost
  rw [div_mul_cancel₀ _ hlog2.ne'] at h
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero)]
  nlinarith

/-- Keeping both prime logarithms gives a square-root product bound
for every marked pair atom, without an order-dependent factorial cost. -/
theorem norm_marked_pair_atom_le (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a p A : ℕ} (ha : 0 < a) (haA : a ≤ A) (hp : p.Prime)
    {L : ℝ} (hL : 0 < L) {c : ℂ}
    (hc : ‖c‖ ≤ Real.log a * Real.log ((a * p : ℕ) : ℝ) / L) :
    ‖c * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)‖ ≤
      ((∑ k ∈ P.support, ‖P.coeff k‖) / L * (1 + Real.log A / Real.log 2)) *
        (Real.log a / Real.sqrt a) * (Real.log p / Real.sqrt p) := by
  have hK := ZetaRieszFixedCofactor.norm_filter_le_inv_sqrt P N y (Nat.mul_pos ha hp.pos)
  have hlog := log_product_le_prime_log ha haA hp
  rw [norm_mul]
  apply (mul_le_mul hc hK (norm_nonneg _) (by positivity)).trans
  have he : Real.sqrt ((a * p : ℕ) : ℝ) = Real.sqrt a * Real.sqrt p := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a)]
  rw [he]
  calc
    _ ≤ (Real.log a * ((1 + Real.log A / Real.log 2) * Real.log p) / L) *
        (1 / (Real.sqrt a * Real.sqrt p) * ∑ k ∈ P.support, ‖P.coeff k‖) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply div_le_div_of_nonneg_right _ hL.le
      exact mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg a)
    _ = _ := by ring

/-- The complete finite prime-pair prefix has an explicit product
budget with the physical 1/L saving still present. Arbitrary pair marks,
including subband masks and diagonal deletion, are allowed by the premise. -/
theorem norm_prime_pair_prefix_le (S T : Finset ℕ) (A X : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ A) (hT : ∀ p ∈ T, p.Prime ∧ p ≤ X)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {L : ℝ} (hL : 0 < L)
    (f : ℕ → ℕ → ℂ)
    (hf : ∀ a ∈ S, ∀ p ∈ T, ‖f a p‖ ≤ Real.log a * Real.log ((a * p : ℕ) : ℝ) / L) :
    ‖∑ a ∈ S, ∑ p ∈ T,
      f a p * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)‖ ≤
      9 * (∑ k ∈ P.support, ‖P.coeff k‖) / L * (1 + Real.log A / Real.log 2) *
        Real.sqrt A * Real.sqrt X := by
  let C : ℝ := (∑ k ∈ P.support, ‖P.coeff k‖) / L * (1 + Real.log A / Real.log 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ S, ∑ p ∈ T, C * (Real.log a / Real.sqrt a) * (Real.log p / Real.sqrt p) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun p hp => norm_marked_pair_atom_le P N y
        (hS a ha).1.pos (hS a ha).2 (hT p hp).1 hL (hf a ha p hp))
    _ = C * (∑ a ∈ S, Real.log a / Real.sqrt a) * ∑ p ∈ T, Real.log p / Real.sqrt p := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ C * (3 * Real.sqrt A) * (3 * Real.sqrt X) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (sum_prime_log_mass_subset_le S A hS) hC)
        (sum_prime_log_mass_subset_le T X hT)
        (Finset.sum_nonneg fun p _ => by positivity) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- At the actual damped physical cutoff, prime pairs with a prime
cofactor through N squared have an explicit all-scale allowance. No
hypothetical zero or arithmetic cancellation assumption is used. -/
theorem norm_physical_prime_prefix_le (S T : Finset ℕ) (P : Polynomial ℂ)
    (N : ℕ) (y : ℝ) {u : ℝ} (hu : 0 < u)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ N ^ 2)
    (hT : ∀ p ∈ T, p.Prime ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (f : ℕ → ℕ → ℂ)
    (hf : ∀ a ∈ S, ∀ p ∈ T, ‖f a p‖ ≤ Real.log a * Real.log ((a * p : ℕ) : ℝ) /
      SquarefreeVaughanLogSource.length u N) :
    ‖(u : ℂ) ^ (N + 1) * ∑ a ∈ S, ∑ p ∈ T,
      f a p * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ)‖ ≤
      (9 * (∑ k ∈ P.support, ‖P.coeff k‖) / SquarefreeVaughanLogSource.length u N *
        (1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) * N) *
          (u / (N + 1) + 2 * u ^ (N + 1)) := by
  let D := ZetaVaughanCutoffBudget.linearDampedCutoff u N
  let C : ℝ := 9 * (∑ k ∈ P.support, ‖P.coeff k‖) / SquarefreeVaughanLogSource.length u N *
        (1 + Real.log ((N ^ 2 : ℕ) : ℝ) / Real.log 2) * N
  have hC : 0 ≤ C := by
    dsimp [C]
    have hL := SquarefreeVaughanLogSource.length_pos u N
    have hlog := Real.log_natCast_nonneg (N ^ 2)
    positivity
  have hb := norm_prime_pair_prefix_le S T (N ^ 2) ((D + 2) ^ 2) hS hT P N y
    (SquarefreeVaughanLogSource.length_pos u N) f hf
  have hN : Real.sqrt ((N ^ 2 : ℕ) : ℝ) = N := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg N)]
  have hD : Real.sqrt (((D + 2) ^ 2 : ℕ) : ℝ) = (D : ℝ) + 2 := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg (D + 2))]
    norm_cast
  rw [hN, hD] at hb
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)).trans
  calc
    _ = C * (u ^ (N + 1) * ((D : ℝ) + 2)) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ZetaRieszFixedCofactor.normalized_shifted_cutoff_le hu N) hC

end
end RiemannGaussian.ZetaRieszSemiprimePrefix
