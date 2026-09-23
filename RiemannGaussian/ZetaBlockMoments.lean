/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockApproximation

/-!
# Finite geometric moments for the certified block evaluator

The moment recurrence compresses a block without dropping any term. Its
denominator is exposed: division requires `q != 1`, and interval evaluation
must either certify the inverse or use the literal finite sum. No claim
of uniform conditioning near resonance is made.
-/

namespace RiemannGaussian.ZetaBlockMoments
noncomputable section
open Complex
open scoped BigOperators

/-- A finite geometric moment with its original step and phase. -/
def moment (q h : ℂ) (K j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range K, ((k : ℂ) * h) ^ j * q ^ k

theorem moment_succ (q h : ℂ) (K j : ℕ) :
    moment q h (K + 1) j = moment q h K j + ((K : ℂ) * h) ^ j * q ^ K :=
  Finset.sum_range_succ _ _

private theorem lower_binomial (a b : ℂ) (j : ℕ) :
    (a + b) ^ j = (∑ l ∈ Finset.range j, (j.choose l : ℂ) * b ^ (j - l) * a ^ l) + a ^ j := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- A denominator-free recurrence valid even at exact resonance. -/
theorem moment_recurrence (q h : ℂ) (K j : ℕ) :
    (q - 1) * moment q h K j = q ^ K * (((K : ℂ) - 1) * h) ^ j +
      (∑ l ∈ Finset.range j, (j.choose l : ℂ) * (-h) ^ (j - l) * moment q h K l) -
        (-h) ^ j := by
  induction K with
  | zero => simp [moment]
  | succ K ih =>
    simp only [moment_succ, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      mul_add, Finset.sum_add_distrib]
    have he := lower_binomial ((K : ℂ) * h) (-h) j
    rw [show (K : ℂ) * h + -h = ((K : ℂ) - 1) * h by ring] at he
    have hsum : (∑ l ∈ Finset.range j,
        (j.choose l : ℂ) * (-h) ^ (j - l) * (((K : ℂ) * h) ^ l * q ^ K)) =
        (∑ l ∈ Finset.range j, (j.choose l : ℂ) * (-h) ^ (j - l) * ((K : ℂ) * h) ^ l) *
          q ^ K := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro l hl; ring
    rw [hsum, pow_succ]
    linear_combination ih + q ^ K * he

/-- Away from resonance the recurrence determines the next moment from
strictly lower moments. -/
theorem moment_eq_div {q : ℂ} (hq : q ≠ 1) (h : ℂ) (K j : ℕ) :
    moment q h K j =
      (q ^ K * (((K : ℂ) - 1) * h) ^ j +
        (∑ l ∈ Finset.range j, (j.choose l : ℂ) * (-h) ^ (j - l) * moment q h K l) -
          (-h) ^ j) / (q - 1) := by
  apply (eq_div_iff (sub_ne_zero.mpr hq)).mpr
  simpa only [mul_comm (moment q h K j)] using moment_recurrence q h K j

/-- Interchanging the two finite sums exposes the compressed block. -/
theorem sum_polynomial_eq_moments (s q h : ℂ) (K m : ℕ) :
    (∑ k ∈ Finset.range K, q ^ k * ZetaBlockTaylor.polynomial s m ((k : ℂ) * h)) =
      ∑ j ∈ Finset.range (m + 1), ZetaBlockTaylor.coefficient s j * moment q h K j := by
  simp only [ZetaBlockTaylor.polynomial, moment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The literal accelerated Dirichlet block is exactly a short sum of
finite geometric moments. -/
theorem block_eq_moments (s : ℂ) (v K : ℕ) :
    ZetaBlockApproximation.block s v K = (v : ℂ) ^ (-s) *
      ∑ j ∈ Finset.range 19, ZetaBlockTaylor.coefficient s j *
        moment (Complex.exp (-s / v)) (300 / v) K j := by
  unfold ZetaBlockApproximation.block ZetaBlockApproximation.geometric
  simp only [Complex.ofReal_natCast, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [← sum_polynomial_eq_moments]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.exp_nat_mul]
  congr 1
  · congr 1; ring
  · congr 1; ring

end
end RiemannGaussian.ZetaBlockMoments
