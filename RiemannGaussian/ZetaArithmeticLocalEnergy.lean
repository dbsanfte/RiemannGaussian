/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.NatDivisorSquareDirichlet
import RiemannGaussian.ZetaPrimeKernelSecondDifference
import RiemannGaussian.ZetaMoebiusMomentBand

/-!
# Local correlations of the complete arithmetic kernel

The divisor-square Dirichlet mass bounds the diagonal energy of the full
factorial kernel, uniformly over all dominated arithmetic coefficients and
finite windows. A finite degree estimate then controls every signed cross
term in an additive neighbourhood of the diagonal. The complementary pairs
remain available in an exact identity; their sum is not bounded here.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian
noncomputable section

/-- The full divisor-log majorant is bounded by its divisor count times
the logarithm, independently of any cutoff or arithmetic sieve. -/
theorem zetaMoebiusLogMajorant_le_card_mul_log (n : ℕ) :
    zetaMoebiusLogMajorant n ≤ (n.divisors.card : ℝ) * Real.log n := by
  rw [zetaMoebiusLogMajorant, Nat.sum_divisorsAntidiagonal (fun _ b ↦ Real.log b)]
  calc
    _ ≤ ∑ d ∈ n.divisors, Real.log n := by
      apply Finset.sum_le_sum
      intro d hd
      have hn : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
      have hdiv : 0 < n / d := Nat.div_pos
        (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1)
        (Nat.pos_of_mem_divisors hd)
      exact Real.log_le_log (by exact_mod_cast hdiv)
        (by exact_mod_cast Nat.div_le_self n d)
    _ = _ := by simp

/-- The explicit energy constant uses a genuinely summable collision
mass whenever the kernel tilt lies strictly between zero and one. -/
def zetaArithmeticEnergyConstant (p : Polynomial ℂ) (r : ℝ) : ℝ :=
  ((∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) / ((1 - r) / 2)) ^ 2 *
    divisorSquareDirichletMass (2 - r)

/-- The diagonal-energy constant is nonnegative. -/
theorem zetaArithmeticEnergyConstant_nonneg (p : Polynomial ℂ) (r : ℝ) :
    0 ≤ zetaArithmeticEnergyConstant p r :=
  mul_nonneg (sq_nonneg _) (divisorSquareDirichletMass_nonneg _)

private theorem arithmetic_atom_sq_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (p : Polynomial ℂ) (N n : ℕ) (y : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ^ 2 ≤
      (r⁻¹ ^ N * ((∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) / ((1 - r) / 2))) ^ 2 *
        ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(2 - r))) := by
  by_cases hn : n = 0
  · subst n
    have hz : a 0 = 0 := norm_eq_zero.mp (le_antisymm
      (by simpa [zetaMoebiusLogMajorant] using ha 0) (norm_nonneg _))
    simp [hz]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let e := (1 - r) / 2
  let B := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have he : 0 < e := by dsimp [e]; linarith
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have hlog := Real.log_le_rpow_div hnR.le he
  have hk := norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * y)
    (x := (n : ℝ)) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hr
  have hexp : Real.exp (-((3 / 2 + I * (y : ℂ)).re - r) * Real.log n) =
      (n : ℝ) ^ (-(3 / 2 - r)) := by
    have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
    rw [hs]
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  rw [hexp] at hk
  have hb : ‖a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      r⁻¹ ^ N * (B / e) * (n.divisors.card : ℝ) * (n : ℝ) ^ (-(2 - r) / 2) := by
    rw [norm_mul]
    calc
      _ ≤ ((n.divisors.card : ℝ) * ((n : ℝ) ^ e / e)) *
          (r⁻¹ ^ N * (n : ℝ) ^ (-(3 / 2 - r)) * B) :=
        mul_le_mul ((ha n).trans ((zetaMoebiusLogMajorant_le_card_mul_log n).trans
          (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)))) hk
          (norm_nonneg _) (by positivity)
      _ = _ := by
        have hp : (n : ℝ) ^ e * (n : ℝ) ^ (-(3 / 2 - r)) =
            (n : ℝ) ^ (-(2 - r) / 2) := by
          rw [← Real.rpow_add hnR]
          congr 1
          dsimp [e]
          ring
        linear_combination (r⁻¹ ^ N * (B / e) * (n.divisors.card : ℝ)) * hp
  calc
    _ ≤ (r⁻¹ ^ N * (B / e) * (n.divisors.card : ℝ) *
        (n : ℝ) ^ (-(2 - r) / 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by
      have hp : ((n : ℝ) ^ (-(2 - r) / 2)) ^ 2 = (n : ℝ) ^ (-(2 - r)) := by
        rw [← Real.rpow_mul_natCast hnR.le]
        congr 1
        norm_num
      simp only [mul_pow, hp]
      dsimp [B, e]
      ring

/-- The complete finite diagonal energy has an independent geometric
moment bound. The coefficient family and finite window are arbitrary. -/
theorem sum_norm_zetaArithmeticKernel_sq_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n)
    (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (T : Finset ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑ n ∈ T, ‖a n * zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ^ 2) ≤
      zetaArithmeticEnergyConstant p r * (r⁻¹ ^ N) ^ 2 := by
  let A := (r⁻¹ ^ N * ((∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) / ((1 - r) / 2))) ^ 2
  calc
    _ ≤ ∑ n ∈ T, A * ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(2 - r))) :=
      Finset.sum_le_sum (fun n _ ↦ arithmetic_atom_sq_le a ha p N n y hr hr1)
    _ = A * ∑ n ∈ T, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-(2 - r)) := by
      rw [Finset.mul_sum]
    _ ≤ A * divisorSquareDirichletMass (2 - r) := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg (by linarith : 1 < 2 - r)).sum_le_tsum _
        (fun n _ ↦ by positivity)) (sq_nonneg _)
    _ = _ := by dsimp [A, zetaArithmeticEnergyConstant]; ring

/-- All ordered pairs within additive distance `H`, including the
diagonal. Both orientations and every original complex phase are retained. -/
def finiteLocalCorrelation (T : Finset ℕ) (f : ℕ → ℂ) (H : ℕ) : ℂ :=
  ∑ n ∈ T, ∑ m ∈ T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H), f n * conj (f m)

/-- The literal complementary ordered pairs, with the same phases. -/
def finiteFarCorrelation (T : Finset ℕ) (f : ℕ → ℂ) (H : ℕ) : ℂ :=
  ∑ n ∈ T, ∑ m ∈ T.filter (fun m ↦ ¬(n ≤ m + H ∧ m ≤ n + H)), f n * conj (f m)

/-- The complete quadratic sum splits exactly into nearby and distant
pairs. No signed cross term is omitted or replaced by a diagonal. -/
theorem finiteLocalCorrelation_add_far (T : Finset ℕ) (f : ℕ → ℂ) (H : ℕ) :
    finiteLocalCorrelation T f H + finiteFarCorrelation T f H =
      (∑ n ∈ T, f n) * conj (∑ n ∈ T, f n) := by
  rw [finiteLocalCorrelation, finiteFarCorrelation, ← Finset.sum_add_distrib]
  simp only [Finset.sum_filter]
  simp_rw [← Finset.sum_add_distrib, ite_not, ite_add_ite, add_zero, zero_add, ite_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem local_row_card_le (T : Finset ℕ) (n H : ℕ) :
    (T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H)).card ≤ 2 * H + 1 := by
  have hsub : T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H) ⊆ Finset.Icc (n - H) (n + H) := by
    intro m hm
    obtain ⟨_, hnm, hmn⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega, hmn⟩
  have h := Finset.card_le_card hsub
  rw [Nat.card_Icc] at h
  omega

/-- One degree budget controls the entire local quadratic form,
including every cross term. It holds for arbitrary complex samples. -/
theorem norm_finiteLocalCorrelation_le (T : Finset ℕ) (f : ℕ → ℂ) (H : ℕ) :
    ‖finiteLocalCorrelation T f H‖ ≤ (2 * H + 1 : ℝ) * ∑ n ∈ T, ‖f n‖ ^ 2 := by
  let E := ∑ n ∈ T, ∑ m ∈ T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H),
    (‖f n‖ ^ 2 + ‖f m‖ ^ 2)
  have hnorm : 2 * ‖finiteLocalCorrelation T f H‖ ≤ E := by
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [norm_mul, norm_conj]
    nlinarith [sq_nonneg (‖f n‖ - ‖f m‖)]
  have hsym : (∑ n ∈ T, ∑ m ∈ T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H), ‖f m‖ ^ 2) =
      ∑ n ∈ T, ∑ m ∈ T.filter (fun m ↦ n ≤ m + H ∧ m ≤ n + H), ‖f n‖ ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    simp only [and_comm]
  have hE : E ≤ 2 * ((2 * H + 1 : ℝ) * ∑ n ∈ T, ‖f n‖ ^ 2) := by
    dsimp [E]
    simp only [Finset.sum_add_distrib]
    rw [hsym, ← two_mul]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simp only [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast local_row_card_le T n H
  linarith

end
end RiemannGaussian
