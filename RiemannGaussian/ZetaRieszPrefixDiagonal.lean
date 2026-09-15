/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnnulusJoint
import RiemannGaussian.ZetaPrimeNonlinearTail

/-!
# Independent decay of the actual prime-square prefix

The genuine physical prefix has exactly one diagonal incidence at each
prime square. Its normalized response has geometric rate 2u/(u+1)<1
for all 0<u<1, uniformly over selected prime families and heights and
for every fixed polynomial filter. Distinct-prime phases are retained.
-/

namespace RiemannGaussian.ZetaRieszPrefixDiagonal
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSemiprimeCompletion ZetaPrimeNonlinearTail

/-- A prime-square label has precisely its single diagonal incidence in
the actual physical prefix; other selected prime cofactors contribute zero. -/
theorem prefixCoefficient_square (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime) {p : ℕ} (hp : p.Prime) (hpA : p ∈ A)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ZetaRieszCrossCompletion.prefixCoefficient A u N (p ^ 2) =
      pairLift (SquarefreeVaughanLogSource.length u N) p (p ^ 2) := by
  unfold ZetaRieszCrossCompletion.prefixCoefficient
  rw [Finset.sum_eq_single p]
  · have he : p ^ 2 / p = p := by rw [pow_two, Nat.mul_div_cancel_left _ hp.pos]
    rw [he, if_pos hpX]
  · intro a ha hap
    have hnd : ¬ a ∣ p ^ 2 := by
      intro hd
      exact hap ((Nat.prime_dvd_prime_iff_eq (hA a ha) hp).mp ((hA a ha).dvd_of_dvd_pow hd))
    have hz : pairLift (SquarefreeVaughanLogSource.length u N) a (p ^ 2) = 0 :=
      if_neg (fun h => hnd h.1)
    simp only [hz, ite_self]
  · exact fun h => (h hpA).elim

/-- The exact diagonal coefficient is bounded by twice the prime
logarithm, independently of the changing physical cutoff. -/
theorem norm_pairLift_square_le (u : ℝ) (N : ℕ) {p : ℕ} (hp : p.Prime)
    (hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖pairLift (SquarefreeVaughanLogSource.length u N) p (p ^ 2)‖ ≤ 2 * Real.log p := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlog : Real.log p ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast hp.pos)
    exact_mod_cast hpX.le
  have he : p ^ 2 / p = p := by rw [pow_two, Nat.mul_div_cancel_left _ hp.pos]
  have hd : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
  rw [pairLift, if_pos ⟨hd, by simpa only [he] using hp⟩,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (Real.log_natCast_nonneg (p ^ 2)),
    abs_of_nonneg (Real.log_natCast_nonneg p), abs_of_pos hL]
  apply (div_le_iff₀ hL).mpr
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hlog (Real.log_natCast_nonneg p)]

/-- The actual diagonal correction on its uniquely indexed prime squares,
with every original physical and factorial factor retained. -/
def diagonalResponse (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ p ∈ A, pairLift (SquarefreeVaughanLogSource.length u N) p (p ^ 2) *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p ^ 2 : ℕ)

/-- Every finite diagonal correction has a convergent prime-square mass
allowance at any tilt q<1, uniformly in height and the selected primes. -/
theorem norm_diagonalResponse_le (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ‖diagonalResponse A P u y N‖ ≤
      q⁻¹ ^ N * (2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ∑' n : ℕ, squareLogWeight (3 / 2 - q) n := by
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hF : 0 ≤ F := Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))
  have hterm (p : ℕ) (hp : p ∈ A) :
      ‖pairLift (SquarefreeVaughanLogSource.length u N) p (p ^ 2) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p ^ 2 : ℕ)‖ ≤
        (q⁻¹ ^ N * (2 * F)) * squareLogWeight (3 / 2 - q) p := by
    have hc := norm_pairLift_square_le u N (hA p hp).1 (hA p hp).2
    have hx : (1 : ℝ) ≤ (p ^ 2 : ℕ) := by exact_mod_cast (one_le_pow₀ (hA p hp).1.one_le : 1 ≤ p ^ 2)
    have hk := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y) hx hq
    have hlog : Real.log (p ^ 2 : ℕ) = 2 * Real.log p := by
      rw [Nat.cast_pow, Real.log_pow]; norm_num
    simp only [show (3 / 2 + Complex.I * (y : ℂ)).re = 3 / 2 by simp, hlog] at hk
    rw [norm_mul]
    apply (mul_le_mul hc hk (norm_nonneg _) (by positivity)).trans_eq
    dsimp [squareLogWeight, zetaPrimeExpWeight, F]
    rw [show -(3 / 2 - q) * (2 * Real.log p) = -(2 * (3 / 2 - q)) * Real.log p by ring]
    ring
  have hmass : ∑ p ∈ A, squareLogWeight (3 / 2 - q) p ≤
      ∑' n : ℕ, squareLogWeight (3 / 2 - q) n :=
    Summable.sum_le_tsum A (fun n _ => mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n))
      (summable_squareLogWeight (by linarith))
  calc
    _ ≤ ∑ p ∈ A, ‖pairLift (SquarefreeVaughanLogSource.length u N) p (p ^ 2) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (p ^ 2 : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ A, (q⁻¹ ^ N * (2 * F)) * squareLogWeight (3 / 2 - q) p := Finset.sum_le_sum hterm
    _ = (q⁻¹ ^ N * (2 * F)) * ∑ p ∈ A, squareLogWeight (3 / 2 - q) p := by simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- The actual source-normalized diagonal has an explicit geometric
allowance for every positive source and every tilt strictly below one.
Taking u<q makes its base strictly less than one. -/
theorem norm_normalized_diagonalResponse_le (A : Finset ℕ) (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u : ℝ} (hu : 0 < u)
    (hA : ∀ p ∈ A, p.Prime ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ‖(u : ℂ) ^ (N + 1) * diagonalResponse A P u y N‖ ≤
      (u / q) ^ N * (u * (2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ∑' n : ℕ, squareLogWeight (3 / 2 - q) n) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  apply (mul_le_mul_of_nonneg_left (norm_diagonalResponse_le A P u y N hA hq hq1)
    (by positivity)).trans_eq
  rw [pow_succ, div_pow, div_eq_mul_inv, inv_pow]
  ring

/-- After original source normalization, every moving physical-prefix
diagonal vanishes independently for ALL 0<u<1. The off-diagonal shared
prime phases are deliberately left outside this estimate. -/
theorem tendsto_diagonalResponse (A : ℕ → Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hA : ∀ N p, p ∈ A N → p.Prime ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * diagonalResponse (A N) P u y N) atTop (𝓝 0) := by
  let q : ℝ := (u + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have huq : u / q < 1 := (div_lt_one hq).mpr (by dsimp [q]; linarith)
  let C : ℝ := u * (2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
    ∑' n : ℕ, squareLogWeight (3 / 2 - q) n
  have hb (N : ℕ) : ‖(u : ℂ) ^ (N + 1) * diagonalResponse (A N) P u y N‖ ≤ (u / q) ^ N * C :=
    norm_normalized_diagonalResponse_le (A N) P y N hu (hA N) hq hq1
  apply squeeze_zero_norm hb
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) huq).mul_const C

/-- Every selected diagonal label lies in the exact finite physical
prefix. This keeps the actual integer cutoff when the component is removed. -/
theorem diagonalLabels_subset_range (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ p ∈ A, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    A.image (fun p => p ^ 2) ⊆
      Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) := by
  intro n hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  apply Finset.mem_range.mpr
  have hh := hA p hp
  nlinarith

/-- The bounded diagonal response is exactly the selected component of
the original finite physical prefix, with each prime-square integer once. -/
theorem sum_prefix_diagonal_eq_response (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    (hA : ∀ p ∈ A, p.Prime ∧ p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    (∑ n ∈ A.image (fun p => p ^ 2),
      ZetaRieszCrossCompletion.prefixCoefficient A u N n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) = diagonalResponse A P u y N := by
  rw [Finset.sum_image (by
    intro a _ b _ h
    exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) h)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [prefixCoefficient_square A u N (fun a ha => (hA a ha).1) (hA p hp).1 hp (hA p hp).2]

end

end RiemannGaussian.ZetaRieszPrefixDiagonal
