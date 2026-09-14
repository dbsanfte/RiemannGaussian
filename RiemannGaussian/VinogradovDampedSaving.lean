/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDirichletSaving
import RiemannGaussian.VinogradovKorobovDamping

/-!
# Amplitude transport of the actual Dirichlet saving

Finite Abel summation preserves the actual weight mass in the linear
cancellation term and charges the constant endpoint error only to the
initial weight. Every nonnegative decreasing weight family is covered,
including the literal zeta coefficients at nonnegative real part. The
fixed-degree constants and thresholds remain unevaluated.
-/
namespace RiemannGaussian.VinogradovDampedSaving
noncomputable section
open scoped BigOperators
open VinogradovKorobovBlock VinogradovKorobovDamping

/-- An affine prefix allowance pays the exact amplitude mass for its linear
part and only the initial amplitude for its constant endpoint cost. -/
theorem abelTransform_norm_affine_le (w : ℕ → ℝ) (F : ℕ → ℂ) (N : ℕ) {E D : ℝ}
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N))
    (hF : ∀ n ≤ N, ‖F (n + 1)‖ ≤ (n + 1 : ℕ) * E + D) :
    ‖abelTransform (fun n => (w n : ℂ)) F N‖ ≤
      E * (∑ n ∈ Finset.range (N + 1), w n) + D * w 0 := by
  have hd (n : ℕ) (hn : n < N) : 0 ≤ w n - w (n + 1) := by
    exact sub_nonneg.mpr (hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  unfold abelTransform
  calc
    _ ≤ ‖(w N : ℂ) * F (N + 1)‖ +
        ∑ n ∈ Finset.range N, ‖((w n : ℂ) - (w (n + 1) : ℂ)) * F (n + 1)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w N * ((N + 1 : ℕ) * E + D) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * ((n + 1 : ℕ) * E + D) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw N le_rfl)]
        exact mul_le_mul_of_nonneg_left (hF N le_rfl) (hw N le_rfl)
      · apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hd n hn')]
        exact mul_le_mul_of_nonneg_left (hF n hn'.le) (hd n hn')
    _ = E * (w N * (N + 1 : ℕ) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * (n + 1 : ℕ)) +
        D * (w N + ∑ n ∈ Finset.range N, (w n - w (n + 1))) := by
      have he (n : ℕ) : (w n - w (n + 1)) * ((n + 1 : ℕ) * E + D) =
          E * ((w n - w (n + 1)) * (n + 1 : ℕ)) + D * (w n - w (n + 1)) := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ = _ := by rw [abel_length_mass, Finset.sum_range_sub']; ring

/-- All nonnegative decreasing weight families retain the actual cancellation
mass and the separate normalized endpoint cost. -/
theorem exists_decreasing_weight_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 2 * (M : ℝ) ^ 4 → ∀ N : ℕ, N + 1 ≤ 2 * M ^ 4 →
      ∀ w : ℕ → ℝ, (∀ n ≤ N, 0 ≤ w n) → AntitoneOn w (Set.Icc 0 N) →
      ‖∑ n ∈ Finset.range (N + 1), (w n : ℂ) * dirichletTerm t z n‖ ≤
        (C * (M : ℝ) ^ (-(1 / (128 * (k : ℝ) ^ 2)))) *
          (∑ n ∈ Finset.range (N + 1), w n) + 2 * (M : ℝ) ^ 2 * w 0 := by
  obtain ⟨C, hC, M₀, h⟩ := VinogradovDirichletSaving.exists_partial_dirichlet_saving k hk
  refine ⟨C, hC, M₀, ?_⟩
  intro M hM t z htlo hthi hzlo hzhi N hN w hw hm
  rw [weighted_identity]
  apply abelTransform_norm_affine_le w _ N hw hm
  intro n hn
  have hp := h M hM t z htlo hthi hzlo hzhi (n + 1) (by omega)
  convert hp using 1
  ring

/-- The actual zeta Dirichlet coefficients inherit the proved cancellation
with their genuine damping mass and initial endpoint weight. -/
theorem exists_feature_block_saving (k : ℕ) (hk : 12 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ s : ℂ,
      0 ≤ s.re → (M : ℝ) ^ (2 * k - 2) ≤ s.im → s.im ≤ (M : ℝ) ^ (2 * k) →
      ∀ a : ℕ, (M : ℝ) ^ 4 ≤ a → (a : ℝ) ≤ 2 * (M : ℝ) ^ 4 →
      ∀ N : ℕ, N + 1 ≤ 2 * M ^ 4 →
      ‖∑ n ∈ Finset.range (N + 1), zetaPrimeFeature s (a + n)‖ ≤
        (C * (M : ℝ) ^ (-(1 / (128 * (k : ℝ) ^ 2)))) *
          (∑ n ∈ Finset.range (N + 1), zetaPrimeExpWeight s.re (a + n)) +
        2 * (M : ℝ) ^ 2 * zetaPrimeExpWeight s.re a := by
  obtain ⟨C, hC, M₀, h⟩ := exists_decreasing_weight_saving k hk
  refine ⟨C, hC, max M₀ 1, ?_⟩
  intro M hM s hσ htlo hthi a halo hahi N hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast (le_max_right M₀ 1).trans hM
  have haR : (0 : ℝ) < a := (pow_pos hMr 4).trans_le halo
  have ha : 0 < a := by exact_mod_cast haR
  have hw (n : ℕ) (_hn : n ≤ N) : 0 ≤ zetaPrimeExpWeight s.re (a + n) :=
    (Real.exp_pos _).le
  have hm : AntitoneOn (fun n : ℕ => zetaPrimeExpWeight s.re (a + n)) (Set.Icc 0 N) := by
    intro i _ j _ hij
    apply DirichletSecondDerivativeBound.damping_antitoneOn hσ
    · change (0 : ℝ) < (a + i : ℕ)
      exact_mod_cast (show 0 < a + i by omega)
    · change (0 : ℝ) < (a + j : ℕ)
      exact_mod_cast (show 0 < a + j by omega)
    · exact_mod_cast (show a + i ≤ a + j by omega)
  simpa only [← feature_eq_damped s ha, Nat.add_zero] using
    h M ((le_max_left _ _).trans hM) s.im a htlo hthi halo hahi N hN
      (fun n => zetaPrimeExpWeight s.re (a + n)) hw hm

end
end RiemannGaussian.VinogradovDampedSaving
