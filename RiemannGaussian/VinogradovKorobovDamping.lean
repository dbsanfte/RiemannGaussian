/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovKorobovBlock
import RiemannGaussian.DirichletDyadicBlocks

/-!
# Product-phase approximation with the actual Dirichlet damping

Exact Abel summation transports the complex product-shift approximation
through any nonnegative decreasing amplitude. A prefix error proportional
to its length pays the actual total amplitude, rather than the block
length times the largest amplitude.

The final theorem applies to the repository's literal `zetaPrimeFeature`
at every positive integer starting point and every nonnegative real part.
All polynomial phases and signed endpoint corrections remain in the
complex approximation. No quantitative polynomial-sum saving is assumed.
-/

namespace RiemannGaussian.VinogradovKorobovDamping
noncomputable section
open scoped BigOperators
open VinogradovKorobovBlock

/-- Exact Abel transport of a prefix family; `N` is the last term index,
so the original weighted block contains `N+1` terms. -/
def abelTransform (w F : ℕ → ℂ) (N : ℕ) : ℂ :=
  w N * F (N + 1) + ∑ n ∈ Finset.range N, (w n - w (n + 1)) * F (n + 1)

/-- The original weighted terms are exactly the Abel transform of their
full complex prefixes. -/
theorem weighted_identity (w f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * f n) =
      abelTransform w (block f) N :=
  FiniteAbelVariation.weighted_sum_eq w f N

/-- Subtracting two prefix families preserves the full complex transform. -/
theorem abelTransform_sub (w F G : ℕ → ℂ) (N : ℕ) :
    abelTransform w F N - abelTransform w G N =
      abelTransform w (fun L => F L - G L) N := by
  simp only [abelTransform, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The length-weighted Abel coefficients have exactly the original
amplitude mass, with no initial-weight majorant. -/
theorem abel_length_mass (w : ℕ → ℝ) (N : ℕ) :
    w N * (N + 1 : ℕ) +
      (∑ n ∈ Finset.range N, (w n - w (n + 1)) * (n + 1 : ℕ)) =
      ∑ n ∈ Finset.range (N + 1), w n := by
  have h := FiniteAbelVariation.weighted_sum_eq (fun n => (w n : ℂ)) (fun _ => 1) N
  simpa using (congrArg Complex.re h).symm

/-- A linear prefix-error allowance pays exactly the total amplitude for
every nonnegative decreasing real weight. -/
theorem abelTransform_norm_le (w : ℕ → ℝ) (F : ℕ → ℂ) (N : ℕ) {E : ℝ}
    (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N))
    (hF : ∀ n ≤ N, ‖F (n + 1)‖ ≤ (n + 1 : ℕ) * E) :
    ‖abelTransform (fun n => (w n : ℂ)) F N‖ ≤
      E * ∑ n ∈ Finset.range (N + 1), w n := by
  have hd (n : ℕ) (hn : n < N) : 0 ≤ w n - w (n + 1) := by
    exact sub_nonneg.mpr (hm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  unfold abelTransform
  calc
    _ ≤ ‖(w N : ℂ) * F (N + 1)‖ +
        ∑ n ∈ Finset.range N, ‖((w n : ℂ) - (w (n + 1) : ℂ)) * F (n + 1)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w N * ((N + 1 : ℕ) * E) +
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * ((n + 1 : ℕ) * E) := by
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
        ∑ n ∈ Finset.range N, (w n - w (n + 1)) * (n + 1 : ℕ)) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro n hn
        ring
    _ = _ := by rw [abel_length_mass]

/-- The product-phase approximation transports through every decreasing
amplitude with the explicit Taylor allowance times its actual mass. -/
theorem weighted_approximation_error_le {z M₁ M₂ : ℝ}
    (hz : 0 < z) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℕ) (t : ℝ) (N : ℕ) (A B : Finset ℕ)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : ∀ a ∈ A, (a : ℝ) ≤ M₁) (hB : ∀ b ∈ B, (b : ℝ) ≤ M₂)
    (w : ℕ → ℝ) (hw : ∀ n ≤ N, 0 ≤ w n) (hm : AntitoneOn w (Set.Icc 0 N)) :
    ‖(∑ n ∈ Finset.range (N + 1), (w n : ℂ) * dirichletTerm t z n) -
      abelTransform (fun n => (w n : ℂ)) (fun L => approximation k t z L A B) N‖ ≤
      (|t| * (M₁ * M₂ / z) ^ (k + 1) / (k + 1)) *
        ∑ n ∈ Finset.range (N + 1), w n := by
  rw [weighted_identity, abelTransform_sub]
  apply abelTransform_norm_le w _ N hw hm
  intro n hn
  exact block_sub_approximation_le hz hM₁ hM₂ k t (n + 1) A B hAn hBn hA hB

/-- The actual zeta Dirichlet feature has precisely the amplitude and
imaginary-power term required by the product-shift approximation. -/
theorem feature_eq_damped (s : ℂ) {a : ℕ} (ha : 0 < a) (n : ℕ) :
    zetaPrimeFeature s (a + n) =
      (zetaPrimeExpWeight s.re (a + n) : ℂ) * dirichletTerm s.im a n := by
  rw [ZetaFiniteDifferencing.feature_polar, dirichletTerm_eq (by exact_mod_cast ha)]
  simp only [basePhase, LogarithmicShiftPhase.phase, Nat.cast_add]

/-- The approximation to a block of the original, fully damped zeta terms. -/
def featureApproximation (s : ℂ) (a k N : ℕ) (A B : Finset ℕ) : ℂ :=
  abelTransform (fun n => (zetaPrimeExpWeight s.re (a + n) : ℂ))
    (fun L => approximation k s.im a L A B) N

/-- Every actual positive Dirichlet block inherits the explicit product-
phase error bound, with its full damping mass and signed approximation. -/
theorem feature_approximation_error_le {s : ℂ} (hσ : 0 ≤ s.re)
    {a : ℕ} (ha : 0 < a) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k N : ℕ) (A B : Finset ℕ) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hA : ∀ i ∈ A, (i : ℝ) ≤ M₁) (hB : ∀ j ∈ B, (j : ℝ) ≤ M₂) :
    ‖(∑ n ∈ Finset.range (N + 1), zetaPrimeFeature s (a + n)) -
      featureApproximation s a k N A B‖ ≤
      (|s.im| * (M₁ * M₂ / a) ^ (k + 1) / (k + 1)) *
        ∑ n ∈ Finset.range (N + 1), zetaPrimeExpWeight s.re (a + n) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hw (n : ℕ) (hn : n ≤ N) : 0 ≤ zetaPrimeExpWeight s.re (a + n) :=
    (Real.exp_pos _).le
  have hm : AntitoneOn (fun n : ℕ => zetaPrimeExpWeight s.re (a + n)) (Set.Icc 0 N) := by
    intro i hi j hj hij
    apply DirichletSecondDerivativeBound.damping_antitoneOn hσ
    · change (0 : ℝ) < (a + i : ℕ)
      exact_mod_cast (show 0 < a + i by omega)
    · change (0 : ℝ) < (a + j : ℕ)
      exact_mod_cast (show 0 < a + j by omega)
    · exact_mod_cast (show a + i ≤ a + j by omega)
  simpa only [← feature_eq_damped s ha, featureApproximation] using
    weighted_approximation_error_le haR hM₁ hM₂ k s.im N A B hAn hBn hA hB
      (fun n => zetaPrimeExpWeight s.re (a + n)) hw hm

end
end RiemannGaussian.VinogradovKorobovDamping
