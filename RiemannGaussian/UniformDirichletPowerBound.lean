/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.UniformDerivativePowerBound
import RiemannGaussian.DirichletHigherDerivativeBound

/-!
# Uniform closed power bounds for the actual Dirichlet terms

The proved analytic cutoff simplifies the entire finite derivative
recurrence. For the genuine logarithmic derivatives, even the dyadic
ratio factor is uniformly bounded by four at every order. The original
complex terms and full real damping therefore have a closed power bound
with constants independent of derivative order.

This is a finite high-height toolbox result. Zeta line estimates and
zero detection still have to be supplied before improving the displayed
zero-free region; extra prime or sieve weights need their own control.
-/

namespace RiemannGaussian.UniformDirichletPowerBound
noncomputable section
open DerivativePowerExponents AnalyticDerivativeCutoff DerivativePowerEnvelope
open LogarithmicDerivativeFamily

/-- The actual dyadic derivative ratio, raised to its shrinking
amplitude exponent, is at most four at every order. -/
theorem ratio_amp_le_four (k : ℕ) : (ratio k) ^ amp k ≤ 4 := by
  have hg : ∀ j : ℕ, ((j + 2 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [pow_succ]
      push_cast at ih ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have he : ((k + 2 : ℕ) : ℝ) * amp k ≤ 2 := by
    unfold amp
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mpr (hg k)
  unfold ratio
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at h ⊢
  exact h

/-- The full literal Dirichlet sum satisfies the closed all-order
power estimate, retaining its exact derivative-ratio and damping factors. -/
theorem feature_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      envelope k N (lowerScale s.im X k) (ratio k) * zetaPrimeExpWeight s.re a := by
  have hratio : 1 ≤ ratio k := by
    unfold ratio
    exact one_le_pow₀ (by norm_num)
  apply (DirichletHigherDerivativeBound.feature_bound cutoffs k hσ ht hX a N ha hb).trans
  exact mul_le_mul_of_nonneg_right
    (UniformDerivativePowerBound.budget_bound k N (lowerScale_pos ht hX k) hratio)
    (Real.exp_pos _).le

/-- The entire original finite Dirichlet sum has one closed estimate
whose leading and complementary constants are uniform in derivative order. -/
theorem uniform_bound (k : ℕ) {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) (a N : ℕ) (ha : X ≤ (a : ℝ)) (hb : (a : ℝ) + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, zetaPrimeFeature s (a + n)‖ ≤
      32 * (4 * N * (lowerScale s.im X k) ^ alpha k +
        (N : ℝ) ^ beta k * (lowerScale s.im X k) ^ (-alpha k)) *
          zetaPrimeExpWeight s.re a := by
  apply (feature_bound k hσ ht hX a N ha hb).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  unfold envelope mainTerm errorTerm
  have hscale := lowerScale_pos ht hX k
  gcongr
  exact ratio_amp_le_four k

end
end RiemannGaussian.UniformDirichletPowerBound
