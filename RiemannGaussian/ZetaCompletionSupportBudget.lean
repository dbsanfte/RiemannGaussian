/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinSupportFloor
import RiemannGaussian.ZetaCompletionReserveZeroFree

/-!
# Support-sensitive arithmetic energy in the retained completion budget

The larger support factor and the negative completion constant coexist in
the same source inequality for all admissible real-frequency families.
For the existing exact family, the energy is an explicit finite expression
in its unchanged coefficients and all linked phases. Every actual zero
near the right edge obeys the resulting necessary inequality. Violating
that explicit inequality gives a literal zeta nonvanishing theorem.

The energy has a proved uniform lower bound. No claim is made that it
beats the growing logarithmic allowance throughout the interior strip.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Classical Topology

/-- The whole phase energy, the selected genuine zero multiplicity,
and the recovered completion reserve share one all-family budget. The
true signed pole subtraction is still present on the right. -/
theorem zetaPhase_source_add_supportEnergy_add_completionReserve_le
    {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (j : ℕ) (hj : ω j = 1)
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re)
    {σ : ℝ} (hσ : 1 < σ) (hσu : σ ≤ 5 / 4)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * rho.1.im|)))) :
    a j * (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) +
      zetaStechkinSupportFactor σ 2 *
        ((Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
          ((∑' n, a n * (2 + 2 * Real.cos (ω n * (rho.1.im * Real.log 2))) ^ 10) -
            184756 * (∑' n, a n))) +
      (1 - zetaStechkinWeight σ) * (Real.log 2 / 2) * (∑' n, a n) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * rho.1.im)) +
        (1 - zetaStechkinWeight σ) *
          ∑' n : ℕ, a n * (Real.log (σ + |ω n * rho.1.im|) / 2) := by
  have hb := zetaPhase_stechkin_source_add_primeWork_add_completionReserve_le
    ha hs j hj rho hρ hσ hH
  have he := zetaPhase_stechkin_binomial_energy_support_floor ha hs hP hσ hσu rho.1.im
  linarith

/-- The actual exact family's arithmetic reserve is an explicit finite
function of the sampling line and the ordinate. All nine coefficients
and their linked phases are retained. -/
def phaseContactExactSupportEnergy (σ y : ℝ) : ℝ :=
  zetaStechkinSupportFactor σ 2 *
    ((Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
      ((∑ i : Fin 9, phaseContactExactCoefficients i *
        (2 + 2 * Real.cos ((phaseContactFrequency i : ℝ) * (y * Real.log 2))) ^ 10) -
          184756 * (∑ i : Fin 9, phaseContactExactCoefficients i)))

/-- The finite reserve is exactly the countable-family expression;
this interface changes no phase or normalization. -/
theorem phaseContactExactSupportEnergy_eq (σ y : ℝ) :
    phaseContactExactSupportEnergy σ y =
      zetaStechkinSupportFactor σ 2 *
        ((Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
          ((∑' n, phaseContactExactFamily n *
            (2 + 2 * Real.cos ((n : ℝ) * (y * Real.log 2))) ^ 10) -
              184756 * (∑' n, phaseContactExactFamily n))) := by
  have hm := (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun _ ↦ 1)).tsum_eq
  simp only [mul_one] at hm
  change (∑' n, phaseContactExactFamily n) = _ at hm
  rw [phaseContactExact_binomial_energy_eq_finite, hm]
  rfl

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- This finite expression bounds the actual complete signed
Stechkin prime work from below at every real ordinate. -/
theorem phaseContactExactSupportEnergy_le_primeWork {σ : ℝ}
    (hσ : 1 < σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    phaseContactExactSupportEnergy σ y ≤
      ∑' m : ℕ, zetaStechkinPrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  rw [phaseContactExactSupportEnergy_eq]
  exact zetaPhase_stechkin_binomial_energy_support_floor
    (ω := fun n ↦ (n : ℝ)) phaseContactExactFamily_nonneg exact_summable
    phaseContactExactFamily_kernel_nonneg hσ hσu y

/-- Keeping the finite phases always recovers the support-dependent
uniform floor, so no ordinate loses the preceding arithmetic gain. -/
theorem phaseContactExactSupportEnergy_ge_support_floor {σ : ℝ}
    (hσ : 1 ≤ σ) (y : ℝ) :
    zetaStechkinSupportFactor σ 2 *
      ((1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2)) ≤
        phaseContactExactSupportEnergy σ y := by
  rw [phaseContactExactSupportEnergy_eq]
  exact mul_le_mul_of_nonneg_left
    (phaseContactExact_binomial_energy_reserve_ge_scaled σ (y * Real.log 2))
    (zetaStechkinSupportFactor_pos hσ (by norm_num)).le

/-- The finite phase reserve is at least the stronger uniform floor
throughout the sampling range; the richer expression remains available. -/
theorem phaseContactExactSupportEnergy_ge_one_sixtieth {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 5 / 4) (y : ℝ) :
    (1 / 60 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) ≤
      phaseContactExactSupportEnergy σ y := by
  have h := mul_le_mul_of_nonneg_right
    (two_thirds_le_zetaStechkinSupportFactor hσ hσu)
    (show 0 ≤ (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) by positivity)
  have he := phaseContactExactSupportEnergy_ge_support_floor hσ y
  nlinarith only [h, he]

/-- For every fixed sampling line, the finite energy is largest at
zero phase. Its height dependence is therefore bounded, even though
retaining all phases improves particular arithmetic lower bounds. -/
theorem phaseContactExactSupportEnergy_le_at_zero {σ : ℝ}
    (hσ : 1 ≤ σ) (y : ℝ) :
    phaseContactExactSupportEnergy σ y ≤ phaseContactExactSupportEnergy σ 0 := by
  rw [phaseContactExactSupportEnergy_eq, phaseContactExactSupportEnergy_eq]
  have he := zetaPhase_binomial_energy_le_mass (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable 10 (y * Real.log 2)
  norm_num only [show 2 * 10 = (20 : ℕ) from rfl,
    show (20 : ℕ).choose 10 = 184756 by decide, Nat.cast_ofNat] at he
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left he
      (show 0 ≤ Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520 by positivity))
    (zetaStechkinSupportFactor_pos hσ (P := 2) (by norm_num)).le
  norm_num only [zero_mul, mul_zero, Real.cos_zero, mul_one,
    show (2 + 2 : ℝ) ^ 10 = 1048576 by norm_num, tsum_mul_right]
  nlinarith only [hm]

/-- Every actual zero in the relevant near-edge strip obeys the
explicit finite energy budget. Both recovered reserves are retained;
there is no remaining arithmetic premise in this necessary inequality. -/
theorem phaseContactExact_completionReserve_support_energy_zero_budget
    (rho : NontrivialZetaZero) (hρ : 12 / 13 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) *
      phaseContactExactSupportEnergy (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) rho.1.im ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((481 / 1600 : ℝ) * (1 - rho.1.re) +
          (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) - 1 / 8) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re) := by linarith
  have hσu : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4 := by linarith
  have he := mul_le_mul_of_nonneg_left
    (phaseContactExactSupportEnergy_le_primeWork hσ hσu rho.1.im) hd.le
  have hb := phaseContactExact_completionReserve_zero_budget rho (by linarith)
  linarith

/-- The stronger independent arithmetic floor reaches the literal
zero source with the negative completion constant still in place. -/
theorem phaseContactExact_completionReserve_support_floor_zero_budget
    (rho : NontrivialZetaZero) (hρ : 12 / 13 ≤ rho.1.re) :
    (11 / 625 : ℝ) + ((1 - rho.1.re) / 60) *
      Real.exp (-13 * (1 - rho.1.re) * Real.log 2) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re))) *
        ((481 / 1600 : ℝ) * (1 - rho.1.re) +
          (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - rho.1.re) + |rho.1.im|) - 1 / 8) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 ≤ 1 + (13 / 4 : ℝ) * (1 - rho.1.re) := by linarith
  have hσu : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4 := by linarith
  have he := mul_le_mul_of_nonneg_left
    (phaseContactExactSupportEnergy_ge_one_sixtieth hσ hσu rho.1.im) hd.le
  rw [show -4 * (1 + (13 / 4 : ℝ) * (1 - rho.1.re) - 1) * Real.log 2 =
    -13 * (1 - rho.1.re) * Real.log 2 by ring] at he
  have hb := phaseContactExact_completionReserve_support_energy_zero_budget rho hρ
  nlinarith only [he, hb]

/-- Any point whose explicit finite phase reserve beats the complete
allowance is a nonzero zeta point. The displayed test is a sufficient
region condition, not a claim that every right-half point satisfies it. -/
theorem riemannZeta_ne_zero_of_completion_support_energy {s : ℂ}
    (hs : 12 / 13 ≤ s.re) (hsu : s.re < 1)
    (hbudget :
      (1 - s.re) * (1 - zetaStechkinWeight (1 + (13 / 4 : ℝ) * (1 - s.re))) *
        ((481 / 1600 : ℝ) * (1 - s.re) +
          (61 / 200 : ℝ) * Real.log (1 + (13 / 4 : ℝ) * (1 - s.re) + |s.im|) - 1 / 8) +
        (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
      (11 / 625 : ℝ) + (1 - s.re) *
        phaseContactExactSupportEnergy (1 + (13 / 4 : ℝ) * (1 - s.re)) s.im) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := by intro he; rw [he, Complex.one_re] at hsu; linarith
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero (by linarith : 0 < s.re) hpole⟩
  exact (not_lt_of_ge (phaseContactExact_completionReserve_support_energy_zero_budget rho hs)) hbudget

end
end RiemannGaussian
