/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiGammaBound
import RiemannGaussian.GaussianFermiLaplaceOrder

/-!
# A Gaussian comparison for every genuine right-half zero

Retaining both distinct horizontal partners cancels the pair-counting
factor of two. At the common zero ordinate the exact Fermi partition
gives a Gaussian half-line lower bound with a nonnegative reserve.
The general phase budget then bounds this source by the proved Gaussian
pole envelope, explicit gamma costs and the complete outside allowance.
-/

namespace RiemannGaussian.GaussianFermiResonantBudget

noncomputable section
open Complex MeasureTheory Set
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiZeroTail
open GaussianFermiPoleFormula GaussianFermiMovingAllowance GaussianFermiGammaBound
open GaussianFermiLaplaceOrder

/-- Horizontal partners have equal full Fermi contributions, including
their genuine analytic multiplicities. -/
theorem contribution_conjugatePartner (b σ t : ℝ) (ρ : NontrivialZetaZero) :
    contribution b σ t (NontrivialZetaZero.conjugatePartner ρ) =
      contribution b σ t ρ := by
  simp [contribution, NontrivialZetaZero.conjugatePartner_coe, map_sub, add_comm]

/-- At the zero's own ordinate both arguments become real. The same-phase
physical partner is retained exactly. -/
theorem contribution_at_ordinate (b σ : ℝ) (ρ : NontrivialZetaZero) :
    contribution b σ ρ.1.im ρ = (analyticZetaZeroMultiplicity ρ : ℝ) / 2 *
      ((transform (2 * σ - 1) (window b) ((σ - ρ.1.re : ℝ) : ℂ)).re +
        (transform (2 * σ - 1) (window b) ((σ + ρ.1.re - 1 : ℝ) : ℂ)).re) := by
  have hleft : (σ : ℂ) + (ρ.1.im : ℂ) * I - ρ.1 = ((σ - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hright : (σ : ℂ) + (ρ.1.im : ℂ) * I - (1 - starRingEnd ℂ ρ.1) =
      ((σ + ρ.1.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [contribution, hleft, hright, Complex.add_re]

/-- The actual resonant contribution has the Gaussian lower bound whenever
the evaluation line lies to the right of that zero. -/
theorem halfGaussian_le_contribution {b σ : ℝ} (hb : 0 < b)
    (ρ : NontrivialZetaZero) (hρ : ρ.1.re ≤ σ) :
    (analyticZetaZeroMultiplicity ρ : ℝ) / 2 * halfGaussian b (σ - ρ.1.re) ≤
      contribution b σ ρ.1.im ρ := by
  rw [contribution_at_ordinate]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := halfGaussian_le_real_pair hb (show 0 ≤ σ - ρ.1.re by linarith) (2 * σ - 1)
  rw [show 2 * σ - 1 - (σ - ρ.1.re) = σ + ρ.1.re - 1 by ring] at h
  exact h

/-- Off the critical line the horizontal partners are distinct; summing
both genuine zeros removes the normalization factor `1/2` exactly. -/
theorem sum_partner_pair_eq (b σ t : ℝ) (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) :
    (∑ η ∈ ({ρ, NontrivialZetaZero.conjugatePartner ρ} : Finset NontrivialZetaZero),
      contribution b σ t η) = 2 * contribution b σ t ρ := by
  classical
  have hne : ρ ≠ NontrivialZetaZero.conjugatePartner ρ := by
    intro he
    have hr := congrArg (fun η : NontrivialZetaZero => η.1.re) he
    simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re,
      Complex.one_re, Complex.conj_re] at hr
    linarith
  rw [Finset.sum_pair hne, contribution_conjugatePartner]
  ring

/-- The complete distinct horizontal pair carries one full multiplicity
times the Gaussian source, not half that amount. -/
theorem halfGaussian_le_partner_pair {b σ : ℝ} (hb : 0 < b)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hσ : ρ.1.re ≤ σ) :
    (analyticZetaZeroMultiplicity ρ : ℝ) * halfGaussian b (σ - ρ.1.re) ≤
      ∑ η ∈ ({ρ, NontrivialZetaZero.conjugatePartner ρ} : Finset NontrivialZetaZero),
        contribution b σ ρ.1.im η := by
  rw [sum_partner_pair_eq b σ ρ.1.im ρ hρ]
  linarith [halfGaussian_le_contribution hb ρ hσ]

/-- Every right-half zero and admissible phase family obey this genuine
Gaussian source comparison. Both horizontal partners are selected from the
actual divisor, all multiplicities are retained, and every upper term is
proved: the pole envelope, gamma cost and full outside allowance. -/
theorem resonant_pair_phase_bound {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {H b c : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hscale : zetaPoleReserveZeroMargin H ^ 2 ≤ b + c) (hupper : b + c ≤ 1)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hheight : |ρ.1.im| ≤ H)
    (ht : ∀ j ∈ J, 2 * |ω j * ρ.1.im| ≤ H)
    (j₀ : ι) (hj₀ : j₀ ∈ J) (hω : ω j₀ = 1) :
    let σ := 1 - zetaPoleReserveZeroMargin H;
    w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) * halfGaussian (b + c) (σ - ρ.1.re) ≤
      (∑ j ∈ J, w j * (poleUpper (b + c) σ (ω j * ρ.1.im) +
        (Real.log (5 / 4 + |ω j * ρ.1.im|) - Real.log Real.pi) / 4 +
        7 / (8 * (5 / 4 + |ω j * ρ.1.im|)))) +
          (∑ j ∈ J, w j) * allowance (b + c) H := by
  classical
  let σ := 1 - zetaPoleReserveZeroMargin H
  let S : Finset NontrivialZetaZero := {ρ, NontrivialZetaZero.conjugatePartner ρ}
  have hS : ∀ η ∈ S, |η.1.im| ≤ H := by
    intro η hη
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl
    · exact hheight
    · simpa [NontrivialZetaZero.conjugatePartner_coe] using hheight
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hσ0 : 1 / 2 ≤ σ := by dsimp [σ]; linarith [hm.2]
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith [hm.1]
  have hσscale : (1 - σ) ^ 2 ≤ b + c := by simpa [σ] using hscale
  have hB : 0 < b + c := add_pos hb hc
  have hre : ρ.1.re ≤ σ := by
    have hmle := zetaPoleReserveZeroMargin_antitone_abs
      (show |ρ.1.im| ≤ |H| by rwa [abs_of_nonneg (by linarith : 0 ≤ H)])
    have hr := (nontrivialZetaZero_mem_poleReserve_strip ρ).2
    dsimp [σ]
    linarith
  have hn (j : ι) (hj : j ∈ J) :
      0 ≤ w j * ∑ η ∈ S, contribution (b + c) σ (ω j * ρ.1.im) η := by
    apply mul_nonneg (hw j hj)
    apply Finset.sum_nonneg
    intro η hη
    unfold contribution
    apply mul_nonneg (by positivity)
    exact nontrivial_zero_pair_re_nonneg_on_band hB H (ω j * ρ.1.im) η
      (by simpa only [abs_of_nonneg (show 0 ≤ H by linarith)] using hS η hη)
  have hsource : w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) *
      halfGaussian (b + c) (σ - ρ.1.re) ≤
      w j₀ * ∑ η ∈ S, contribution (b + c) σ (ω j₀ * ρ.1.im) η := by
    rw [hω, one_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (halfGaussian_le_partner_pair hB ρ hρ hre) (hw j₀ hj₀)
  have hphasebudget := selected_zero_phase_log_budget J w ω hw hphase hH hb hc
    hscale hupper ht S hS
  apply (hsource.trans (Finset.single_le_sum hn hj₀)).trans
  apply hphasebudget.trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  have h := polePair_le_poleUpper hB hσ0 hσ1 hσscale (ω j * ρ.1.im)
  change polePair (b + c) σ (ω j * ρ.1.im) + _ + _ ≤ _
  linarith

end
end RiemannGaussian.GaussianFermiResonantBudget
