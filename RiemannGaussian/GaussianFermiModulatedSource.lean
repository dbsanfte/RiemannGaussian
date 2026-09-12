/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiModulatedBudget

/-!
# The complete resonant source and pole for a modulated Gaussian

The three actual zero evaluations equal the Fermi transform of the
retained modulated window. Both horizontal partners supply one full
analytic multiplicity. The source is bounded below, and the constant
pole above, by the real Laplace transform of that same window. The
general all-family zero budget then keeps this new source without
increasing the complete outside allowance.
-/

namespace RiemannGaussian.GaussianFermiModulatedSource
noncomputable section
open Complex Filter Set
open MeasureTheory hiding average
open scoped Topology Classical
open FermiLaplaceReflection FermiCosineModulation GaussianFermiModulatedBudget
open GaussianFermiZeroPair GaussianFermiZeroTail GaussianFermiPoleFormula
open GaussianFermiResonantBudget GaussianFermiMovingAllowance

/-- Averaging the three actual ordinates is exactly the transform of
the modulated window, at every complex center. -/
theorem average_transform (δ a : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hi : ∀ x : ℝ, Integrable (fun u : ℝ ↦ g u * Real.exp (-x * u))) (z : ℂ) (t : ℝ) :
    average δ (fun v ↦ (transform a g (z + I * v)).re) t =
      (transform a (modulate δ g) (z + I * t)).re := by
  have h := congrArg Complex.re (transform_modulate δ a hg hi (z + I * t))
  have hp : z + I * t + I * δ = z + I * ((t + δ : ℝ) : ℂ) := by push_cast; ring
  have hm : z + I * t - I * δ = z + I * ((t - δ : ℝ) : ℂ) := by push_cast; ring
  rw [hp, hm] at h
  simpa only [average, Complex.add_re, Complex.div_ofNat_re] using h.symm

/-- The original modulated contribution retains both physical partners
and the exact analytic multiplicity at every evaluation ordinate. -/
theorem average_contribution_eq {B : ℝ} (hB : 0 < B) (δ σ t : ℝ) (ρ : NontrivialZetaZero) :
    average δ (fun v ↦ contribution B σ v ρ) t =
      (analyticZetaZeroMultiplicity ρ : ℝ) / 2 *
        (transform (2 * σ - 1) (modulate δ (window B)) (((σ : ℂ) - ρ.1) + I * t) +
          transform (2 * σ - 1) (modulate δ (window B))
            (((σ : ℂ) - (1 - starRingEnd ℂ ρ.1)) + I * t)).re := by
  have h1 := average_transform δ (2 * σ - 1) (continuous_window B)
    (integrable_window_exp hB) ((σ : ℂ) - ρ.1) t
  have h2 := average_transform δ (2 * σ - 1) (continuous_window B)
    (integrable_window_exp hB) ((σ : ℂ) - (1 - starRingEnd ℂ ρ.1)) t
  have he (z : ℂ) (v : ℝ) : (σ : ℂ) + (v : ℂ) * I - z = ((σ : ℂ) - z) + I * v := by ring
  unfold average at h1 h2 ⊢
  simp only [contribution, he, Complex.add_re]
  linear_combination (analyticZetaZeroMultiplicity ρ : ℝ) / 2 * h1 +
    (analyticZetaZeroMultiplicity ρ : ℝ) / 2 * h2

/-- At the selected zero's ordinate, the complete average has the real
source arguments of the same modulated time window. -/
theorem average_contribution_at_ordinate {B : ℝ} (hB : 0 < B) (δ σ : ℝ) (ρ : NontrivialZetaZero) :
    average δ (fun v ↦ contribution B σ v ρ) ρ.1.im =
      (analyticZetaZeroMultiplicity ρ : ℝ) / 2 *
        ((transform (2 * σ - 1) (modulate δ (window B)) ((σ - ρ.1.re : ℝ) : ℂ)).re +
          (transform (2 * σ - 1) (modulate δ (window B)) ((σ + ρ.1.re - 1 : ℝ) : ℂ)).re) := by
  have h1 : ((σ : ℂ) - ρ.1) + I * ρ.1.im = ((σ - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have h2 : ((σ : ℂ) - (1 - starRingEnd ℂ ρ.1)) + I * ρ.1.im =
      ((σ + ρ.1.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  rw [average_contribution_eq hB, h1, h2, Complex.add_re]

/-- The genuine modulated resonant contribution contains its complete
Laplace source with a nonnegative retained Fermi reserve. -/
theorem halfLaplace_le_contribution {B σ : ℝ} (hB : 0 < B) (δ : ℝ)
    (ρ : NontrivialZetaZero) (hρ : ρ.1.re ≤ σ) :
    (analyticZetaZeroMultiplicity ρ : ℝ) / 2 * halfLaplace (modulate δ (window B)) (σ - ρ.1.re) ≤
      average δ (fun v ↦ contribution B σ v ρ) ρ.1.im := by
  rw [average_contribution_at_ordinate hB]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := halfLaplace_le_real_pair (2 * σ - 1)
    (continuous_modulate δ (continuous_window B))
    (modulate_nonneg δ (fun u ↦ (Real.exp_pos _).le))
    (fun x ↦ integrable_modulate_exp δ (continuous_window B) x (integrable_window_exp hB x))
    (show 0 ≤ σ - ρ.1.re by linarith)
  rw [show 2 * σ - 1 - (σ - ρ.1.re) = σ + ρ.1.re - 1 by ring] at h
  exact h

/-- The two distinct actual horizontal partners carry the full
multiplicity times the Laplace source, with all three frequencies kept. -/
theorem halfLaplace_le_partner_pair {B σ : ℝ} (hB : 0 < B) (δ : ℝ)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hσ : ρ.1.re ≤ σ) :
    (analyticZetaZeroMultiplicity ρ : ℝ) * halfLaplace (modulate δ (window B)) (σ - ρ.1.re) ≤
      average δ (fun v ↦ ∑ η ∈ ({ρ, NontrivialZetaZero.conjugatePartner ρ} : Finset NontrivialZetaZero),
        contribution B σ v η) ρ.1.im := by
  simp_rw [sum_partner_pair_eq B σ _ ρ hρ]
  have h := halfLaplace_le_contribution hB δ ρ hσ
  unfold average at h ⊢
  linarith

/-- The complete averaged constant pole is the exact real pair for
the same modulated window; its shifted pole phases are combined first. -/
theorem average_pole_zero_eq {B : ℝ} (hB : 0 < B) (δ σ : ℝ) :
    average δ (polePair B σ) 0 =
      (transform (2 * σ - 1) (modulate δ (window B)) (σ : ℂ)).re +
        (transform (2 * σ - 1) (modulate δ (window B)) ((σ - 1 : ℝ) : ℂ)).re := by
  have h1 := average_transform δ (2 * σ - 1) (continuous_window B)
    (integrable_window_exp hB) (σ : ℂ) 0
  have h2 := average_transform δ (2 * σ - 1) (continuous_window B)
    (integrable_window_exp hB) ((σ - 1 : ℝ) : ℂ) 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at h1 h2
  have he (z : ℂ) (v : ℝ) : z + (v : ℂ) * I = z + I * v := by ring
  unfold average at h1 h2 ⊢
  simp only [polePair_eq_physical, he]
  linarith

/-- The actual averaged constant pole has one modulated Laplace upper
bound. Separating the three ordinates would lose this estimate. -/
theorem average_pole_zero_le {B σ : ℝ} (hB : 0 < B) (δ : ℝ) (hσ : σ ≤ 1) :
    average δ (polePair B σ) 0 ≤ halfLaplace (modulate δ (window B)) (σ - 1) := by
  rw [average_pole_zero_eq hB]
  have h := real_pole_pair_le_halfLaplace (continuous_modulate δ (continuous_window B))
    (modulate_nonneg δ (fun u ↦ (Real.exp_pos _).le))
    (fun x ↦ integrable_modulate_exp δ (continuous_window B) x (integrable_window_exp hB x)) hσ
  linarith

/-- Every admissible original phase family now has the modulated
resonant source in its actual zero budget, with the same complete outside
allowance and both selected horizontal partners accounted for. -/
theorem resonant_pair_phase_bound {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {m H b c δ : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hm : zetaPoleReserveZeroMargin H ≤ m) (hmu : m ≤ 1 / 4) (hscale : m ^ 2 ≤ b + c)
    (hzeros : ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H → m ≤ ρ.1.re ∧ ρ.1.re ≤ 1 - m)
    (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (hheight : |ρ.1.im| ≤ H)
    (ht : ∀ j ∈ J, 2 * (|ω j * ρ.1.im| + |δ|) ≤ H)
    (j₀ : ι) (hj₀ : j₀ ∈ J) (hω : ω j₀ = 1) :
    w j₀ * (analyticZetaZeroMultiplicity ρ : ℝ) *
      halfLaplace (modulate δ (window (b + c))) ((1 - m) - ρ.1.re) ≤
      (∑ j ∈ J, w j * average δ (fun v ↦ polePair (b + c) (1 - m) v - Real.log Real.pi / 4 +
        digammaAverage (1 - 2 * m) b c v) (ω j * ρ.1.im)) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  let S : Finset NontrivialZetaZero := {ρ, NontrivialZetaZero.conjugatePartner ρ}
  have hS : ∀ η ∈ S, |η.1.im| ≤ H := by
    intro η hη
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hη
    rcases hη with rfl | rfl
    · exact hheight
    · simpa [NontrivialZetaZero.conjugatePartner_coe] using hheight
  have hn (v : ℝ) : 0 ≤ ∑ η ∈ S, contribution (b + c) (1 - m) v η := by
    apply Finset.sum_nonneg
    intro η hη
    exact GaussianFermiMarginBudget.contribution_nonneg_of_strip (add_pos hb hc) hmu v η
      (hzeros η (hS η hη)).1 (hzeros η (hS η hη)).2
  have havg (v : ℝ) : 0 ≤ average δ (fun v ↦ ∑ η ∈ S, contribution (b + c) (1 - m) v η) v := by
    unfold average
    linarith [hn v, hn (v + δ), hn (v - δ)]
  have hs := Finset.single_le_sum (fun j hj ↦ mul_nonneg (hw j hj) (havg (ω j * ρ.1.im))) hj₀
  have hsource := mul_le_mul_of_nonneg_left
    (halfLaplace_le_partner_pair (add_pos hb hc) δ ρ hρ (hzeros ρ hheight).2) (hw j₀ hj₀)
  rw [hω, one_mul] at hs
  have hbudget := GaussianFermiModulatedBudget.selected_zero_phase_budget J w ω hw hphase
    hH hb hc hm hmu hscale hzeros ht S hS
  dsimp [S] at hs hbudget
  simpa only [mul_assoc] using (hsource.trans hs).trans hbudget

end
end RiemannGaussian.GaussianFermiModulatedSource
