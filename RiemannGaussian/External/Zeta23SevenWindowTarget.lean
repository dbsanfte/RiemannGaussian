/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.External.Zeta23BlockEndgame
import RiemannGaussian.MontgomeryTaylorSevenWindowParameters
import RiemannGaussian.MontgomeryTaylorSevenWindowModel

/-!
# Exact numerical target and its remaining seven-point input

These parameters translate a uniform seven-point floor into a literal
simple-critical-zero proportion exceeding `6731/10000`. The analytic inputs
and coefficient comparisons are proved here. The floor remains an explicit
input to this reusable module; the optional integer certificate supplies it.
-/

namespace RiemannGaussian.Zeta23InverseSampling
noncomputable section
open scoped BigOperators
open MontgomeryTaylorSevenWindowParameters

/-- The fixed kernel coefficient is the complement of the exact imported
Montgomery--Taylor baseline. -/
theorem kernel_eta_eq_baseline_complement :
    MontgomeryTaylorKernelFormula.eta = 3 / 2 - Zeta23.ThmD.HD 1 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp [hs.ne']
    nlinarith
  rw [MontgomeryTaylorKernelFormula.eta_eq_cos_div, Zeta23.ThmD.HD_one, ← hinv]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact ratio associated with the proposed seven-point floor. This
definition does not assert that the floor has been verified. -/
def sevenWindowTargetCoefficient : ℝ :=
  (5180000 * Zeta23.ThmD.HD 1 - 10320) / 5160013

/-- The proposed coefficient is rigorously above 67.31 percent; this is an
arithmetic comparison, independent of the remaining uniform-floor proof. -/
theorem sevenWindowTargetCoefficient_gt_6731 :
    (6731 : ℝ) / 10000 < sevenWindowTargetCoefficient := by
  have he := MontgomeryTaylorNumericalKernel.eta_bounds.2
  rw [kernel_eta_eq_baseline_complement] at he
  unfold sevenWindowTargetCoefficient
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 5160013)]
  nlinarith

/-- Exact rational enclosure for the proposed coefficient. -/
theorem sevenWindowTargetCoefficient_bounds :
    (6731055996 : ℝ) / 10000000000 < sevenWindowTargetCoefficient ∧
      sevenWindowTargetCoefficient < (6731055998 : ℝ) / 10000000000 := by
  have he := MontgomeryTaylorNumericalKernel.eta_bounds
  rw [kernel_eta_eq_baseline_complement] at he
  unfold sevenWindowTargetCoefficient
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 5160013)]
    nlinarith [he.2]
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 5160013)]
    nlinarith [he.1]

/-- The proposed coefficient improves the imported exact baseline by over 0.0006. -/
theorem sevenWindowTargetCoefficient_gain :
    (3 : ℝ) / 5000 < sevenWindowTargetCoefficient - Zeta23.ThmD.HD 1 := by
  have he := MontgomeryTaylorNumericalKernel.eta_bounds.2
  rw [kernel_eta_eq_baseline_complement] at he
  unfold sevenWindowTargetCoefficient
  have hden : (0 : ℝ) < 5160013 := by norm_num
  have h : (3 : ℝ) / 5000 + Zeta23.ThmD.HD 1 <
      (5180000 * Zeta23.ThmD.HD 1 - 10320) / 5160013 := by
    rw [lt_div_iff₀ hden]
    nlinarith
  linarith

/-- Translate a uniform seven-point floor in cycle units into the affine
259-point block input in the radian units of the actual sampler. -/
theorem blockFloor_of_sevenWindowFloor
    (hfloor : ∀ x : ℕ → ℝ, Monotone x → targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy
        (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) pairWeight x 6 0 +
      MontgomeryTaylorWindowEnergy.windowPressure pressureWeight x 6 0) :
    ∀ x : ℕ → ℝ, Monotone x → (19987 : ℝ) / 20000 ≤
      MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x 259 +
          (1 / (1000 * Real.pi)) * (x 258 - x 0) := by
  intro x hx
  let y : ℕ → ℝ := fun i => x i / (2 * Real.pi)
  have hy : Monotone y := fun _ _ hij => div_le_div_of_nonneg_right
    (hx hij) (by positivity)
  have hlocal : ∀ start < 253, targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy
        (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) pairWeight y 6 start +
      MontgomeryTaylorWindowEnergy.windowPressure pressureWeight y 6 start := by
    intro start _
    have h := hfloor (fun i => y (start + i))
      (fun _ _ hij => hy (Nat.add_le_add_left hij start))
    simpa only [MontgomeryTaylorWindowEnergy.windowEnergy,
      MontgomeryTaylorWindowEnergy.windowPressure, Nat.zero_add, Nat.add_assoc] using h
  have hblock := block_floor_of_local_floors
    (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) (fun _ => sq_nonneg _) y hy hlocal
  have hscale : ∀ a b : ℝ,
      2 * Real.pi * (a / (2 * Real.pi) - b / (2 * Real.pi)) = a - b := by
    intro a b
    field_simp
  simp only [MontgomeryTaylorWindowEnergy.lagEnergy, y, hscale] at hblock ⊢
  convert hblock using 1
  field_simp
  ring

/-- The exact remaining seven-point floor would give the proposed
coefficient for the literal zeta counting functions. -/
theorem simpleCritical_of_sevenWindowFloor
    (hfloor : ∀ x : ℕ → ℝ, Monotone x → targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy
        (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) pairWeight x 6 0 +
      MontgomeryTaylorWindowEnergy.windowPressure pressureWeight x 6 0) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sevenWindowTargetCoefficient - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have hmain := simpleCritical_of_blockFloor 258 (by norm_num)
    (A := 19987 / 20000) (B := 1 / (1000 * Real.pi))
    (by norm_num) (by positivity) (by norm_num) (blockFloor_of_sevenWindowFloor hfloor)
  have hcoef :
      ((259 : ℝ) * Zeta23.ThmD.HD 1 - 2 * 258 * Real.pi * (1 / (1000 * Real.pi))) /
          (259 - 19987 / 20000) = sevenWindowTargetCoefficient := by
    unfold sevenWindowTargetCoefficient
    field_simp
    ring
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hmain hcoef
  rw [hcoef] at hmain
  exact hmain

/-- Exact rational endpoint with the uniform floor explicitly outstanding.
No stronger numerical zeta certificate is claimed by this implication. -/
theorem simpleCritical_6731_of_sevenWindowFloor
    (hfloor : ∀ x : ℕ → ℝ, Monotone x → targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy
        (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) pairWeight x 6 0 +
      MontgomeryTaylorWindowEnergy.windowPressure pressureWeight x 6 0) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simpleCritical_of_sevenWindowFloor hfloor ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right sevenWindowTargetCoefficient_gt_6731.le ε) (Nat.cast_nonneg _)).trans
      (hT₀ T hT)

/-- A kernel-certified floor on the explicit compact six-gap box would
complete the 67.31 percent certificate for the literal zero counts.
The compact inequality remains the only undischarged input. -/
theorem simpleCritical_6731_of_compact_model_floor
    (hfloor : ∀ g : Fin 6 → ℝ, (∀ j, g j ∈ Set.Icc (1 / 3) 20) →
      modelFloor ≤ MontgomeryTaylorSevenWindowModel.finiteModel g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) :=
  simpleCritical_6731_of_sevenWindowFloor
    (MontgomeryTaylorSevenWindowModel.window_floor_of_compact_model_floor hfloor)

end
end RiemannGaussian.Zeta23InverseSampling
