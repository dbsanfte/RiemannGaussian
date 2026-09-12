/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAngularPhaseExclusion
import RiemannGaussian.ZetaPhaseExactZeroBound

/-!
# The existing exact phase family in the signed angular detector

The repository's mathematically defined contact family supplies the
general angular theorem with every coefficient, phase positivity and
frequency cost proved. Its existing source and mass enclosures give
the larger coefficient range `0<C<22*pi/(1525*log(2))`. No coefficient
search or new numerical definition is used.
-/

namespace RiemannGaussian.ZetaExactPhaseAngularExclusion
noncomputable section
open Filter ZetaAngularPhaseAllowance ZetaLogLogScale
open scoped Topology

/-- The existing exact contact family is summable before applying
the different angular cost functional. -/
theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The complete logarithmic frequency cost is finite for the exact
family, including each of its separated high frequencies. -/
theorem exact_log_summable :
    Summable (fun n ↦ tail phaseContactExactFamily n * Real.log (n : ℝ)) := by
  have h := (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun n ↦ Real.log (n : ℝ))).summable
  apply h.congr
  intro n
  by_cases hn : n = 0 <;> simp [tail, hn, phaseContactExactFamily]

/-- The full nonconstant mass is the previously bounded exact
oscillatory mass, with every nonconstant coefficient retained. -/
theorem mass_eq_oscillatoryMass :
    mass phaseContactExactFamily = phaseOscillatoryMass phaseContactExactFamily := by
  unfold mass
  rw [(tail_summable phaseContactExactFamily_nonneg exact_summable).tsum_eq_zero_add]
  simp [tail, phaseOscillatoryMass]

/-- The exact contact family has positive nonconstant mass, bounded
by its existing enclosure under the new angular budget. -/
theorem mass_bounds : 0 < mass phaseContactExactFamily ∧
    mass phaseContactExactFamily ≤ 61 / 100 := by
  constructor
  · apply (tail_summable phaseContactExactFamily_nonneg exact_summable).tsum_pos
      (tail_nonneg phaseContactExactFamily_nonneg) 1
    change 0 < phaseContactFrequencyFamily phaseContactExactCoefficients (phaseContactFrequency 1)
    rw [phaseContactFrequencyFamily_apply]
    exact phaseContactExactCoefficients_pos 1
  · rw [mass_eq_oscillatoryMass]
    exact phaseContactExactFamily_oscillatoryMass_le

/-- The selected source at the existing shift remains the exact
contact root under the new boundary estimate. -/
theorem source_margin :
    PhasePoleMargin.margin (phaseContactExactFamily 0) (phaseContactExactFamily 1) (13 / 4) =
      phaseContactExactRoot 8 := by
  calc
    _ = phaseContactSource phaseContactExactFamily := by
      unfold PhasePoleMargin.margin phaseContactSource
      ring
    _ = _ := phaseContactExactFamily_source

/-- The entire actual angular cost is strictly below the unchanged
exact source throughout the stated open coefficient range. -/
theorem coefficient_surplus {C : ℝ} (hC : 0 < C)
    (hlim : 1525 * C * Real.log 2 < 22 * Real.pi) :
    2 * mass phaseContactExactFamily * C * Real.log 2 <
      Real.pi * PhasePoleMargin.margin (phaseContactExactFamily 0) (phaseContactExactFamily 1)
        (13 / 4) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_right mass_bounds.2 (mul_pos hC hlog).le
  have hs := mul_le_mul_of_nonneg_left phaseContactExactRoot_source_lower Real.pi_pos.le
  rw [source_margin]
  nlinarith only [hlim, hm, hs]

/-- The existing exact family now excludes actual right-edge zeros
for every coefficient below `22*pi/(1525*log(2))`, with a finite
coefficient-dependent threshold and no unproved arithmetic input. -/
theorem exists_eventual_margin {C : ℝ} (hC : 0 < C)
    (hlim : 1525 * C * Real.log 2 < 22 * Real.pi) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      width C |ρ.1.im| < 1 - ρ.1.re := by
  apply ZetaAngularPhaseExclusion.exists_eventual_margin
    phaseContactExactFamily_nonneg exact_summable
    phaseContactExactFamily_kernel_nonneg (by norm_num) (by norm_num)
    (fun n hn ↦ by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    exact_log_summable mass_bounds.1 hC (by norm_num : (0 : ℝ) < 13 / 4)
  exact coefficient_surplus hC hlim

end
end RiemannGaussian.ZetaExactPhaseAngularExclusion
