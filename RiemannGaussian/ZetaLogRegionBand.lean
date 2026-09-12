/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiSharpZeroFree

/-!
# Feeding any proved logarithmic zero-free region into complete height bands

An eventual logarithmic strip theorem supplies a common margin for every
zero in an entire sufficiently large height band. The bounded-height zeros
are controlled by the existing positive global margin. Instantiating the
general construction with the proved `9/50` region makes that stronger
margin available in the full Fermi phase budget.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter Topology

/-- Every proved positive eventual logarithmic strip coefficient gives
a common margin for the complete actual divisor below a sufficiently
large height, including all zeros below the original threshold. -/
theorem exists_eventual_common_log_margin {a : ℝ} (ha : 0 < a)
    (hregion : ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      a / Real.log |ρ.1.im| < ρ.1.re ∧ ρ.1.re < 1 - a / Real.log |ρ.1.im|) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < a / Real.log H ∧ a / Real.log H < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          a / Real.log H < ρ.1.re ∧ ρ.1.re < 1 - a / Real.log H := by
  obtain ⟨T₀, hT₀, hzero⟩ := hregion
  let T := max T₀ (Real.exp 1)
  let d := zetaFermiZeroMargin T
  have hd : 0 < d := (zetaFermiZeroMargin_bounds T).1
  have hdu : d < 1 / 4 := (zetaFermiZeroMargin_bounds T).2
  have hT1 : 1 ≤ T := hT₀.trans (le_max_left _ _)
  have hTp : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right T₀ (Real.exp 1))
    simpa only [Real.log_exp] using h
  refine ⟨max T (Real.exp (a / d + 1)), hT1.trans (le_max_left _ _), ?_⟩
  intro H hH
  have hTH : T ≤ H := (le_max_left _ _).trans hH
  have hlog : 1 ≤ Real.log H := hlogT.trans (Real.log_le_log hTp hTH)
  have hlogp : 0 < Real.log H := by linarith
  have hlarge : a / d ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos (a / d + 1)) ((le_max_right _ _).trans hH)
    rw [Real.log_exp] at h
    linarith
  have hcap : a / Real.log H ≤ d := by
    apply (div_le_iff₀ hlogp).mpr
    have h := (div_le_iff₀ hd).mp hlarge
    linarith
  refine ⟨div_pos ha hlogp, hcap.trans_lt hdu, ?_⟩
  intro ρ hρH
  by_cases hρT : |ρ.1.im| ≤ T
  · have hm := zetaFermiZeroMargin_antitone_abs
      (show |ρ.1.im| ≤ |T| by simpa only [abs_of_pos hTp] using hρT)
    have hz := nontrivialZetaZero_mem_fermi_strip ρ
    have hsmall : a / Real.log H ≤ zetaFermiZeroMargin ρ.1.im := hcap.trans hm
    exact ⟨hsmall.trans_lt hz.1, by linarith [hz.2]⟩
  · have hTρ : T ≤ |ρ.1.im| := (lt_of_not_ge hρT).le
    have hρpos : 0 < |ρ.1.im| := hTp.trans_le hTρ
    have hρlog : 0 < Real.log |ρ.1.im| := by
      have h := hlogT.trans (Real.log_le_log hTp hTρ)
      linarith
    have hcompare : a / Real.log H ≤ a / Real.log |ρ.1.im| :=
      div_le_div_of_nonneg_left ha.le hρlog (Real.log_le_log hρpos hρH)
    have hz := hzero ρ ((le_max_left _ _).trans hTρ)
    exact ⟨hcompare.trans_lt hz.1, by linarith [hz.2]⟩

/-- The actual proved `9/50` region supplies its common margin for the
entire bounded-height divisor at every sufficiently large height. -/
theorem exists_eventual_sharp_common_margin :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      0 < 9 / (50 * Real.log H) ∧ 9 / (50 * Real.log H) < 1 / 4 ∧
        ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≤ H →
          9 / (50 * Real.log H) < ρ.1.re ∧ ρ.1.re < 1 - 9 / (50 * Real.log H) := by
  have hregion : ∃ T : ℝ, 1 ≤ T ∧ ∀ ρ : NontrivialZetaZero, T ≤ |ρ.1.im| →
      (9 / 50 : ℝ) / Real.log |ρ.1.im| < ρ.1.re ∧
        ρ.1.re < 1 - (9 / 50 : ℝ) / Real.log |ρ.1.im| := by
    simpa only [div_div] using GaussianFermiSharpZeroFree.exists_eventual_strip
  simpa only [div_div] using exists_eventual_common_log_margin (by norm_num : (0 : ℝ) < 9 / 50) hregion

end
end RiemannGaussian
