/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.External.Zeta23SevenWindowTarget
import RiemannGaussian.MontgomeryTaylorIntegerCover
import RiemannGaussian.CertificateData.MontgomeryTaylorIntegerRanges
import RiemannGaussian.CertificateData.MontgomeryTaylorIntegerAnchors
import RiemannGaussian.CertificateData.MontgomeryTaylorCover

/-!
# Literal zero-count endpoint of the integer cover check

The general integer-cover implication is specialized to the complete proved
cover. Its continuous compact floor feeds the unrestricted seven-point
inequality and the literal zeta counting functions. Both dyadic and cumulative
counts are included, with the exact coefficient and an eventual rational
6731/10000 bound. The height threshold is not numerically evaluated.
-/

namespace RiemannGaussian.Zeta23InverseSampling
open MontgomeryTaylorIntegerBoxCertificate

/-- The actual proved tables reduce the proposed numerical improvement to
one complete, kernel-accepted integer cover of the compact gap domain. -/
theorem simpleCritical_6731_of_integer_cover (tree : Tree)
    (hc : check CertificateData.table 9960000 568320000 CertificateData.lookup tree rootBox = true) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) :=
  simpleCritical_6731_of_compact_model_floor
    (compact_floor_of_check CertificateData.table_valid CertificateData.lookup
      CertificateData.lookup_valid tree hc)

/-- The complete accepted cover proves the fixed continuous model floor
on every real point of the compact six-gap domain. -/
theorem sevenWindow_compact_floor :
    ∀ g : Fin 6 → ℝ, (∀ j, g j ∈ Set.Icc (1 / 3) 20) →
      MontgomeryTaylorSevenWindowParameters.modelFloor ≤
        MontgomeryTaylorSevenWindowModel.finiteModel g :=
  compact_floor_of_check CertificateData.table_valid CertificateData.lookup
    CertificateData.lookup_valid CertificateData.Cover.tree CertificateData.Cover.checked

/-- The certified compact floor and the proved small- and large-gap reductions
give the exact target floor for every ordered seven-point configuration. -/
theorem sevenWindow_floor :
    ∀ x : ℕ → ℝ, Monotone x → MontgomeryTaylorSevenWindowParameters.targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy
        (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2)
        MontgomeryTaylorSevenWindowParameters.pairWeight x 6 0 +
      MontgomeryTaylorWindowEnergy.windowPressure
        MontgomeryTaylorSevenWindowParameters.pressureWeight x 6 0 :=
  MontgomeryTaylorSevenWindowModel.window_floor_of_compact_model_floor sevenWindow_compact_floor

/-- The exact seven-window coefficient for literal simple critical-line zeros
in (T, 2T]. All numerical and analytic premises are discharged. -/
theorem simpleCritical_sevenWindow :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sevenWindowTargetCoefficient - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) :=
  simpleCritical_of_sevenWindowFloor sevenWindow_floor

/-- The exact seven-window coefficient for cumulative literal counts in (0, T]. -/
theorem simpleCritical_sevenWindow_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sevenWindowTargetCoefficient - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam) simpleCritical_sevenWindow

/-- The exact rational 6731/10000 certificate for literal dyadic zero counts. -/
theorem simpleCritical_6731 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) :=
  simpleCritical_6731_of_integer_cover CertificateData.Cover.tree CertificateData.Cover.checked

/-- The exact rational 6731/10000 certificate for cumulative literal counts. -/
theorem simpleCritical_6731_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam) simpleCritical_6731

/-- The strict coefficient margin pays the asymptotic error completely:
at sufficiently large heights the dyadic proportion is at least 6731/10000. -/
theorem simpleCritical_6731_eventually :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  obtain ⟨T₀, hT₀⟩ := simpleCritical_sevenWindow
    (sevenWindowTargetCoefficient - 6731 / 10000)
    (sub_pos.mpr sevenWindowTargetCoefficient_gt_6731)
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [sub_sub_cancel] using hT₀ T hT

/-- Every sufficiently large cumulative window has at least a 6731/10000
proportion of simple critical-line zeros. The height threshold is unevaluated. -/
theorem simpleCritical_6731_cumulative_eventually :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T := by
  obtain ⟨T₀, hT₀⟩ := simpleCritical_sevenWindow_cumulative
    (sevenWindowTargetCoefficient - 6731 / 10000)
    (sub_pos.mpr sevenWindowTargetCoefficient_gt_6731)
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [sub_sub_cancel] using hT₀ T hT

end RiemannGaussian.Zeta23InverseSampling
