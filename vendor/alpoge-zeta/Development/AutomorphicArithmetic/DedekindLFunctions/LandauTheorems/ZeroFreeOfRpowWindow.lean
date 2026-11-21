import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypOfRpow

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)

end Deduction

end
