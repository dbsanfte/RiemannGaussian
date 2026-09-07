import RiemannGaussian.EtaRationalTranslateGram
import RiemannGaussian.EtaCurrentTranslatedProjectionPower
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Four explicit eta translates with a full residual budget below one fifth

The coefficient search suggests the rational physical scales
`1/4, 1/2, 3/4, 1` with coefficients `-1/2, -1/2, 1/2, 1`.
The finite interval Gram and full tail at the original cutoff `N=64`
are checked by rational kernel reduction. The target pairing retains its
exact logarithms. The resulting bound concerns the complete continuous
residual and is available for both branches of the original current.
-/

open Complex Set

namespace RiemannGaussian

/-- Four rational physical scales, including two internal and two endpoint translates. -/
def pairedEtaFourProjectionScale : Fin 4 → ℚ := ![1 / 4, 1 / 2, 3 / 4, 1]

/-- The explicit signed rational coefficients found by the finite full-budget search. -/
def pairedEtaFourProjectionCoefficient : Fin 4 → ℚ := ![-(1 / 2), -(1 / 2), 1 / 2, 1]

/-- Every selected physical scale belongs to the original allowed interval. -/
theorem pairedEtaFourProjectionScale_bounds (j : Fin 4) :
    0 < pairedEtaFourProjectionScale j ∧ pairedEtaFourProjectionScale j ≤ 1 := by
  fin_cases j <;> norm_num [pairedEtaFourProjectionScale]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The entire rational quadratic Gram and coefficient tail have a strict rational upper bound, checked by Lean's kernel. -/
theorem pairedEtaFourProjection_rationalQuadraticBudget_lt :
    pairedEtaRationalQuadraticBudget 64 pairedEtaFourProjectionScale pairedEtaFourProjectionCoefficient < 99 / 100 := by
  decide +kernel

end RiemannGaussian
