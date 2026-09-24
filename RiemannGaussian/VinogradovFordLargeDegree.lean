/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordAllOrders
import RiemannGaussian.VinogradovRosserLargeSupply

/-!
# Ford's actual complete moments at explicit large degree

The independently proved short-prime packets discharge the remaining
arithmetic premise in the complete Ford moment theorem when log(k)>=1700.
The order range, real endpoint, coefficient and defect are unchanged.
The smaller degrees and incomplete-system estimates remain separate targets.
-/

namespace RiemannGaussian.VinogradovFordLargeDegree
noncomputable section
open VinogradovMeanValue VinogradovFordScales VinogradovFordOrderBudget

/-- The actual complete Ford moment bound, with no prime-supply premise,
for every original allowed order and every real endpoint at explicit large degree. -/
theorem moment_bound_real {k s : ℕ} (hk : (1700 : ℝ) ≤ Real.log k)
    (hlower : 2*k^2 ≤ s)
    (hupper : (s : ℝ) ≤ ((k : ℝ)^2/2)*(1/2+Real.log (3*(k : ℝ)/8)))
    {P : ℝ} (hP : 1 ≤ P) :
    meanValue s k ⌊P⌋₊ ≤ coefficient k (s : ℝ)*
      P ^ sourceExponent k s (defect k (s : ℝ)) := by
  exact VinogradovFordAllOrders.published_moment_bound_real
    (by have := VinogradovRosserLargeSupply.degree_ge_of_log_ge hk; omega)
    hlower hupper (VinogradovRosserLargeSupply.fixedWidth_shortPrimeSupply hk) hP

end
end RiemannGaussian.VinogradovFordLargeDegree
