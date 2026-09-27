/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RieszFourCapacityBin0.Assembly
import RieszFiveCapacityBin0.Assembly

/-!
# Optional checked first-bin angular surplus

Both separately generated covers must be checked before running this file,
with their directories on LEAN_PATH. This check is outside ordinary CI.
The theorem certifies a continuum angular surplus and room for the stated
boundary allowances. The whole five-prime arithmetic transfer is still open.
-/

open MeasureTheory RiemannGaussian
namespace RieszCapacitySurplus

/-- The two complete first-bin covers leave two percent angular surplus
even after one ordering budget and ONE aggregate approximation budget.
This is not a signed arithmetic floor. -/
theorem first_bin_angular_surplus {lam : ℝ}
    (hlam : (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ lam ∧
      lam ≤ RieszFourCapacityBin0.Assembly.high) :
    (102/100 : ℝ)*
      ((∫ x in ZetaRieszCapacityCover.region RieszFourCapacityBin0.Assembly.part0000_box,
        ZetaRieszFourCapacityCover.density lam x)+1/1250+1/2000) ≤
      ∫ x in ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
        ZetaRieszFiveCapacityCover.density RieszFiveCapacityBin0.Assembly.low
          RieszFiveCapacityBin0.Assembly.high (1/100) x := by
  have hu := RieszFourCapacityBin0.Assembly.whole_debit_upper hlam
  have hl := RieszFiveCapacityBin0.Assembly.whole_supply_lower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hu hl
  linarith

#print axioms RieszFiveCapacityBin0.Assembly.whole_supply_lower
#print axioms first_bin_angular_surplus
end RieszCapacitySurplus
