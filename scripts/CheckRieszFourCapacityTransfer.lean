/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourAngularDomain
import RieszFourCapacityBin0.Assembly

/-!
# Optional whole-region certificate transfer to the literal prime sum

Run only after the separate four-prime cover has been generated and checked.
Put `.lake/riesz-four-capacity-cover` on LEAN_PATH in the pinned environment.
This imports its checked assembly; it is intentionally outside ordinary CI.
No JSON or numerical probe is trusted. The theorem combines the exact upper
certificate with the root-imported arithmetic/domain transfer.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget ZetaRieszFourAngularDomain

namespace RieszFourCapacityTransfer

/-- Every selected adverse four-prime label in the first cutoff bin has
an independent literal debit at most 133421/1000000 times the ORIGINAL
radial/phase factor. The complete remaining core stays signed. -/
theorem eventually_first_bin_core_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := clippedSupport S
      let Q := adversePopulation P L t h y (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin0.Assembly.high →
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        ((133421/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_core_capacity_floor hu hU hh hhu hδ hδu]
    with j hJ t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hf := hJ t y RieszFourCapacityBin0.Assembly.low htlo hthi
    (by norm_num [RieszFourCapacityBin0.Assembly.low]) hlo
  have hbox : outerBox RieszFourCapacityBin0.Assembly.low =
      RieszFourCapacityBin0.Assembly.part0000_box := by
    funext i
    fin_cases i <;> norm_num [outerBox,RieszFourCapacityBin0.Assembly.low,
      RieszFourCapacityBin0.Assembly.part0000_box]
  have hupp := RieszFourCapacityBin0.Assembly.whole_debit_upper ⟨hlo,hhi⟩
  rw [← hbox] at hupp
  have hcost : (1003/1000 : ℝ)*
      ((∫ x in ZetaRieszCapacityCover.region (outerBox RieszFourCapacityBin0.Assembly.low),
        ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000 ≤ 133421/1000000 := by
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hupp
    linarith
  have hE : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h := by
    have hn := Nat.cast_nonneg N (α := ℝ)
    have ht : 0 ≤ t := by linarith
    positivity
  have hprod := mul_le_mul_of_nonneg_right hcost hE
  linarith

#print axioms eventually_first_bin_core_floor
end RieszFourCapacityTransfer
