/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFiveAngularDomain
import RieszFiveCapacityBin0.Assembly

/-!
# Optional five-prime certificate transfer to the literal prime sum

Run only after the separate five-prime cover has been generated and checked.
Put `.lake/riesz-five-capacity-cover` on LEAN_PATH in the pinned environment.
This imports its checked assembly; it is intentionally outside ordinary CI.
The exact certificate supplies a numerical credit for the actual finite
prime sum, retaining its radial/phase factor and entire signed complement.
The final rational surplus compares constants only: common phase aggregation
and one disjoint spending ledger are still required for joint cancellation.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFiveAngularDomain

namespace RieszFiveCapacityTransfer

/-- Every outer certificate point satisfies the exact domain comparison premises. -/
theorem first_bin_geometry {x : Fin 2 → ℝ}
    (hx : x ∈ ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box) :
    x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ) := by
  have h0 := (hx 0 (Set.mem_univ _)).2
  have h1 := (hx 1 (Set.mem_univ _)).2
  norm_num [RieszFiveCapacityBin0.Assembly.part0000_box] at h0 h1
  constructor <;> linarith

/-- The checked first-bin supply gives an independent literal credit of
8529739/62500000 times the ORIGINAL radial/phase factor. All other core
labels remain signed; this is not the whole-carrier numerical floor. -/
theorem eventually_first_bin_core_floor {u h b : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin0.Assembly.low RieszFiveCapacityBin0.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFiveCapacityBin0.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFiveCapacityBin0.Assembly.high →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        ((8529739/62500000 : ℝ)*
          ((Real.exp (-(t+h)/2)*t^N/N.factorial)*
            max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_core_capacity_floor
    RieszFiveCapacityBin0.Assembly.part0000_box
    (lo := RieszFiveCapacityBin0.Assembly.low) (hi := RieszFiveCapacityBin0.Assembly.high)
    hu hU hh hhu hb hsmall hcover
    (by norm_num [RieszFiveCapacityBin0.Assembly.low]) (fun _ hx => first_bin_geometry hx)]
    with j hJ t y
  dsimp only
  intro htlo hthi hlo hhi
  have hf := hJ t y htlo hthi hlo hhi
  have hl := RieszFiveCapacityBin0.Assembly.whole_supply_lower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hl
  have hcredit : (8529739/62500000 : ℝ) ≤
      (996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region RieszFiveCapacityBin0.Assembly.part0000_box,
        ZetaRieszFiveCapacityCover.density RieszFiveCapacityBin0.Assembly.low
          RieszFiveCapacityBin0.Assembly.high (1/100) x)-1/50000 := by
    linarith
  have ht : 0 ≤ t := (show 0 ≤ (39/20 : ℝ)*
    ZetaRieszPrimeCountFrequency.dyadicMomentOrder j by positivity).trans htlo
  have hF : 0 ≤ (Real.exp (-(t+h)/2)*t^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)*
        max 0 (-Real.cos (y*t)-|y| * h)*h := by positivity
  have hprod := mul_le_mul_of_nonneg_right hcredit hF
  linarith only [hf,hprod]

/-- The literal first-bin constants retain more than two percent room;
the two distinct radial/phase factors still need common-period comparison. -/
theorem first_bin_credit_surplus :
    (8529739/62500000 : ℝ)-(102/100)*(133421/1000000) = 96601/250000000 ∧
      (0 : ℝ) < 96601/250000000 := by
  norm_num

#print axioms eventually_first_bin_core_floor
#print axioms first_bin_credit_surplus
end RieszFiveCapacityTransfer
