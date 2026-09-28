/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBroadTripleBudget
import RiemannGaussian.ZetaRieszOppositePhase
import RiemannGaussian.ZetaRieszCapacityPhaseBudget
import RiemannGaussian.ZetaRieszCentralReserve
import RiemannGaussian.ZetaRieszCentralSharpBudget
import RiemannGaussian.ZetaRieszJointFullFiveBounds
import RiemannGaussian.ZetaRieszPositiveFiveBoundary
import RiemannGaussian.ZetaRieszSaddleCredit
import RiemannGaussian.ZetaRieszJointPositiveFiveBounds
import RiemannGaussian.ZetaRieszJointOwnerPayment
import RiemannGaussian.ZetaRieszFiveOwnerBoxes
import RieszFourCapacityBin2.Assembly
import RieszFiveCapacityBin2.Assembly
import Mathlib.Tactic.Linter

/-!
# Optional joint three/four/five-prime bounds in the central saddle bin

This application requires both separately kernel-checked bin-two assemblies.
It is outside ordinary builds and retains the complete signed complement.
Importing cached assemblies never reruns their exhaustive covers.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

namespace RieszCentralCapacityTransfer

/-- The complete checked central cover enters the original ordered
five-prime integral uniformly throughout its exact padded cutoff bin. -/
theorem central_ordered_integral_lower {lam : ℝ}
    (hlo : (RieszFiveCapacityBin2.Assembly.low : ℝ) ≤ lam)
    (hhi : lam ≤ RieszFiveCapacityBin2.Assembly.high) :
    (13021/100000 : ℝ) ≤ ∫ x in ZetaRieszFiveAngularBoundary.orderedRegion
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high,
      ZetaRieszFiveInteriorBudget.density lam x := by
  have hgeom : ∀ x ∈ ZetaRieszCapacityCover.region RieszFiveCapacityBin2.Assembly.part0000_box,
      x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ) := by
    intro x hx
    have h0 := (hx 0 (Set.mem_univ _)).2
    have h1 := (hx 1 (Set.mem_univ _)).2
    norm_num [RieszFiveCapacityBin2.Assembly.part0000_box] at h0 h1
    constructor <;> linarith
  have hL : (17/25 : ℝ) ≤ lam :=
    (by norm_num [RieszFiveCapacityBin2.Assembly.low] :
      (17/25 : ℝ) ≤ RieszFiveCapacityBin2.Assembly.low).trans hlo
  have he := ZetaRieszFiveAngularDomain.supply_integral_le_ordered
    RieszFiveCapacityBin2.Assembly.part0000_box hL hlo hhi hgeom
  have hs := RieszFiveCapacityBin2.Assembly.whole_supply_lower
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hs
  exact hs.trans he

/-- The owner-enhanced, separately checked five-prime credit is at least
1309/10000 in the central bin, in the actual original-height prime sum. -/
theorem eventually_central_bin_five_floor {u h b : ℝ} {M : ℕ}
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
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFiveCapacityBin2.Assembly.low : ℝ) ≤ L/t → L/t ≤ RieszFiveCapacityBin2.Assembly.high →
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        ((1309/10000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (-Real.cos (y*t)-|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszFiveOwnerBoxes.eventually_owner_core_floor
    (lo := RieszFiveCapacityBin2.Assembly.low) (hi := RieszFiveCapacityBin2.Assembly.high)
    hu hU hh hhu hb hsmall hcover
    (by norm_num [RieszFiveCapacityBin2.Assembly.low])
    (by norm_num [RieszFiveCapacityBin2.Assembly.high])] with j hJ t y
  dsimp only
  intro htlo hthi hlo hhi
  have hf := hJ t y htlo hthi hlo hhi
  have hc := central_ordered_integral_lower hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  have ht : 0 ≤ t := (show 0 ≤ (39/20 : ℝ)*N by positivity).trans htlo
  have hcredit : (1309/10000 : ℝ) ≤ (996/1000 : ℝ)*
      (∫ x in ZetaRieszFiveAngularBoundary.orderedRegion
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high,
        ZetaRieszFiveInteriorBudget.density (SquarefreeVaughanLogSource.length u N/t) x)-1/50000+1/800 := by
    linarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hcredit
    (show 0 ≤ (Real.exp (-(t+h)/2)*t^N/N.factorial)*
      max 0 (-Real.cos (y*t)-|y| * h)*h by positivity)
  linarith only [hf,hp]

/-- Calibration costs are included in the same central credit 1309/10000;
the original-height negative five-prime contribution yields a ceiling. -/
theorem eventually_central_bin_five_ceiling {u h b : ℝ} {M : ℕ}
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
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFiveCapacityBin2.Assembly.low : ℝ) ≤ L/t → L/t ≤ RieszFiveCapacityBin2.Assembly.high →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\D, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        ((1309/10000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          (Real.cos (y*t)-|y| * h)*h)) := by
  filter_upwards [ZetaRieszFiveOwnerBoxes.eventually_owner_core_ceiling
    (lo := RieszFiveCapacityBin2.Assembly.low) (hi := RieszFiveCapacityBin2.Assembly.high)
    hu hU hh hhu hb hsmall hcover
    (by norm_num [RieszFiveCapacityBin2.Assembly.low])
    (by norm_num [RieszFiveCapacityBin2.Assembly.high]),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let C := (996/1000 : ℝ)*(∫ x in ZetaRieszFiveAngularBoundary.orderedRegion
    RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high,
    ZetaRieszFiveInteriorBudget.density (L/t) x)-1/50000+1/800
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc := central_ordered_integral_lower hlo hhi
  have hbase : (13091916/100000000 : ℝ) ≤ C := by dsimp only [C,L,N]; linarith only [hc]
  have hcal := ZetaRieszOppositePhase.calibration_phase ht hh.le hhu
  have hpos : 0 ≤ 1-|Real.pi/t| * h := by linarith only [hcal.2]
  have hmul := mul_le_mul_of_nonneg_right hbase hpos
  have hcredit : (1309/10000 : ℝ) ≤ C*(1-|Real.pi/t| * h) := by nlinarith only [hmul,hcal.2]
  have hV : 0 ≤ (Real.exp (-(t+h)/2)*t^N/N.factorial)*(Real.cos (y*t)-|y| * h)*h :=
    mul_nonneg (mul_nonneg (by positivity) hphase) hh.le
  have hp := mul_le_mul_of_nonneg_right hcredit hV
  have hf := hJ t y htlo hthi hlo hhi hphase
  dsimp only [C,L,N] at hp
  nlinarith only [hp,hf]

/-- The checked debit also controls the entire positive-coefficient
four-prime population from above at the original height. Calibration and
its relative error are discharged; the complement is kept signed. -/
theorem eventually_central_bin_four_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (121003/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (Real.cos (y*t))+|y| * h)*h) := by
  filter_upwards [ZetaRieszOppositePhase.eventually_four_core_ceiling hu hU hh hhu hδ hδu,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlo hhi
  have hf := hJ t y RieszFourCapacityBin2.Assembly.low htlo hthi
    (by norm_num [RieszFourCapacityBin2.Assembly.low]) hlo
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let D := (1003/1000 : ℝ)*
    ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox
        RieszFourCapacityBin2.Assembly.low),
      ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000
  have hbox : ZetaRieszFourAngularDomain.outerBox RieszFourCapacityBin2.Assembly.low =
      RieszFourCapacityBin2.Assembly.part0000_box := by
    funext i
    fin_cases i <;> norm_num [ZetaRieszFourAngularDomain.outerBox,
      RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.part0000_box]
  have hupp := RieszFourCapacityBin2.Assembly.whole_debit_upper ⟨hlo,hhi⟩
  rw [← hbox] at hupp
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hupp
  have hD : D ≤ 120882/1000000 := by dsimp only [D,L,N]; linarith only [hupp]
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hcal := ZetaRieszOppositePhase.calibration_cost_le ht hh.le hhu
  have hc0 : 0 ≤ (10000/9999 : ℝ)*(1+|Real.pi/t| * h) := by positivity
  have hpaid : (10000/9999 : ℝ)*(1+|Real.pi/t| * h)*D ≤ 121003/1000000 := by
    have h₁ := mul_le_mul_of_nonneg_left hD hc0
    have h₂ := mul_le_mul_of_nonneg_right hcal (by norm_num : (0 : ℝ) ≤ 120882/1000000)
    linarith only [h₁,h₂]
  have hV : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (Real.cos (y*t))+|y| * h)*h := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpaid hV
  dsimp only [D,L,N] at hscaled
  linarith only [hf,hscaled]

/-- The moving cutoff premises are discharged on an actual band
containing the factorial saddle T=2N. The entire original-height
positive-coefficient four-prime population retains its explicit ceiling. -/
theorem eventually_central_window_four_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (1999/1000 : ℝ)*N ≤ t → t+h ≤ (2001/1000 : ℝ)*N →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (121003/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (Real.cos (y*t))+|y| * h)*h) := by
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_central_bin_ratio hu.le hU)
  filter_upwards [eventually_central_bin_four_ceiling hu hU hh hhu hδ hδu,hgeom]
    with j hJ hbin t y
  dsimp only
  intro htlo hthi
  have hb := hbin t htlo (by linarith only [hthi,hh])
  have hn : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ t := by
    linarith only [htlo,hn]
  have hhi : t+h ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
    linarith only [hthi,hn]
  apply hJ t y hlo hhi
  · simpa only [RieszFourCapacityBin2.Assembly.low,Rat.cast_div,Rat.cast_ofNat] using hb.1
  · simpa only [RieszFourCapacityBin2.Assembly.high,Rat.cast_div,Rat.cast_ofNat] using hb.2

/-- The checked central-bin debit also supplies the original-height lower inequality. -/
theorem eventually_central_bin_four_floor {u h δ : ℝ}
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
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (∑ n ∈ S\Q, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        ((120882/1000000 : ℝ)*
          ((Real.exp (-t/2)*(t+h)^N/N.factorial)*
            (max 0 (-Real.cos (y*t))+|y| * h)*h)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [ZetaRieszFourAngularDomain.eventually_core_capacity_floor hu hU hh hhu hδ hδu]
    with j hJ t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  have hf := hJ t y RieszFourCapacityBin2.Assembly.low htlo hthi
    (by norm_num [RieszFourCapacityBin2.Assembly.low]) hlo
  have hbox : ZetaRieszFourAngularDomain.outerBox RieszFourCapacityBin2.Assembly.low =
      RieszFourCapacityBin2.Assembly.part0000_box := by
    funext i
    fin_cases i <;> norm_num [ZetaRieszFourAngularDomain.outerBox,RieszFourCapacityBin2.Assembly.low,
      RieszFourCapacityBin2.Assembly.part0000_box]
  have hupp := RieszFourCapacityBin2.Assembly.whole_debit_upper ⟨hlo,hhi⟩
  rw [← hbox] at hupp
  have hcost : (1003/1000 : ℝ)*
      ((∫ x in ZetaRieszCapacityCover.region (ZetaRieszFourAngularDomain.outerBox RieszFourCapacityBin2.Assembly.low),
        ZetaRieszFourCapacityCover.density (L/t) x)+1/1000000000+1/78000000)+1/100000 ≤ 120882/1000000 := by
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hupp
    linarith
  have hE : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h := by
    have hn := Nat.cast_nonneg N (α := ℝ)
    have ht : 0 ≤ t := by linarith
    positivity
  have hprod := mul_le_mul_of_nonneg_right hcost hE
  linarith


/-- A single literal ledger bounds the broad triple band AND the complete selected
four-prime population. Every unselected original term remains signed. -/
theorem eventually_central_bin_three_four_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (∑ n ∈ S\(B ∪ Q), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (125882/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have htriple := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszBroadTripleBudget.eventually_signed_bounds hh hhu)
  filter_upwards [eventually_central_bin_four_floor hu hU hh hhu hδ hδu,
    htriple,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ htri hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBroadTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hNt : (N : ℝ) ≤ t := by linarith only [htlo,hn]
  have hLlo := (le_div_iff₀ ht0).mp hlo
  norm_num only [RieszFourCapacityBin2.Assembly.low,Rat.cast_div,Rat.cast_ofNat] at hLlo
  have hmid : t+h ≤ 2*L := by dsimp only [L,N]; linarith only [hLlo,ht,hhu]
  have hT := htri S A t L y hNt (SquarefreeVaughanLogSource.length_pos u N) hmid
  have hfour := hJ t y htlo hthi hlo hhi
  have hdis : Disjoint B Q := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hthree := (Finset.mem_filter.mp hn).2.2.1
    have hfour := (Finset.mem_filter.mp hn').2.2.1
    omega
  have hsub : B ⊆ S\Q := Finset.subset_sdiff.mpr ⟨Finset.filter_subset _ _,hdis⟩
  have hsplit := congrArg Complex.re (Finset.sum_sdiff (f := f) hsub)
  have hid : (S\Q)\B = S\(B ∪ Q) := by ext n; simp; tauto
  rw [hid] at hsplit
  simp only [Complex.add_re] at hsplit
  unfold ZetaRieszParityPacket.coreResponse at hfour ⊢
  dsimp only [N,K,L,A,S,B,Q,f,ZetaRieszBroadTripleBudget.population] at hsplit hT ⊢
  nlinarith only [hsplit,hfour,hT.1]


/-- A single literal ledger bounds the broad triple band AND the complete selected
four-prime population. Every unselected original term remains signed. -/
theorem eventually_central_window_three_four_floor {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      (1999/1000 : ℝ)*N ≤ t → t+h ≤ (2001/1000 : ℝ)*N →
      (∑ n ∈ S\(B ∪ Q), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (125882/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_central_bin_ratio hu.le hU)
  filter_upwards [eventually_central_bin_three_four_floor hu hU hh hhu hδ hδu,hgeom]
    with j hJ hbin t y
  dsimp only
  intro htlo hthi
  have hb := hbin t htlo (by linarith only [hthi,hh])
  have hn : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ t := by
    linarith only [htlo,hn]
  have hhi : t+h ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
    linarith only [hthi,hn]
  apply hJ t y hlo hhi
  · simpa only [RieszFourCapacityBin2.Assembly.low,Rat.cast_div,Rat.cast_ofNat] using hb.1
  · simpa only [RieszFourCapacityBin2.Assembly.high,Rat.cast_div,Rat.cast_ofNat] using hb.2


/-- A single literal ledger bounds the broad triple band AND the complete selected
four-prime population. Every unselected original term remains signed. -/
theorem eventually_central_bin_three_four_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t →
      L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ Q), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (126003/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h) := by
  have htriple := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszBroadTripleBudget.eventually_signed_bounds hh hhu)
  filter_upwards [eventually_central_bin_four_ceiling hu hU hh hhu hδ hδu,
    htriple,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ htri hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBroadTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ t := by linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hNt : (N : ℝ) ≤ t := by linarith only [htlo,hn]
  have hLlo := (le_div_iff₀ ht0).mp hlo
  norm_num only [RieszFourCapacityBin2.Assembly.low,Rat.cast_div,Rat.cast_ofNat] at hLlo
  have hmid : t+h ≤ 2*L := by dsimp only [L,N]; linarith only [hLlo,ht,hhu]
  have hT := htri S A t L y hNt (SquarefreeVaughanLogSource.length_pos u N) hmid
  have hfour := hJ t y htlo hthi hlo hhi
  have hdis : Disjoint B Q := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hthree := (Finset.mem_filter.mp hn).2.2.1
    have hfour := (Finset.mem_filter.mp hn').2.2.1
    omega
  have hsub : B ⊆ S\Q := Finset.subset_sdiff.mpr ⟨Finset.filter_subset _ _,hdis⟩
  have hsplit := congrArg Complex.re (Finset.sum_sdiff (f := f) hsub)
  have hid : (S\Q)\B = S\(B ∪ Q) := by ext n; simp; tauto
  rw [hid] at hsplit
  simp only [Complex.add_re] at hsplit
  unfold ZetaRieszParityPacket.coreResponse at hfour ⊢
  dsimp only [N,K,L,A,S,B,Q,f,ZetaRieszBroadTripleBudget.population] at hsplit hT ⊢
  nlinarith only [hsplit,hfour,hT.2]


/-- A single literal ledger bounds the broad triple band AND the complete selected
four-prime population. Every unselected original term remains signed. -/
theorem eventually_central_window_three_four_ceiling {u h δ : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      (1999/1000 : ℝ)*N ≤ t → t+h ≤ (2001/1000 : ℝ)*N →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ Q), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (126003/1000000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h) := by
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_central_bin_ratio hu.le hU)
  filter_upwards [eventually_central_bin_three_four_ceiling hu hU hh hhu hδ hδu,hgeom]
    with j hJ hbin t y
  dsimp only
  intro htlo hthi
  have hb := hbin t htlo (by linarith only [hthi,hh])
  have hn : (0 : ℝ) ≤ ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by positivity
  have hlo : (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ t := by
    linarith only [htlo,hn]
  have hhi : t+h ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j := by
    linarith only [hthi,hn]
  apply hJ t y hlo hhi
  · simpa only [RieszFourCapacityBin2.Assembly.low,Rat.cast_div,Rat.cast_ofNat] using hb.1
  · simpa only [RieszFourCapacityBin2.Assembly.high,Rat.cast_div,Rat.cast_ofNat] using hb.2


/-- The broad triple band and complete selected four-prime debit are paid
by one owner-enhanced five-prime population, keeping the full signed rest. -/
theorem eventually_central_bin_three_four_five_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t → L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (1309/10000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (-Real.cos (y*t)-|y| * h)*h)-
        (1261/10000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (-Real.cos (y*t))+|y| * h)*h) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_central_bin_three_four_floor hu hU hh hhu hδ hδu,
    eventually_central_bin_five_floor hu hU hh hhu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hfour hfive hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBroadTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h y (δ*N)
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h y
    (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have ht : 0 < t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have hsub : B ∪ Q ⊆ S := Finset.union_subset (Finset.filter_subset _ _)
    (by intro n hn; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
  have hdis : Disjoint (B ∪ Q) D := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hn'
    have hc5 := ZetaRieszJointCapacityFloor.interior_supply_count ht hv hnv
    rcases Finset.mem_union.mp hn with hn | hn
    · have hc3 := (Finset.mem_filter.mp hn).2.2.1
      omega
    · have hc4 := (Finset.mem_filter.mp hn).2.2.1
      omega
  have h34 := hfour t y htlo hthi hlo hhi
  have h5 := hfive t y htlo hthi hlo hhi
  have hj := ZetaRieszJointCapacityFloor.joint_floor_of_disjoint f hsub hdis h34 h5
  rw [Finset.union_assoc] at hj
  have hV : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (-Real.cos (y*t))+|y| * h)*h := by positivity
  change _ ≤ (∑ n ∈ S, f n).re
  nlinarith only [hj,hV]

/-- All phases are covered in the central upper ledger. Five-prime
credit is spent only at positive phase; the other labels stay signed. -/
theorem eventually_central_bin_three_four_five_all_phase_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let B := ZetaRieszBroadTripleBudget.population S t h
      let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
      let D := if 0 ≤ Real.cos (y*t)-|y| * h then
        I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
          (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) else ∅
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/t → L/t ≤ RieszFourCapacityBin2.Assembly.high →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\(B ∪ (Q ∪ D)), ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (1261/10000 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (Real.cos (y*t))+|y| * h)*h)-
        (1309/10000 : ℝ)*((Real.exp (-(t+h)/2)*t^N/N.factorial)*
          max 0 (Real.cos (y*t)-|y| * h)*h) := by
  filter_upwards [eventually_central_bin_three_four_ceiling hu hU hh hhu hδ hδu,
    eventually_central_bin_five_ceiling hu hU hh hhu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hfour hfive hN t y
  dsimp only
  intro htlo hthi hlo hhi
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := ZetaRieszBroadTripleBudget.population S t h
  let Q := adversePopulation (clippedSupport S) L t h (Real.pi/t) (δ*N)
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
    (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have ht : 0 < t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have h34 := hfour t y htlo hthi hlo hhi
  have hV : 0 ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*
      (max 0 (Real.cos (y*t))+|y| * h)*h := by positivity
  by_cases hphase : 0 ≤ Real.cos (y*t)-|y| * h
  · have hsub : B ∪ Q ⊆ S := Finset.union_subset (Finset.filter_subset _ _)
      (by intro n hn; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1)
    have hdis : Disjoint (B ∪ Q) D := by
      apply Finset.disjoint_left.mpr
      intro n hn hn'
      obtain ⟨v,hv,hnv⟩ := Finset.mem_biUnion.mp hn'
      have hc5 := ZetaRieszJointCapacityFloor.interior_supply_count ht hv hnv
      rcases Finset.mem_union.mp hn with hn | hn
      · have hc3 := (Finset.mem_filter.mp hn).2.2.1
        omega
      · have hc4 := (Finset.mem_filter.mp hn).2.2.1
        omega
    have h5 := hfive t y htlo hthi hlo hhi hphase
    have hj := ZetaRieszJointCapacityCeiling.joint_ceiling_of_disjoint f hsub hdis h34 h5
    rw [Finset.union_assoc] at hj
    simp only [if_pos hphase,max_eq_right hphase]
    change (∑ n ∈ S, f n).re ≤ _
    nlinarith only [hj,hV]
  · simp only [if_neg hphase,Finset.union_empty,max_eq_left (le_of_not_ge hphase),
      mul_zero,zero_mul,sub_zero]
    change (∑ n ∈ S, f n).re ≤ _
    change (∑ n ∈ S, f n).re ≤ _ at h34
    nlinarith only [h34,hV]

/-- All three selected prime-count classes are spent jointly over disjoint log windows. -/
theorem eventually_central_bin_three_four_five_family_floor {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b))))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (1309/10000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (-Real.cos (y*T i)-|y| * h)*h)-
          (1261/10000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (-Real.cos (y*T i))+|y| * h)*h))) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_central_bin_three_four_five_floor hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityFloor.family_floor_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · simpa only [if_true] using
      ZetaRieszBroadTripleBudget.joint_populations_disjoint I _ T (fun _ => y)
        (fun _ => True) hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- All-phase three/four/five upper payments have one disjoint signed complement. -/
theorem eventually_central_bin_three_four_five_family_ceiling {u h b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ℕ) (T : ℕ → ℝ) (y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun v => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b v k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      (∀ i ∈ I, (39/20 : ℝ)*N ≤ T i ∧ T i+h ≤ (203/100 : ℝ)*N ∧
        (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
          L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      (∀ i ∈ I, ∀ k ∈ I, i < k → T i+h ≤ T k) →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\I.biUnion P, ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ I, (
          (1261/10000 : ℝ)*
            ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
              (max 0 (Real.cos (y*T i))+|y| * h)*h)-
          (1309/10000 : ℝ)*
            ((Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
              max 0 (Real.cos (y*T i)-|y| * h)*h))) := by
  filter_upwards [eventually_central_bin_three_four_five_all_phase_ceiling hu hU hh hhu hδ hδu hb hsmall hcover]
    with j hJ I T y
  dsimp only
  intro hgeom hsep
  unfold ZetaRieszParityPacket.coreResponse
  refine ZetaRieszJointCapacityCeiling.family_ceiling_of_pairwise_disjoint I _ _ _ _ ?_ ?_
  · exact ZetaRieszBroadTripleBudget.joint_populations_disjoint I _ T
      (fun i => Real.pi/T i) (fun i => 0 ≤ Real.cos (y*T i)-|y| * h) hsep
  · intro i hi
    obtain ⟨htlo,hthi,hlt,htl⟩ := hgeom i hi
    simpa only [ZetaRieszParityPacket.coreResponse,add_sub_assoc] using
      hJ (T i) y htlo hthi hlt htl

/-- A complete original phase period pays the broader triple band and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_central_bin_three_four_five_period_payment_with_radial {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (m : ℝ)/500*V₀*h ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_central_bin_three_four_five_family_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_central_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- The original signed payment follows with the complete complement;
the stronger statement also records the scale of its radial witness. -/
theorem eventually_central_bin_three_four_five_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (m : ℝ)/500*V₀*h ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  filter_upwards [eventually_central_bin_three_four_five_period_payment_with_radial
    hu hU hy hm hhu hε hδ hδu hb hsmall hcover] with j hJ v
  dsimp only
  intro hpeak hlo hhi hbin
  obtain ⟨V₀,hV₀,_,hpay⟩ := hJ v hpeak hlo hhi hbin
  exact ⟨V₀,hV₀,hpay⟩

/-- A complete original phase period pays the broader triple band and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_central_bin_three_four_five_upper_period_payment_with_radial {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
          (m : ℝ)/500*V₀*h := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_central_bin_three_four_five_family_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszCapacityPhaseBudget.original_central_upper_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

/-- The original signed payment follows with the complete complement;
the stronger statement also records the scale of its radial witness. -/
theorem eventually_central_bin_three_four_five_upper_period_payment {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
          (m : ℝ)/500*V₀*h := by
  filter_upwards [eventually_central_bin_three_four_five_upper_period_payment_with_radial
    hu hU hy hm hhu hε hδ hδu hb hsmall hcover] with j hJ v
  dsimp only
  intro hpeak hlo hhi hbin
  obtain ⟨V₀,hV₀,_,hpay⟩ := hJ v hpeak hlo hhi hbin
  exact ⟨V₀,hV₀,hpay⟩

/-- A complete original phase period pays the broader triple band and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_exists_central_bin_three_four_five_period {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re <
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period hu.le hU)
  filter_upwards [eventually_central_bin_three_four_five_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hfloor⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/500*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hfloor,hp]⟩

/-- A complete original phase period pays the broader triple band and four-prime debit
from the same five-prime population; the full signed complement remains. -/
theorem eventually_exists_central_bin_three_four_five_upper_period {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      (ZetaRieszParityPacket.coreResponse u y N K).re <
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period hu.le hU)
  filter_upwards [eventually_central_bin_three_four_five_upper_period_payment hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom] with j hpay hJ
  obtain ⟨v,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hceiling⟩ := hpay v hpeak hlo hhi hbins
  have hp : 0 < (m : ℝ)/500*V₀*(Real.pi/(4*m*|y|)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  exact ⟨v,hpeak,hlo,hhi,by linarith only [hceiling,hp]⟩


/-- The actual central signed comparison retains its explicit source-scaled
credit, which grows geometrically for every radius strictly above one half.
The complete signed complement is retained, and no zero hypothesis is used. -/
theorem eventually_exists_central_bin_lower_source_credit {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*(∑ n ∈ S\(Finset.range (8*m)).biUnion P,
        ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
            ZetaRieszCentralReserve.sourceCredit u y N ≤
        u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  filter_upwards [eventually_central_bin_three_four_five_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom, ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hVr,hbound⟩ := hpay v hpeak hlo hhi hbins
  have hu0 : 0 ≤ u := by linarith
  have hyne : y ≠ 0 := abs_pos.mp hy0
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 hyne hN hm hv
    (by linarith only [hvu])
  have hhalf : (Real.exp (-v/2)*v^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)/1000 ≤ V₀/500 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr
    (pow_nonneg hu0 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1))
  have hbnd := mul_le_mul_of_nonneg_left hbound
    (pow_nonneg hu0 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1))
  exact ⟨v,hpeak,hlo,hhi,by nlinarith only [hc,hrs,hbnd]⟩

/-- The actual central signed comparison retains its explicit source-scaled
credit, which grows geometrically for every radius strictly above one half.
The complete signed complement is retained, and no zero hypothesis is used. -/
theorem eventually_exists_central_bin_upper_source_credit {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤
        u^(N+1)*(∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
              ZetaRieszCentralReserve.sourceCredit u y N := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  refine ⟨m,hm,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  filter_upwards [eventually_central_bin_three_four_five_upper_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom, ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  have hy0 : 0 < |y| := by linarith
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
        (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) ≤
          RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y| ≤ v+Real.pi/|y| := by
      linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  obtain ⟨V₀,hV₀,hVr,hbound⟩ := hpay v hpeak hlo hhi hbins
  have hu0 : 0 ≤ u := by linarith
  have hyne : y ≠ 0 := abs_pos.mp hy0
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 hyne hN hm hv
    (by linarith only [hvu])
  have hhalf : (Real.exp (-v/2)*v^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j).factorial)/1000 ≤ V₀/500 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr
    (pow_nonneg hu0 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1))
  have hbnd := mul_le_mul_of_nonneg_left hbound
    (pow_nonneg hu0 (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1))
  exact ⟨v,hpeak,hlo,hhi,by nlinarith only [hc,hrs,hbnd]⟩

/-- The whole joint SUM now pays a fixed positive-five sector in every
phase cell, retaining half the previous central reserve and the exact
signed rest. Cached covers discharge every population premise. -/
theorem eventually_joint_positive_five_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+max (∑ n ∈ B, f n).re 0)+
        ZetaRieszCentralReserve.sourceCredit u y N/2-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  filter_upwards [eventually_central_bin_three_four_five_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwhole := ZetaRieszJointPositiveFiveBounds.joint_floor_of_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,f]; ring)
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (Real.exp (-v/2)*v^N/N.factorial)/2000 ≤ V₀/1000 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+max (∑ n ∈ B, f n).re 0)+
    ZetaRieszCentralReserve.sourceCredit u y N/2-err j ≤ _
  nlinarith only [hc,hrs,hscaled,(abs_le.mp herr).2]

#print axioms eventually_joint_positive_five_floor

/-- The whole joint SUM now pays a fixed positive-five sector in every
phase cell, retaining half the previous central reserve and the exact
signed rest. Cached covers discharge every population premise. -/
theorem eventually_joint_positive_five_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+min (∑ n ∈ B, f n).re 0)-
          ZetaRieszCentralReserve.sourceCredit u y N/2+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  filter_upwards [eventually_central_bin_three_four_five_upper_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwhole := ZetaRieszJointPositiveFiveBounds.joint_ceiling_of_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,f]; ring)
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (Real.exp (-v/2)*v^N/N.factorial)/2000 ≤ V₀/1000 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+min (∑ n ∈ B, f n).re 0)-
    ZetaRieszCentralReserve.sourceCredit u y N/2+err j
  nlinarith only [hc,hrs,hscaled,(abs_le.mp herr).1]

#print axioms eventually_joint_positive_five_ceiling

/-- The actual WHOLE joint floor pays every newly selected owner label
across the entire core and every prime count. The earlier positive-five
payment and both favorable observations are retained; the central credit
is spent only once and the exact signed complement remains explicit. -/
theorem eventually_joint_owner_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        (3/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,err,hm,he0,heLim,he⟩ := eventually_joint_positive_five_floor hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [he,hmass] with j hpaid hmass
  obtain ⟨v,hpeak,hlo,hhi,hpaid⟩ := hpaid
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hcost := hmass (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcost
  have hD : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcost
    (g := u^(N+1)*max (∑ n ∈ B, f n).re 0+ZetaRieszCentralReserve.sourceCredit u y N/2-err j)
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,B,f]; ring)
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  change u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+
    max (∑ n ∈ D, f n).re 0)+(3/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hbound]

#print axioms eventually_joint_owner_floor

/-- The actual WHOLE joint ceiling pays every newly selected owner label
across the entire core and every prime count. The earlier positive-five
payment and both favorable observations are retained; the central credit
is spent only once and the exact signed complement remains explicit. -/
theorem eventually_joint_owner_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          (3/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,err,hm,he0,heLim,he⟩ := eventually_joint_positive_five_ceiling hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [he,hmass] with j hpaid hmass
  obtain ⟨v,hpeak,hlo,hhi,hpaid⟩ := hpaid
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hcost := hmass (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcost
  have hD : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcost
    (g := ZetaRieszCentralReserve.sourceCredit u y N/2-err j-u^(N+1)*min (∑ n ∈ B, f n).re 0)
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,B,f]; ring)
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+
    min (∑ n ∈ D, f n).re 0)-(3/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hbound]

#print axioms eventually_joint_owner_ceiling

#print axioms eventually_central_bin_four_floor
#print axioms eventually_central_bin_three_four_floor
#print axioms eventually_central_window_three_four_floor
#print axioms eventually_central_bin_three_four_ceiling
#print axioms eventually_central_window_three_four_ceiling

#print axioms eventually_central_window_four_ceiling
#print axioms eventually_central_bin_four_ceiling
#print axioms central_ordered_integral_lower
#print axioms eventually_central_bin_five_floor
#print axioms eventually_central_bin_five_ceiling
#print axioms eventually_central_bin_three_four_five_floor
#print axioms eventually_central_bin_three_four_five_all_phase_ceiling
#print axioms eventually_central_bin_three_four_five_family_floor
#print axioms eventually_central_bin_three_four_five_family_ceiling
#print axioms eventually_central_bin_three_four_five_period_payment
#print axioms eventually_central_bin_three_four_five_upper_period_payment
#print axioms eventually_exists_central_bin_three_four_five_period
#print axioms eventually_exists_central_bin_three_four_five_upper_period
#print axioms eventually_central_bin_three_four_five_period_payment_with_radial
#print axioms eventually_central_bin_three_four_five_upper_period_payment_with_radial
#print axioms eventually_exists_central_bin_lower_source_credit
#print axioms eventually_exists_central_bin_upper_source_credit
/-- Sharper payment on the same certified populations and original phase period. -/
theorem eventually_sharp_central_period_payment_with_radial {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
          (m : ℝ)/125*V₀*h ≤ (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_central_bin_three_four_five_family_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszCentralSharpBudget.original_central_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

#print axioms eventually_sharp_central_period_payment_with_radial


/-- Sharper payment on the same certified populations and original phase period. -/
theorem eventually_sharp_central_upper_period_payment_with_radial {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\(Finset.range (8*m)).biUnion P,
          ZetaRieszJointAllocation.residualCoefficient A L N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
          (m : ℝ)/125*V₀*h := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_central_bin_three_four_five_family_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN v
  dsimp only
  intro hpeak hlo hhi hbin
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszCentralSharpBudget.original_central_upper_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  dsimp only [T] at hjoint
  linarith only [hpay,hjoint]

#print axioms eventually_sharp_central_upper_period_payment_with_radial


/-- The actual whole floor retains six source credits after the unchanged positive-five payment. -/
theorem eventually_joint_sharp_positive_five_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+max (∑ n ∈ B, f n).re 0)+
        6*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  filter_upwards [eventually_sharp_central_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwhole := ZetaRieszJointOwnerPayment.floor_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : 6*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ 7*V₀/1000 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+max (∑ n ∈ B, f n).re 0)+
    6*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hc,hrs,hscaled,(abs_le.mp herr).2]

#print axioms eventually_joint_sharp_positive_five_floor


/-- The actual whole ceiling retains six source credits after the unchanged positive-five payment. -/
theorem eventually_joint_sharp_positive_five_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+min (∑ n ∈ B, f n).re 0)-
          6*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  filter_upwards [eventually_sharp_central_upper_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwhole := ZetaRieszJointOwnerPayment.ceiling_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : 6*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ 7*V₀/1000 := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B), f n).re+min (∑ n ∈ B, f n).re 0)-
    6*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hc,hrs,hscaled,(abs_le.mp herr).1]

#print axioms eventually_joint_sharp_positive_five_ceiling


/-- The actual whole floor retains 47/8 source credits with every old payment and the exact signed rest. -/
theorem eventually_joint_sharp_owner_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        (47/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,err,hm,he0,heLim,he⟩ := eventually_joint_sharp_positive_five_floor hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [he,hmass] with j hpaid hmass
  obtain ⟨v,hpeak,hlo,hhi,hpaid⟩ := hpaid
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hcost := hmass (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcost
  have hD : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcost
    (g := u^(N+1)*max (∑ n ∈ B, f n).re 0+6*ZetaRieszCentralReserve.sourceCredit u y N-err j)
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,B,f]; ring)
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  change u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+
    max (∑ n ∈ D, f n).re 0)+(47/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hbound]

#print axioms eventually_joint_sharp_owner_floor


/-- The actual whole ceiling retains 47/8 source credits with every old payment and the exact signed rest. -/
theorem eventually_joint_sharp_owner_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          (47/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,err,hm,he0,heLim,he⟩ := eventually_joint_sharp_positive_five_ceiling hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [he,hmass] with j hpaid hmass
  obtain ⟨v,hpeak,hlo,hhi,hpaid⟩ := hpaid
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hcost := hmass (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcost
  have hD : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcost
    (g := 6*ZetaRieszCentralReserve.sourceCredit u y N-err j-u^(N+1)*min (∑ n ∈ B, f n).re 0)
    (by convert hpaid using 1; dsimp only [P,T,h,S,L,N,K,A,B,f]; ring)
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+
    min (∑ n ∈ D, f n).re 0)-(47/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hbound]

#print axioms eventually_joint_sharp_owner_ceiling

/-- The actual whole floor also pays the complete positive-five least-prime boundary, preserving every old payment and the full 47/8 source credit. -/
theorem eventually_joint_boundary_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        (47/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_sharp_central_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwholeB := ZetaRieszJointOwnerPayment.floor_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwholeB
  have hHbase : H ⊆ S\(P ∪ B ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ B) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ B ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1200*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.floor_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := max (∑ n ∈ B, f n).re 0+(m : ℝ)/125*V₀*h-(m : ℝ)/1000*V₀*h) (by nlinarith only [hwholeB])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : 6*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (37/6000 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ B ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H), f n).re+
      (u^(N+1)*(max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0)+
        6*ZetaRieszCentralReserve.sourceCredit u y N) ≤
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
    (47/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hbound,(abs_le.mp herr).2]

#print axioms eventually_joint_boundary_floor


/-- The actual whole ceiling also pays the complete positive-five least-prime boundary, preserving every old payment and the full 47/8 source credit. -/
theorem eventually_joint_boundary_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          (47/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_sharp_central_upper_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwholeB := ZetaRieszJointOwnerPayment.ceiling_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwholeB
  have hHbase : H ⊆ S\(P ∪ B ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ B) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ B ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1200*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.ceiling_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (m : ℝ)/125*V₀*h-(m : ℝ)/1000*V₀*h-min (∑ n ∈ B, f n).re 0) (by nlinarith only [hwholeB])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszCentralReserve.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : 6*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (37/6000 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ B ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤
      u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H), f n).re-
      (6*ZetaRieszCentralReserve.sourceCredit u y N-
        u^(N+1)*(min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0)) := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
    (47/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hbound,(abs_le.mp herr).1]

#print axioms eventually_joint_boundary_ceiling


/-- The same whole floor retains the factorial square-root gain after every old payment, with the sharper boundary debit, identical signed rest and favorable observations. -/
theorem eventually_joint_saddle_boundary_floor {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_sharp_central_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwholeB := ZetaRieszJointOwnerPayment.floor_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwholeB
  have hHbase : H ⊆ S\(P ∪ B ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ B) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ B ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.floor_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := max (∑ n ∈ B, f n).re 0+(m : ℝ)/125*V₀*h-(m : ℝ)/1000*V₀*h) (by nlinarith only [hwholeB])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (25/4)*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (51/8000 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ B ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H), f n).re+
      (u^(N+1)*(max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0)+
        (25/2)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N) ≤
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
    ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hbound,(abs_le.mp herr).2]

#print axioms eventually_joint_saddle_boundary_floor


/-- The same whole ceiling retains the factorial square-root gain after every old payment, with the sharper boundary debit, identical signed rest and favorable observations. -/
theorem eventually_joint_saddle_boundary_ceiling {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hmass := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointPositiveFiveBounds.eventually_period_norm_mass hm hy hhu)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_sharp_central_upper_period_payment_with_radial hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hmass,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hmass hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let B := ZetaRieszJointPositiveFiveBounds.periodPopulation (S\P) L v y m
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ B)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ B ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins
  have hcost := hmass (S\P) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ B, ‖f n‖) ≤ (m : ℝ)/1000*V₀*h at hcost
  have hwholeB := ZetaRieszJointOwnerPayment.ceiling_after_payment f
    (ZetaRieszJointPositiveFiveBounds.periodPopulation_subset (S\P) L v y m) hcost
    (g := (m : ℝ)/125*V₀*h) hpaid
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwholeB
  have hHbase : H ⊆ S\(P ∪ B ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ B) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ B ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.ceiling_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (m : ℝ)/125*V₀*h-(m : ℝ)/1000*V₀*h-min (∑ n ∈ B, f n).re 0) (by nlinarith only [hwholeB])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (25/4)*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (51/8000 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ B) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ B ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ B)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤
      u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H), f n).re-
      ((25/2)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-
        u^(N+1)*(min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0)) := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
    ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hbound,(abs_le.mp herr).1]

#print axioms eventually_joint_saddle_boundary_ceiling

/-- The checked full positive-five interior is paid before the phase surplus is collapsed. -/
theorem eventually_full_five_period_floor_with_radial (tree : ZetaRieszPositiveFiveCover.Cover.Tree)
    (hcheck : ZetaRieszPositiveFiveCover.Cover.check
      (ZetaRieszPositiveFiveCover.check (693/1000) (1733/2500) (119/200))
      tree ZetaRieszPositiveFiveCells.root = true)
    (htotal : (ZetaRieszPositiveFiveCover.Cover.totals tree ZetaRieszPositiveFiveCells.root).2 ≤ 3961/1000000)
    {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation
        (S\(Finset.range (8*m)).biUnion P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      (∀ i ∈ Finset.range (8*m), (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧
        (∑ n ∈ S\((Finset.range (8*m)).biUnion P ∪ I), f n).re+
          (∑ n ∈ I, max 0 (f n).re)+(m : ℝ)/1200*V₀*h ≤
            (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  have hIpay := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveSignedPayment.eventually_directed_period_of_checked_tree
      (δ := ZetaRieszPositiveFiveBoundary.headShare)
      tree hcheck htotal (by norm_num) (by norm_num) hm hy0 hhu
        (by norm_num [ZetaRieszPositiveFiveBoundary.headShare]))
  filter_upwards [hIpay,eventually_central_bin_three_four_five_family_floor hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hIpay hJ hN v
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hIpay
  dsimp only
  intro hpeak hlo hhi hbin hnewbin
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation
    (S\(Finset.range (8*m)).biUnion P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  have hnewgeom : ∀ i ∈ Finset.range (8*m), (N : ℝ) ≤ T i ∧
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hnR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    exact ⟨by nlinarith only [(hgeom i hi).1,hnR],hnewbin i hi⟩
  have hcost := hIpay (S\(Finset.range (8*m)).biUnion P) A L v (-1) hnewgeom (by norm_num)
  simp only [neg_one_mul] at hcost
  have hwhole := ZetaRieszJointFullFiveBounds.floor_after_directed_payment f
    (ZetaRieszPositiveFiveSignedPayment.periodPopulation_subset _ _ _ _ _ _) hcost hjoint
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszPositiveFiveWholeBudget.interior_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  let X := fun i => (Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
    max 0 (-Real.cos (y*T i)-|y| * h)*h
  let Y := fun i => (Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
    (max 0 (-Real.cos (y*T i))+|y| * h)*h
  have heq : (∑ i ∈ Finset.range (8*m), ((1309/10000 : ℝ)*X i-(1301/10000 : ℝ)*Y i)) =
      (∑ i ∈ Finset.range (8*m), ((1309/10000 : ℝ)*X i-(1261/10000 : ℝ)*Y i))-
      ∑ i ∈ Finset.range (8*m), (1/250 : ℝ)*Y i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (m : ℝ)/1200*V₀*h ≤ ∑ i ∈ Finset.range (8*m),
    ((1309/10000 : ℝ)*X i-(1301/10000 : ℝ)*Y i) at hpay
  change (∑ n ∈ S\((Finset.range (8*m)).biUnion P ∪ I), f n).re+
    (∑ n ∈ I, max 0 (f n).re)+
    (∑ i ∈ Finset.range (8*m), ((1309/10000 : ℝ)*X i-(1261/10000 : ℝ)*Y i))-
    (∑ i ∈ Finset.range (8*m), (1/250 : ℝ)*Y i) ≤ _ at hwhole
  rw [heq] at hpay
  linarith only [hpay,hwhole]

#print axioms eventually_full_five_period_floor_with_radial

/-- The same full positive-five interior is paid in the whole upper comparison. -/
theorem eventually_full_five_period_ceiling_with_radial (tree : ZetaRieszPositiveFiveCover.Cover.Tree)
    (hcheck : ZetaRieszPositiveFiveCover.Cover.check
      (ZetaRieszPositiveFiveCover.check (693/1000) (1733/2500) (119/200))
      tree ZetaRieszPositiveFiveCells.root = true)
    (htotal : (ZetaRieszPositiveFiveCover.Cover.totals tree ZetaRieszPositiveFiveCells.root).2 ≤ 3961/1000000)
    {u b δ y : ℝ} {M m : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54 ≤ |y|) (hm : 0 < m)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hε : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000)
    (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∀ᶠ j : ℕ in atTop, ∀ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
        RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
      let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation
        (S\(Finset.range (8*m)).biUnion P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
        L/T i ≤ RieszFourCapacityBin2.Assembly.high) →
      (∀ i ∈ Finset.range (8*m), (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i) →
      ∃ V₀ : ℝ, 0 < V₀ ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ ∧ (ZetaRieszParityPacket.coreResponse u y N K).re ≤
        (∑ n ∈ S\((Finset.range (8*m)).biUnion P ∪ I), f n).re+
          (∑ n ∈ I, min (f n).re 0)-(m : ℝ)/1200*V₀*h := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  have hIpay := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveSignedPayment.eventually_directed_period_of_checked_tree
      (δ := ZetaRieszPositiveFiveBoundary.headShare)
      tree hcheck htotal (by norm_num) (by norm_num) hm hy0 hhu
        (by norm_num [ZetaRieszPositiveFiveBoundary.headShare]))
  filter_upwards [hIpay,eventually_central_bin_three_four_five_family_ceiling hu hU hh hhu hδ hδu hb hsmall hcover,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hIpay hJ hN v
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hIpay
  dsimp only
  intro hpeak hlo hhi hbin hnewbin
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let D := fun i => (ZetaRieszFiveAngularBoundary.interiorFamily M
    RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))
  let P := fun i => ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then D i else ∅))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation
    (S\(Finset.range (8*m)).biUnion P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hgeom : ∀ i ∈ Finset.range (8*m),
      (39/20 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ≤ T i ∧
      T i+Real.pi/(4*m*|y|) ≤ (203/100 : ℝ)*ZetaRieszPrimeCountFrequency.dyadicMomentOrder j ∧
      (RieszFourCapacityBin2.Assembly.low : ℝ) ≤
        SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ∧
      SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)/T i ≤
        RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    exact ⟨hlo.trans ht.1,ht.2.trans hhi,hbin i hi⟩
  have hsep : ∀ i ∈ Finset.range (8*m), ∀ k ∈ Finset.range (8*m),
      i < k → T i+Real.pi/(4*m*|y|) ≤ T k := by
    intro i _ k _ hik
    exact ZetaRieszCapacityPhaseBudget.period_cells_separated hm hik v hy0
  have hjoint := hJ (Finset.range (8*m)) T y hgeom hsep
  have hnewgeom : ∀ i ∈ Finset.range (8*m), (N : ℝ) ≤ T i ∧
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hnR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    exact ⟨by nlinarith only [(hgeom i hi).1,hnR],hnewbin i hi⟩
  have hcost := hIpay (S\(Finset.range (8*m)).biUnion P) A L v 1 hnewgeom (by norm_num)
  simp only [one_mul] at hcost
  let X := fun i => (Real.exp (-(T i+h)/2)*(T i)^N/N.factorial)*
    max 0 (Real.cos (y*T i)-|y| * h)*h
  let Y := fun i => (Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
    (max 0 (Real.cos (y*T i))+|y| * h)*h
  change (ZetaRieszParityPacket.coreResponse u y N K).re ≤
    (∑ n ∈ S\(Finset.range (8*m)).biUnion P, f n).re+
    ∑ i ∈ Finset.range (8*m), ((1261/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i) at hjoint
  have hwhole := ZetaRieszJointFullFiveBounds.ceiling_after_directed_payment f
    (ZetaRieszPositiveFiveSignedPayment.periodPopulation_subset _ _ _ _ _ _) hcost
    (g := -(∑ i ∈ Finset.range (8*m), ((1261/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i)))
    (by simpa only [sub_neg_eq_add] using hjoint)
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  obtain ⟨V₀,hV₀,hVr,hpay⟩ := ZetaRieszPositiveFiveWholeBudget.interior_upper_period_budget_with_radial
    (by omega : 0 < ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) hm hy hpeak hlo hhi hh hhu hε
  refine ⟨V₀,hV₀,hVr,?_⟩
  have heq : (∑ i ∈ Finset.range (8*m), ((1301/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i)) =
      (∑ i ∈ Finset.range (8*m), ((1261/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i))+
      ∑ i ∈ Finset.range (8*m), (1/250 : ℝ)*Y i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i ∈ Finset.range (8*m), ((1301/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i)) ≤
    -(m : ℝ)/1200*V₀*h at hpay
  change _ ≤ (∑ n ∈ S\((Finset.range (8*m)).biUnion P ∪ I), f n).re+
    (∑ n ∈ I, min (f n).re 0)-
    -(∑ i ∈ Finset.range (8*m), ((1261/10000 : ℝ)*Y i-(1309/10000 : ℝ)*X i))+
    (∑ i ∈ Finset.range (8*m), (1/250 : ℝ)*Y i) at hwhole
  rw [heq] at hpay
  linarith only [hpay,hwhole]

#print axioms eventually_full_five_period_ceiling_with_radial

/-- The whole floor pays the full positive-five interior, its owner and small-prime boundary, retaining all favorable atoms and the exact signed rest. The finite cover premise is discharged by the optional positive-five assembly. -/
theorem eventually_joint_full_positive_five_floor (tree : ZetaRieszPositiveFiveCover.Cover.Tree)
    (hcheck : ZetaRieszPositiveFiveCover.Cover.check
      (ZetaRieszPositiveFiveCover.check (693/1000) (1733/2500) (119/200))
      tree ZetaRieszPositiveFiveCells.root = true)
    (htotal : (ZetaRieszPositiveFiveCover.Cover.totals tree ZetaRieszPositiveFiveCells.root).2 ≤ 3961/1000000)
    {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
        ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ D), f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((2/5)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveInterior.eventually_saddle_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_full_five_period_floor_with_radial tree hcheck htotal hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hcutoff,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hcutoff hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h y (δ*N) ∪
    ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h y
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b)))))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+1 := by linarith only [hcell.2,hvu,hpi]
    have ht0 : 0 < T i := by linarith only [hcell.1,hlo,hNR]
    have hh0 : 0 < T i+h := by linarith only [ht0,hh]
    have hlow := (hcutoff (T i+h) (by linarith only [htl,hh]) htu).1
    have hhigh := (hcutoff (T i) htl (by linarith only [htu,hh])).2
    exact ⟨(le_div_iff₀ hh0).mp hlow,(div_le_iff₀ ht0).mp hhigh⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins hnewbin
  have hHbase : H ⊆ S\(P ∪ I ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ I) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ I ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.floor_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (∑ n ∈ I, max 0 (f n).re)+(m : ℝ)/1200*V₀*h) (by nlinarith only [hpaid])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (1/5)*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ I) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ I)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H), f n).re+
      (u^(N+1)*((∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0)+
        (2/5)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N) ≤
      u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_floor_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ D), f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
    ((2/5)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ _
  nlinarith only [hbound,(abs_le.mp herr).2]

#print axioms eventually_joint_full_positive_five_floor

/-- The whole ceiling pays the full positive-five interior, its owner and small-prime boundary, retaining all favorable atoms and the exact signed rest. The finite cover premise is discharged by the optional positive-five assembly. -/
theorem eventually_joint_full_positive_five_ceiling (tree : ZetaRieszPositiveFiveCover.Cover.Tree)
    (hcheck : ZetaRieszPositiveFiveCover.Cover.check
      (ZetaRieszPositiveFiveCover.check (693/1000) (1733/2500) (119/200))
      tree ZetaRieszPositiveFiveCells.root = true)
    (htotal : (ZetaRieszPositiveFiveCover.Cover.totals tree ZetaRieszPositiveFiveCells.root).2 ≤ 3961/1000000)
    {u b δ : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (hy : 54 ≤ |y|) (hδ : 0 < δ) (hδu : δ ≤ 1/128)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b) :
    ∃ m : ℕ, ∃ err : ℕ → ℝ, 0 < m ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      let P := (Finset.range (8*m)).biUnion (fun i =>
        ZetaRieszBroadTripleBudget.population S (T i) h ∪
        (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
        (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
          RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
          (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
            (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
      let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
      let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
      let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ D), f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((2/5)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,hm,hh,hhu,hε⟩ := ZetaRieszCapacityPhaseBudget.exists_period_mesh hy
  obtain ⟨err,he0,heLim,he⟩ := ZetaRieszJointReflectionBounds.exists_joint_core_error
    (by linarith : 0 ≤ u) hU y
  refine ⟨m,err,hm,he0,heLim,?_⟩
  have hgeom := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszCapacityPhaseBudget.eventually_exists_central_bin_period_at_saddle hu.le hU)
  have hcutoff := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveInterior.eventually_saddle_cutoff_ratio hu.le hU)
  have hboundary := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszPositiveFiveBoundary.eventually_period_norm_mass_sharp hm hy hhu)
  have hyne : y ≠ 0 := abs_pos.mp (by linarith : 0 < |y|)
  have howner := ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszJointOwnerPayment.eventually_norm_mass_credit hyne (by norm_num : (0 : ℝ) < 1/8))
  filter_upwards [eventually_full_five_period_ceiling_with_radial tree hcheck htotal hu hU hy hm hhu hε hδ hδu hb hsmall hcover,
    hgeom,hcutoff,hboundary,howner,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hpay hJ hcutoff hboundary howner hN
  obtain ⟨v,hv,hvu,hpeak,hlo,hhi,hbin⟩ := hJ y hy
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
  let P := (Finset.range (8*m)).biUnion (fun i =>
    ZetaRieszBroadTripleBudget.population S (T i) h ∪
    (adversePopulation (clippedSupport S) L (T i) h (Real.pi/T i) (δ*N) ∪
    (if 0 ≤ Real.cos (y*T i)-|y| * h then ((ZetaRieszFiveAngularBoundary.interiorFamily M
      RieszFiveCapacityBin2.Assembly.low RieszFiveCapacityBin2.Assembly.high (h/T i) b).biUnion
      (fun w => ZetaRieszJointPrimeCells.supplyCell (T i) h (Real.pi/T i)
        (fun k => T i*ZetaRieszFiveInteriorBudget.gridLo 0 b w k) (fun _ => T i*b))) else ∅)))
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hy0 : 0 < |y| := by linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbins : ∀ i ∈ Finset.range (8*m), (RieszFourCapacityBin2.Assembly.low : ℝ) ≤ L/T i ∧
      L/T i ≤ RieszFourCapacityBin2.Assembly.high := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht' : T i ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2]
    simpa only [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high,
      Rat.cast_div,Rat.cast_ofNat] using hbin _ ht.1 ht'
  have hbasic : ∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*T i ≤ L ∧ L ≤ (7/10 : ℝ)*T i := by
    intro i hi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have ht0 : 0 < T i := by dsimp [T]; nlinarith [ht.1]
    have hb := hbins i hi
    norm_num [RieszFourCapacityBin2.Assembly.low,RieszFourCapacityBin2.Assembly.high] at hb
    exact ⟨(le_div_iff₀ ht0).mp (by linarith [hb.1]),
      (div_le_iff₀ ht0).mp (by linarith [hb.2])⟩
  have hpi : Real.pi/|y| ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hy0).mpr
    linarith only [hy,Real.pi_lt_four]
  have hnewbin : ∀ i ∈ Finset.range (8*m),
      (693/1000 : ℝ)*(T i+h) ≤ L ∧ L ≤ (1733/2500 : ℝ)*T i := by
    intro i hi
    have hcell := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    change v-Real.pi/|y| ≤ T i ∧ T i+h ≤ v+Real.pi/|y| at hcell
    have htl : 2*(N : ℝ)-1 ≤ T i := by linarith only [hcell.1,hv,hpi]
    have htu : T i+h ≤ 2*(N : ℝ)+1 := by linarith only [hcell.2,hvu,hpi]
    have ht0 : 0 < T i := by linarith only [hcell.1,hlo,hNR]
    have hh0 : 0 < T i+h := by linarith only [ht0,hh]
    have hlow := (hcutoff (T i+h) (by linarith only [htl,hh]) htu).1
    have hhigh := (hcutoff (T i) htl (by linarith only [htu,hh])).2
    exact ⟨(le_div_iff₀ hh0).mp hlow,(div_le_iff₀ ht0).mp hhigh⟩
  obtain ⟨V₀,hV₀,hVr,hpaid⟩ := hpay v hpeak hlo hhi hbins hnewbin
  have hHbase : H ⊆ S\(P ∪ I ∪ D) := ZetaRieszPositiveFiveBoundary.periodPopulation_subset _ _ _ _ _
  have hH : H ⊆ S\(P ∪ I) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hHbase hn)
    exact Finset.mem_sdiff.mpr ⟨hnS,fun h => hnnot (Finset.mem_union_left _ h)⟩
  have hcostH := hboundary (S\(P ∪ I ∪ D)) A L v V₀ hlo hhi hbasic hV₀.le hVr
  change (∑ n ∈ H, ‖f n‖) ≤ (m : ℝ)/1600*V₀*h at hcostH
  have hwhole := ZetaRieszJointOwnerPayment.ceiling_after_payment f hH hcostH
    (whole := (ZetaRieszParityPacket.coreResponse u y N K).re)
    (g := (m : ℝ)/1200*V₀*h-(∑ n ∈ I, min (f n).re 0)) (by nlinarith only [hpaid])
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hwhole
  have hu0 : 0 ≤ u := by linarith
  have hpow : 0 ≤ u^(N+1) := pow_nonneg hu0 _
  have hc := ZetaRieszSaddleCredit.sourceCredit_le_scaled_margin hu0 (abs_pos.mp hy0)
    hN hm hv (by linarith only [hvu])
  have hhalf : (1/5)*(Real.exp (-v/2)*v^N/N.factorial)/1000 ≤ (1/4800 : ℝ)*V₀ := by
    linarith only [hVr,hV₀]
  have hr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg m)) hh.le
  have hrs := mul_le_mul_of_nonneg_left hr hpow
  have hscaled := mul_le_mul_of_nonneg_left hwhole hpow
  have hDbase : D ⊆ S\(P ∪ I) := ZetaRieszJointOwnerPayment.population_subset _ _
  have hD : D ⊆ S\(P ∪ I ∪ H) := by
    intro n hn
    obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp (hDbase hn)
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with hp | hh
    · exact hnnot hp
    · exact (Finset.mem_sdiff.mp (hHbase hh)).2 (Finset.mem_union_right _ hn)
  have hcostD := howner (S\(P ∪ I)) A L u (SquarefreeVaughanLogSource.length_pos u N) hu0
  change u^(N+1)*(∑ n ∈ D, ‖f n‖) ≤ (1/8)*ZetaRieszCentralReserve.sourceCredit u y N at hcostD
  have hbody : u^(N+1)*(ZetaRieszParityPacket.coreResponse u y N K).re ≤
      u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H), f n).re-
      ((2/5)*Real.sqrt ((N : ℝ)+1)*ZetaRieszCentralReserve.sourceCredit u y N-
        u^(N+1)*((∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0)) := by
    nlinarith only [hc,hrs,hscaled]
  have hbound := ZetaRieszJointOwnerPayment.scaled_ceiling_after_payment f hpow hD hcostD hbody
  rw [sdiff_sdiff_left,Finset.sup_eq_union] at hbound
  have herr := he j
  dsimp only at herr
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at herr
  refine ⟨v,hpeak,hlo,hhi,?_⟩
  dsimp only
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ ≤ u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ D), f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
    ((2/5)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hbound,(abs_le.mp herr).1]

#print axioms eventually_joint_full_positive_five_ceiling

end RieszCentralCapacityTransfer

#lint+ in RieszCentralCapacityTransfer
