/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBroadTripleBudget
import RiemannGaussian.ZetaRieszOppositePhase
import RiemannGaussian.ZetaRieszCapacityPhaseBudget
import RiemannGaussian.ZetaRieszCentralReserve
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
end RieszCentralCapacityTransfer

#lint+ in RieszCentralCapacityTransfer
