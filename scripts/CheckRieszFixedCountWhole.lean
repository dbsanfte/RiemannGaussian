/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszFixedCountJoint
import RiemannGaussian.ZetaRieszSixSmallPrimes
import Mathlib.Tactic.Linter

/-! # Whole bounds with fixed-count cancellation and all six-prime costs
Every six-prime label in the exact unpaid complement now has an independent
signed cost. The growing phase-period credits and prior reflection bounds
remain intact. Neither period nor global-owner supply is spent twice. -/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian RieszFixedCountJoint
open ZetaRieszMultiPeriodSix (center)
namespace RieszFixedCountWhole

/-- The growing-band whole floor also pays the no-reflected-large six-prime part of its exact unpaid rest. -/
theorem eventually_whole_floor {u b δ : ℝ} {M : ℕ}
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
      let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
      let data := fun i => localData false u b δ y (center v y i) N K M m
      let E := B.biUnion (fun i => (data i).1)
      let D := ZetaRieszJointOwnerPayment.population (S\E) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ 2*(N : ℝ) ≤ v ∧ v ≤ 2*N+1/2 ∧
      u^(N+1)*((∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.floorCost L y n else (f n).re)+(∑ i ∈ B, (data i).2)+max (∑ n ∈ D, f n).re 0)+
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,err,hm,he0,heLim,hbase⟩ := RieszFixedCountJoint.eventually_combined_floor
    hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  filter_upwards [hbase,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSixSmallPrimes.eventually_core_subset_bounds hu hU)] with j hj hsum
  obtain ⟨v,hphase,hv,hvu,hwhole⟩ := hj
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
  let data := fun i => localData false u b δ y (center v y i) N K M m
  let E := B.biUnion (fun i => (data i).1)
  let D := ZetaRieszJointOwnerPayment.population (S\E) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
  have hc := (hsum K y (S\(E ∪ D)) Finset.sdiff_subset).1
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  refine ⟨v,hphase,hv,hvu,?_⟩
  dsimp only
  change u^(N+1)*((∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.floorCost L y n else (f n).re)+(∑ i ∈ B, (data i).2)+max (∑ n ∈ D, f n).re 0)+
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re
  change u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+max (∑ n ∈ D, f n).re 0)+
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re at hwhole
  change u^(N+1)*(∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.floorCost L y n else (f n).re) ≤ u^(N+1)*(∑ n ∈ S\(E ∪ D), f n).re at hc
  nlinarith only [hc,hwhole]

#print axioms eventually_whole_floor

/-- The growing-band whole ceiling also pays the no-reflected-large six-prime part of its exact unpaid rest. -/
theorem eventually_whole_ceiling {u b δ : ℝ} {M : ℕ}
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
      let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
      let data := fun i => localData true u b δ y (center v y i) N K M m
      let E := B.biUnion (fun i => (data i).1)
      let D := ZetaRieszJointOwnerPayment.population (S\E) A
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ 2*(N : ℝ) ≤ v ∧ v ≤ 2*N+1/2 ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.ceilingCost L y n else (f n).re)+(∑ i ∈ B, (data i).2)+min (∑ n ∈ D, f n).re 0)-
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,err,hm,he0,heLim,hbase⟩ := RieszFixedCountJoint.eventually_combined_ceiling
    hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,he0,heLim,?_⟩
  filter_upwards [hbase,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (ZetaRieszSixSmallPrimes.eventually_core_subset_bounds hu hU)] with j hj hsum
  obtain ⟨v,hphase,hv,hvu,hwhole⟩ := hj
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let B := Finset.range (ZetaRieszSaddlePacking.periodCount y N)
  let data := fun i => localData true u b δ y (center v y i) N K M m
  let E := B.biUnion (fun i => (data i).1)
  let D := ZetaRieszJointOwnerPayment.population (S\E) A
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
  have hc := (hsum K y (S\(E ∪ D)) Finset.sdiff_subset).2
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  refine ⟨v,hphase,hv,hvu,?_⟩
  dsimp only
  change ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.ceilingCost L y n else (f n).re)+(∑ i ∈ B, (data i).2)+min (∑ n ∈ D, f n).re 0)-
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  change ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(E ∪ D), f n).re+(∑ i ∈ B, (data i).2)+min (∑ n ∈ D, f n).re 0)-
        ((B.card : ℝ)*Real.sqrt ((N : ℝ)+1)/16-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j at hwhole
  change u^(N+1)*(∑ n ∈ S\(E ∪ D), f n).re ≤ u^(N+1)*(∑ n ∈ S\(E ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixSmallPrimes.ceilingCost L y n else (f n).re) at hc
  nlinarith only [hc,hwhole]

#print axioms eventually_whole_ceiling

end RieszFixedCountWhole

#lint+ in RieszFixedCountWhole
