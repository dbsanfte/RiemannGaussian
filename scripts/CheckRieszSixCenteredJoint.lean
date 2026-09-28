/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszCentralCapacityTransfer
import RiemannGaussian.ZetaRieszSixPrimeCentered
import Mathlib.Tactic.Linter

/-!
# Centered six-prime cancellation in the certified whole comparisons

Only the two previously accepted four-prime and negative-five-prime
assemblies are imported. The new positive-five cover is not a premise.
Both comparisons retain their original P,B,D,H populations, radial margin
and exact unpaid rest. No extra credit or completed carrier is introduced.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget
namespace RieszSixCenteredJointTransfer

/-- The previously certified whole floor also applies the centered six-prime charges only to its exact unpaid rest, preserving every previous payment and favorable observation. -/
theorem eventually_joint_saddle_six_floor {u b δ : ℝ} {M : ℕ}
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
      u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,err,hm,herr,hevent,hbase⟩ := RieszCentralCapacityTransfer.eventually_joint_saddle_boundary_floor
    hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,herr,hevent,?_⟩
  filter_upwards [hbase,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (2 : ℕ))] with j hj hN
  obtain ⟨v,hv⟩ := hj
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
  let E := S\(P ∪ B ∪ H ∪ D)
  have hsub : E ⊆ S := Finset.sdiff_subset
  have hc := (ZetaRieszSixPrimeCentered.core_centered_subset_bounds hu.le hN K y E hsub).1
  dsimp only at hv ⊢
  refine ⟨v,hv.1,hv.2.1,hv.2.2.1,?_⟩
  have hwhole := hv.2.2.2
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  change u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re) ≤ u^(N+1)*(∑ n ∈ E, f n).re at hc
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re at hwhole
  change u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+max (∑ n ∈ B, f n).re 0+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ D, f n).re 0)+((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re
  nlinarith only [hc,hwhole]

#print axioms eventually_joint_saddle_six_floor

/-- The previously certified whole ceiling also applies the centered six-prime charges only to its exact unpaid rest, preserving every previous payment and favorable observation. -/
theorem eventually_joint_saddle_six_ceiling {u b δ : ℝ} {M : ℕ}
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
        u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,err,hm,herr,hevent,hbase⟩ := RieszCentralCapacityTransfer.eventually_joint_saddle_boundary_ceiling
    hu hU y hy hδ hδu hb hsmall hcover
  refine ⟨m,err,hm,herr,hevent,?_⟩
  filter_upwards [hbase,ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
    (eventually_ge_atTop (2 : ℕ))] with j hj hN
  obtain ⟨v,hv⟩ := hj
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
  let E := S\(P ∪ B ∪ H ∪ D)
  have hsub : E ⊆ S := Finset.sdiff_subset
  have hc := (ZetaRieszSixPrimeCentered.core_centered_subset_bounds hu.le hN K y E hsub).2
  dsimp only at hv ⊢
  refine ⟨v,hv.1,hv.2.1,hv.2.2.1,?_⟩
  have hwhole := hv.2.2.2
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  change u^(N+1)*(∑ n ∈ E, f n).re ≤ u^(N+1)*(∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re) at hc
  change ((u : ℂ)^(N+1)*J).re ≤ u^(N+1)*((∑ n ∈ E, f n).re+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j at hwhole
  change ((u : ℂ)^(N+1)*J).re ≤ u^(N+1)*((∑ n ∈ S\(P ∪ B ∪ H ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+min (∑ n ∈ B, f n).re 0+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ D, f n).re 0)-((25/2)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hc,hwhole]

#print axioms eventually_joint_saddle_six_ceiling

end RieszSixCenteredJointTransfer

#lint+ in RieszSixCenteredJointTransfer
