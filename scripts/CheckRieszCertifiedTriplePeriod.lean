/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import CheckRieszTriplePeriodJoint
import CheckRieszFullPositiveFive
import Mathlib.Tactic.Linter

/-!
# Certified combined whole bounds with triple cancellation

All numerical cover premises are discharged by the cached assemblies.
The new triple period is paid once, with its geometric allocation error,
while all previous favorable observations and the exact rest are retained.
-/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open RiemannGaussian
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget
namespace RieszCertifiedTriplePeriod

/-- The actual combined whole floor has every finite cover premise discharged. -/
theorem eventually_combined_floor {u b δ : ℝ} {M : ℕ}
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
      let Q := ZetaRieszTriplePeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  exact RieszTriplePeriodJoint.eventually_combined_floor
    RieszPositiveFiveInterior.Assembly.part0000_tree
    RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total
    hu hU y hy hδ hδu hb hsmall hcover

#print axioms eventually_combined_floor

/-- The actual combined whole ceiling has every finite cover premise discharged. -/
theorem eventually_combined_ceiling {u b δ : ℝ} {M : ℕ}
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
      let Q := ZetaRieszTriplePeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  exact RieszTriplePeriodJoint.eventually_combined_ceiling
    RieszPositiveFiveInterior.Assembly.part0000_tree
    RieszFullPositiveFiveTransfer.checked_cover RieszFullPositiveFiveTransfer.checked_total
    hu hU y hy hδ hδu hb hsmall hcover

#print axioms eventually_combined_ceiling

/-- The expanded whole floor also applies the centered six-prime charges only to its exact unpaid rest, preserving every previous payment and favorable observation. -/
theorem eventually_combined_six_floor {u b δ : ℝ} {M : ℕ}
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
      let Q := ZetaRieszTriplePeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ D, f n).re 0)+
        ((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re := by
  obtain ⟨m,err,hm,herr,hevent,hbase⟩ := eventually_combined_floor
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
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let Q := ZetaRieszTriplePeriod.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
  let E := S\(P ∪ I ∪ H ∪ Q ∪ D)
  have hsub : E ⊆ S := Finset.sdiff_subset
  have hc := (ZetaRieszSixPrimeCentered.core_centered_subset_bounds hu.le hN K y E hsub).1
  dsimp only at hv ⊢
  refine ⟨v,hv.1,hv.2.1,hv.2.2.1,?_⟩
  have hwhole := hv.2.2.2
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  change u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re) ≤ u^(N+1)*(∑ n ∈ E, f n).re at hc
  change u^(N+1)*((∑ n ∈ E, f n).re+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ D, f n).re 0)+((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re at hwhole
  change u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then max (f n).re 0-ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+(∑ n ∈ I, max 0 (f n).re)+max (∑ n ∈ H, f n).re 0+max (∑ n ∈ Q, f n).re 0+max (∑ n ∈ D, f n).re 0)+((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N-err j ≤ ((u : ℂ)^(N+1)*J).re
  nlinarith only [hc,hwhole]

#print axioms eventually_combined_six_floor

/-- The expanded whole ceiling also applies the centered six-prime charges only to its exact unpaid rest, preserving every previous payment and favorable observation. -/
theorem eventually_combined_six_ceiling {u b δ : ℝ} {M : ℕ}
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
      let Q := ZetaRieszTriplePeriod.population v y
      let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n
      let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
        ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
      Real.cos (y*v) = -1 ∧ (39/20 : ℝ)*N ≤ v-Real.pi/|y| ∧
      v+Real.pi/|y| ≤ (203/100 : ℝ)*N ∧
      ((u : ℂ)^(N+1)*J).re ≤
        u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ D, f n).re 0)-
          ((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j := by
  obtain ⟨m,err,hm,herr,hevent,hbase⟩ := eventually_combined_ceiling
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
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation (S\P) L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\(P ∪ I)) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(P ∪ I ∪ D)) L v y m
  let Q := ZetaRieszTriplePeriod.population v y
  let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let J := ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y N K-
    ZetaRieszLeastOrderOverflow.shortOverflowPacket u y N K+ZetaRieszLeastBoundary.rest u y N K
  let E := S\(P ∪ I ∪ H ∪ Q ∪ D)
  have hsub : E ⊆ S := Finset.sdiff_subset
  have hc := (ZetaRieszSixPrimeCentered.core_centered_subset_bounds hu.le hN K y E hsub).2
  dsimp only at hv ⊢
  refine ⟨v,hv.1,hv.2.1,hv.2.2.1,?_⟩
  have hwhole := hv.2.2.2
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  change u^(N+1)*(∑ n ∈ E, f n).re ≤ u^(N+1)*(∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re) at hc
  change ((u : ℂ)^(N+1)*J).re ≤ u^(N+1)*((∑ n ∈ E, f n).re+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ D, f n).re 0)-((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j at hwhole
  change ((u : ℂ)^(N+1)*J).re ≤ u^(N+1)*((∑ n ∈ S\(P ∪ I ∪ H ∪ Q ∪ D), if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes (Real.log n-L) n).card then min (f n).re 0+ZetaRieszOneSidedArithmetic.weight A N n*ZetaRieszSixPrimeCentered.centeredSixCost L y n else (f n).re)+(∑ n ∈ I, min (f n).re 0)+min (∑ n ∈ H, f n).re 0+min (∑ n ∈ Q, f n).re 0+min (∑ n ∈ D, f n).re 0)-((2/25)*Real.sqrt ((N : ℝ)+1)-1/8)*ZetaRieszCentralReserve.sourceCredit u y N+err j
  nlinarith only [hc,hwhole]

#print axioms eventually_combined_six_ceiling

end RieszCertifiedTriplePeriod

#lint+ in RieszCertifiedTriplePeriod
