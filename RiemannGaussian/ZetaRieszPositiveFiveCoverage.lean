/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointFullFiveBounds

/-!
# The expanded payments cover every positive five-prime term in the period

The full interior, owner and small-prime boundary populations leave no
nonzero positive five-prime coefficient in the selected original period.
This is a support theorem for the same signed complement, not a bound on
the other prime counts or on periods outside the selected saddle period.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveCoverage
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation

/-- Every original positive five-prime label left by the owner and
small-prime cuts belongs to the complete interior phase population. -/
theorem mem_interior_period {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < |y|)
    {S : Finset ℕ} {L v δ : ℝ} {n : ℕ} (hn : n ∈ S)
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hlo : v-Real.pi/|y| < Real.log n) (hhi : Real.log n ≤ v+Real.pi/|y|)
    (hLlo : (693/1000 : ℝ)*Real.log n ≤ L)
    (hLhi : L ≤ (1733/2500 : ℝ)*Real.log n)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re)
    (howner : Real.log (largestPrime n) ≤ (119/200 : ℝ)*Real.log n)
    (hsmall : ∀ p ∈ n.primeFactors, δ*Real.log n < Real.log p) :
    n ∈ ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v y m δ := by
  obtain ⟨i,hi,hil,hih⟩ := ZetaRieszCapacityPhaseBudget.period_cells_cover hm hy hlo hhi
  exact Finset.mem_biUnion.mpr ⟨i,hi,ZetaRieszPositiveFiveCells.mem_root_population
    hn hs hc hil hih hLlo hLhi howner hpos hsmall⟩

/-- On the actual core, the expanded three payments exhaust every
positive five-prime atom in the selected phase period. Any such atom in
the exact remaining set has zero original unassigned coefficient. -/
theorem remaining_positive_five_coefficient_eq_zero (j : ℕ) (hj : 32 ≤ j) (u : ℝ)
    {S : Finset ℕ} (hS : S ⊆ ZetaRieszParityPacket.coreBand u
      (dyadicMomentOrder j) (dyadicPrimeCount j))
    {m : ℕ} (hm : 0 < m) {v y : ℝ} (hy : 0 < |y|) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 5)
    (hlo : v-Real.pi/|y| < Real.log n) (hhi : Real.log n ≤ v+Real.pi/|y|)
    (hLlo : (693/1000 : ℝ)*Real.log n ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hLhi : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) ≤ (1733/2500 : ℝ)*Real.log n)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n).re) :
    let N := dyadicMomentOrder j
    let L := SquarefreeVaughanLogSource.length u N
    let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
    let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v y m ZetaRieszPositiveFiveBoundary.headShare
    let D := ZetaRieszJointOwnerPayment.population (S\I) A
    let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(I ∪ D)) L v y m
    n ∈ S\(I ∪ D ∪ H) → residualCoefficient A L N n = 0 := by
  dsimp only
  intro hn
  by_contra hcoef
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let I := ZetaRieszPositiveFiveSignedPayment.periodPopulation S L v y m ZetaRieszPositiveFiveBoundary.headShare
  let D := ZetaRieszJointOwnerPayment.population (S\I) A
  let H := ZetaRieszPositiveFiveBoundary.periodPopulation (S\(I ∪ D)) L v y m
  change n ∈ S\(I ∪ D ∪ H) at hn
  have hnS := (Finset.mem_sdiff.mp hn).1
  have hnnot := (Finset.mem_sdiff.mp hn).2
  have hnI : n ∉ I := fun hi => hnnot (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hnD : n ∈ (S\I)\D := Finset.mem_sdiff.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hnS,hnI⟩,fun hd => hnnot (Finset.mem_union_left _ (Finset.mem_union_right _ hd))⟩
  have hp := ZetaRieszJointOwnerPayment.remaining_prime_log_lt j hj u
    ((Finset.sdiff_subset : S\I ⊆ S).trans hS) hnD hcoef
  have hP : largestPrime n ∈ n.primeFactors := by
    have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    rw [largestPrime,dif_pos hne]
    exact Finset.max'_mem _ _
  have howner := hp _ hP
  have hnH : n ∈ (S\(I ∪ D))\H := Finset.mem_sdiff.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hnS,fun hi => hnnot (Finset.mem_union_left _ hi)⟩,
      fun hh => hnnot (Finset.mem_union_right _ hh)⟩
  have hsmall := ZetaRieszPositiveFiveBoundary.remaining_prime_log_gt hm hy hnH hs hc hlo hhi hpos howner
  exact hnI (mem_interior_period hm hy hnS hs hc hlo hhi hLlo hLhi hpos howner.le hsmall)

end
end RiemannGaussian.ZetaRieszPositiveFiveCoverage
