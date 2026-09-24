/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleLedger

/-!
# The reserve inside the original completion correction

Reindex the concrete rectangle into the literal second-prime cofactor
rows. This identifies its sign in both exact ledgers. The rest of the
completion correction remains a signed arithmetic sum, not a paid error.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint

/-- The same rectangle, indexed by the second-prime cofactor order k=j+h. -/
def rectangleRowOrders (N k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun j =>
    21 * N ≤ 40 * j ∧ 40 * j ≤ 23 * N ∧
      N ≤ 100 * (k - j + 1) ∧ 100 * (k - j + 1) ≤ 4 * N)

/-- Exact finite reindexing; no factorial orders or prime incidences are added. -/
theorem sum_rectangleOrders_eq_rows (N : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j, f j h) =
      ∑ k ∈ ownerOrders N, ∑ j ∈ rectangleRowOrders N k, f j (k - j) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun a _ => ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hj, hh⟩ := Finset.mem_sigma.mp ha
    obtain ⟨_, hk, h₁, h₂, h₃, h₄⟩ := Finset.mem_filter.mp hh
    apply Finset.mem_sigma.mpr
    refine ⟨hk, ?_⟩
    simp only [rectangleRowOrders, Finset.mem_filter, Finset.mem_range]
    omega
  · intro a ha b hb he
    have hj : a.1 = b.1 := congrArg (fun c : (k : ℕ) × ℕ => c.2) he
    have hk : a.1 + a.2 = b.1 + b.2 := congrArg Sigma.fst he
    exact Sigma.ext hj (by simp only [heq_eq_eq]; omega)
  · intro b hb
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.mp hb
    have hkM := ownerOrders_le hk
    obtain ⟨hr, h₁, h₂, h₃, h₄⟩ := Finset.mem_filter.mp hj
    have hr' := Finset.mem_range.mp hr
    refine ⟨⟨b.2, b.1 - b.2⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (by change b.2 < N + 2; omega), ?_⟩, ?_⟩
    · simp only [rectangleOrders, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by simpa only [Nat.add_sub_of_le (by omega : b.2 ≤ b.1)] using hk,
        h₁, h₂, h₃, h₄⟩
    · exact Sigma.ext (by change b.2 + (b.1 - b.2) = b.1; omega)
        (by simp only [heq_eq_eq])
  · intro a _
    simp only [Nat.add_sub_cancel_left]

/-- The rectangle's selected piece of one original nonowner cofactor row. -/
def rectangleRow (y : ℝ) (N n q k : ℕ) : ℂ :=
  ∑ j ∈ rectangleRowOrders N k,
    (((k - j + 1 : ℕ) : ℂ) *
      zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n) *
      zetaPrimeLogKernel (N + 1 - k) (3 / 2 + Complex.I * y) q *
      zetaPrimeLogKernel (k - j + 1) (3 / 2 + Complex.I * y) (smallPrime n q))

/-- Reindex the literal unassigned atom into its original nonowner rows. -/
theorem rectangleAtom_eq_rows {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ rectangleIncidences u N n) (y : ℝ) :
    rectangleAtom u y N n q =
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ ownerOrders N,
          ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
            rectangleRow y N n q k := by
  rw [rectangleAtom_eq_factorials hn hc (Finset.mem_filter.mp hq).1,
    sum_rectangleOrders_eq_rows]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold rectangleRow
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  have hkM := ownerOrders_le hk
  have he : N + 1 - j - (k - j) = N + 1 - k := by omega
  simp only [factorialAtom, he]
  ring

/-- Exactly the selected second-incidence rows, in the same indexing as
the nonowner term of ownerCompletionCorrection. -/
def rectangleNonownerRows (u y : ℝ) (N K : ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ ownerOrders N, ∑ q ∈ intermediatePrimes u N,
      ∑ n ∈ (tripleBand u N K).filter (fun n => q ∈ rectangleIncidences u N n),
        ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
          rectangleRow y N n q k

/-- The independently estimated rectangle is the actual selected
nonowner correction, including its original unassigned factor. -/
theorem rectangleResponse_eq_nonowner_rows (u y : ℝ) (N K : ℕ) :
    rectangleResponse u y N K = rectangleNonownerRows u y N K := by
  have heq : rectangleResponse u y N K = ∑ n ∈ tripleBand u N K,
      ∑ q ∈ rectangleIncidences u N n,
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ ownerOrders N,
          ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
            rectangleRow y N n q k := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro q hq
    exact rectangleAtom_eq_rows (Finset.mem_filter.mp hn).2.1
      (Finset.mem_filter.mp hn).2.2 hq y
  rw [heq]
  unfold rectangleNonownerRows
  simp only [Finset.mul_sum]
  have hswap (n : ℕ) : (∑ q ∈ rectangleIncidences u N n, ∑ k ∈ ownerOrders N,
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        (((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * rectangleRow y N n q k)) =
      ∑ k ∈ ownerOrders N, ∑ q ∈ rectangleIncidences u N n,
        (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          (((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * rectangleRow y N n q k) :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have he (n : ℕ) : rectangleIncidences u N n =
      (intermediatePrimes u N).filter (fun q => q ∈ rectangleIncidences u N n) := by
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1, h⟩,
      fun h => h.2⟩
  have hsum (n : ℕ) : (∑ q ∈ rectangleIncidences u N n,
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        (((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * rectangleRow y N n q k)) =
      ∑ q ∈ intermediatePrimes u N, if q ∈ rectangleIncidences u N n then
        (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          (((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * rectangleRow y N n q k)
        else 0 := by conv_lhs => rw [he n, Finset.sum_filter]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

/-- The literal unselected factorial orders in a marked second-prime
row; all other incidences retain the original composite atom. -/
def rectangleRowRest (u y : ℝ) (N n q k : ℕ) : ℂ :=
  if q ∈ rectangleIncidences u N n then
    ∑ j ∈ Finset.range (k + 1) \ rectangleRowOrders N k,
      (((k - j + 1 : ℕ) : ℂ) *
        zetaPrimeLogKernel j (3 / 2 + Complex.I * y) (largestPrime n) *
        zetaPrimeLogKernel (N + 1 - k) (3 / 2 + Complex.I * y) q *
        zetaPrimeLogKernel (k - j + 1) (3 / 2 + Complex.I * y) (smallPrime n q))
  else ZetaRieszJointCofactor.compositeAtom (SquarefreeVaughanLogSource.length u N)
    y k (N + 1 - k) q (n / q)

/-- Exact partition of a cofactor row into the selected rectangle and
its finite order complement, with no infinite cofactor completion. -/
theorem rectangle_row_partition (u y : ℝ) (N q k : ℕ) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 3) :
    ZetaRieszJointCofactor.compositeAtom (SquarefreeVaughanLogSource.length u N)
      y k (N + 1 - k) q (n / q) = rectangleRowRest u y N n q k +
        if q ∈ rectangleIncidences u N n then rectangleRow y N n q k else 0 := by
  by_cases hq : q ∈ rectangleIncidences u N n
  · rw [rectangleRowRest, if_pos hq, if_pos hq,
      second_composite_convolution hn hc (Finset.mem_filter.mp hq).1]
    exact (Finset.sum_sdiff (Finset.filter_subset _ _)).symm
  · simp only [rectangleRowRest, if_neg hq, add_zero]

/-- What the completion correction still contains after harvesting
the rectangle: all completion/off-mask/allocation differences, all other
nonowner incidences, and the unselected orders of the marked incidence. -/
def rectangleCorrectionRest (u y : ℝ) (N K : ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ ownerOrders N, ∑ q ∈ intermediatePrimes u N,
      ((∑' a, ZetaRieszJointCofactor.compositeAtom
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q a) -
        ∑ n ∈ (tripleBand u N K).filter (fun n => q ∈ n.primeFactors),
          ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
            ZetaRieszJointCofactor.compositeAtom
              (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) q (n / q)) +
  (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ ownerOrders N, ∑ q ∈ intermediatePrimes u N,
      ∑ n ∈ ((tripleBand u N K).filter (fun n => q ∈ n.primeFactors)).filter
          (fun n => largestPrime n ≠ q),
        ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
          rectangleRowRest u y N n q k

/-- The reserve is exactly minus the selected contribution to the
original correction. The displayed remainder has not been estimated. -/
theorem correction_eq_rectangle_rest (u y : ℝ) (N K : ℕ) :
    ownerCompletionCorrection u y N K =
      rectangleCorrectionRest u y N K + rectangleResponse u y N K := by
  rw [correction_eq_nonowner_rows, rectangleResponse_eq_nonowner_rows]
  unfold rectangleCorrectionRest rectangleNonownerRows
  rw [add_assoc]
  congr 1
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have he : (((tripleBand u N K).filter (fun n => q ∈ n.primeFactors)).filter
      (fun n => largestPrime n ≠ q)).filter (fun n => q ∈ rectangleIncidences u N n) =
      (tripleBand u N K).filter (fun n => q ∈ rectangleIncidences u N n) := by
    ext n
    constructor
    · intro hn
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).1, (Finset.mem_filter.mp hn).2⟩
    · intro hn
      obtain ⟨hn, hq⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨second_mem_nonowner_row hn (Finset.mem_filter.mp hq).1, hq⟩
  rw [← he]
  conv_rhs => rhs; rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  rw [rectangle_row_partition u y N q k (Finset.mem_filter.mp hn').2.1
    (Finset.mem_filter.mp hn').2.2, mul_add]
  simp only [mul_ite, mul_zero]

/-- Direct comparison of the two actual ledgers. Before adding the
positive correction reserve, this expression still contains two copies
of the selected negative rectangle and the unestimated owned complement. -/
theorem completion_rest_rectangle_ledger (t : ℕ) (ht : 32 ≤ t) (u y : ℝ) :
    wideComplete u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t) -
      rectangleCorrectionRest u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) =
    ownerRectangleComplement u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) -
      2 * rectangleReserve u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) := by
  have ht' := triple_completed_decomposition t ht u y
  rw [correction_eq_rectangle_rest, triple_decomposition,
    ownerCompanion_rectangle_partition] at ht'
  unfold rectangleReserve
  linear_combination -ht'

/-- The reserve has its positive correction sign in the original narrow
carrier, with every remaining signed contribution displayed. -/
theorem narrow_rectangle_completion_ledger (t : ℕ) (ht : 32 ≤ t) (u y : ℝ) :
    ZetaRieszTypeII.narrowResponse u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
      (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) =
    (∑ n ∈ ZetaRieszTypeII.narrowBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) \
        tripleBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t),
      residualCoefficient (intermediatePrimes u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t))
        (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t))
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t) n *
        zetaPrimeLogKernel (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
          (3 / 2 + Complex.I * y) n) +
      wideComplete u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t) -
        rectangleCorrectionRest u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) +
      rectangleReserve u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) +
      unallocatedTriples u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder t)
        (ZetaRieszPrimeCountFrequency.dyadicPrimeCount t) := by
  rw [narrow_completed_decomposition t ht, correction_eq_rectangle_rest, rectangleReserve]
  ring

end
end RiemannGaussian.ZetaRieszSkewAllocation
