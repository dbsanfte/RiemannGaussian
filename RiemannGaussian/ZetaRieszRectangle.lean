/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSkewFactorial

/-!
# The concrete allocation-safe second-incidence rectangle

The selection is finite and retains the original integer masks, unique
second incidence, physical prime set, old allocation and complex phase.
This file supplies exact bookkeeping, not a signed lower bound.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint

/-- The requested rectangle, including the actual owner cofactor order. -/
def rectangleOrders (N j : ℕ) : Finset ℕ :=
  (Finset.range (N + 1 - j + 1)).filter (fun h =>
    j + h ∈ ownerOrders N ∧ 21 * N ≤ 40 * j ∧ 40 * j ≤ 23 * N ∧
      N ≤ 100 * (h + 1) ∧ 100 * (h + 1) ≤ 4 * N)

/-- Every selected atom has the exact correlated total order. -/
theorem rectangle_orders_sum {N j h : ℕ} (hj : j < N + 2)
    (hh : h ∈ rectangleOrders N j) : j + (N + 1 - j - h) + h + 1 = N + 2 := by
  have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
  omega

/-- The rectangle fits the existing cofactor completion band without
changing its endpoints. -/
theorem rectangle_mem_owner {N j h : ℕ}
    (hjlo : 21 * N ≤ 40 * j) (hjhi : 40 * j ≤ 23 * N)
    (hh : 100 * (h + 1) ≤ 4 * N) : j + h ∈ ownerOrders N := by
  simp only [ownerOrders, Finset.mem_filter, Finset.mem_range]
  omega

/-- The exact multinomial selection, before applying any phase or sign. -/
def rectangleMass (N : ℕ) (x c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 2), mass (N + 1) j (1 - x) *
    ∑ h ∈ rectangleOrders N j, mass (N + 1 - j) h c

/-- Its largest-prime marginal keeps the upper order cut. -/
def rectangleMarginal (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (N + 2)).filter (fun j => 40 * j ≤ 23 * N),
    mass (N + 1) j (1 - x)

theorem rectangleMass_bounds (N : ℕ) {x c : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ rectangleMass N x c ∧ rectangleMass N x c ≤ rectangleMarginal N x := by
  have hm := fun j => mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x)
    (by linarith : 1 - x ≤ 1)
  have hi (j : ℕ) : 0 ≤ ∑ h ∈ rectangleOrders N j, mass (N + 1 - j) h c :=
    Finset.sum_nonneg (fun h _ => mass_nonneg _ _ hc hc1)
  have hb (j : ℕ) : (∑ h ∈ rectangleOrders N j, mass (N + 1 - j) h c) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h _ _ => mass_nonneg _ _ hc hc1)).trans_eq (mass_total _ _)
  refine ⟨Finset.sum_nonneg (fun j _ => mul_nonneg (hm j) (hi j)), ?_⟩
  unfold rectangleMass rectangleMarginal
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : 40 * j ≤ 23 * N
  · rw [if_pos hj]
    exact mul_le_of_le_one_right (hm j) (hb j)
  · rw [if_neg hj]
    have he : rectangleOrders N j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hj (Finset.mem_filter.mp hh).2.2.2.1
    simp [he]

theorem rectangleMarginal_bounds (N : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ rectangleMarginal N x ∧ rectangleMarginal N x ≤ 1 := by
  have hm := fun j => mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x)
    (by linarith : 1 - x ≤ 1)
  exact ⟨Finset.sum_nonneg (fun j _ => hm j),
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => hm j)).trans_eq (mass_total _ _)⟩

/-- Weight-one rectangle at the literal integer and second incidence. -/
def rawRectangleAtom (u y : ℝ) (N n q : ℕ) : ℂ :=
  (rectangleMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
    (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ)) : ℂ) *
      (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)

/-- The exact original unassigned fraction; no new allocation is substituted. -/
def rectangleAtom (u y : ℝ) (N n q : ℕ) : ℂ :=
  ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
    rawRectangleAtom u y N n q

/-- Weight-one version of the exact three-leg expansion. -/
theorem rawRectangleAtom_eq_factorials {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) (y : ℝ) :
    rawRectangleAtom u y N n q =
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
          factorialAtom y N n q j h := by
  simp only [rawRectangleAtom, rectangleMass, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [Complex.ofReal_mul] using second_mass_kernel (j := j) (h := h) hn hc hq
    (by have := Finset.mem_range.mp hj; omega)
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega) y

/-- Exact three-leg identity with the distinguished small-prime derivative. -/
theorem rectangleAtom_eq_factorials {u : ℝ} {N n q : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 3) (hq : q ∈ secondIncidences u N n) (y : ℝ) :
    rectangleAtom u y N n q =
      ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) *
        (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
          ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
            factorialAtom y N n q j h := by
  simp only [rectangleAtom, rawRectangleAtom, rectangleMass, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  have hm := second_mass_kernel (j := j) (h := h) hn hc hq
    (by have := Finset.mem_range.mp hj; omega)
    (by have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega) y
  simp only [Complex.ofReal_mul] at hm
  linear_combination ((1 - boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ) * hm

/-- The requested finite support, including the small prime's physical
and quadratic-prefix masks. The other two prime masks remain inherited. -/
def rectangleIncidences (u : ℝ) (N n : ℕ) : Finset ℕ :=
  (secondIncidences u N n).filter (fun q => smallPrime n q ∈ intermediatePrimes u N)

/-- The literal unassigned rectangle, with no completion or incidence average. -/
def rectangleResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ rectangleIncidences u N n, rectangleAtom u y N n q

/-- The same finite rectangle before the old allocation split. -/
def rawRectangleResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ rectangleIncidences u N n, rawRectangleAtom u y N n q

/-- Precisely the old allocated mass on the same literal support. -/
def allocatedRectangleResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K, ∑ q ∈ rectangleIncidences u N n,
    (boundedShare (intermediatePrimes u N) N n : ℂ) * rawRectangleAtom u y N n q

theorem rawRectangleResponse_eq (u y : ℝ) (N K : ℕ) :
    rawRectangleResponse u y N K = allocatedRectangleResponse u y N K +
      rectangleResponse u y N K := by
  unfold rawRectangleResponse allocatedRectangleResponse rectangleResponse
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  unfold rectangleAtom
  push_cast
  ring

end
end RiemannGaussian.ZetaRieszSkewAllocation
