/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidEnumeratedSource
import RiemannGaussian.SemiprimePaidOriginalConstraints

/-! # Enumeration-inclusive acquisition of the original integer constraint family
The original n,F,r,Q,arity and coordinate data supply every finite menu, chosen
word, packing address and integer row. No rank, row, block or label answer occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidEnumeratedConstraints
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeMaterializedSourceUniversal
variable {n F r Q : ℕ} [NeZero r]

/-- Execute the paid finite enumerator followed by the actual original integer-row producer. -/
def acquire (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) :
    Run (SemiprimePaidConstraintAcquisition.Family ((e : Fin F) × Fin (arity e)) r Q) :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let rows := SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en.value eps R
  ⟨rows.value,en.work+rows.work+1⟩

/-- The exact original stored integer family, including its original row ordering. -/
theorem acquire_value (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) :
    (acquire (r:=r) (Q:=Q) arity coordinate eps R).value=
      (SemiprimePaidOriginalConstraints.acquire
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R).value := by
  simp only [acquire,SemiprimePaidFiniteEnumerations.indexed_value]

/-- Every acquired head-column entry is the original padded integer matrix entry. -/
theorem read_acquire (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) (t : Fin Q) (g : Fin r)
    (j : Fin (SemiprimeSourceConstraintAcquisition.rowIndices
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps).values.length)
    (v : Fin n) (hv : SemiprimeSourceConstraintAcquisition.head
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps t v=g) :
    (SemiprimePaidOriginalConstraints.read (acquire (r:=r) (Q:=Q) arity coordinate eps R).value
      t.val g.val j.val v.val).value=
      SemiprimeSourceConstraintAcquisition.matrix
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R t g j v := by
  rw [acquire_value]
  exact SemiprimePaidOriginalConstraints.read_acquire (n:=n) (r:=r) (Q:=Q)
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2)
    (fun i : (e : Fin F) × Fin (arity e) => i.1)
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R t g j v hv

/-- Enlarging the explicitly acquired word menu only enlarges the integer-row envelope. -/
theorem polynomial_mono_words (M n a A D T N Q R start r : ℕ) (ha : a≤A) :
    SemiprimePaidOriginalConstraints.polynomial M n a D T N Q R start r ≤
      SemiprimePaidOriginalConstraints.polynomial M n A D T N Q R start r := by
  unfold SemiprimePaidOriginalConstraints.polynomial
    SemiprimeMaterializedSourceWords.producerBudget
    SemiprimeMaterializedScoreSearch.evaluatorBudget
  gcongr

/-- Entire source-enumeration plus original integer-family polynomial envelope. -/
def budget (n F r Q R M : ℕ) : ℕ :=
  SemiprimePaidFiniteEnumerations.budget n F r Q M+
    SemiprimePaidOriginalConstraints.polynomial M n (r^Q) (r^(2*Q)) (M^2+Q*n^2) (n+F) Q R
      (Subexp.TailInterval.intervalStart r Q R) r+1

/-- Complete finite-menu and original integer-row acquisition, without unknown block or label costs. -/
theorem acquire_work_native (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (hr : 2≤r) (eps : ℚ) (R : ℕ) :
    (acquire (r:=r) (Q:=Q) arity coordinate eps R).work ≤ budget n F r Q R (∑ e,arity e) := by
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  have he := SemiprimePaidFiniteEnumerations.indexed_work n F r Q arity
  have hs := SemiprimePaidOriginalConstraints.acquire_work_native owner Sigma.fst en.value hr eps R
  have ht : en.value.wordTail.length≤r^Q := by
    rw [SemiprimePaidFiniteEnumerations.indexed_value]
    exact (List.length_filter_le _ _).trans_eq (SemiprimeFiniteEnumerations.words_length r Q)
  rw [SemiprimePaidFiniteEnumerations.indexed_incidence_length,
    SemiprimePaidFiniteEnumerations.indexed_universal_length,
    SemiprimePaidFiniteEnumerations.indexed_score_length,
    SemiprimePaidFiniteEnumerations.indexed_indices_length] at hs
  have hm := polynomial_mono_words (∑ e,arity e) n en.value.wordTail.length (r^Q)
    (r^(2*Q)) ((∑ e,arity e)^2+Q*n^2) (n+F) Q R (Subexp.TailInterval.intervalStart r Q R) r ht
  unfold acquire budget
  dsimp only
  change en.work+_+1≤_
  exact Nat.add_le_add_right (Nat.add_le_add he (hs.trans hm)) 1

end RiemannGaussian.SemiprimePaidEnumeratedConstraints
