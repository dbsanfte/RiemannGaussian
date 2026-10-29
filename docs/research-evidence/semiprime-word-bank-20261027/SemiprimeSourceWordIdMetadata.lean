/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerations
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Original indexed source metadata without native word-menu construction
Only original incidences, score terms and variable/factor indices are produced.
The physical word-bank caller supplies its separately acquired candidate rows
and IDs. No Word-valued field or decoder is constructed by this metadata path.
Finite arity/index/descriptor operations retain native scalar ledgers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeSourceWordIdMetadata
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open SemiprimePaidFiniteEnumerationLists SemiprimeReportPolynomialGrowth

/-- Original finite source records, with no candidate word-function payload. -/
structure Metadata (n F Q : ℕ) (arity : Fin F → ℕ) where
  /-- The actual original dependent incidence list. -/
  incidences : List ((e : Fin F) × Fin (arity e))
  /-- Actual original incidence/head score terms. -/
  terms : List (Packing.ScoreTerm ((e : Fin F) × Fin (arity e)) (Fin n) Q)
  /-- The original left-variable/right-factor ID order. -/
  indices : List (Fin n ⊕ Fin F)
  /-- Native finite construction and list-cell work. -/
  clock : ℕ

/-- Construct only the original finite metadata actually consumed by source search. -/
def acquire (n F Q : ℕ) (arity : Fin F → ℕ) : Metadata n F Q arity :=
  let vs := fin n
  let fs := fin F
  let is := SemiprimePaidFiniteEnumerations.incidences F arity
  let qs := fin Q
  let ts := SemiprimePaidFiniteEnumerations.scores is.value vs.value qs.value
  let ids := SemiprimePaidFiniteEnumerationLists.sum vs.value fs.value
  ⟨is.value,ts.value,ids.value,vs.work+fs.work+is.work+qs.work+ts.work+ids.work+6⟩

/-- All actual metadata fields equal the original fully indexed constructor. -/
theorem indexed_fields (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    (acquire n F Q arity).incidences=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.incidences.values ∧
      (acquire n F Q arity).terms=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.terms.values ∧
      (acquire n F Q arity).indices=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.indices.values :=
  ⟨rfl,rfl,rfl⟩

/-- Original metadata indices are complete and duplicate-free, from actual data. -/
theorem indices_certificate (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).indices.Nodup ∧ ∀ z,z∈(acquire n F Q arity).indices := by
  rw [(indexed_fields n F 1 Q arity).2.2]
  refine ⟨?_,(SemiprimePaidFiniteEnumerations.indexed n F 1 Q arity).value.indices.complete⟩
  exact (SemiprimePaidFiniteEnumerations.indexed n F 1 Q arity).value.indices.nodup

/-- Actual original metadata sizes; no supplied network/menu-size answer. -/
theorem sizes (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).incidences.length=(∑ e,arity e) ∧
      (acquire n F Q arity).terms.length=(∑ e,arity e)^2+Q*n^2 ∧
      (acquire n F Q arity).indices.length=n+F := by
  have h := indexed_fields n F 1 Q arity
  rw [h.1,h.2.1,h.2.2]
  exact ⟨SemiprimePaidFiniteEnumerations.indexed_incidence_length n F 1 Q arity,
    SemiprimePaidFiniteEnumerations.indexed_score_length n F 1 Q arity,
    SemiprimePaidFiniteEnumerations.indexed_indices_length n F 1 Q arity⟩

/-- Closed native metadata envelope in original factor/variable/coordinate/incidence counts. -/
def budget (n F Q M : ℕ) : ℕ :=
  3*(n+1)^2+3*(F+1)^2+SemiprimePaidFiniteEnumerations.incidenceBudget F M+3*(Q+1)^2+
    SemiprimePaidFiniteEnumerations.scoreBudget M n Q+4*(n+F)+10

/-- Every actual constructor and map/product/list traversal remains in the report. -/
theorem acquire_clock (n F Q : ℕ) (arity : Fin F → ℕ) :
    (acquire n F Q arity).clock ≤ budget n F Q (∑ e,arity e) := by
  have hv := fin_work n
  have hf := fin_work F
  have hi := SemiprimePaidFiniteEnumerations.incidences_work F arity
  have hq := fin_work Q
  have ht := SemiprimePaidFiniteEnumerations.scores_work
    (SemiprimePaidFiniteEnumerations.incidences F arity).value (fin n).value (fin Q).value
  rw [SemiprimePaidFiniteEnumerations.incidences_length,fin_value,fin_value,
    List.length_finRange,List.length_finRange] at ht
  have hid := sum_work (fin n).value (fin F).value
  rw [fin_value,fin_value,List.length_finRange,List.length_finRange] at hid
  unfold acquire budget
  dsimp only
  simp only [fin_value]
  omega

/-- Input-independent monomial closure for original metadata construction. -/
theorem budget_monomial : ∃ C k : ℕ,∀ n F Q M S,
    n ≤ S → F ≤ S → Q ≤ S → M ≤ S → budget n F Q M ≤ C*(S+1)^k := by
  have h : Bound (fun S => budget S S S S) := by
    simp only [budget,SemiprimePaidFiniteEnumerations.incidenceBudget,SemiprimePaidFiniteEnumerations.scoreBudget]
    boundArithmetic
  obtain ⟨C,k,h⟩ := h
  refine ⟨C,k,?_⟩
  intro n F Q M S hn hF hQ hM
  apply le_trans _ (h S)
  simp only [budget,SemiprimePaidFiniteEnumerations.incidenceBudget,SemiprimePaidFiniteEnumerations.scoreBudget]
  gcongr

end RiemannGaussian.SemiprimeSourceWordIdMetadata
