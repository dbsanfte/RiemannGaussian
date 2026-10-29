/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCountRecovery

/-! # Report-preserving zero-first recovery
Each count report is acquired ONCE on its actual branch and its entire work is
retained. The generic callback is instantiated by the actual source counter in
the public companion; no count-answer parameter reaches the N-only interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimePaidPrefixController

/-- Computed output and its selected scalar/list-control acquisition work. -/
structure Run (A : Type*) where
  /-- Actual output, not supplied in a correctness premise. -/
  value : A
  /-- All work retained by this interpreter stage. -/
  work : ℕ

/-- Acquire the literal ordered finite index list with actual map/cons work. -/
def finIndices : (n : ℕ) → Run (List (Fin n))
  | 0 => ⟨[],1⟩
  | n+1 =>
    let tail := finIndices n
    ⟨0::tail.value.map Fin.succ,tail.work+5*tail.value.length+5⟩

/-- Acquired indices have exactly the standard original ascending order. -/
theorem finIndices_value (n : ℕ) : (finIndices n).value=List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finIndices,ih,List.finRange_succ]

/-- Every map cell, constructor, and recursion step has a finite polynomial report. -/
theorem finIndices_work (n : ℕ) : (finIndices n).work≤3*(n+1)^2 := by
  induction n with
  | zero => simp [finIndices]
  | succ n ih =>
    have hl : (finIndices n).value.length=n := by rw [finIndices_value,List.length_finRange]
    simp only [finIndices,hl]
    nlinarith

/-- Actual selected bit list, callback count, and retained acquisition work. -/
structure Selection (I : Type*) where
  /-- Returned literal bit labels. -/
  values : List (I × Bool)
  /-- Number of actual conditional counter invocations. -/
  queries : ℕ
  /-- Callback work plus selected branch/list-control work. -/
  work : ℕ

/-- One cached report per zero-child query, followed by the actual selected branch. -/
def select {I : Type*} (count : List (I × Bool) → Run ℕ) :
    List I → List (I × Bool) → Selection I
  | [], _ => ⟨[],0,1⟩
  | i::rest, fixed =>
    let query := count ((i,false)::fixed)
    let b := if 0< query.value then false else true
    let tail := select count rest ((i,b)::fixed)
    ⟨(i,b)::tail.values,tail.queries+1,query.work+tail.work+8⟩

/-- Actual outputs and query counts coincide with the original selector. -/
theorem select_result {I : Type*} (count : List (I × Bool) → Run ℕ)
    (indices : List I) (fixed : List (I × Bool)) :
    (select count indices fixed).values=(SemiprimeCountRecovery.select (fun p => (count p).value) indices fixed).values ∧
      (select count indices fixed).queries=(SemiprimeCountRecovery.select (fun p => (count p).value) indices fixed).queries := by
  induction indices generalizing fixed with
  | nil => exact ⟨rfl,rfl⟩
  | cons i rest ih =>
    have ht := ih ((i,if 0<(count ((i,false)::fixed)).value then false else true)::fixed)
    simp only [select,SemiprimeCountRecovery.select,ht.1,ht.2,and_self]

/-- Exactly one conditional query per requested index. -/
theorem select_queries {I : Type*} (count : List (I × Bool) → Run ℕ)
    (indices : List I) (fixed : List (I × Bool)) :
    (select count indices fixed).queries=indices.length :=
  (select_result count indices fixed).2.trans (SemiprimeCountRecovery.select_queries _ _ _)

/-- Returned label length is exact even for arbitrary supplied callback values. -/
theorem select_length {I : Type*} (count : List (I × Bool) → Run ℕ)
    (indices : List I) (fixed : List (I × Bool)) :
    (select count indices fixed).values.length=indices.length := by
  rw [(select_result count indices fixed).1]
  have h := congrArg List.length (SemiprimeCountRecovery.select_indices (fun p => (count p).value) indices fixed)
  simpa only [List.length_map] using h

/-- Every actual callback work is retained; only reachable prefix lengths need a budget. -/
theorem select_work {I : Type*} (count : List (I × Bool) → Run ℕ)
    (B N : ℕ) (hb : ∀ fixed, fixed.length≤ N → (count fixed).work≤ B)
    (indices : List I) (fixed : List (I × Bool)) (hlen : indices.length+fixed.length≤ N) :
    (select count indices fixed).work≤ indices.length*(B+8)+1 := by
  induction indices generalizing fixed with
  | nil => simp [select]
  | cons i rest ih =>
    have hq := hb ((i,false)::fixed) (by simp only [List.length_cons] at *; omega)
    have ht := ih ((i,if 0<(count ((i,false)::fixed)).value then false else true)::fixed)
      (by simp only [List.length_cons] at *; omega)
    simp only [select,List.length_cons]
    nlinarith

/-- Existence result with work from every executed lower report. -/
structure SearchResult (I : Type*) where
  /-- None precisely when the initial acquired count is zero. -/
  values : Option (List (I × Bool))
  /-- Initial plus conditional counter invocations. -/
  queries : ℕ
  /-- Retained counter reports plus selected control work. -/
  work : ℕ

/-- Acquire the initial report once; the positive branch executes the selector. -/
def search {I : Type*} (count : List (I × Bool) → Run ℕ) (indices : List I) : SearchResult I :=
  let initial := count []
  if 0< initial.value then
    let result := select count indices []
    ⟨some result.values,result.queries+1,initial.work+result.work+4⟩
  else ⟨none,1,initial.work+3⟩

/-- No work accounting changes the original exact zero-first selected witness. -/
theorem search_result {I : Type*} (count : List (I × Bool) → Run ℕ) (indices : List I) :
    (search count indices).values=(SemiprimeCountRecovery.search (fun p => (count p).value) indices).values ∧
      (search count indices).queries=(SemiprimeCountRecovery.search (fun p => (count p).value) indices).queries := by
  unfold search SemiprimeCountRecovery.search
  by_cases h : 0<(count []).value
  · simp only [ite_eq_left h,select_result,and_self]
  · simp only [ite_eq_right h,and_self]

/-- At most one actual initial and one actual conditional query per wire. -/
theorem search_queries {I : Type*} (count : List (I × Bool) → Run ℕ) (indices : List I) :
    (search count indices).queries≤ indices.length+1 :=
  (search_result count indices).2.trans_le (SemiprimeCountRecovery.search_queries_le _ _)

/-- Successful output contains exactly the requested number of literal labels. -/
theorem search_length {I : Type*} (count : List (I × Bool) → Run ℕ) (indices : List I)
    (values : List (I × Bool)) (h : (search count indices).values=some values) :
    values.length=indices.length := by
  by_cases hp : 0<(count []).value
  · have he : some (select count indices []).values=some values := by
      simpa only [search,ite_eq_left hp] using h
    rw [← Option.some.inj he]
    exact select_length count indices []
  · have he : (none : Option (List (I × Bool)))=some values := by
      simpa only [search,ite_eq_right hp] using h
    cases he

/-- Uniform complete aggregate bound, with no unrecorded lower count invocation. -/
theorem search_work {I : Type*} (count : List (I × Bool) → Run ℕ) (B : ℕ)
    (indices : List I) (hb : ∀ fixed, fixed.length≤ indices.length → (count fixed).work≤ B) :
    (search count indices).work≤(indices.length+1)*(B+8)+1 := by
  have hi := hb [] (by simp)
  have hs := select_work count B indices.length hb indices [] (by simp)
  by_cases hp : 0<(count []).value
  · simp only [search,ite_eq_left hp]
    nlinarith
  · simp only [search,ite_eq_right hp]
    nlinarith

end RiemannGaussian.SemiprimePaidPrefixController
