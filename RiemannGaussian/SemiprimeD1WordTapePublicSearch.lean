/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapePublicCounter
import RiemannGaussian.SemiprimeD1PhysicalPublicSearch

/-! # Actual public search retains every acquired prefix report
The closed selector below calls the original-input physical prefix counter on
the same zero-first branches as the public search. Its query-work field adds
every actual root acquisition and recursive report. Metadata remains an explicit
separate report; no whole primitive search/decoder clock is asserted here.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapePublicSearch
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic
open SemiprimeD1WordTapePublicCounter
attribute [local irreducible] prefixRun

/-- Literal selected data, call count and both retained report contributions. -/
structure SelectionRun (I : Type) where
  /-- Selected original wire labels and exact number of executed queries. -/
  selection : SemiprimeCountRecovery.Selection I
  /-- Sum of the actual prefix counters' own complete retained reports. -/
  queryWork : ℕ
  /-- Finite selection/list/control report, separate from primitive lowering. -/
  metadataWork : ℕ

/-- Closed actual zero-first selector. No count callback is an input. -/
def select (N : ℕ) (hN : 0 < N) :
    List (Fin (wireCount N)) → List (Fin (wireCount N) × Bool) → SelectionRun (Fin (wireCount N))
  | [],_ => ⟨⟨[],0⟩,0,1⟩
  | i::rest,fixed =>
    let current := prefixRun N hN ((i,false)::fixed)
    let n := bitValue ((current.words[0]?).getD [])
    let b := if 0 < n then false else true
    let tail := select N hN rest ((i,b)::fixed)
    ⟨⟨(i,b)::tail.selection.values,tail.selection.queries+1⟩,
      current.clock+tail.queryWork,tail.metadataWork+10*(wireCount N+fixed.length+rest.length+1)+3⟩

/-- Actual selected data and query count coincide with the already proved public
selector, while the new report records every real prefix execution. -/
theorem select_spec (N : ℕ) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) :
    (select N hN indices fixed).selection =
      SemiprimeCountRecovery.select (SemiprimeD1WordTapePublicCounter.prefixCount N hN) indices fixed := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select,SemiprimeCountRecovery.select,SemiprimeD1WordTapePublicCounter.prefixCount,ih]
    rfl

/-- Every actual selected prefix has length at most the original wire count.
Thus a uniform bound for original prefix runs suffices; no arbitrary global
predicate counter or supplied solved branch is introduced. -/
theorem select_queryWork (N : ℕ) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) (C : ℕ)
    (hC : ∀ fixedQuery : List (Fin (wireCount N) × Bool), fixedQuery.length ≤ wireCount N →
      (prefixRun N hN fixedQuery).clock ≤ C)
    (hsize : fixed.length+indices.length ≤ wireCount N) :
    (select N hN indices fixed).queryWork ≤ indices.length*C := by
  induction indices generalizing fixed with
  | nil => simp only [select,List.length_nil,Nat.zero_mul,le_refl]
  | cons i rest ih =>
    let b := if 0 < SemiprimeD1WordTapePublicCounter.prefixCount N hN ((i,false)::fixed) then false else true
    have hc := hC ((i,false)::fixed) (by simp only [List.length_cons] at *;omega)
    have ht := ih ((i,b)::fixed) (by simp only [List.length_cons] at *;omega)
    change (prefixRun N hN ((i,false)::fixed)).clock+
      (select N hN rest ((i,b)::fixed)).queryWork ≤ (rest.length+1)*C
    nlinarith

/-- The literal selector metadata report has an original wire-count polynomial,
with each growing prefix and shrinking remaining list charged. -/
theorem select_metadataWork (N : ℕ) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool))
    (hsize : fixed.length+indices.length ≤ wireCount N) :
    (select N hN indices fixed).metadataWork ≤ (indices.length+1)*40*(wireCount N+1) := by
  induction indices generalizing fixed with
  | nil => simp only [select,List.length_nil];omega
  | cons i rest ih =>
    let b := if 0 < SemiprimeD1WordTapePublicCounter.prefixCount N hN ((i,false)::fixed) then false else true
    have ht := ih ((i,b)::fixed) (by simp only [List.length_cons] at *;omega)
    change (select N hN rest ((i,b)::fixed)).metadataWork+
      10*(wireCount N+fixed.length+rest.length+1)+3 ≤ (rest.length+1+1)*40*(wireCount N+1)
    simp only [List.length_cons] at hsize
    nlinarith

/-- Initial existence result, selected original wires, and all retained reports. -/
structure SearchRun (I : Type) where
  /-- Actual public search data and executed count-query counter. -/
  result : SemiprimeCountRecovery.SearchResult I
  /-- Every executed prefix's original acquisition and recursion work. -/
  queryWork : ℕ
  /-- Original search/list/control report, with host lowering still separate. -/
  metadataWork : ℕ

/-- Concrete original-N search executes its own prefix runs on every branch. -/
def search (N : ℕ) (hN : 0 < N) : SearchRun (Fin (wireCount N)) :=
  let initial := prefixRun N hN []
  if 0 < bitValue ((initial.words[0]?).getD []) then
    let chosen := select N hN (List.finRange (wireCount N)) []
    ⟨⟨some chosen.selection.values,chosen.selection.queries+1⟩,
      initial.clock+chosen.queryWork,chosen.metadataWork+10*(wireCount N+1)+3⟩
  else ⟨⟨none,1⟩,initial.clock,10*(wireCount N+1)+3⟩

/-- The entire actual new search result is the proved public search result. -/
theorem search_spec (N : ℕ) (hN : 0 < N) :
    (search N hN).result = SemiprimeD1WordTapePublicCounter.search N hN := by
  by_cases h : 0 < SemiprimeD1WordTapePublicCounter.prefixCount N hN []
  · have hb : 0 < bitValue (((prefixRun N hN []).words[0]?).getD []) := h
    simp only [search,SemiprimeD1WordTapePublicCounter.search,SemiprimeCountRecovery.search,
      ite_eq_left h,ite_eq_left hb,select_spec]
  · have hb : ¬0 < bitValue (((prefixRun N hN []).words[0]?).getD []) := h
    simp only [search,SemiprimeD1WordTapePublicCounter.search,SemiprimeCountRecovery.search,
      ite_eq_right h,ite_eq_right hb]

/-- Exact original query-count bound applies to the report-producing search. -/
theorem search_queries (N : ℕ) (hN : 0 < N) :
    (search N hN).result.queries ≤ wireCount N+1 := by
  rw [search_spec]
  exact SemiprimeD1WordTapePublicCounter.search_queries N hN

/-- Aggregation pays for one actual original-input run per executed prefix.
This is an internal composition lemma; the final rate must discharge hC from
the actual root/recursive report bounds, not assume an acquired count budget. -/
theorem search_queryWork (N : ℕ) (hN : 0 < N) (C : ℕ)
    (hC : ∀ fixedQuery : List (Fin (wireCount N) × Bool), fixedQuery.length ≤ wireCount N →
      (prefixRun N hN fixedQuery).clock ≤ C) :
    (search N hN).queryWork ≤ (wireCount N+1)*C := by
  have hi := hC [] (by simp)
  have hs := select_queryWork N hN (List.finRange (wireCount N)) [] C hC (by simp)
  simp only [List.length_finRange] at hs
  dsimp only [search]
  split
  · dsimp only
    nlinarith
  · dsimp only
    nlinarith

/-- Explicit original-size search metadata, including initial existence test. -/
theorem search_metadataWork (N : ℕ) (hN : 0 < N) :
    (search N hN).metadataWork ≤ (wireCount N+2)*60*(wireCount N+1) := by
  have hs := select_metadataWork N hN (List.finRange (wireCount N)) [] (by simp)
  simp only [List.length_finRange] at hs
  dsimp only [search]
  split <;> dsimp only <;> nlinarith

/-- Actual new search data match the former physical search, not its query work. -/
theorem search_result_eq_physical (N : ℕ) (hN : 0<N) :
    (search N hN).result=(SemiprimeD1PhysicalPublicSearch.search N hN).result :=
  (search_spec N hN).trans ((SemiprimeD1WordTapePublicCounter.search_eq_physical N hN).trans
    (SemiprimeD1PhysicalPublicSearch.search_spec N hN).symm)

/-- Only native list/control metadata agrees after proved actual branch equality. -/
theorem select_metadata_eq_physical (N : ℕ) (hN : 0<N)
    (indices : List (Fin (wireCount N))) (fixed : List (Fin (wireCount N)×Bool)) :
    (select N hN indices fixed).metadataWork=
      (SemiprimeD1PhysicalPublicSearch.select N hN indices fixed).metadataWork := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select,SemiprimeD1PhysicalPublicSearch.select,
      SemiprimeD1WordTapePublicCounter.prefixRun_words_eq_physical,ih]

/-- Search metadata equality does not identify the changed prefix reports. -/
theorem search_metadata_eq_physical (N : ℕ) (hN : 0<N) :
    (search N hN).metadataWork=(SemiprimeD1PhysicalPublicSearch.search N hN).metadataWork := by
  simp only [search,SemiprimeD1PhysicalPublicSearch.search,
    SemiprimeD1WordTapePublicCounter.prefixRun_words_eq_physical]
  split
  · exact congrArg (fun k => k+10*(wireCount N+1)+3)
      (select_metadata_eq_physical N hN (List.finRange (wireCount N)) [])
  · rfl

/-- Proof-side chronological query list; it is not allocated by executed select. -/
def selectPrefixes (N : ℕ) (hN : 0<N) : List (Fin (wireCount N)) →
    List (Fin (wireCount N)×Bool) → List (List (Fin (wireCount N)×Bool))
  | [],_ => []
  | i::rest,fixed =>
    let b:=if 0<SemiprimeD1WordTapePublicCounter.prefixCount N hN ((i,false)::fixed) then false else true
    ((i,false)::fixed)::selectPrefixes N hN rest ((i,b)::fixed)

/-- Exact sum of reports of all actual selector queries, with multiplicity. -/
theorem select_queryWork_eq (N : ℕ) (hN : 0<N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N)×Bool)) :
    (select N hN indices fixed).queryWork=
      ((selectPrefixes N hN indices fixed).map (fun f => (prefixRun N hN f).clock)).sum := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select,selectPrefixes,List.map_cons,List.sum_cons,
      SemiprimeD1WordTapePublicCounter.prefixCount,ih]
    rfl

/-- Proof-side complete executed-prefix trace, including initial existence query. -/
def queriedPrefixes (N : ℕ) (hN : 0<N) : List (List (Fin (wireCount N)×Bool)) :=
  []::(if 0<SemiprimeD1WordTapePublicCounter.prefixCount N hN [] then
    selectPrefixes N hN (List.finRange (wireCount N)) [] else [])

/-- Every retained query report is exactly an actual closed original-prefix run. -/
theorem search_queryWork_eq (N : ℕ) (hN : 0<N) :
    (search N hN).queryWork=
      ((queriedPrefixes N hN).map (fun f => (prefixRun N hN f).clock)).sum := by
  unfold search queriedPrefixes
  dsimp only
  split_ifs <;> simp_all [SemiprimeD1WordTapePublicCounter.prefixCount,select_queryWork_eq]

end RiemannGaussian.SemiprimeD1WordTapePublicSearch
