/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFactorDecoder
import RiemannGaussian.SemiprimeCachedSourcePublicExecution

/-!
# Actual public counter reports survive prefixRun recovery and decoding

Every query executes CachedSourceCounter ONCE and retains its full source/native
report. No count callback is a public runtime input. The budget theorem takes a
bound on this ACTUAL counter report; raw/setup acquisition and physical bit
refinements retain their distinct obligations until their reports are joined.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidPublicController
open scoped BigOperators
open SemiprimePaidPrefixController SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeLocalArrayFrontend

/-- Actual public restricted scalar counter, never a supplied count answer. -/
def counter (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : SemiprimeAcquiredHermite.ScalarRun :=
  SemiprimeCachedSourceCounter.count (r := r) (Q := Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)

/-- One cached scalar report, an actual rational floor, and retained prefixRun metadata work. -/
def prefixRun (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : Run ℕ :=
  let result := counter N hN r Q eps R J fixed
  ⟨Nat.floor result.value,result.work+fixed.length+3⟩

/-- The exact old public count, now with its actual acquisition work retained. -/
theorem prefix_value (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN r Q eps R J fixed).value=
      SemiprimeCachedSourcePublicExecution.prefixCount N hN r Q eps R J fixed := rfl

/-- No source/native work is discarded by floor or prefixRun recovery. -/
theorem prefix_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN r Q eps R J fixed).work=
      (counter N hN r Q eps R J fixed).work+fixed.length+3 := rfl

/-- Actual paid original local checker plus a uniform all-reachable-prefixRun gate budget. -/
def entryBudget (N : ℕ) : ℕ :=
  1048576*(64*bitLength N+2)^10+wireCount N*(3*scopeBound (bitLength N)+2)+1

/-- The terminal callback budget is derived, not supplied as a unit-cost table. -/
theorem entry_work_le (N : ℕ) (hN : 0< N) (fixed : List (Fin (wireCount N) × Bool))
    (hf : fixed.length≤ wireCount N) (e : Fin (factorCount N))
    (input : Fin (indexedArity N e) → Bool) :
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed e input).arithmetic≤ entryBudget N ∧
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed e input).reads≤ entryBudget N := by
  have hw := SemiprimeAcquiredPrefixSearch.entry_work (indexedArity N) (indexedCoordinate N hN)
    (indexedEntry N hN) fixed e input
  have hc := indexedEntry_clock N hN e input
  have he := indexedArity_le N e
  have hm := Nat.mul_le_mul hf (show 3*indexedArity N e+2≤3*scopeBound (bitLength N)+2 by omega)
  rw [hw.1,hw.2]
  constructor <;> unfold entryBudget <;> omega

/-- Report-bearing search invokes the actual acquired counter at every query. -/
def search (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    SearchResult (Fin (wireCount N)) :=
  let indices := finIndices (wireCount N)
  let result := SemiprimePaidPrefixController.search (prefixRun N hN r Q eps R J) indices.value
  ⟨result.values,result.queries,result.work+indices.work+1⟩

/-- Exact selected list and query count are preserved without numeric promises. -/
theorem search_result (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (search N hN r Q eps R J).values=(SemiprimeCachedSourcePublicExecution.search N hN r Q eps R J).values ∧
      (search N hN r Q eps R J).queries=(SemiprimeCachedSourcePublicExecution.search N hN r Q eps R J).queries := by
  simpa only [search,finIndices_value,prefix_value,SemiprimeCachedSourcePublicExecution.search] using
    SemiprimePaidPrefixController.search_result (prefixRun N hN r Q eps R J) (List.finRange (wireCount N))

/-- Complete aggregate count-work bound at every reachable prefixRun length. -/
theorem search_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J B : ℕ)
    (hb : ∀ fixed, fixed.length≤ wireCount N → (counter N hN r Q eps R J fixed).work≤ B) :
    (search N hN r Q eps R J).work≤(wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1 := by
  have h := SemiprimePaidPrefixController.search_work (prefixRun N hN r Q eps R J)
    (B+wireCount N+3) (List.finRange (wireCount N)) (by
      intro fixed hf
      simp only [List.length_finRange] at hf
      have hc := hb fixed hf
      rw [prefix_work]
      omega)
  simp only [List.length_finRange] at h
  have he : B+wireCount N+3+8=B+wireCount N+11 := by omega
  rw [he] at h
  have ha := finIndices_work (wireCount N)
  simp only [search,finIndices_value]
  omega

/-- Actual factor output with both all counter work and the physical decoder work. -/
structure FactorRun where
  /-- Actual decoded integer, or no original accepted factor assignment. -/
  value : Option ℕ
  /-- Number of actual acquired counter calls. -/
  queries : ℕ
  /-- Complete retained lower reports and selected controller work. -/
  work : ℕ

/-- Search once, then decode once on its actual positive branch. -/
def factor (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) : FactorRun :=
  let selected := search N hN r Q eps R J
  match selected.values with
  | none => ⟨none,selected.queries,selected.work+2⟩
  | some values =>
    let decoded := SemiprimePaidFactorDecoder.decode N values 0
    ⟨some decoded.value,selected.queries,selected.work+decoded.work+2⟩

/-- Every public output agrees exactly with the actual prior source-counter factorer. -/
theorem factor_value (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (factor N hN r Q eps R J).value=SemiprimeCachedSourcePublicExecution.factor N hN r Q eps R J := by
  have hs := (search_result N hN r Q eps R J).1
  unfold SemiprimeCachedSourcePublicExecution.factor
  rw [← hs]
  unfold factor
  cases he : (search N hN r Q eps R J).values <;>
    simp only [he,SemiprimePaidFactorDecoder.decode_value,Option.map_none,Option.map_some]

/-- At most one initial plus one acquired counter call per actual public wire. -/
theorem factor_queries (N : ℕ) (hN : 0<N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (factor N hN r Q eps R J).queries≤wireCount N+1 := by
  have hs := SemiprimePaidPrefixController.search_queries (prefixRun N hN r Q eps R J)
    (List.finRange (wireCount N))
  simp only [List.length_finRange] at hs
  unfold factor
  cases he : (search N hN r Q eps R J).values <;> simp only [he] <;> simpa only [search,finIndices_value] using hs

/-- Complete uniform factor-controller envelope, with explicit physical decoder dimensions. -/
theorem factor_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J B : ℕ)
    (hb : ∀ fixed, fixed.length≤ wireCount N → (counter N hN r Q eps R J fixed).work≤ B) :
    (factor N hN r Q eps R J).work≤
      (wireCount N+1)*(B+wireCount N+3*(wireCount N+1)^2+SemiprimePaidFactorDecoder.budget N (wireCount N)+16) := by
  have hs := search_work N hN r Q eps R J B hb
  have hlarge : (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+
      SemiprimePaidFactorDecoder.budget N (wireCount N)+2≤
        (wireCount N+1)*(B+wireCount N+3*(wireCount N+1)^2+SemiprimePaidFactorDecoder.budget N (wireCount N)+16) := by
    nlinarith [Nat.zero_le (wireCount N*SemiprimePaidFactorDecoder.budget N (wireCount N))]
  unfold factor
  cases he : (search N hN r Q eps R J).values with
  | none =>
    simp only [he]
    calc
      _ ≤ (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+2 := Nat.add_le_add_right hs 2
      _ ≤ (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+SemiprimePaidFactorDecoder.budget N (wireCount N)+2 := by omega
      _ ≤ _ := hlarge
  | some values =>
    have hl := SemiprimePaidPrefixController.search_length (prefixRun N hN r Q eps R J)
      (List.finRange (wireCount N)) values (by simpa only [search,finIndices_value] using he)
    simp only [List.length_finRange] at hl
    have hd := SemiprimePaidFactorDecoder.decode_work N values 0
    rw [hl] at hd
    simp only [he]
    exact (Nat.add_le_add_right (Nat.add_le_add hs hd) 2).trans hlarge

end RiemannGaussian.SemiprimePaidPublicController
