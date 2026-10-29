/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridCorrectness

/-! # Exact original-input report joins for the boundary hybrid

The changed recursion retains its own partition and contraction reports. The
unchanged physical factor decoder transfers through exact selected bytes.
Uniform prefix bounds below are internal budget composition, not runtime inputs
or a closed primitive-machine complexity assertion.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HybridPublicExecution
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
attribute [local irreducible] prefixRun search SemiprimeD1WordTapePublicSearch.search
  SemiprimeD1PublicOperandBits.run SemiprimeD1FactorValidationBits.run

/-- Only the unchanged selector metadata agrees; changed query reports stay distinct. -/
theorem select_metadata_eq_tape (N : Nat) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) :
    (select N hN indices fixed).metadataWork =
      (SemiprimeD1WordTapePublicSearch.select N hN indices fixed).metadataWork := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select, SemiprimeD1WordTapePublicSearch.select, prefixRun_words_eq_tape, ih]

/-- Exact original search metadata after the proved same branch decisions. -/
theorem search_metadata_eq_tape (N : Nat) (hN : 0 < N) :
    (search N hN).metadataWork = (SemiprimeD1WordTapePublicSearch.search N hN).metadataWork := by
  simp only [search, SemiprimeD1WordTapePublicSearch.search, prefixRun_words_eq_tape]
  split
  · exact congrArg (fun k => k + 10 * (wireCount N + 1) + 3)
      (select_metadata_eq_tape N hN (List.finRange (wireCount N)) [])
  · rfl

/-- Actual selector query reports follow the proved original chronological prefix list. -/
theorem select_queryWork_eq (N : Nat) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) :
    (select N hN indices fixed).queryWork =
      ((SemiprimeD1WordTapePublicSearch.selectPrefixes N hN indices fixed).map
        (fun f => (prefixRun N hN f).clock)).sum := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select, SemiprimeD1WordTapePublicSearch.selectPrefixes,
      SemiprimeD1WordTapePublicCounter.prefixCount, ←prefixRun_words_eq_tape,
      List.map_cons, List.sum_cons, ih]

/-- Every repeated actual prefix acquisition is retained exactly once. -/
theorem search_queryWork_eq (N : Nat) (hN : 0 < N) :
    (search N hN).queryWork =
      ((SemiprimeD1WordTapePublicSearch.queriedPrefixes N hN).map
        (fun f => (prefixRun N hN f).clock)).sum := by
  simp only [search, SemiprimeD1WordTapePublicSearch.queriedPrefixes,
    SemiprimeD1WordTapePublicCounter.prefixCount, ←prefixRun_words_eq_tape]
  split
  · simp only [List.map_cons, List.sum_cons, select_queryWork_eq]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The binary endpoint keeps precisely that sum of new original-prefix executions. -/
theorem run_queryWork_eq (input : List Bool) (hN : 0 < bitValue input) :
    (run input).queryWork =
      ((SemiprimeD1WordTapePublicSearch.queriedPrefixes (bitValue input) hN).map
        (fun f => (prefixRun (bitValue input) hN f).clock)).sum := by
  have hz := (nonzeroBits_correct input).mpr hN
  dsimp only [run]
  rw [dite_eq_left hz]
  split <;> exact search_queryWork_eq (bitValue input) hN

/-- A bound on all actually reachable prefix lengths composes through selection. -/
theorem select_queryWork (N : Nat) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) (C : Nat)
    (hC : ∀ f : List (Fin (wireCount N) × Bool), f.length ≤ wireCount N →
      (prefixRun N hN f).clock ≤ C)
    (hsize : fixed.length + indices.length ≤ wireCount N) :
    (select N hN indices fixed).queryWork ≤ indices.length * C := by
  induction indices generalizing fixed with
  | nil => simp only [select, List.length_nil, Nat.zero_mul, le_refl]
  | cons i rest ih =>
    let b := if 0 < prefixCount N hN ((i, false) :: fixed) then false else true
    have hc := hC ((i, false) :: fixed) (by simp only [List.length_cons] at *; omega)
    have ht := ih ((i, b) :: fixed) (by simp only [List.length_cons] at *; omega)
    change (prefixRun N hN ((i, false) :: fixed)).clock +
      (select N hN rest ((i, b) :: fixed)).queryWork ≤ (rest.length + 1) * C
    nlinarith

/-- The concrete initial query and all selected prefix queries pay their own costs. -/
theorem search_queryWork (N : Nat) (hN : 0 < N) (C : Nat)
    (hC : ∀ f : List (Fin (wireCount N) × Bool), f.length ≤ wireCount N →
      (prefixRun N hN f).clock ≤ C) :
    (search N hN).queryWork ≤ (wireCount N + 1) * C := by
  have hi := hC [] (by simp)
  have hs := select_queryWork N hN (List.finRange (wireCount N)) [] C hC (by simp)
  simp only [List.length_finRange] at hs
  by_cases h : 0 < bitValue (((prefixRun N hN []).words[0]?).getD [])
  · simp only [search, ite_eq_left h]
    nlinarith
  · simp only [search, ite_eq_right h]
    nlinarith

/-- Physical radix construction, validation and native metadata are unchanged. -/
theorem run_local_eq_tape (input : List Bool) :
    (run input).arithmeticClock + (run input).metadataWork =
      (SemiprimeD1WordTapeBinaryFactorExecution.run input).arithmeticClock +
        (SemiprimeD1WordTapeBinaryFactorExecution.run input).metadataWork := by
  by_cases hz : (nonzeroBits input).nonzero = true
  · have hN := (nonzeroBits_correct input).mp hz
    have hv := congrArg SemiprimeCountRecovery.SearchResult.values
      (search_result_eq_tape (bitValue input) hN)
    have hm := search_metadata_eq_tape (bitValue input) hN
    dsimp only [run, SemiprimeD1WordTapeBinaryFactorExecution.run]
    simp only [dite_eq_left hz]
    rw [hv, hm]
    cases (SemiprimeD1WordTapePublicSearch.search (bitValue input) hN).result.values <;> rfl
  · simp only [run, SemiprimeD1WordTapeBinaryFactorExecution.run, dite_eq_right hz]

/-- Unchanged decoder arithmetic retains the original proved polynomial allowance. -/
theorem run_local_work (input : List Bool) (hc : SemiprimeSourceCompactBits.Compact input)
    (hN : 0 < bitValue input) :
    (run input).arithmeticClock + (run input).metadataWork ≤
      SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  rw [run_local_eq_tape]
  exact SemiprimeD1WordTapePublicReport.run_local_work input hc hN

/-- Whole actual public report from an internally derived bound on its actual prefixes. -/
theorem work_le (input : List Bool) (hc : SemiprimeSourceCompactBits.Compact input)
    (hN : 0 < bitValue input) (C : Nat)
    (hC : ∀ f : List (Fin (wireCount (bitValue input)) × Bool),
      f.length ≤ wireCount (bitValue input) → (prefixRun (bitValue input) hN f).clock ≤ C) :
    work input ≤ (wireCount (bitValue input) + 1) * C +
      SemiprimeD1PublicRecoveryBudget.localBudget (wireCount (bitValue input)) := by
  have hz := (nonzeroBits_correct input).mpr hN
  have hs := search_queryWork (bitValue input) hN C hC
  have hq : (run input).queryWork ≤ (wireCount (bitValue input) + 1) * C := by
    dsimp only [run]
    rw [dite_eq_left hz]
    split <;> exact hs
  have hl := run_local_work input hc hN
  unfold work
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1HybridPublicExecution
