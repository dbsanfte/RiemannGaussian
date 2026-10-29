/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridRecursiveCounter
import RiemannGaussian.SemiprimeD1WordTapePublicReport

/-! # Original-binary factor execution with the boundary contraction leaf

This is the concrete replacement path from original binary input, through every
acquired prefix and recursive mode, to physical factor bytes. Its own query
reports include partition acquisition and record contraction. Correctness and
resource theorems for the changed path are attached separately.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HybridPublicExecution
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
open SemiprimeD1WordTapePublicSearch (SelectionRun SearchRun)
open SemiprimeD1WordTapeBinaryFactorExecution (Run)
attribute [local irreducible] SemiprimeD1PublicOperandBits.run
  SemiprimeD1FactorValidationBits.run SemiprimeD1RootTapeNetwork.acquirePositive
  SemiprimeD1HybridRecursiveCounter.run

/-- Each prefix acquires its original root and executes the closed hybrid recursion. -/
def prefixRun (N : Nat) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    SemiprimeD1JetRingBits.Run :=
  let root := SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed
  let s := SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam := SemiprimeD1PackingReady.logarithm s
  let out := SemiprimeD1HybridRecursiveCounter.run s (lam + 1) 0
    SemiprimeD1RootOwnerTables.rootContext root.network
  ⟨out.words, root.clock + out.clock +
    10 * (wireCount N + fixed.length + SemiprimeMacroParameters.bitLength N + 1)⟩

attribute [local irreducible] prefixRun

/-- The actual scalar count read from the acquired full-jet output. -/
def prefixCount (N : Nat) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) : Nat :=
  bitValue (((prefixRun N hN fixed).words[0]?).getD [])

/-- Execute the original zero-first selection order with this program's own queries. -/
def select (N : Nat) (hN : 0 < N) : List (Fin (wireCount N)) →
    List (Fin (wireCount N) × Bool) → SelectionRun (Fin (wireCount N))
  | [], _ => ⟨⟨[], 0⟩, 0, 1⟩
  | i :: rest, fixed =>
    let current := prefixRun N hN ((i, false) :: fixed)
    let n := bitValue ((current.words[0]?).getD [])
    let b := if 0 < n then false else true
    let tail := select N hN rest ((i, b) :: fixed)
    ⟨⟨(i, b) :: tail.selection.values, tail.selection.queries + 1⟩,
      current.clock + tail.queryWork,
      tail.metadataWork + 10 * (wireCount N + fixed.length + rest.length + 1) + 3⟩

/-- One existence query followed by the concrete factor-bit selection. -/
def search (N : Nat) (hN : 0 < N) : SearchRun (Fin (wireCount N)) :=
  let initial := prefixRun N hN []
  if 0 < bitValue ((initial.words[0]?).getD []) then
    let chosen := select N hN (List.finRange (wireCount N)) []
    ⟨⟨some chosen.selection.values, chosen.selection.queries + 1⟩,
      initial.clock + chosen.queryWork, chosen.metadataWork + 10 * (wireCount N + 1) + 3⟩
  else ⟨⟨none, 1⟩, initial.clock, 10 * (wireCount N + 1) + 3⟩

attribute [local irreducible] search

/-- Closed binary endpoint; every count query uses the concrete boundary evaluator. -/
def run (input : List Bool) : Run :=
  let initial := nonzeroBits input
  if hz : initial.nonzero = true then
    let N := bitValue input
    let hN : 0 < N := (nonzeroBits_correct input).mp hz
    let queried := search N hN
    match queried.result.values with
    | none => ⟨none, queried.result.queries, queried.queryWork, initial.clock + 3,
      queried.metadataWork + 10 * (wireCount N + input.length + 1)⟩
    | some values =>
      let operand := SemiprimeD1PublicOperandBits.run N values 0
      let checked := SemiprimeD1FactorValidationBits.run input operand.bits
      let answer := if checked.valid then some (operand.bits, checked.cofactor) else none
      ⟨answer, queried.result.queries, queried.queryWork,
        initial.clock + operand.arithmeticClock + checked.clock + 7,
        queried.metadataWork + operand.metadataWork +
          10 * (wireCount N + input.length + values.length + 1)⟩
  else ⟨none, 0, 0, initial.clock + 3, 10 * (input.length + 1)⟩

/-- Retain every executed query, arithmetic operation and native metadata report. -/
def work (input : List Bool) : Nat :=
  let out := run input
  out.queryWork + out.arithmeticClock + out.metadataWork

/-- Actual successful output always passes the physical proper-factor validation. -/
theorem run_sound (input left right : List Bool) (h : (run input).factors = some (left, right)) :
    bitValue left * bitValue right = bitValue input ∧ 2 ≤ bitValue left ∧ 2 ≤ bitValue right := by
  dsimp only [run] at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
        exact SemiprimeD1FactorValidationBits.run_factor_pair _ _ (by assumption)
      · cases h
  · cases h

/-- Executed selection makes exactly one acquired query per selected wire. -/
theorem select_queries (N : Nat) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) :
    (select N hN indices fixed).selection.queries = indices.length := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih => simp only [select, ih, List.length_cons]

/-- The concrete search retains the original linear query bound. -/
theorem search_queries (N : Nat) (hN : 0 < N) :
    (search N hN).result.queries ≤ wireCount N + 1 := by
  by_cases h : 0 < bitValue (((prefixRun N hN []).words[0]?).getD [])
  · simp only [search, ite_eq_left h, select_queries, List.length_finRange, le_refl]
  · simp only [search, ite_eq_right h]
    omega

/-- Factor-byte decoding and validation add no count queries. -/
theorem run_queries (input : List Bool) :
    (run input).queries ≤ wireCount (bitValue input) + 1 := by
  dsimp only [run]
  split
  · have hs := search_queries (bitValue input) ((nonzeroBits_correct input).mp (by assumption))
    split <;> exact hs
  · dsimp only
    omega

end RiemannGaussian.SemiprimeD1HybridPublicExecution
