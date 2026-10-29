/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCounter
import RiemannGaussian.SemiprimeD1RootNetwork
import RiemannGaussian.SemiprimeD1SemiprimePrefix

/-! # Original-binary-input caller for the concrete recursive counter
The prefix solver acquires its root graph/tables from N and the actual prefix,
runs the fixed recursive controller at precision2, and decodes its literal
residue word. Conditional-count search and integer operand decoding are actual
executed existing routines; a final arithmetic guard validates every output.

This module supplies the concrete caller, canonical output/range and unconditional
output validation. Semiprime completeness requires the pending full recursive
contraction proof; the complete primitive-bit bound is also still open.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1PublicCounter
open SemiprimeBitArithmetic SemiprimePublicAcquiredExecution

/-- Actual original-N/prefix source acquisition and the fixed own recursive run. -/
def prefixRun (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    SemiprimeD1JetRingBits.Run :=
  let root := SemiprimeD1RootNetwork.acquirePositive N hN fixed
  let s := SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam := SemiprimeD1PackingReady.logarithm s
  let out := SemiprimeD1RecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext root.network
  ⟨out.words,root.clock+out.clock+10*(wireCount N+fixed.length+SemiprimeMacroParameters.bitLength N+1)⟩

/-- The actual caller always returns one canonical word of at most two bits. -/
theorem prefixRun_good (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    SemiprimeD1TensorTables.GoodWords SemiprimeD1RootOwnerTables.rootContext (prefixRun N hN fixed).words := by
  unfold prefixRun
  dsimp only
  exact SemiprimeD1RecursiveCounter.run_good _ _ _ _ _

/-- Actual natural residue used by conditional-count recovery, not an input count answer. -/
def prefixCount (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) : ℕ :=
  bitValue (((prefixRun N hN fixed).words[0]?).getD [])

/-- The actual queried integer is always in the four-element root residue range. -/
theorem prefixCount_lt_four (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN fixed < 4 := by
  have hg := prefixRun_good N hN fixed
  have hw : (((prefixRun N hN fixed).words[0]?).getD []).length ≤ 2 := by
    cases he : (prefixRun N hN fixed).words with
    | nil => simp only [List.getElem?_nil,Option.getD_none,List.length_nil]; omega
    | cons w ws =>
      have hh := (hg.2 w (by rw [he]; exact List.mem_cons_self)).2
      simpa only [he,List.getElem?_cons_zero,Option.getD_some,SemiprimeD1RootOwnerTables.rootContext] using hh
  exact (bitValue_lt_width _).trans_le (by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hw)

/-- Original zero-first prefix search, wired to the actual new counter. -/
def search (N : ℕ) (hN : 0 < N) : SemiprimeCountRecovery.SearchResult (Fin (wireCount N)) :=
  SemiprimeCountRecovery.search (prefixCount N hN) (List.finRange (wireCount N))

/-- Every input executes at most one initial and one per-wire prefix query. -/
theorem search_queries (N : ℕ) (hN : 0 < N) : (search N hN).queries ≤ wireCount N+1 := by
  simpa only [search,List.length_finRange] using
    SemiprimeCountRecovery.search_queries_le (prefixCount N hN) (List.finRange (wireCount N))

/-- Executed candidate factor from original N, followed by actual integer validation.
There is no count, layout, table, coefficient, weight, or factor oracle argument. -/
def factor (N : ℕ) : Option ℕ :=
  if hN : 0 < N then
    match (search N hN).values with
    | none => none
    | some values =>
      let d := decodeOperand N values 0
      if 2 ≤ d ∧ d < N ∧ N%d = 0 then some d else none
  else none

/-- Every returned result passes the actual proper-divisor validation, on ALL
inputs. This is soundness only; semiprime completeness remains a separate goal. -/
theorem factor_valid (N d : ℕ) (h : factor N = some d) : 2 ≤ d ∧ d < N ∧ N%d = 0 := by
  unfold factor at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h
        assumption
      · cases h
  · cases h

/-- Direct literal little-endian binary-input entry point. -/
def factorBits (input : List Bool) : Option ℕ := factor (bitValue input)

/-- The binary caller validates each returned proper divisor of its decoded input. -/
theorem factorBits_valid (input : List Bool) (d : ℕ) (h : factorBits input = some d) :
    2 ≤ d ∧ d < bitValue input ∧ bitValue input%d = 0 := factor_valid (bitValue input) d h

end RiemannGaussian.SemiprimeD1PublicCounter
