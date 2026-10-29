/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PhysicalRecursiveCorrectness
import RiemannGaussian.SemiprimeD1PublicCorrectness

/-! # Original binary caller using closed physical scalar recovery
This caller acquires its own original root tables and executes the NEW physical
recursive counter. Literal output equality transfers correctness of the search
and decoder; no equality of old and new clocks is assumed. Every prefix report
retains its actual root acquisition and physical recursive reports. The aggregate
still includes native metadata and is not yet a whole primitive-machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PhysicalPublicCounter
open SemiprimeBitArithmetic SemiprimePublicAcquiredExecution
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive

/-- Original-N/prefix acquisition and this actual physical-recovery recursion. -/
def prefixRun (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) :
    SemiprimeD1JetRingBits.Run :=
  let root := SemiprimeD1RootNetwork.acquirePositive N hN fixed
  let s := SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam := SemiprimeD1PackingReady.logarithm s
  let out := SemiprimeD1PhysicalRecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext root.network
  ⟨out.words,root.clock+out.clock+10*(wireCount N+fixed.length+SemiprimeMacroParameters.bitLength N+1)⟩

/-- All actual new caller words equal the original caller's words on every
positive input and prefix; this statement does not identify their clocks. -/
theorem prefixRun_words_eq_original (N : ℕ) (hN : 0 < N)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN fixed).words = (SemiprimeD1PublicCounter.prefixRun N hN fixed).words := by
  unfold prefixRun SemiprimeD1PublicCounter.prefixRun
  dsimp only
  apply SemiprimeD1PhysicalRecursiveCorrectness.run_words_eq_original
  · simp [SemiprimeD1JetAxes.Context.Positive,SemiprimeD1RootOwnerTables.rootContext]
  · exact SemiprimeD1RootNetwork.acquirePositive_wellFormed N hN fixed
  · exact SemiprimeD1RootNetwork.acquirePositive_good N hN fixed

/-- The actual returned two-bit scalar is the conditional count query. -/
def prefixCount (N : ℕ) (hN : 0 < N) (fixed : List (Fin (wireCount N) × Bool)) : ℕ :=
  bitValue (((prefixRun N hN fixed).words[0]?).getD [])

/-- Equality of actual scalar values, not an assumed count supplier. -/
theorem prefixCount_eq_original (N : ℕ) (hN : 0 < N)
    (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN fixed = SemiprimeD1PublicCounter.prefixCount N hN fixed := by
  unfold prefixCount SemiprimeD1PublicCounter.prefixCount
  rw [prefixRun_words_eq_original]

/-- Every semiprime prefix is exactly counted by the actual physical pipeline. -/
theorem prefixCount_exact (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p*q) (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN fixed = SemiprimeCountRecovery.acceptedCount
      (SemiprimeCountRecovery.restricted SemiprimeCounterSearch.assignmentBit
        (indexedPredicate N hN) fixed) :=
  (prefixCount_eq_original N hN fixed).trans
    (SemiprimeD1PublicCorrectness.prefixCount_exact N p q hN hp hq hsem fixed)

/-- Literal zero-first original-prefix search using this physical counter. -/
def search (N : ℕ) (hN : 0 < N) : SemiprimeCountRecovery.SearchResult (Fin (wireCount N)) :=
  SemiprimeCountRecovery.search (prefixCount N hN) (List.finRange (wireCount N))

/-- The actual search outputs, including its query counter, agree literally. -/
theorem search_eq_original (N : ℕ) (hN : 0 < N) :
    search N hN = SemiprimeD1PublicCounter.search N hN := by
  have he : prefixCount N hN = SemiprimeD1PublicCounter.prefixCount N hN :=
    funext (prefixCount_eq_original N hN)
  exact congrArg (fun count => SemiprimeCountRecovery.search count
    (List.finRange (wireCount N))) he

/-- No more than one initial and one query per actual original wire. -/
theorem search_queries (N : ℕ) (hN : 0 < N) : (search N hN).queries ≤ wireCount N+1 := by
  rw [search_eq_original]
  exact SemiprimeD1PublicCounter.search_queries N hN

attribute [local irreducible] search SemiprimeD1PublicCounter.search
  SemiprimePublicAcquiredExecution.decodeOperand

/-- Execute the actual physical counter, decode its selected operand, and
perform ordinary integer proper-divisor validation. All inputs are original N. -/
def factor (N : ℕ) : Option ℕ :=
  if hN : 0 < N then
    match (search N hN).values with
    | none => none
    | some values =>
      let d := decodeOperand N values 0
      if 2 ≤ d ∧ d < N ∧ N%d = 0 then some d else none
  else none

/-- The new executed physical path has the same factor answer on all inputs,
without transferring any old report or runtime bound. -/
theorem factor_eq_original (N : ℕ) : factor N = SemiprimeD1PublicCounter.factor N := by
  unfold factor SemiprimeD1PublicCounter.factor
  split
  · rw [search_eq_original]
    rfl
  · rfl

/-- Every output is an actual validated proper divisor on every input. -/
theorem factor_valid (N d : ℕ) (h : factor N = some d) : 2 ≤ d ∧ d < N ∧ N%d = 0 :=
  SemiprimeD1PublicCounter.factor_valid N d ((factor_eq_original N).symm.trans h)

/-- Closed all-semiprime completeness for the new executed physical path. -/
theorem factor_complete (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hsem : N = p*q) :
    ∃ d,factor N = some d ∧ 2 ≤ d ∧ d < N ∧ N%d = 0 ∧ (d = p ∨ d = q) := by
  rw [factor_eq_original]
  exact SemiprimeD1PublicCorrectness.factor_complete N p q hp hq hsem

/-- Direct original little-endian binary input; no acquired auxiliary input. -/
def factorBits (input : List Bool) : Option ℕ := factor (bitValue input)

/-- All binary answers are validated proper divisors of the decoded input. -/
theorem factorBits_valid (input : List Bool) (d : ℕ) (h : factorBits input = some d) :
    2 ≤ d ∧ d < bitValue input ∧ bitValue input%d = 0 := factor_valid (bitValue input) d h

/-- The binary entry point succeeds for every semiprime, including squares. -/
theorem factorBits_complete (input : List Bool) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hsem : bitValue input = p*q) :
    ∃ d,factorBits input = some d ∧
      2 ≤ d ∧ d < bitValue input ∧ bitValue input%d = 0 ∧ (d = p ∨ d = q) :=
  factor_complete (bitValue input) p q hp hq hsem

end RiemannGaussian.SemiprimeD1PhysicalPublicCounter
