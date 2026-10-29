/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HybridPublicExecution
import RiemannGaussian.SemiprimeD1BoundaryLeafValue

/-! # Closed recursive and original-binary correctness of the boundary hybrid

The leaf equality is proved from the actual acquired records. This module fixes
that evaluator throughout the original public program and transfers complete
factor bytes while retaining the changed program's own work reports.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HybridRecursiveCounter
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorNetwork (Network)

/-- Every hybrid recursive call preserves all old physical coefficient words. -/
theorem run_words_eq_physical (s fuel depth : Nat) (ctx : Context) (net : Network)
    (hp : ctx.Positive) :
    (run s fuel depth ctx net).words =
      (SemiprimeD1PhysicalRecursiveCounter.run s fuel depth ctx net).words :=
  SemiprimeD1HybridRecursiveKernel.run_words_eq_physical SemiprimeD1BoundaryLeaf.checked
    SemiprimeD1BoundaryLeaf.checked_words s fuel depth ctx net hp

/-- All coefficient words remain canonical at every supplied fuel and depth. -/
theorem run_good (s fuel depth : Nat) (ctx : Context) (net : Network) (hp : ctx.Positive) :
    SemiprimeD1TensorTables.GoodWords ctx (run s fuel depth ctx net).words :=
  SemiprimeD1HybridRecursiveKernel.run_good SemiprimeD1BoundaryLeaf.checked
    SemiprimeD1BoundaryLeaf.checked_words s fuel depth ctx net hp

/-- The complete literal contraction is preserved, including every jet coordinate. -/
theorem run_words_eq_leaf (s fuel depth : Nat) (ctx : Context) (net : Network)
    (hp : ctx.Positive) (hw : SemiprimeD1TensorNetwork.WellFormed net)
    (hg : SemiprimeD1TensorNetwork.Good ctx net) :
    (run s fuel depth ctx net).words = (SemiprimeD1TensorNetwork.leaf ctx net).words :=
  SemiprimeD1HybridRecursiveKernel.run_words_eq_leaf SemiprimeD1BoundaryLeaf.checked
    SemiprimeD1BoundaryLeaf.checked_words s fuel depth ctx net hp hw hg

end RiemannGaussian.SemiprimeD1HybridRecursiveCounter

namespace RiemannGaussian.SemiprimeD1HybridPublicExecution
open SemiprimePublicAcquiredExecution SemiprimeBitArithmetic SemiprimeBitDivision
attribute [local irreducible] SemiprimeD1RootTapeNetwork.acquirePositive
  SemiprimeD1HybridRecursiveCounter.run SemiprimeD1WordTapeRecursiveCounter.run
  search
  SemiprimeD1WordTapePublicSearch.search SemiprimeD1PublicOperandBits.run
  SemiprimeD1FactorValidationBits.run

/-- Each original prefix returns exactly the previous program's complete words. -/
theorem prefixRun_words_eq_tape (N : Nat) (hN : 0 < N)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN fixed).words =
      (SemiprimeD1WordTapePublicCounter.prefixRun N hN fixed).words := by
  let s := SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam := SemiprimeD1PackingReady.logarithm s
  have hp : SemiprimeD1RootOwnerTables.rootContext.Positive := by
    simp [SemiprimeD1JetAxes.Context.Positive, SemiprimeD1RootOwnerTables.rootContext]
  change (SemiprimeD1HybridRecursiveCounter.run s (lam + 1) 0
    SemiprimeD1RootOwnerTables.rootContext
      (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).network).words =
    (SemiprimeD1WordTapeRecursiveCounter.run s (lam + 1) 0
      SemiprimeD1RootOwnerTables.rootContext
        (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).network).words
  exact (SemiprimeD1HybridRecursiveCounter.run_words_eq_physical s (lam + 1) 0 _ _ hp).trans
    (SemiprimeD1WordTapeRecursiveCounter.run_words_eq_physical s (lam + 1) 0 _ _ hp).symm

attribute [local irreducible] prefixRun SemiprimeD1WordTapePublicCounter.prefixRun

/-- The changed concrete prefix execution preserves every original scalar count. -/
theorem prefixCount_eq_tape (N : Nat) (hN : 0 < N)
    (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN fixed = SemiprimeD1WordTapePublicCounter.prefixCount N hN fixed := by
  unfold prefixCount SemiprimeD1WordTapePublicCounter.prefixCount
  rw [prefixRun_words_eq_tape]

/-- Exact original semiprime count semantics include arbitrary repeated/conflicting prefixes. -/
theorem prefixCount_exact (N p q : Nat) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p * q) (fixed : List (Fin (wireCount N) × Bool)) :
    prefixCount N hN fixed = SemiprimeCountRecovery.acceptedCount
      (SemiprimeCountRecovery.restricted SemiprimeCounterSearch.assignmentBit
        (indexedPredicate N hN) fixed) :=
  (prefixCount_eq_tape N hN fixed).trans
    (SemiprimeD1WordTapePublicCounter.prefixCount_exact N p q hN hp hq hsem fixed)

/-- Every actual zero-first selection, including its ties, is preserved literally. -/
theorem select_eq_tape (N : Nat) (hN : 0 < N) (indices : List (Fin (wireCount N)))
    (fixed : List (Fin (wireCount N) × Bool)) :
    (select N hN indices fixed).selection =
      (SemiprimeD1WordTapePublicSearch.select N hN indices fixed).selection := by
  induction indices generalizing fixed with
  | nil => rfl
  | cons i rest ih =>
    simp only [select, SemiprimeD1WordTapePublicSearch.select, prefixRun_words_eq_tape, ih]

/-- The entire closed original-input search returns the exact previous selected data. -/
theorem search_result_eq_tape (N : Nat) (hN : 0 < N) :
    (search N hN).result = (SemiprimeD1WordTapePublicSearch.search N hN).result := by
  simp only [search, SemiprimeD1WordTapePublicSearch.search, prefixRun_words_eq_tape]
  split
  · exact congrArg (fun s : SemiprimeCountRecovery.Selection (Fin (wireCount N)) =>
      SemiprimeCountRecovery.SearchResult.mk (some s.values) (s.queries + 1))
      (select_eq_tape N hN (List.finRange (wireCount N)) [])
  · rfl

/-- The final factors agree byte for byte on every original binary input. -/
theorem run_factors_eq_tape (input : List Bool) :
    (run input).factors = (SemiprimeD1WordTapeBinaryFactorExecution.run input).factors := by
  by_cases hz : (nonzeroBits input).nonzero = true
  · have hN := (nonzeroBits_correct input).mp hz
    have hv := congrArg SemiprimeCountRecovery.SearchResult.values
      (search_result_eq_tape (bitValue input) hN)
    dsimp only [run, SemiprimeD1WordTapeBinaryFactorExecution.run]
    simp only [dite_eq_left hz]
    rw [hv]
    cases (SemiprimeD1WordTapePublicSearch.search (bitValue input) hN).result.values <;> rfl
  · simp only [run, SemiprimeD1WordTapeBinaryFactorExecution.run, dite_eq_right hz]

/-- Every original binary semiprime, including a square, yields an actual factor pair. -/
theorem run_complete (input : List Bool) (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hsem : bitValue input = p * q) :
    ∃ left right, (run input).factors = some (left, right) ∧
      bitValue left * bitValue right = bitValue input ∧
      2 ≤ bitValue left ∧ 2 ≤ bitValue right ∧ (bitValue left = p ∨ bitValue left = q) := by
  obtain ⟨left, right, hout, hrest⟩ :=
    SemiprimeD1WordTapeBinaryFactorExecution.run_complete input p q hp hq hsem
  exact ⟨left, right, (run_factors_eq_tape input).trans hout, hrest⟩

end RiemannGaussian.SemiprimeD1HybridPublicExecution
