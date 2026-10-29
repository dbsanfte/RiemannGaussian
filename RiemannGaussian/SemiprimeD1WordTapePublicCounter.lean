/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordTapeRecursiveReport
import RiemannGaussian.SemiprimeD1PhysicalPublicCounter
import RiemannGaussian.SemiprimeD1RootTapeNetwork

/-! # Actual original-input public prefix caller with tape-backed recursion
Every query acquires its root and executes the new closed recursion. Only word
semantics transfer; its actual setup and recursive reports remain distinct.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordTapePublicCounter
open SemiprimeBitArithmetic SemiprimePublicAcquiredExecution
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
  SemiprimeD1RootTapeNetwork.acquirePositive SemiprimeD1RootNetwork.acquirePositive
  SemiprimeD1WordTapeRecursiveCounter.run SemiprimeD1PhysicalRecursiveCounter.run

/-- Actual original-N/prefix root acquisition followed by the new tape recursion. -/
def prefixRun (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) :
    SemiprimeD1JetRingBits.Run :=
  let root:=SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed
  let s:=SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam:=SemiprimeD1PackingReady.logarithm s
  let out:=SemiprimeD1WordTapeRecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext root.network
  ⟨out.words,root.clock+out.clock+10*(wireCount N+fixed.length+SemiprimeMacroParameters.bitLength N+1)⟩

/-- Public words agree literally, with no old/new query-clock identification. -/
theorem prefixRun_words_eq_physical (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (wireCount N)×Bool)) :
    (prefixRun N hN fixed).words=(SemiprimeD1PhysicalPublicCounter.prefixRun N hN fixed).words := by
  let s:=SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength N)
  let lam:=SemiprimeD1PackingReady.logarithm s
  have hp : SemiprimeD1RootOwnerTables.rootContext.Positive := by
    simp [SemiprimeD1JetAxes.Context.Positive,SemiprimeD1RootOwnerTables.rootContext]
  have he:=SemiprimeD1RootTapeNetwork.acquirePositive_network N hN fixed
  change (SemiprimeD1WordTapeRecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext (SemiprimeD1RootTapeNetwork.acquirePositive N hN fixed).network).words=
    (SemiprimeD1PhysicalRecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words
  exact (congrArg (fun net => (SemiprimeD1WordTapeRecursiveCounter.run s (lam+1) 0
    SemiprimeD1RootOwnerTables.rootContext net).words) he).trans
    (SemiprimeD1WordTapeRecursiveCounter.run_words_eq_physical s (lam+1) 0 _ _ hp)

/-- Actual two-bit scalar count returned by the new executed query. -/
def prefixCount (N : ℕ) (hN : 0<N) (fixed : List (Fin (wireCount N)×Bool)) : ℕ :=
  bitValue (((prefixRun N hN fixed).words[0]?).getD [])

/-- Literal scalar equality, not a supplied conditional-count oracle. -/
theorem prefixCount_eq_physical (N : ℕ) (hN : 0<N)
    (fixed : List (Fin (wireCount N)×Bool)) :
    prefixCount N hN fixed=SemiprimeD1PhysicalPublicCounter.prefixCount N hN fixed := by
  unfold prefixCount SemiprimeD1PhysicalPublicCounter.prefixCount
  rw [prefixRun_words_eq_physical]

/-- Closed original count semantics for every semiprime prefix, including squares. -/
theorem prefixCount_exact (N p q : ℕ) (hN : 0<N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N=p*q) (fixed : List (Fin (wireCount N)×Bool)) :
    prefixCount N hN fixed=SemiprimeCountRecovery.acceptedCount
      (SemiprimeCountRecovery.restricted SemiprimeCounterSearch.assignmentBit
        (indexedPredicate N hN) fixed) :=
  (prefixCount_eq_physical N hN fixed).trans
    (SemiprimeD1PhysicalPublicCounter.prefixCount_exact N p q hN hp hq hsem fixed)

/-- Mathematical search specification using this same actual prefix value. -/
def search (N : ℕ) (hN : 0<N) : SemiprimeCountRecovery.SearchResult (Fin (wireCount N)) :=
  SemiprimeCountRecovery.search (prefixCount N hN) (List.finRange (wireCount N))

/-- Exact search data and query counter, without transferring report fields. -/
theorem search_eq_physical (N : ℕ) (hN : 0<N) :
    search N hN=SemiprimeD1PhysicalPublicCounter.search N hN := by
  have he : prefixCount N hN=SemiprimeD1PhysicalPublicCounter.prefixCount N hN :=
    funext (prefixCount_eq_physical N hN)
  exact congrArg (fun count => SemiprimeCountRecovery.search count (List.finRange (wireCount N))) he

/-- Original linear query count for the actual new prefix values. -/
theorem search_queries (N : ℕ) (hN : 0<N) : (search N hN).queries ≤ wireCount N+1 := by
  rw [search_eq_physical]
  exact SemiprimeD1PhysicalPublicCounter.search_queries N hN

end RiemannGaussian.SemiprimeD1WordTapePublicCounter
