/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PublicCountConsequences
import RiemannGaussian.SemiprimeD1RecursiveCorrectness
import RiemannGaussian.SemiprimeD1RootNetworkContraction

/-! # Closed original-input semiprime factorization correctness
The executed prefix counter acquires its own original root network. Its actual
recursive output equals the complete original contraction, whose residue modulo
four is the exact semiprime prefix count. The existing literal search, operand
decoder and integer validation therefore recover a prime factor. No count,
phase, coefficient, layout or factor answer is supplied to the algorithm.
This is a correctness theorem; the whole primitive bit-time theorem is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PublicCorrectness
open SemiprimePublicAcquiredExecution SemiprimeD1TensorNetwork
open SemiprimeCountRecovery SemiprimeCounterSearch SemiprimeBitArithmetic
attribute [local irreducible] SemiprimeD1RootTensorTables.acquirePositive
  SemiprimePublicAcquiredExecution.indexedPredicate

/-- The actual original-prefix caller returns the canonical complete root
contraction, with all recursive child semantics discharged internally. -/
theorem prefixRun_words (N : ℕ) (hN : 0 < N)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (SemiprimeD1PublicCounter.prefixRun N hN fixed).words =
      (leaf SemiprimeD1RootOwnerTables.rootContext
        (SemiprimeD1RootNetwork.acquirePositive N hN fixed).network).words := by
  unfold SemiprimeD1PublicCounter.prefixRun
  dsimp only
  apply SemiprimeD1RecursiveCorrectness.run_words_eq_leaf
  · simp [SemiprimeD1JetAxes.Context.Positive,SemiprimeD1RootOwnerTables.rootContext]
  · exact SemiprimeD1RootNetwork.acquirePositive_wellFormed N hN fixed
  · exact SemiprimeD1RootNetwork.acquirePositive_good N hN fixed

/-- EVERY original semiprime prefix is counted exactly by this executed
recursive counter, including repeated primes and inconsistent prefixes. -/
theorem prefixCount_exact (N p q : ℕ) (hN : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hsem : N = p*q) (fixed : List (Fin (wireCount N) × Bool)) :
    SemiprimeD1PublicCounter.prefixCount N hN fixed =
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed) := by
  have hex := SemiprimeD1RootNetworkContraction.acquired_leaf_exact
    N p q hN hp hq hsem fixed
  have hval : (SemiprimeD1JetRingBits.coefficient SemiprimeD1RootOwnerTables.rootContext
      (SemiprimeD1PublicCounter.prefixRun N hN fixed).words 0).val =
      acceptedCount (restricted assignmentBit (indexedPredicate N hN) fixed) := by
    rw [prefixRun_words N hN fixed]
    exact hex
  change SemiprimeD1PublicCounter.prefixCount N hN fixed % 4 = _ at hval
  exact (Nat.mod_eq_of_lt (SemiprimeD1PublicCounter.prefixCount_lt_four N hN fixed)).symm.trans hval

/-- Closed completeness for the fixed original-N public algorithm: every
semiprime produces a proper divisor equal to one of its prime factors. -/
theorem factor_complete (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hsem : N = p*q) :
    ∃ d,SemiprimeD1PublicCounter.factor N = some d ∧
      2 ≤ d ∧ d < N ∧ N%d = 0 ∧ (d = p ∨ d = q) := by
  have hN : 0 < N := by rw [hsem];exact Nat.mul_pos hp.pos hq.pos
  exact SemiprimeD1PublicCountConsequences.factor_complete N p q hN hp hq hsem
    (prefixCount_exact N p q hN hp hq hsem)

/-- The actual binary-input entry point factors every decoded semiprime.
Correctness is independent of input padding; runtime uses canonical input size. -/
theorem factorBits_complete (input : List Bool) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hsem : bitValue input = p*q) :
    ∃ d,SemiprimeD1PublicCounter.factorBits input = some d ∧
      2 ≤ d ∧ d < bitValue input ∧ bitValue input%d = 0 ∧ (d = p ∨ d = q) :=
  factor_complete (bitValue input) p q hp hq hsem

end RiemannGaussian.SemiprimeD1PublicCorrectness
