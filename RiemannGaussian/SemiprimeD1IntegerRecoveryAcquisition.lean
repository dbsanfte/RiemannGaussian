/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IntegerRecoveryResidue

/-! # Cached original weight acquisition joined to integer recovery
Each active original weight packet is acquired exactly once. The existing
cardinal/inverse arithmetic and read reports are retained. These reports do NOT
cover Ezero, slope metadata, or the scalar localWeight loops; no whole producer
or primitive-bit clock is asserted.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegerRecoveryAcquisition
open SemiprimeD1IntegerRecovery SemiprimeD1JetRecoveryWeights
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid SemiprimeJetArray

/-- Acquired terms with the existing packet operation reports retained. -/
structure TermsReport where
  /-- Original acquired scalar weights paired with actual child words. -/
  terms : List Term
  /-- Cardinal and inverse scalar operations, excluding the explicitly open stages. -/
  packetArithmetic : ℕ
  /-- Cardinal and inverse array reads. -/
  packetReads : ℕ

/-- One actual acquisition per active node, with its returned reports preserved. -/
def gather (a h u : ℕ) (children : ℕ → Array (List Bool)) : List ℕ → TermsReport
  | [] => ⟨[],0,0⟩
  | t::ts =>
    let w := acquire a h u t
    let tail := gather a h u children ts
    let localTerms := (List.range w.retained).map fun j =>
      Term.mk (coefficient w.weights j) ((children t)[j]?.getD [])
    ⟨localTerms++tail.terms,
      w.denominator.arithmetic+w.inverse.arithmetic+tail.packetArithmetic,
      w.denominator.reads+w.inverse.reads+tail.packetReads⟩

/-- Cached acquisition preserves the literal original term ordering. -/
theorem gather_terms (a h u : ℕ) (children : ℕ → Array (List Bool)) (nodes : List ℕ) :
    (gather a h u children nodes).terms=nodes.flatMap (fun t =>
      let w := acquire a h u t
      (List.range w.retained).map fun j =>
        Term.mk (coefficient w.weights j) ((children t)[j]?.getD [])) := by
  induction nodes with
  | nil => rfl
  | cons t ts ih => simp only [gather,List.flatMap_cons,ih]

/-- One cached weight-acquisition result and the executed integer recovery. -/
structure Report where
  /-- Actual executed integer result. -/
  result : Result
  /-- Existing acquired cardinal/inverse operation reports retained. -/
  packetArithmetic : ℕ
  /-- Existing acquired cardinal/inverse read reports retained. -/
  packetReads : ℕ

/-- Actual original-grid acquisition and integer numerator call path. -/
def run (a M u : ℕ) (children : ℕ → Array (List Bool)) : Report :=
  let nodes := (List.range (SemiprimeD1WireKernelOriginal.size a)).filter (fun t =>
    t≠SemiprimeD1WireKernelOriginal.center a ∧ 0<nodeMultiplicity a (height M u) u t)
  let acquired := gather a (height M u) u children nodes
  let dr := denominatorRun acquired.terms
  let ar := accumulateRun dr.1 acquired.terms
  ⟨⟨dr.1,ar.1,dr.2+ar.2.1,ar.2.2⟩,acquired.packetArithmetic,acquired.packetReads⟩

/-- The cached producer path has precisely the already verified integer recovery result. -/
theorem run_result (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).result=SemiprimeD1IntegerRecovery.run a M u children := by
  simp only [run,gather_terms,SemiprimeD1IntegerRecovery.run,terms]

/-- Exact number of native scalar arithmetic operations in the denominator traversal. -/
theorem denominatorRun_arithmetic (ts : List Term) : (denominatorRun ts).2=ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [denominatorRun,ih]

/-- Exact numerator arithmetic count for the actual recursive accumulator. -/
theorem accumulateRun_arithmetic (D : ℕ) (ts : List Term) :
    (accumulateRun D ts).2.1=4*ts.length+2*(ts.map fun t => t.child.length).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [accumulateRun,ih];omega

/-- Exact child-cell read count for the actual decoder traversals. -/
theorem accumulateRun_reads (D : ℕ) (ts : List Term) :
    (accumulateRun D ts).2.2=(ts.map fun t => t.child.length).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [accumulateRun,ih,Nat.add_comm]

/-- Actual numerator plus denominator traversal takes five operations per term and two per decoded digit. -/
theorem run_arithmetic (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).result.arithmetic=5*(terms a M u children).length+
      2*((terms a M u children).map fun t => t.child.length).sum := by
  rw [run_result]
  simp only [SemiprimeD1IntegerRecovery.run,denominatorRun_arithmetic,accumulateRun_arithmetic]
  omega

end RiemannGaussian.SemiprimeD1IntegerRecoveryAcquisition
