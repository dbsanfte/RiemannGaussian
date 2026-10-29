/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTableSource
/-! # Literal source is the complete original checker-built root table
Reference construction is proof-side only. The actual source takes no N,
predicate, table, coefficient or evaluator input; every byte is a fixed push.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1BooleanRootTablesOriginal
open SemiprimeD1TensorTables SemiprimeD1BooleanRootTables
open SemiprimeMacroGraph SemiprimeMacroParameters
/-- The EXACT old factor producer/materializer at an original vertex, before
its Fin-factor reindexing. This reference is NEVER called by the new source. -/
def reference (N : ℕ) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N) :
    Table (subdividedArity v) :=
  (build (subdividedArity v) (fun bits=>
    let input:=bits.toArray
    let check:=SemiprimeSubdividedEntry.publicSubdividedEntry N hN v (fun i=>(input[i.val]?).getD false)
    ⟨[if check.accepted then [true] else []],check.clock+3*bits.length+5⟩)).table
/-- Exact indexed original factor producer, not an advised comparison table. -/
theorem reference_indexed (N : ℕ) (hN : 0<N) (e : Fin (SemiprimePublicAcquiredExecution.factorCount N)) :
    reference N hN ((SemiprimePublicAcquiredExecution.vertexEnumeration N).equivFin e)=
      (build (SemiprimePublicAcquiredExecution.indexedArity N e)
        (SemiprimeD1RootTensorTables.factorProducer N hN e)).table := rfl
/-- ENTIRE original OR table, with false-first ordered ports, is the literal table. -/
theorem or_table (N : ℕ) (hN : 0<N) (side : Fin 2) (j : Fin (digitCount (bitLength N)-1)) :
    reference N hN (.inl (.orGate side j))=table .orGate := rfl
/-- ENTIRE original one-port input-check table is the literal table. -/
theorem input_table (N : ℕ) (hN : 0<N) (side : Fin 2) :
    reference N hN (.inl (.inputCheck side))=table .inputCheck := rfl
/-- ENTIRE original subdivided equality table is the literal two-port table. -/
theorem equality_table (N : ℕ) (hN : 0<N)
    (signal : BitSignal (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))) :
    reference N hN (.inr signal)=table .equality := rfl
/-- Acquired OR bytes are EXACTLY the original complete tagged tree. -/
theorem source_or (N : ℕ) (hN : 0<N) (side : Fin 2) (j : Fin (digitCount (bitLength N)-1)) :
    SemiprimeD1StackBooleanTableSource.B.run SemiprimeD1StackBooleanTableSource.code 48
      (SemiprimeD1StackBooleanTableSource.initial .orGate)=
      some ⟨none,none,fun _=>SemiprimeD1TensorTapeCodec.tape (reference N hN (.inl (.orGate side j)))⟩ := by
  rw [or_table]
  exact SemiprimeD1StackBooleanTableSource.source_run .orGate
/-- Acquired input-check bytes are EXACTLY its original complete tagged tree. -/
theorem source_input (N : ℕ) (hN : 0<N) (side : Fin 2) :
    SemiprimeD1StackBooleanTableSource.B.run SemiprimeD1StackBooleanTableSource.code 12
      (SemiprimeD1StackBooleanTableSource.initial .inputCheck)=
      some ⟨none,none,fun _=>SemiprimeD1TensorTapeCodec.tape (reference N hN (.inl (.inputCheck side)))⟩ := by
  rw [input_table]
  exact SemiprimeD1StackBooleanTableSource.source_run .inputCheck
/-- Acquired equality bytes are EXACTLY its original complete tagged tree. -/
theorem source_equality (N : ℕ) (hN : 0<N)
    (signal : BitSignal (firstAxis (bitLength N)) (secondAxis (bitLength N)) (digitCount (bitLength N))) :
    SemiprimeD1StackBooleanTableSource.B.run SemiprimeD1StackBooleanTableSource.code 24
      (SemiprimeD1StackBooleanTableSource.initial .equality)=
      some ⟨none,none,fun _=>SemiprimeD1TensorTapeCodec.tape (reference N hN (.inr signal))⟩ := by
  rw [equality_table]
  exact SemiprimeD1StackBooleanTableSource.source_run .equality
end RiemannGaussian.SemiprimeD1BooleanRootTablesOriginal
