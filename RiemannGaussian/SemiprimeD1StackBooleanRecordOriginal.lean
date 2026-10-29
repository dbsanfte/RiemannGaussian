/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanRecordBounds
import RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
import RiemannGaussian.SemiprimeD1BooleanRootTablesOriginal
/-! # Exact original Boolean-family rows, with caller-acquired ordered numeric scopes
Scope acquisition, routing and parsing the original finite vertex tag remain
caller operations. No original-input whole-graph runtime claim is made here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
open SemiprimeD1StackBooleanRecord SemiprimeD1StackBooleanRecordExecution
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt id_value id_length)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Proof-only identification with an original local factor table, never runtime advice. -/
def Matches (N : Nat) (hN : 0<N) (mode : SemiprimeD1StackBooleanEntry.Mode)
    (v : SemiprimePublicAcquiredExecution.PublicVertex N) : Prop :=
  table mode=SemiprimeD1TensorTapeCodec.tape (SemiprimeD1BooleanRootTablesOriginal.reference N hN v)
/-- Every original OR vertex has the fixed literal OR table in unchanged port order. -/
theorem matches_or (N : Nat) (hN : 0<N) (side : Fin 2)
    (j : Fin (SemiprimeMacroParameters.digitCount (SemiprimeMacroParameters.bitLength N)-1)) :
    Matches N hN .orGate (.inl (.orGate side j)) := by
  unfold Matches
  rw [SemiprimeD1BooleanRootTablesOriginal.or_table]
  rfl
/-- Every original input-check vertex has the fixed literal one-port table. -/
theorem matches_input (N : Nat) (hN : 0<N) (side : Fin 2) :
    Matches N hN .inputCheck (.inl (.inputCheck side)) := by
  unfold Matches
  rw [SemiprimeD1BooleanRootTablesOriginal.input_table]
  rfl
/-- Every original equality subdivision has the fixed literal two-port table. -/
theorem matches_equality (N : Nat) (hN : 0<N)
    (signal : SemiprimeMacroGraph.BitSignal
      (SemiprimeMacroParameters.firstAxis (SemiprimeMacroParameters.bitLength N))
      (SemiprimeMacroParameters.secondAxis (SemiprimeMacroParameters.bitLength N))
      (SemiprimeMacroParameters.digitCount (SemiprimeMacroParameters.bitLength N))) :
    Matches N hN .equality (.inr signal) := by
  unfold Matches
  rw [SemiprimeD1BooleanRootTablesOriginal.equality_table]
  rfl
/-- Exact old indexed factor producer, retaining its original arity and port order. -/
theorem indexed_bytes (N : Nat) (hN : 0<N)
    (e : Fin (SemiprimePublicAcquiredExecution.factorCount N))
    (mode : SemiprimeD1StackBooleanEntry.Mode)
    (hm : Matches N hN mode ((SemiprimePublicAcquiredExecution.vertexEnumeration N).equivFin e)) :
    table mode=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1TensorTables.build (SemiprimePublicAcquiredExecution.indexedArity N e)
        (SemiprimeD1RootTensorTables.factorProducer N hN e)).table := by
  rw [←SemiprimeD1BooleanRootTablesOriginal.reference_indexed]
  exact hm
/-- Each acquired literal entry is the integer zero or one before multiplication. -/
theorem entry_coefficient (mode : SemiprimeD1StackBooleanEntry.Mode)
    (input : Fin (SemiprimeD1StackBooleanEntryMachine.arity mode)→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (SemiprimeD1TensorTables.valueAt
        (SemiprimeD1BooleanRootTables.table mode) input))=
      if SemiprimeD1StackBooleanEntryMachine.value mode input then 1 else 0 :=
  SemiprimeD1BooleanRootTables.literal_entry_coefficient mode input
/-- Changing only a table's type index leaves every original tape byte unchanged. -/
theorem tape_cast {m n : Nat} (h : m=n) (t : SemiprimeD1TensorTables.Table m) :
    SemiprimeD1TensorTapeCodec.tape (cast (congrArg SemiprimeD1TensorTables.Table h) t)=
      SemiprimeD1TensorTapeCodec.tape t := by
  cases h;rfl
/-- Proof-side vertex with the caller's exact ordered global occurrence scope and
the original complete table; this constructor is never executed. -/
def vertex (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N) (ports : List Nat)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity v) :
    SemiprimeD1LeafCounter.Vertex :=
  ⟨ports,cast (congrArg SemiprimeD1TensorTables.Table hlen.symm)
    (SemiprimeD1BooleanRootTablesOriginal.reference N hN v)⟩
/-- Exact row bytes bind numeric IDs to unary global ports without a permutation. -/
theorem row_original (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm : Matches N hN mode v) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      v) :
    R.row (S.result (ports.map (Bank.idAt M))) (table mode)=
      R.row (SemiprimeD1StackVertexReadExecution.portTape
        (vertex N hN v ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape
          (vertex N hN v ports hlen).table) := by
  rw [SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp,hm]
  exact congrArg (R.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (tape_cast hlen.symm (SemiprimeD1BooleanRootTablesOriginal.reference
      (N) hN v)).symm
/-- Literal acquired row prepends exactly the frozen original product-reader record. -/
theorem record_bytes_original (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm : Matches N hN mode v) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      v)
    (rest : List SemiprimeD1LeafCounter.Vertex) :
    R.row (S.result (ports.map (Bank.idAt M))) (table mode)++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex N hN v ports hlen::rest) := by
  rw [row_original N hN v mode hm M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- The actual halt keeps every previous row in its original forward order. -/
theorem history_original (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm : Matches N hN mode v) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      v)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done mode (ports.map (Bank.idAt M)) (Log.history previous old) out).data history=
      Log.history (previous++[vertex N hN v ports hlen]) old := by
  change (R.row (S.result (ports.map (Bank.idAt M))) (table mode)).reverse++Log.history previous old=_
  rw [row_original N hN v mode hm M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One later physical logger reversal gives the exact frozen record list, including
its one final false tag and retained caller suffix. No host reversal supplies output. -/
theorem reverse_original (N : Nat) (hN : 0<N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm : Matches N hN mode v) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      v)
    (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run R.code
      (2*(Log.rows (previous++[vertex N hN v ports hlen])).length+2)
      ⟨some .reverse,none,R.data [] []
        ((done mode (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data history) (false::out)⟩=
      some ⟨none,none,R.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex N hN v ports hlen])++out)⟩ := by
  rw [history_original N hN v mode hm M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- Real whole-source clock for caller-acquired padded numeric scope IDs. -/
theorem selected_timeBound (mode : SemiprimeD1StackBooleanEntry.Mode) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M) :
    timeBound mode (ports.map (Bank.idAt M))≤110*(ports.length+1)*(M+1)+210 := by
  have h:=SemiprimeD1StackBooleanRecordBounds.timeBound_le mode (ports.map (Bank.idAt M)) M
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;exact (Bank.id_length M i (hp i hi)).le)
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;rw [Bank.id_value M i (hp i hi)];exact (hp i hi).le)
  simpa only [List.length_map] using h
/-- Source execution and original forward-row semantics hold together, with only
the finite mode, acquired binary-ID vector and actual caller accumulators as data. -/
theorem source_run_original (N : Nat) (hN : 0<N)
    (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (hm : Matches N hN mode v) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      v)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound mode (ports.map (Bank.idAt M)),∃finish,
      C.run program t (initial mode (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
        (Log.history previous old) out)=some finish ∧
      finish=done mode (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data history=Log.history
        (previous++[vertex N hN v ports hlen]) old := by
  obtain ⟨t,ht,hr⟩:=source_run mode (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original N hN v mode hm M ports hp hlen previous old out⟩
end RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
