/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBoundaryRecordBounds
import RiemannGaussian.SemiprimeD1StackVertexRecordStreamExecution
/-! # Exact original carry boundary record bytes in the original scope order
The acquired scope is a caller cache: routing is not computed by this join.
Every numeric ID is converted to the frozen unary port field, and the table is
the exact old initial/terminal reference in its unchanged local port order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBoundaryRecordOriginal
open SemiprimeD1StackBoundaryRecord SemiprimeD1StackBoundaryRecordExecution
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt id_value id_length)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- The two original public carry endpoints, with no runtime selector advice. -/
def endpoint (N : Nat) (terminal : Bool) : SemiprimePublicAcquiredExecution.PublicVertex N :=
  .inl (if terminal then .carryTerminal else .carryInitial)
/-- Changing only a table's type index leaves every original tape byte unchanged. -/
theorem tape_cast {m n : Nat} (h : m=n) (t : SemiprimeD1TensorTables.Table m) :
    SemiprimeD1TensorTapeCodec.tape (cast (congrArg SemiprimeD1TensorTables.Table h) t)=
      SemiprimeD1TensorTapeCodec.tape t := by
  cases h;rfl
/-- Proof-side vertex with the caller's exact ordered global occurrence scope and
the original complete boundary table; this constructor is never executed. -/
def vertex (N : Nat) (hN : 0<N) (terminal : Bool) (ports : List Nat)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity (endpoint N terminal)) :
    SemiprimeD1LeafCounter.Vertex :=
  ⟨ports,cast (congrArg SemiprimeD1TensorTables.Table hlen.symm)
    (SemiprimeD1BooleanRootTablesOriginal.reference N hN (endpoint N terminal))⟩
/-- The very same actual table is the exact INITIAL or TERMINAL old reference. -/
theorem table_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) :
    table bits=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (SemiprimeBitArithmetic.bitValue bits) hN
        (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal)) := by
  cases terminal with
  | false => exact SemiprimeD1StackZeroBoundaryTableBounds.initial_output bits hc hN
  | true => exact SemiprimeD1StackZeroBoundaryTableBounds.terminal_output bits hc hN
/-- Exact row bytes bind numeric IDs to unary global ports without a permutation. -/
theorem row_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal)) :
    R.row (S.result (ports.map (Bank.idAt M))) (table bits)=
      R.row (SemiprimeD1StackVertexReadExecution.portTape
        (vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape
          (vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen).table) := by
  rw [SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp,table_original bits hc hN terminal]
  exact congrArg (R.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (tape_cast hlen.symm (SemiprimeD1BooleanRootTablesOriginal.reference
      (SemiprimeBitArithmetic.bitValue bits) hN (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal))).symm
/-- Literal acquired row prepends exactly the frozen original product-reader record. -/
theorem record_bytes_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal))
    (rest : List SemiprimeD1LeafCounter.Vertex) :
    R.row (S.result (ports.map (Bank.idAt M))) (table bits)++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen::rest) := by
  rw [row_original bits hc hN terminal M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- The actual halt keeps every previous row in its original forward order. -/
theorem history_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal))
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done bits (ports.map (Bank.idAt M)) (Log.history previous old) out).data history=
      Log.history (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen]) old := by
  change (R.row (S.result (ports.map (Bank.idAt M))) (table bits)).reverse++Log.history previous old=_
  rw [row_original bits hc hN terminal M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One later physical logger reversal gives the exact frozen record list, including
its one final false tag and retained caller suffix. No host reversal supplies output. -/
theorem reverse_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal))
    (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run R.code
      (2*(Log.rows (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen])).length+2)
      ⟨some .reverse,none,R.data [] []
        ((done bits (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data history) (false::out)⟩=
      some ⟨none,none,R.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen])++out)⟩ := by
  rw [history_original bits hc hN terminal M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- Actual whole join clock for the padded acquired scope bank. Original N remains
binary; the only value-to-unary cost is bounded occurrence metadata. -/
theorem selected_timeBound (bits : List Bool) (M : Nat) (ports : List Nat) (hp : ∀i∈ports,i<M) :
    timeBound bits (ports.map (Bank.idAt M))≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
      61*2^(SemiprimeD1StackZeroBoundaryTable.cached bits).length+
      110*(ports.length+1)*(M+1)+20 := by
  have h:=SemiprimeD1StackBoundaryRecordBounds.timeBound_le bits (ports.map (Bank.idAt M)) M
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;exact (Bank.id_length M i (hp i hi)).le)
    (by intro w hw;obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw;rw [Bank.id_value M i (hp i hi)];exact (hp i hi).le)
  simpa only [List.length_map] using h
/-- Source execution and original forward-row semantics hold together, with only
original N, the acquired binary-ID vector and actual caller accumulators as data. -/
theorem source_run_original (bits : List Bool) (hb : bits≠[]) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) (terminal : Bool) (M : Nat) (ports : List Nat)
    (hp : ∀i∈ports,i<M)
    (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
      (endpoint (SemiprimeBitArithmetic.bitValue bits) terminal))
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound bits (ports.map (Bank.idAt M)),∃finish,
      C.run program t (initial bits (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
        (Log.history previous old) out)=some finish ∧
      finish=done bits (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data history=Log.history
        (previous++[vertex (SemiprimeBitArithmetic.bitValue bits) hN terminal ports hlen]) old := by
  obtain ⟨t,ht,hr⟩:=source_run bits hb (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN terminal M ports hp hlen previous old out⟩
end RiemannGaussian.SemiprimeD1StackBoundaryRecordOriginal
