/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicInputTableOriginal
import RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
/-! # Entire original input tensor and chronological old record bytes
The caller acquires the actual ordered numeric scope and descriptor index.
No assignment, table, native evaluator or verdict is supplied to the source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicInputRecordOriginal
open SemiprimeD1StackPublicInputRecord SemiprimeD1StackPublicInputRecordExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- The read-only template is ONLY original N and descriptor index bytes;
all raw assignments, metadata, caches, results and clock fields start empty. -/
theorem initial_template_only (bits indexWord bank hist out : List Bool) (k : SemiprimeD1StackPublicInput.Stack) :
    (initial bits indexWord bank hist out).data (G.tableStack (SemiprimeD1StackStaticTable.template k))=
      if k=.inl SemiprimeD1StackPublicInput.H.original then bits
      else if k=SemiprimeD1StackPublicInput.index then indexWord else [] :=
  SemiprimeD1StackPublicInputTableTrace.template_only bits indexWord k
/-- Same proof-side original input vertex with the caller's ordered numeric scope. -/
abbrev vertex :=SemiprimeD1StackBooleanRecordOriginal.vertex
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (side : Fin 2) (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
  (indexWord : List Bool) (hi : indexWord.length=i.val) (M : Nat) (ports : List Nat)
  (hp : ∀j∈ports,j<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.input side i):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hi hp
/-- Exactly the complete original input table and unchanged unary port order. -/
theorem row_original :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicInputTableExecution.table bits indexWord (ports.map (Bank.idAt M)))=
      SemiprimeD1StackVertexRecordStream.row
        (SemiprimeD1StackVertexReadExecution.portTape (vertex (bitValue bits) hN (.inl (.input side i)) ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape (vertex (bitValue bits) hN (.inl (.input side i)) ports hlen).table) := by
  have hs:=SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp
  have ht:=SemiprimeD1StackPublicInputTableOriginal.table_original bits hc hN side i indexWord hi
    (ports.map (Bank.idAt M)) (by simpa only [List.length_map] using hlen)
  rw [hs,ht]
  exact congrArg (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (SemiprimeD1StackBooleanRecordOriginal.tape_cast hlen.symm
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.input side i)))).symm
/-- Literal actual row prepends exactly the unchanged old product-reader record. -/
theorem record_bytes_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicInputTableExecution.table bits indexWord (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (bitValue bits) hN (.inl (.input side i)) ports hlen::rest) := by
  rw [row_original bits hc hN side i indexWord hi M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- Appending one actual input row retains the chronological order of all old rows. -/
theorem history_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done bits indexWord (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen]) old := by
  rw [history_row,row_original bits hc hN side i indexWord hi M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One final actual logger reversal emits the exact forward old records and
one final false tag, without copying the accumulated tail at every node. -/
theorem reverse_original (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done bits indexWord (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen])++out)⟩ := by
  rw [history_original bits hc hN side i indexWord hi M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- The actual source execution and exact old chronological record hold together. -/
theorem source_run_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound bits indexWord (ports.map (Bank.idAt M)),∃finish,
      SemiprimeD1StackCalls.run program t
        (initial bits indexWord (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
          (Log.history previous old) out)=some finish ∧
      finish=done bits indexWord (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen]) old := by
  have hb:bits≠[]:=by intro he;subst bits;exact (Nat.not_lt_zero _ hN).elim
  obtain ⟨t,ht,hr⟩:=source_run bits indexWord hb (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN side i indexWord hi M ports hp hlen previous old out⟩
omit hp in
/-- Each individual acquired coefficient is the exact original integer0/1. -/
theorem literal_original_coefficient
    (input : Fin (SemiprimeMacroGraph.arity (.input side i : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal []
        (SemiprimeD1StackStaticTableSpec.leafWords (T.answer bits indexWord) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.input side i) input).accepted
        then 1 else 0 :=
  SemiprimeD1StackPublicInputTableOriginal.literal_original_coefficient bits hc hN side i indexWord hi input
end RiemannGaussian.SemiprimeD1StackPublicInputRecordOriginal
