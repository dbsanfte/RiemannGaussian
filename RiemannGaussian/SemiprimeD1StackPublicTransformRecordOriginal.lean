/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformRecordBounds
import RiemannGaussian.SemiprimeD1StackPublicTransformTableOriginal
import RiemannGaussian.SemiprimeD1StackBooleanRecordOriginal
/-! # Entire original transform tensor and chronological old record bytes
The caller acquires the actual ordered numeric scope and descriptor index.
No assignment, table, native evaluator or verdict is supplied to the source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformRecordOriginal
open SemiprimeD1StackPublicTransformRecord SemiprimeD1StackPublicTransformRecordExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackPublicScaleFinite (selector)
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Only N and two singleton descriptor flags initialize the read-only template.
All acquired axes/roots/normalizers/vectors/guards/results and raw bits start empty. -/
theorem initial_template_only (bits : List Bool) (second inverse : Bool)
    (bank hist out : List Bool) (k : SemiprimeD1StackPublicTransform.Stack) :
    (initial bits second inverse bank hist out).data
      (G.tableStack (SemiprimeD1StackStaticTable.template k))=
      if k=SemiprimeD1StackPublicTransformTable.P.inputRole then bits else
      if k=SemiprimeD1StackPublicTransformTable.P.second then [second] else
      if k=SemiprimeD1StackPublicTransformTable.P.inverse then [inverse] else [] :=
  SemiprimeD1StackPublicTransformTableTrace.template_only bits second inverse k
/-- Same proof-side original transform vertex with the actual caller scope. -/
abbrev vertex :=SemiprimeD1StackBooleanRecordOriginal.vertex
section First
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (tr : SemiprimeMacroGraph.Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
  (M : Nat) (ports : List Nat) (hp : ∀q∈ports,q<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.first tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hp
/-- Exactly the complete original transform table and unchanged unary port order. -/
theorem row_first_original :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits false (selector tr) (ports.map (Bank.idAt M)))=
      SemiprimeD1StackVertexRecordStream.row
        (SemiprimeD1StackVertexReadExecution.portTape (vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape (vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen).table) := by
  have hs:=SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp
  have ht:=SemiprimeD1StackPublicTransformTableOriginal.table_first_original bits hc hN tr j
    (ports.map (Bank.idAt M)) (by simpa only [List.length_map] using hlen)
  rw [hs,ht]
  exact congrArg (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (SemiprimeD1StackBooleanRecordOriginal.tape_cast hlen.symm
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.first tr j)))).symm
/-- Literal actual row prepends exactly the unchanged old product-reader record. -/
theorem record_bytes_first_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits false (selector tr) (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen::rest) := by
  rw [row_first_original bits hc hN tr j M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- Appending one actual input row retains the chronological order of all old rows. -/
theorem history_first_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done bits false (selector tr) (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen]) old := by
  rw [history_row,row_first_original bits hc hN tr j M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One final actual logger reversal emits the exact forward old records and
one final false tag, without copying the accumulated tail at every node. -/
theorem reverse_first_original (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done bits false (selector tr) (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen])++out)⟩ := by
  rw [history_first_original bits hc hN tr j M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- The actual source execution and exact old chronological record hold together. -/
theorem source_run_first_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound bits false (selector tr) (ports.map (Bank.idAt M)),∃finish,
      SemiprimeD1StackCalls.run program t
        (initial bits false (selector tr) (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
          (Log.history previous old) out)=some finish ∧
      finish=done bits false (selector tr) (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen]) old := by
  obtain ⟨t,ht,hr⟩:=source_run bits false (selector tr) hc hN (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_first_original bits hc hN tr j M ports hp hlen previous old out⟩
omit hp in
/-- Each individual acquired coefficient is the exact original integer0/1. -/
theorem literal_first_original_coefficient
    (input : Fin (SemiprimeMacroGraph.arity (.first tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal []
        (SemiprimeD1StackStaticTableSpec.leafWords (T.answer bits false (selector tr)) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.first tr j) input).accepted
        then 1 else 0 :=
  SemiprimeD1StackPublicTransformTableOriginal.literal_first_original_coefficient bits hc hN tr j input
end First
section Second
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (tr : SemiprimeMacroGraph.Transform) (j : Fin (secondAxis (bitLength (bitValue bits))))
  (M : Nat) (ports : List Nat) (hp : ∀q∈ports,q<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.second tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hp
/-- Exactly the complete original transform table and unchanged unary port order. -/
theorem row_second_original :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits true (selector tr) (ports.map (Bank.idAt M)))=
      SemiprimeD1StackVertexRecordStream.row
        (SemiprimeD1StackVertexReadExecution.portTape (vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen).ports)
        (SemiprimeD1TensorTapeCodec.tape (vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen).table) := by
  have hs:=SemiprimeD1StackPortOrdinalStreamOriginal.selected_portTape M ports hp
  have ht:=SemiprimeD1StackPublicTransformTableOriginal.table_second_original bits hc hN tr j
    (ports.map (Bank.idAt M)) (by simpa only [List.length_map] using hlen)
  rw [hs,ht]
  exact congrArg (SemiprimeD1StackVertexRecordStream.row (SemiprimeD1StackVertexReadExecution.portTape ports))
    (SemiprimeD1StackBooleanRecordOriginal.tape_cast hlen.symm
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.second tr j)))).symm
/-- Literal actual row prepends exactly the unchanged old product-reader record. -/
theorem record_bytes_second_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits true (selector tr) (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen::rest) := by
  rw [row_second_original bits hc hN tr j M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStream.row_records _ rest
/-- Appending one actual input row retains the chronological order of all old rows. -/
theorem history_second_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done bits true (selector tr) (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen]) old := by
  rw [history_row,row_second_original bits hc hN tr j M ports hp hlen]
  simp only [Log.history,SemiprimeD1StackVertexRecordStreamExecution.rows_append,Log.rows,
    List.append_nil,List.reverse_append,List.append_assoc]
/-- One final actual logger reversal emits the exact forward old records and
one final false tag, without copying the accumulated tail at every node. -/
theorem reverse_second_original (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done bits true (selector tr) (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen])++out)⟩ := by
  rw [history_second_original bits hc hN tr j M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- The actual source execution and exact old chronological record hold together. -/
theorem source_run_second_original (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound bits true (selector tr) (ports.map (Bank.idAt M)),∃finish,
      SemiprimeD1StackCalls.run program t
        (initial bits true (selector tr) (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M)))
          (Log.history previous old) out)=some finish ∧
      finish=done bits true (selector tr) (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.second tr j)) ports hlen]) old := by
  obtain ⟨t,ht,hr⟩:=source_run bits true (selector tr) hc hN (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_second_original bits hc hN tr j M ports hp hlen previous old out⟩
omit hp in
/-- Each individual acquired coefficient is the exact original integer0/1. -/
theorem literal_second_original_coefficient
    (input : Fin (SemiprimeMacroGraph.arity (.second tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal []
        (SemiprimeD1StackStaticTableSpec.leafWords (T.answer bits true (selector tr)) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.second tr j) input).accepted
        then 1 else 0 :=
  SemiprimeD1StackPublicTransformTableOriginal.literal_second_original_coefficient bits hc hN tr j input
end Second
end RiemannGaussian.SemiprimeD1StackPublicTransformRecordOriginal
