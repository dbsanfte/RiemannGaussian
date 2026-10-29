/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDescriptorRecordBounds
/-! # Exact old input row from the actual retained six-field descriptor
The N and descriptor/scope acquisitions are explicit upstream caller work.
This actual loader consumes their physical bytes, constructs no advised cache,
and returns the entire original row in unchanged chronological port order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackInputDescriptorRecordOriginal
open SemiprimeD1StackInputDescriptorRecord SemiprimeD1StackInputDescriptorRecordExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Exact old input vertex with the caller's unchanged ordered numeric scope. -/
abbrev vertex :=SemiprimeD1StackPublicInputRecordOriginal.vertex
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (side : Fin 2) (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
  (indexWord : List Bool) (hi : indexWord.length=i.val) (M : Nat) (ports : List Nat)
  (hp : ∀j∈ports,j<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.input side i):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hi hp
/-- Actual newly loaded input row bytes are exactly the frozen entire old input
record, including complete original tensor framing and unary numeric ports. -/
theorem record_bytes_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicInputTableExecution.table bits indexWord (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records
        (vertex (bitValue bits) hN (.inl (.input side i)) ports hlen::rest) :=
  SemiprimeD1StackPublicInputRecordOriginal.record_bytes_original bits hc hN side i indexWord hi M ports hp hlen rest
/-- Actual physical descriptor initialization followed by the actual record
call preserves every previous row in its original chronological order. -/
theorem history_original (tag coord0 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done (fields bits tag coord0 indexWord coord2 coord3) (ports.map (Bank.idAt M))
      (Log.history previous old) out).data D.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen]) old := by
  change (done _ _ _ _).data (D.recordStack SemiprimeD1StackPublicInputRecord.G.history)=_
  rw [component_done]
  exact SemiprimeD1StackPublicInputRecordOriginal.history_original bits hc hN side i indexWord hi M ports hp hlen previous old out
/-- One final actual logger reversal emits exactly the forward old record list
and final false tag, retaining the caller's final output suffix. -/
theorem reverse_original (tag coord0 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done (fields bits tag coord0 indexWord coord2 coord3) (ports.map (Bank.idAt M))
          (Log.history previous []) (false::out)).data D.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen])++out)⟩ := by
  rw [history_original bits hc hN side i indexWord hi M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- Complete real source trace and exact old chronological record, from ONLY
actual six acquired fields, acquired numeric scope, caller words and erased dirty template. -/
theorem source_run_original (oldTemplate : Checker→List Bool) (tag coord0 coord2 coord3 : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound oldTemplate (fields bits tag coord0 indexWord coord2 coord3)
      (ports.map (Bank.idAt M)) (Log.history previous old) out,∃finish,
      SemiprimeD1StackCalls.run program t
        (initial oldTemplate (fields bits tag coord0 indexWord coord2 coord3)
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) (Log.history previous old) out)=some finish ∧
      finish=done (fields bits tag coord0 indexWord coord2 coord3) (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data D.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.input side i)) ports hlen]) old := by
  have hb:bits≠[]:=by intro he;subst bits;exact (Nat.not_lt_zero _ hN).elim
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate (fields bits tag coord0 indexWord coord2 coord3) hb
    (ports.map (Bank.idAt M)) (Log.history previous old) out
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN side i indexWord hi M ports hp hlen tag coord0 coord2 coord3 previous old out⟩
end RiemannGaussian.SemiprimeD1StackInputDescriptorRecordOriginal
