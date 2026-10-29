/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScaleDescriptorRecordBounds
/-! # Exact original scale rows from physically decoded original descriptors -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackScaleDescriptorRecordOriginal
open SemiprimeD1StackScaleDescriptorRecord
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1StackPublicScaleFinite (selector)
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Proof view of the six ACTUAL original scale descriptor fields. -/
def rawFields (bits : List Bool) (tr : SemiprimeMacroGraph.Transform) (stride frequency coord3 : List Bool) : Fin 6→List Bool :=
  ![bits,[true,true],List.replicate (SemiprimeD1VertexCatalogueEncoding.transformCode tr) true,stride,frequency,coord3]
/-- Same original scale node with the actual caller's ordered numeric port scope. -/
abbrev vertex :=SemiprimeD1StackPublicScaleRecordOriginal.vertex
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (tr : SemiprimeMacroGraph.Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
  (k : Fin (secondAxis (bitLength (bitValue bits)))) (M : Nat) (ports : List Nat) (hp : ∀q∈ports,q<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.scale tr j k):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hp
/-- The actually acquired whole row is the exact frozen original scale record. -/
theorem record_bytes_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicScaleTableExecution.table bits (unary j.val) (unary k.val) (selector tr) (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records (vertex (bitValue bits) hN (.inl (.scale tr j k)) ports hlen::rest) :=
  SemiprimeD1StackPublicScaleRecordOriginal.record_bytes_original bits hc hN tr j k M ports hp hlen rest
/-- Physical selector/template acquisition preserves exact chronological old-row order. -/
theorem history_original (coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done (rawFields bits tr (unary j.val) (unary k.val) coord3) (selector tr)
      (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.scale tr j k)) ports hlen]) old :=by
  change (done _ _ _ _ _).data
    (G.descriptorStack (SemiprimeD1StackDescriptorRecord.recordStack SemiprimeD1StackPublicScaleRecord.G.history))=_
  rw [component_done]
  exact SemiprimeD1StackPublicScaleRecordOriginal.history_original bits hc hN tr j k M ports hp hlen previous old out
/-- One later actual logger reversal emits precisely the old forward records and finalfalse. -/
theorem reverse_original (coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.scale tr j k)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done (rawFields bits tr (unary j.val) (unary k.val) coord3) (selector tr)
          (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.scale tr j k)) ports hlen])++out)⟩ :=by
  rw [history_original bits hc hN tr j k M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- ALL original scale directions/coordinates: real physical selector decode,
complete real metadata/table/scope/logger source and exact old chronological record. -/
theorem source_run_original (oldTemplate : Checker→List Bool) (coord3 oldStage oldInverse : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound oldTemplate (rawFields bits tr (unary j.val) (unary k.val) coord3) (selector tr)
      (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out,∃finish,
      SemiprimeD1StackCalls.run program t
        (initial oldTemplate (rawFields bits tr (unary j.val) (unary k.val) coord3) oldStage oldInverse
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) (Log.history previous old) out)=some finish ∧
      finish=done (rawFields bits tr (unary j.val) (unary k.val) coord3) (selector tr)
        (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.scale tr j k)) ports hlen]) old :=by
  let raw:=rawFields bits tr (unary j.val) (unary k.val) coord3
  have hj:raw 3=unary (raw 3).length:=by
    change List.replicate j.val true=List.replicate (List.replicate j.val true).length true
    rw [List.length_replicate]
  have hk:raw 4=unary (raw 4).length:=by
    change List.replicate k.val true=List.replicate (List.replicate k.val true).length true
    rw [List.length_replicate]
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate raw
    ⟨SemiprimeD1VertexCatalogueEncoding.transformCode tr,SemiprimeD1StackTransformSelectorsOriginal.transform_code_lt tr⟩
    rfl rfl hj hk hc hN (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out
  change t≤timeBound oldTemplate raw (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2)
    (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out at ht
  change SemiprimeD1StackCalls.run program t _=
    some (done raw (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2) _ _ _) at hr
  rw [SemiprimeD1StackTransformSelectorsOriginal.inverse_original] at ht hr
  exact ⟨t,ht,_,hr,rfl,history_original bits hc hN tr j k M ports hp hlen coord3 previous old out⟩
end RiemannGaussian.SemiprimeD1StackScaleDescriptorRecordOriginal
