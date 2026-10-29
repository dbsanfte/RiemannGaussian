/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordBounds
/-! # Exact original transform rows from physically decoded original descriptors -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordOriginal
open SemiprimeD1StackTransformDescriptorRecord
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1StackPublicScaleFinite (selector)
namespace Bank
export SemiprimeD1OrdinalBankSpec (idAt)
end Bank
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (rows history)
end Log
/-- Proof view of the actual six original transform descriptor words. -/
def rawFields (bits : List Bool) (second : Bool) (tr : SemiprimeMacroGraph.Transform)
    (coord1 coord2 coord3 : List Bool) : Fin 6→List Bool :=
  ![bits,List.replicate (tagCode second).val true,
    List.replicate (SemiprimeD1VertexCatalogueEncoding.transformCode tr) true,coord1,coord2,coord3]
/-- The old transform node in the actual caller's ordered numeric scope. -/
abbrev vertex :=SemiprimeD1StackPublicTransformRecordOriginal.vertex
section First
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (tr : SemiprimeMacroGraph.Transform) (j : Fin (firstAxis (bitLength (bitValue bits))))
  (M : Nat) (ports : List Nat) (hp : ∀q∈ports,q<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.first tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hp
/-- The actually acquired whole row is the exact frozen original transform record. -/
theorem record_bytes_first_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits false (selector tr) (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records (vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen::rest) :=
  SemiprimeD1StackPublicTransformRecordOriginal.record_bytes_first_original bits hc hN tr j M ports hp hlen rest
/-- Physical selector/template acquisition preserves exact chronological old-row order. -/
theorem history_first_original (coord2 coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done (rawFields bits false tr (unary j.val) coord2 coord3) false (selector tr)
      (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen]) old :=by
  change (done _ _ _ _ _ _).data
    (G.descriptorStack (SemiprimeD1StackDescriptorRecord.recordStack SemiprimeD1StackPublicTransformRecord.G.history))=_
  rw [component_done]
  exact SemiprimeD1StackPublicTransformRecordOriginal.history_first_original bits hc hN tr j M ports hp hlen previous old out
/-- One later actual logger reversal emits precisely the old forward records and finalfalse. -/
theorem reverse_first_original (coord2 coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done (rawFields bits false tr (unary j.val) coord2 coord3) false (selector tr)
          (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen])++out)⟩ :=by
  rw [history_first_original bits hc hN tr j M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- ALL original transform directions/coordinates: real physical selector decode,
complete real metadata/table/scope/logger source and exact old chronological record. -/
theorem source_run_first_original (oldTemplate : Checker→List Bool) (coord2 coord3 oldStage oldInverse : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound oldTemplate (rawFields bits false tr (unary j.val) coord2 coord3) false (selector tr)
      (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out,∃finish,
      SemiprimeD1StackCalls.run program t
        (initial oldTemplate (rawFields bits false tr (unary j.val) coord2 coord3) oldStage oldInverse
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) (Log.history previous old) out)=some finish ∧
      finish=done (rawFields bits false tr (unary j.val) coord2 coord3) false (selector tr)
        (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.first tr j)) ports hlen]) old :=by
  let raw:=rawFields bits false tr (unary j.val) coord2 coord3
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate raw false 
    ⟨SemiprimeD1VertexCatalogueEncoding.transformCode tr,SemiprimeD1StackTransformSelectorsOriginal.transform_code_lt tr⟩
    rfl rfl hc hN (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out
  change t≤timeBound oldTemplate raw false (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2)
    (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out at ht
  change SemiprimeD1StackCalls.run program t _=
    some (done raw false (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2) _ _ _) at hr
  rw [SemiprimeD1StackTransformSelectorsOriginal.inverse_original] at ht hr
  exact ⟨t,ht,_,hr,rfl,history_first_original bits hc hN tr j M ports hp hlen coord2 coord3 previous old out⟩
end First

section Second
variable (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
  (tr : SemiprimeMacroGraph.Transform) (k : Fin (secondAxis (bitLength (bitValue bits))))
  (M : Nat) (ports : List Nat) (hp : ∀q∈ports,q<M)
  (hlen : ports.length=SemiprimeMacroGraph.subdividedArity
    (.inl (.second tr k):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)))
include hc hp
/-- The actually acquired whole row is the exact frozen original transform record. -/
theorem record_bytes_second_original (rest : List SemiprimeD1LeafCounter.Vertex) :
    SemiprimeD1StackVertexRecordStream.row
      (SemiprimeD1StackPortOrdinalStream.result (ports.map (Bank.idAt M)))
      (SemiprimeD1StackPublicTransformTableExecution.table bits true (selector tr) (ports.map (Bank.idAt M)))++
      SemiprimeD1StackVertexProduct.records rest=
      SemiprimeD1StackVertexProduct.records (vertex (bitValue bits) hN (.inl (.second tr k)) ports hlen::rest) :=
  SemiprimeD1StackPublicTransformRecordOriginal.record_bytes_second_original bits hc hN tr k M ports hp hlen rest
/-- Physical selector/template acquisition preserves exact chronological old-row order. -/
theorem history_second_original (coord2 coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    (done (rawFields bits true tr (unary k.val) coord2 coord3) true (selector tr)
      (ports.map (Bank.idAt M)) (Log.history previous old) out).data G.history=
      Log.history (previous++[vertex (bitValue bits) hN (.inl (.second tr k)) ports hlen]) old :=by
  change (done _ _ _ _ _ _).data
    (G.descriptorStack (SemiprimeD1StackDescriptorRecord.recordStack SemiprimeD1StackPublicTransformRecord.G.history))=_
  rw [component_done]
  exact SemiprimeD1StackPublicTransformRecordOriginal.history_second_original bits hc hN tr k M ports hp hlen previous old out
/-- One later actual logger reversal emits precisely the old forward records and finalfalse. -/
theorem reverse_second_original (coord2 coord3 : List Bool) (previous : List SemiprimeD1LeafCounter.Vertex) (out : List Bool) :
    SemiprimeD1StackBytecode.run SemiprimeD1StackVertexRecordStream.code
      (2*(Log.rows (previous++[vertex (bitValue bits) hN (.inl (.second tr k)) ports hlen])).length+2)
      ⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] []
        ((done (rawFields bits true tr (unary k.val) coord2 coord3) true (selector tr)
          (ports.map (Bank.idAt M)) (Log.history previous []) (false::out)).data G.history) (false::out)⟩=
      some ⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] []
        (SemiprimeD1StackVertexProduct.records
          (previous++[vertex (bitValue bits) hN (.inl (.second tr k)) ports hlen])++out)⟩ :=by
  rw [history_second_original bits hc hN tr k M ports hp hlen]
  exact SemiprimeD1StackVertexRecordStreamExecution.reverse_original _ out
/-- ALL original transform directions/coordinates: real physical selector decode,
complete real metadata/table/scope/logger source and exact old chronological record. -/
theorem source_run_second_original (oldTemplate : Checker→List Bool) (coord2 coord3 oldStage oldInverse : List Bool)
    (previous : List SemiprimeD1LeafCounter.Vertex) (old out : List Bool) :
    ∃t≤timeBound oldTemplate (rawFields bits true tr (unary k.val) coord2 coord3) true (selector tr)
      (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out,∃finish,
      SemiprimeD1StackCalls.run program t
        (initial oldTemplate (rawFields bits true tr (unary k.val) coord2 coord3) oldStage oldInverse
          (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (Bank.idAt M))) (Log.history previous old) out)=some finish ∧
      finish=done (rawFields bits true tr (unary k.val) coord2 coord3) true (selector tr)
        (ports.map (Bank.idAt M)) (Log.history previous old) out ∧
      finish.data G.history=Log.history
        (previous++[vertex (bitValue bits) hN (.inl (.second tr k)) ports hlen]) old :=by
  let raw:=rawFields bits true tr (unary k.val) coord2 coord3
  obtain ⟨t,ht,hr⟩:=source_run oldTemplate raw true 
    ⟨SemiprimeD1VertexCatalogueEncoding.transformCode tr,SemiprimeD1StackTransformSelectorsOriginal.transform_code_lt tr⟩
    rfl rfl hc hN (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out
  change t≤timeBound oldTemplate raw true (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2)
    (ports.map (Bank.idAt M)) oldStage oldInverse (Log.history previous old) out at ht
  change SemiprimeD1StackCalls.run program t _=
    some (done raw true (SemiprimeD1VertexCatalogueEncoding.transformCode tr==2) _ _ _) at hr
  rw [SemiprimeD1StackTransformSelectorsOriginal.inverse_original] at ht hr
  exact ⟨t,ht,_,hr,rfl,history_second_original bits hc hN tr k M ports hp hlen coord2 coord3 previous old out⟩
end Second
end RiemannGaussian.SemiprimeD1StackTransformDescriptorRecordOriginal
