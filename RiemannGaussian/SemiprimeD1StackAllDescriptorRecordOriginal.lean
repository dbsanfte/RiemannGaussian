/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordBounds
import RiemannGaussian.SemiprimeD1EdgeCatalogueEncoding
/-! # Every original eighteen-tag descriptor and exact old chronological record -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordOriginal
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordSpec
open SemiprimeD1StackAllDescriptorRecordExecution SemiprimeMacroGraph
open SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
namespace E
export SemiprimeD1EdgeCatalogueEncoding (vertex)
end E
namespace Log
export SemiprimeD1StackVertexRecordStreamExecution (history)
end Log
/-- Exact six acquired words: original binary N followed by all five physically
parsed original catalogue fields. This is a specification, never executed advice. -/
def rawFields {r t digits:Nat} (bits:List Bool) (v:SubdividedVertex r t digits) : Fin 6→List Bool :=
  ![bits,E.vertex v 0,E.vertex v 1,E.vertex v 2,E.vertex v 3,E.vertex v 4]
/-- Literal original constructor position; actual program obtains it by paid pops. -/
def originalCode {r t digits:Nat} : SubdividedVertex r t digits→Fin 18
  | .inl (.input _ _)=>0 | .inl (.first _ _)=>1 | .inl (.scale _ _ _)=>2
  | .inl (.second _ _)=>3 | .inl (.product _)=>4 | .inl .carryInitial=>5
  | .inl (.carry _)=>6 | .inl .carryTerminal=>7 | .inl (.orGate _ _)=>8 | .inl (.inputCheck _)=>9
  | .inr (.inl (.input _ _,_))=>10 | .inr (.inl (.first _ _ _,_))=>11
  | .inr (.inl (.twiddle _ _ _,_))=>12 | .inr (.inl (.second _ _ _,_))=>13
  | .inr (.inl (.product _,_))=>14 | .inr (.inl (.carry _,_))=>15
  | .inr (.inr (.digit _ _))=>16 | .inr (.inr (.orOut _ _))=>17
/-- Original binary N is retained verbatim in actual source field zero. -/
theorem raw_binaryN {r t digits:Nat} (bits:List Bool) (v:SubdividedVertex r t digits) : rawFields bits v 0=bits :=rfl
/-- Every original tag and coordinate has the canonical physically emitted true-marker word. -/
theorem raw_canonical {r t digits:Nat} (bits:List Bool) (v:SubdividedVertex r t digits) :
    rawFields bits v 1=List.replicate (originalCode v).val true ∧
    rawFields bits v 2=unary (rawFields bits v 2).length ∧
    rawFields bits v 3=unary (rawFields bits v 3).length ∧
    rawFields bits v 4=unary (rawFields bits v 4).length :=by
  cases v with
  | inl v=>cases v <;> simp [rawFields,originalCode,SemiprimeD1EdgeCatalogueEncoding.vertex,
      SemiprimeD1EdgeCatalogueEncoding.arithmetic,SemiprimeD1EdgeCatalogueEncoding.fields,
      SemiprimeD1VertexCatalogueModes.code,unary]
  | inr signal=>
    rcases signal with ⟨word,bit⟩|flag
    · cases word <;> simp [rawFields,originalCode,SemiprimeD1EdgeCatalogueEncoding.vertex,
        SemiprimeD1EdgeCatalogueEncoding.bit,SemiprimeD1EdgeCatalogueEncoding.fields,
        SemiprimeD1VertexCatalogueModes.code,unary]
    · cases flag <;> simp [rawFields,originalCode,SemiprimeD1EdgeCatalogueEncoding.vertex,
        SemiprimeD1EdgeCatalogueEncoding.bit,SemiprimeD1EdgeCatalogueEncoding.fields,
        SemiprimeD1VertexCatalogueModes.code,unary]
/-- Original transform fields contain exactly one of the three literal bounded codes. -/
theorem raw_transform_bound {r t digits:Nat} (bits:List Bool) (v:SubdividedVertex r t digits) :
    ((originalCode v).val=1∨(originalCode v).val=2∨(originalCode v).val=3)→
      (rawFields bits v 2).length<3 :=by
  cases v with
  | inl v=>
    cases v <;> simp [originalCode,rawFields,SemiprimeD1EdgeCatalogueEncoding.vertex,
      SemiprimeD1EdgeCatalogueEncoding.arithmetic,SemiprimeD1EdgeCatalogueEncoding.fields,
      SemiprimeD1StackTransformSelectorsOriginal.transform_code_lt]
  | inr signal=>
    rcases signal with ⟨word,bit⟩|flag
    · cases word <;> simp [originalCode]
    · cases flag <;> simp [originalCode]
/-- The old tensor vertex uses the original complete table and the caller's
unchanged ordered numeric occurrence scope. It is proof-side only. -/
abbrev vertex :=SemiprimeD1StackBooleanRecordOriginal.vertex
/-- All original arithmetic and Boolean/equality tags append the EXACT old row
while retaining every previous row in its original chronological order. -/
theorem history_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (v:SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)) (M:Nat) (ports:List Nat)
    (hp:∀i∈ports,i<M) (hlen:ports.length=subdividedArity v)
    (previous:List SemiprimeD1LeafCounter.Vertex) (old out:List Bool) :
    nextHistory (originalCode v) (rawFields bits v) (ports.map (SemiprimeD1OrdinalBankSpec.idAt M))
      (Log.history previous old) out=Log.history (previous++[vertex (bitValue bits) hN v ports hlen]) old :=by
  cases v with
  | inl v=>
    cases v with
    | input side i=>
      change (SemiprimeD1StackInputDescriptorRecordExecution.done
        (SemiprimeD1StackInputDescriptorRecord.fields bits [] (unary side.val) (unary i.val) [] [])
        _ _ _).data SemiprimeD1StackDescriptorRecord.history=_
      exact SemiprimeD1StackInputDescriptorRecordOriginal.history_original bits hc hN side i (unary i.val)
        (by simp only [unary,List.length_replicate]) M ports hp hlen [] (unary side.val) [] [] previous old out
    | first tr j=>
      change (SemiprimeD1StackTransformDescriptorRecord.done
        (SemiprimeD1StackTransformDescriptorRecordOriginal.rawFields bits false tr (unary j.val) [] []) false
        ((List.replicate (SemiprimeD1VertexCatalogueEncoding.transformCode tr) true).length==2) _ _ _).data
          SemiprimeD1StackSelectedDescriptorRecord.history=_
      rw [List.length_replicate,SemiprimeD1StackTransformSelectorsOriginal.inverse_original]
      exact SemiprimeD1StackTransformDescriptorRecordOriginal.history_first_original bits hc hN tr j M ports hp hlen [] [] previous old out
    | scale tr j k=>
      change (SemiprimeD1StackScaleDescriptorRecord.done
        (SemiprimeD1StackScaleDescriptorRecordOriginal.rawFields bits tr (unary j.val) (unary k.val) [])
        ((List.replicate (SemiprimeD1VertexCatalogueEncoding.transformCode tr) true).length==2) _ _ _).data
          SemiprimeD1StackSelectedDescriptorRecord.history=_
      rw [List.length_replicate,SemiprimeD1StackTransformSelectorsOriginal.inverse_original]
      exact SemiprimeD1StackScaleDescriptorRecordOriginal.history_original bits hc hN tr j k M ports hp hlen [] previous old out
    | second tr k=>
      change (SemiprimeD1StackTransformDescriptorRecord.done
        (SemiprimeD1StackTransformDescriptorRecordOriginal.rawFields bits true tr (unary k.val) [] []) true
        ((List.replicate (SemiprimeD1VertexCatalogueEncoding.transformCode tr) true).length==2) _ _ _).data
          SemiprimeD1StackSelectedDescriptorRecord.history=_
      rw [List.length_replicate,SemiprimeD1StackTransformSelectorsOriginal.inverse_original]
      exact SemiprimeD1StackTransformDescriptorRecordOriginal.history_second_original bits hc hN tr k M ports hp hlen [] [] previous old out
    | product i=>exact SemiprimeD1StackProductRecordOriginal.history_original bits hc hN i M ports hp hlen previous old out
    | carryInitial=>exact SemiprimeD1StackBoundaryRecordOriginal.history_original bits hc hN false M ports hp hlen previous old out
    | carry i=>
      change (SemiprimeD1StackCarryDescriptorRecordExecution.done
        (SemiprimeD1StackCarryDescriptorRecord.fields bits (List.replicate 6 true) (unary i.val) [] [] [])
        _ _ _).data SemiprimeD1StackDescriptorRecord.history=_
      exact SemiprimeD1StackCarryDescriptorRecordOriginal.history_original bits hc hN i (unary i.val)
        (by simp only [unary,List.length_replicate]) M ports hp hlen (List.replicate 6 true) [] [] [] previous old out
    | carryTerminal=>exact SemiprimeD1StackBoundaryRecordOriginal.history_original bits hc hN true M ports hp hlen previous old out
    | orGate side i=>
      exact SemiprimeD1StackBooleanRecordOriginal.history_original (bitValue bits) hN (.inl (.orGate side i))
        .orGate (SemiprimeD1StackBooleanRecordOriginal.matches_or _ _ side i) M ports hp hlen previous old out
    | inputCheck side=>
      exact SemiprimeD1StackBooleanRecordOriginal.history_original (bitValue bits) hN (.inl (.inputCheck side))
        .inputCheck (SemiprimeD1StackBooleanRecordOriginal.matches_input _ _ side) M ports hp hlen previous old out
  | inr signal=>
    have hf:family (originalCode (.inr signal))=.boolean .equality:=by
      rcases signal with ⟨word,bit⟩|flag
      · cases word <;> rfl
      · cases flag <;> rfl
    simp only [nextHistory,hf]
    exact SemiprimeD1StackBooleanRecordOriginal.history_original (bitValue bits) hN (.inr signal)
      .equality (SemiprimeD1StackBooleanRecordOriginal.matches_equality _ _ signal) M ports hp hlen previous old out
/-- Full actual source trace for EVERY original vertex, with exact old row/order,
all private roles cleared and the entire prepared binary input/descriptor/scope retained. -/
theorem source_run_original (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (v:SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits)) (M:Nat) (ports:List Nat)
    (hp:∀i∈ports,i<M) (hlen:ports.length=subdividedArity v)
    (previous:List SemiprimeD1LeafCounter.Vertex) (old out:List Bool) :
    ∃t≤ timeBound (originalCode v) (rawFields bits v) (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)) (Log.history previous old) out,
      C.run program t (initial (rawFields bits v) (SemiprimeD1TensorTapeCodec.vectorBits
        (ports.map (SemiprimeD1OrdinalBankSpec.idAt M))) (Log.history previous old) out)=
      some ⟨none,none,none,cleanData (rawFields bits v) (SemiprimeD1TensorTapeCodec.vectorBits
        (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)))
          (Log.history (previous++[vertex (bitValue bits) hN v ports hlen]) old) out,[]⟩ :=by
  obtain ⟨htag,h2,h3,h4⟩:=raw_canonical bits v
  obtain ⟨t,ht,hr⟩:=source_run (originalCode v) (rawFields bits v) htag h2 h3 h4 (raw_transform_bound bits v)
    hc hN (ports.map (SemiprimeD1OrdinalBankSpec.idAt M)) (Log.history previous old) out
  refine ⟨t,ht,?_⟩
  simpa only [done,history_original bits hc hN v M ports hp hlen previous old out] using hr
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordOriginal
