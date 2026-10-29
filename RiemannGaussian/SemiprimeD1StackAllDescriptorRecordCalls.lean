/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordComponents
/-! # Closed concrete complete family traces in the same1263-role dispatcher -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCalls
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordWiring
open SemiprimeD1StackAllDescriptorRecordComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Complete actual input row call, with no template/checker/clock supplier. -/
theorem input_call (raw:Fin 6→List Bool) (hb:raw 0≠[]) (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackInputDescriptorRecordExecution.timeBound (fun _=>[]) raw words hist out+1,
      Runs program t (.inl (.record .input)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after inputStack (SemiprimeD1StackInputDescriptorRecordExecution.done raw words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackInputDescriptorRecordExecution.source_run (fun _=>[]) raw hb words hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call inputStack inputLabel inputStack_injective I.program (.inl .start) .input (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (input_initial raw (vectorBits words) hist out) hr
/-- Complete actual carry row call, starting with an empty private template. -/
theorem carry_call (raw:Fin 6→List Bool) (hb:raw 0≠[]) (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackCarryDescriptorRecordExecution.timeBound (fun _=>[]) raw words hist out+1,
      Runs program t (.inl (.record .carry)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after carryStack (SemiprimeD1StackCarryDescriptorRecordExecution.done raw words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackCarryDescriptorRecordExecution.source_run (fun _=>[]) raw hb words hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call carryStack carryLabel carryStack_injective A.program (.inl .start) .carry (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (carry_initial raw (vectorBits words) hist out) hr
/-- Actual raw transform code is physically decoded before scale's real whole row source. -/
theorem scale_call (raw:Fin 6→List Bool) (tr:Fin 3)
    (htag:raw 1=[true,true]) (htr:raw 2=List.replicate tr.val true)
    (hj:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (hk:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackScaleDescriptorRecord.timeBound (fun _=>[]) raw (tr.val==2) words [] [] hist out+1,
      Runs program t (.inl (.record .scale)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after scaleStack (SemiprimeD1StackScaleDescriptorRecord.done raw (tr.val==2) words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackScaleDescriptorRecord.source_run (fun _=>[]) raw tr htag htr hj hk hc hN words [] [] hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call scaleStack scaleLabel scaleStack_injective S.program (.inl .start) .scale (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (scale_initial raw (vectorBits words) hist out) hr
/-- Both physical flags are decoded before the actual first/second entire transform row source. -/
theorem transform_call (raw:Fin 6→List Bool) (second:Bool) (tr:Fin 3)
    (htag:raw 1=List.replicate (SemiprimeD1StackTransformDescriptorRecord.tagCode second).val true)
    (htr:raw 2=List.replicate tr.val true)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackTransformDescriptorRecord.timeBound (fun _=>[]) raw second (tr.val==2) words [] [] hist out+1,
      Runs program t (.inl (.record .transform)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after transformStack (SemiprimeD1StackTransformDescriptorRecord.done raw second (tr.val==2) words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackTransformDescriptorRecord.source_run (fun _=>[]) raw second tr htag htr hc hN words [] [] hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call transformStack transformLabel transformStack_injective T.program (.inl .start) .transform (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (transform_initial raw (vectorBits words) hist out) hr
/-- Actual N-only full product table source, serializer and consuming logger are called unchanged. -/
theorem product_call (raw:Fin 6→List Bool) (hb:raw 0≠[]) (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackProductRecordExecution.timeBound (raw 0) words+1,
      Runs program t (.inl (.record .product)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after productStack (SemiprimeD1StackProductRecord.done (raw 0) words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductRecordExecution.source_run (raw 0) hb words hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call productStack productLabel productStack_injective P.program (.inl .start) .product (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (product_initial raw (vectorBits words) hist out) hr
/-- Both endpoint tags call the same unchanged actual N-only complete boundary source. -/
theorem boundary_call (raw:Fin 6→List Bool) (hb:raw 0≠[]) (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackBoundaryRecordExecution.timeBound (raw 0) words+1,
      Runs program t (.inl (.record .boundary)) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after boundaryStack (SemiprimeD1StackBoundaryRecord.done (raw 0) words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBoundaryRecordExecution.source_run (raw 0) hb words hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call boundaryStack boundaryLabel boundaryStack_injective Z.program (.inl .start) .boundary (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (boundary_initial raw (vectorBits words) hist out) hr
/-- All ten Boolean/equality tags execute a literal complete Boolean table source. -/
theorem boolean_call (mode:SemiprimeD1StackBooleanEntry.Mode)
    (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∃t≤SemiprimeD1StackBooleanRecordExecution.timeBound mode words+1,
      Runs program t (.inl (.record (.boolean mode))) (cleanData raw (vectorBits words) hist out) (.inl (.clear 0))
        (after booleanStack (SemiprimeD1StackBooleanRecord.done mode words hist out).data
          (cleanData raw (vectorBits words) hist out)) :=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackBooleanRecordExecution.source_run mode words hist out
  refine ⟨t+1,by omega,?_⟩
  exact component_call booleanStack booleanLabel booleanStack_injective B.program (.inl (.start mode)) (.boolean mode) (fun _=>rfl) rfl
    t _ _ _ rfl rfl rfl rfl (boolean_initial mode raw (vectorBits words) hist out) hr
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCalls
