/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordResults
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCleanup
/-! # Proof-side exact component result and complete dispatcher own clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordSpec
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordComponents
open SemiprimeD1StackAllDescriptorRecordResults SemiprimeD1StackAllDescriptorRecordCleanup
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Mathematical name for the literal dispatch; never an input or program parameter. -/
def family (code:Fin 18) : Family :=
  if code.val=0 then .input else if code.val=1 then .transform else if code.val=2 then .scale
  else if code.val=3 then .transform else if code.val=4 then .product else if code.val=5 then .boundary
  else if code.val=6 then .carry else if code.val=7 then .boundary else if code.val=8 then .boolean .orGate
  else if code.val=9 then .boolean .inputCheck else .boolean .equality
/-- The physical decoder targets exactly this fixed literal family entry. -/
theorem dispatch_family (code:Fin 18) : dispatch code=.inl (.record (family code)) :=rfl
/-- Complete actual component source clock, including the outer physical call. -/
def componentClock (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) : Nat :=
  (match family code with
  | .input=>SemiprimeD1StackInputDescriptorRecordExecution.timeBound (fun _=>[]) raw words hist out
  | .carry=>SemiprimeD1StackCarryDescriptorRecordExecution.timeBound (fun _=>[]) raw words hist out
  | .scale=>SemiprimeD1StackScaleDescriptorRecord.timeBound (fun _=>[]) raw ((raw 2).length==2) words [] [] hist out
  | .transform=>SemiprimeD1StackTransformDescriptorRecord.timeBound (fun _=>[]) raw (code.val==3) ((raw 2).length==2) words [] [] hist out
  | .product=>SemiprimeD1StackProductRecordExecution.timeBound (raw 0) words
  | .boundary=>SemiprimeD1StackBoundaryRecordExecution.timeBound (raw 0) words
  | .boolean mode=>SemiprimeD1StackBooleanRecordExecution.timeBound mode words
)+1
/-- Mathematical exact store after the actual component return, retaining every untouched word. -/
noncomputable def afterComponent (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) : Stack→List Bool :=
  match family code with
  | .input=>after inputStack (SemiprimeD1StackInputDescriptorRecordExecution.done raw words hist out).data (cleanData raw (vectorBits words) hist out)
  | .carry=>after carryStack (SemiprimeD1StackCarryDescriptorRecordExecution.done raw words hist out).data (cleanData raw (vectorBits words) hist out)
  | .scale=>after scaleStack (SemiprimeD1StackScaleDescriptorRecord.done raw ((raw 2).length==2) words hist out).data (cleanData raw (vectorBits words) hist out)
  | .transform=>after transformStack (SemiprimeD1StackTransformDescriptorRecord.done raw (code.val==3) ((raw 2).length==2) words hist out).data (cleanData raw (vectorBits words) hist out)
  | .product=>after productStack (SemiprimeD1StackProductRecord.done (raw 0) words hist out).data (cleanData raw (vectorBits words) hist out)
  | .boundary=>after boundaryStack (SemiprimeD1StackBoundaryRecord.done (raw 0) words hist out).data (cleanData raw (vectorBits words) hist out)
  | .boolean mode=>after booleanStack (SemiprimeD1StackBooleanRecord.done mode words hist out).data (cleanData raw (vectorBits words) hist out)
/-- Exact chronological reverse history resulting from the actual full component. -/
def nextHistory (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) : List Bool :=
  match family code with
  | .input=>(SemiprimeD1StackInputDescriptorRecordExecution.done raw words hist out).data SemiprimeD1StackDescriptorRecord.history
  | .carry=>(SemiprimeD1StackCarryDescriptorRecordExecution.done raw words hist out).data SemiprimeD1StackDescriptorRecord.history
  | .scale=>(SemiprimeD1StackScaleDescriptorRecord.done raw ((raw 2).length==2) words hist out).data SemiprimeD1StackSelectedDescriptorRecord.history
  | .transform=>(SemiprimeD1StackTransformDescriptorRecord.done raw (code.val==3) ((raw 2).length==2) words hist out).data SemiprimeD1StackSelectedDescriptorRecord.history
  | .product=>(SemiprimeD1StackProductRecord.done (raw 0) words hist out).data SemiprimeD1StackProductRecord.history
  | .boundary=>(SemiprimeD1StackBoundaryRecord.done (raw 0) words hist out).data SemiprimeD1StackBoundaryRecord.history
  | .boolean mode=>(SemiprimeD1StackBooleanRecord.done mode words hist out).data SemiprimeD1StackBooleanRecord.history
/-- All common fields retain their actual bytes, with the actual appended row history. -/
theorem afterComponent_common (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) :
    ∀c,afterComponent code raw words hist out (.inl c)=commonData raw (vectorBits words)
      (nextHistory code raw words hist out) out c :=by
  cases h:family code with
  | input=>simpa only [afterComponent,nextHistory,h] using input_common raw words hist out
  | carry=>simpa only [afterComponent,nextHistory,h] using carry_common raw words hist out
  | scale=>simpa only [afterComponent,nextHistory,h] using scale_common raw _ words hist out
  | transform=>simpa only [afterComponent,nextHistory,h] using transform_common raw _ _ words hist out
  | product=>simpa only [afterComponent,nextHistory,h] using product_common raw words hist out
  | boundary=>simpa only [afterComponent,nextHistory,h] using boundary_common raw words hist out
  | boolean mode=>simpa only [afterComponent,nextHistory,h] using boolean_common mode raw words hist out
/-- Exact actual final state: all1252 private/shadow words cleared, original
N/descriptor/scope bytes retained, history in unchanged chronological order. -/
def done (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) : C.State Stack Label :=
  ⟨none,none,none,cleanData raw (vectorBits words) (nextHistory code raw words hist out) out,[]⟩
/-- One complete source clock: real tag copy, all marker pops, actual component,
every actual private drain/EOF, final jump and halt. No clock belongs to the program. -/
def timeBound (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (hist out:List Bool) : Nat :=
  6*code.val+5+componentClock code raw words hist out+
    1252*(1263*(mass (cleanData raw (vectorBits words) hist out)+componentClock code raw words hist out)+1)+2
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordSpec
