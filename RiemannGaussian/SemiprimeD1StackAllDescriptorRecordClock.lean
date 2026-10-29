/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordOriginal
/-! # Concrete inherited original-checker bit clocks for the actual dispatcher -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordClock
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordSpec
open SemiprimeD1StackAllDescriptorRecordExecution SemiprimeD1StackAllDescriptorRecordCleanup
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- The actual inherited concrete whole-checker clock, not a report/advised
cost: actual whole table, physical selectors/loaders, ordinal conversion and row. -/
def componentBound (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool) : Nat :=
  (match family code with
  | .input=>SemiprimeD1StackInputDescriptorRecordBounds.runBound (fun _=>[]) raw words M hist out
  | .carry=>SemiprimeD1StackCarryDescriptorRecordBounds.runBound (fun _=>[]) raw words M hist out
  | .scale=>SemiprimeD1StackScaleDescriptorRecord.runBound (fun _=>[]) raw ((raw 2).length==2) words M [] [] hist out
  | .transform=>SemiprimeD1StackTransformDescriptorRecord.runBound (fun _=>[]) raw (code.val==3) ((raw 2).length==2) words M [] [] hist out
  | .product=>SemiprimeD1StackProductTableBounds.runBound (raw 0)+
      21*2^(SemiprimeD1StackProductTableSpec.arity (raw 0))+110*(words.length+1)*(M+1)+20
  | .boundary=>SemiprimeD1BinaryPublicAcquisitionExecution.timeBound (raw 0)+
      61*2^(SemiprimeD1StackZeroBoundaryTable.cached (raw 0)).length+110*(words.length+1)*(M+1)+20
  | .boolean _=>110*(words.length+1)*(M+1)+210)+1
/-- Every actual fixed family source is bounded by its previously proved
concrete own clock, with physical scope lengths/values as proof-only premises. -/
theorem componentClock_le (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool)
    (hl:∀w∈words,w.length≤M) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    componentClock code raw words hist out≤ componentBound code raw words M hist out :=by
  unfold componentClock componentBound
  apply Nat.add_le_add_right
  cases h:family code with
  | input=>exact SemiprimeD1StackInputDescriptorRecordBounds.timeBound_le (fun _=>[]) raw words M hist out hl hv
  | carry=>exact SemiprimeD1StackCarryDescriptorRecordBounds.timeBound_le (fun _=>[]) raw words M hist out hl hv
  | scale=>exact SemiprimeD1StackScaleDescriptorRecord.timeBound_le (fun _=>[]) raw _ words M [] [] hist out hl hv
  | transform=>exact SemiprimeD1StackTransformDescriptorRecord.timeBound_le (fun _=>[]) raw _ _ words M [] [] hist out hl hv
  | product=>exact SemiprimeD1StackProductRecordBounds.timeBound_le (raw 0) words M hl hv
  | boundary=>exact SemiprimeD1StackBoundaryRecordBounds.timeBound_le (raw 0) words M hl hv
  | boolean mode=>exact SemiprimeD1StackBooleanRecordBounds.timeBound_le mode words M hl hv
/-- Closed concrete dispatcher clock includes tag acquisition, the same actual
whole component, all1252 physical drains, real calls/returns and final halt. -/
def runBound (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool) : Nat :=
  2000000*(mass (cleanData raw (vectorBits words) hist out)+componentBound code raw words M hist out+1)
/-- Whole actual source clock is below the concrete same-checker bit bound. -/
theorem timeBound_le (code:Fin 18) (raw:Fin 6→List Bool) (words:List (List Bool)) (M:Nat) (hist out:List Bool)
    (hl:∀w∈words,w.length≤M) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound code raw words hist out≤ runBound code raw words M hist out :=by
  have h0:=SemiprimeD1StackAllDescriptorRecordBounds.timeBound_linear code raw words hist out
  have h1:=componentClock_le code raw words M hist out hl hv
  unfold runBound
  exact h0.trans (Nat.mul_le_mul_left 2000000 (Nat.add_le_add_right (Nat.add_le_add_left h1 _) 1))
/-- The complete same fixed actual source, now with every inherited concrete
checker bit clock and every physical acquired byte charged explicitly. -/
theorem source_run_bounded (code:Fin 18) (raw:Fin 6→List Bool)
    (htag:raw 1=List.replicate code.val true)
    (h2:raw 2=SemiprimeD1StackUnaryDivmod.unary (raw 2).length)
    (h3:raw 3=SemiprimeD1StackUnaryDivmod.unary (raw 3).length)
    (h4:raw 4=SemiprimeD1StackUnaryDivmod.unary (raw 4).length)
    (htr:(code.val=1∨code.val=2∨code.val=3)→(raw 2).length<3)
    (hc:SemiprimeSourceCompactBits.Compact (raw 0)) (hN:0<SemiprimeBitArithmetic.bitValue (raw 0))
    (words:List (List Bool)) (hist out:List Bool) (M:Nat) (hl:∀w∈words,w.length≤M) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    ∃t≤ runBound code raw words M hist out,C.run program t
      (initial raw (vectorBits words) hist out)=some (done code raw words hist out) :=by
  obtain ⟨t,ht,hr⟩:=source_run code raw htag h2 h3 h4 htr hc hN words hist out
  exact ⟨t,ht.trans (timeBound_le code raw words M hist out hl hv),hr⟩
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordClock
