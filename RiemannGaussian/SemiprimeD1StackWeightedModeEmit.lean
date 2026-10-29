/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCleanup
/-! # Actual path-field reversal, tuple emission and complete leaf return
Every output tuple is built by parsing the copied current path and physically
framing each field. No tuple encoder or feasible leaf is an instruction operand.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeEmit
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModePrimitives SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeActivation (join)
open SemiprimeD1StackWeightedModeCleanup
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Literal copied path suffix and already physically reversed tuple fields. -/
def scanning (v:Words) (remaining accumulated:List (List Bool)) :Words:=
  {v with pathReader:=vectorBits remaining,tuple:=vectorBits accumulated,weight:=[],valid:=[]}
/-- Exact output of the field-reversal scan, before the actual tuple logger is called. -/
def scanned (v:Words) (fields:List (List Bool)) :Words:=
  {v with pathReader:=[],tuple:=vectorBits fields,weight:=[],valid:=[]}
/-- Exact real field-reversal clock, including one final false-tag pop. -/
def scanBudget (fields:List (List Bool)) :Nat:=15*(fields.map List.length).sum+16*fields.length+1
/-- Each actual coordinate is parsed, physically prepended and cleaned before the next coordinate. -/
theorem scan_one (v:Words) (word:List Bool) (remaining accumulated:List (List Bool))
    (hf:v.fieldScratch=[]) (hs:v.frameScratch=[]) :
    Runs program (15*word.length+16) (ctl .tupleNext) (store (scanning v (word::remaining) accumulated))
      (ctl .tupleNext) (store (scanning v remaining (word::accumulated))):=by
  let a:=scanning v (word::remaining) accumulated
  let b:Words:={a with pathReader:=frame word (vectorBits remaining)}
  let c:Words:={b with pathReader:=vectorBits remaining,weight:=word,valid:=[true]}
  let d:Words:={c with valid:=[]}
  let e:Words:={d with tuple:=frame word (vectorBits accumulated)}
  let f:Words:={e with tuple:=vectorBits (word::accumulated)}
  have h0:=pop_run .tupleNext (ctl .abort) (ctl .emit) (ctl .tupleRead) .pathReader (store a)
    (true::frame word (vectorBits remaining)) rfl rfl
  rw [store_write] at h0
  change Runs program 1 _ _ (ctl .tupleRead) (store b) at h0
  have h1:=field_call .path .tupleRead .tupleValid rfl (store b) word (vectorBits remaining) rfl rfl hf rfl
  rw [store_write,store_write,store_write] at h1
  change Runs program (8*word.length+7) _ _ _ (store c) at h1
  have h2:=pop_run .tupleValid (ctl .abort) (ctl .abort) (ctl .tupleFrame) .valid (store c) [true] rfl rfl
  rw [store_write] at h2
  change Runs program 1 _ _ (ctl .tupleFrame) (store d) at h2
  have h3:=SemiprimeD1StackWeightedModeActivation.frame_view .tuple .tupleFrame (ctl .tupleTag) rfl d hs
  change Runs program (6*word.length+5) _ _ _ (store e) at h3
  have h4:=push_run .tupleTag (ctl .tupleClear) .tuple true (store e) rfl
  rw [store_write] at h4
  change Runs program 1 _ _ _ (store f) at h4
  have h5:=drain_loop .tupleClear (ctl .tupleNext) .weight rfl (store f) word rfl
  rw [store_write] at h5
  change Runs program (word.length+1) _ _ _ (store (scanning v remaining (word::accumulated))) at h5
  have hh:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
  convert hh using 1;omega
/-- The full copied-path scan reverses coordinate order by actual field operations. -/
theorem scan_run (v:Words) (fields accumulated:List (List Bool))
    (hf:v.fieldScratch=[]) (hs:v.frameScratch=[]) :
    Runs program (scanBudget fields) (ctl .tupleNext) (store (scanning v fields accumulated))
      (ctl .emit) (store (scanned v (fields.reverse++accumulated))):=by
  induction fields generalizing accumulated with
  | nil=>
    have h:=pop_run .tupleNext (ctl .abort) (ctl .emit) (ctl .tupleRead) .pathReader
      (store (scanning v [] accumulated)) [false] rfl rfl
    rw [store_write] at h
    change Runs program 1 _ _ (ctl .emit) (store (scanned v accumulated)) at h
    exact h
  | cons word fields ih=>
    have h0:=scan_one v word fields accumulated hf hs
    have h1:=ih (word::accumulated)
    have hh:=join h0 h1
    have htime:(15*word.length+16)+scanBudget fields=scanBudget (word::fields):=by
      simp only [scanBudget,List.map_cons,List.sum_cons,List.length_cons]
      omega
    rw [htime] at hh
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
/-- Every scanned coordinate and terminator is paid by its actual physical path bytes. -/
theorem scan_length_le (fields:List (List Bool)) :scanBudget fields ≤8*(vectorBits fields).length:=by
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  unfold scanBudget
  omega
/-- Reversing only field order preserves the literal encoded byte length. -/
theorem vector_reverse_length (fields:List (List Bool)) :
    (vectorBits fields.reverse).length=(vectorBits fields).length:=by
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length,SemiprimeD1TensorTapeCodec.vectorBits_length,
    List.map_reverse,List.sum_reverse,List.length_reverse]
/-- Complete actual leaf tuple construction/logging/cleanup, with no supplied tuple output. -/
theorem leaf_run (cat width:List Bool) (R:Nat) (fields:List (List Bool)) (frames hist out:List Bool) :
    ∃t ≤70*(R+(vectorBits fields).length+1),Runs program t (ctl .tupleSeed)
      (store {base cat width frames hist out with budget:=unary R,path:=vectorBits fields})
      (ctl .returning)
      (store (base cat width frames ((row (vectorBits fields.reverse)).reverse++hist) out)):=by
  let v:Words:={base cat width frames hist out with budget:=unary R,path:=vectorBits fields}
  let v1:Words:={v with tuple:=[false]}
  have h0:=push_run .tupleSeed (ctl .copyPath) .tuple false (store v) rfl
  rw [store_write] at h0
  change Runs program 1 _ _ _ (store v1) at h0
  have h1:=copy_call .path .copyPath .tupleNext rfl (store v1) (vectorBits fields) [] rfl rfl rfl
  rw [List.append_nil,store_write] at h1
  change Runs program (5*(vectorBits fields).length+4) _ _ _ (store (scanning v fields [])) at h1
  have h2:=scan_run v fields [] rfl rfl
  simp only [List.append_nil] at h2
  let v2:=scanned v fields.reverse
  change Runs program (scanBudget fields) _ _ _ (store v2) at h2
  obtain ⟨t,ht,h3⟩:=body_call (store v2) (vectorBits fields.reverse) hist rfl rfl rfl
  rw [store_write] at h3
  let v3:Words:={v2 with history:=(row (vectorBits fields.reverse)).reverse++hist}
  change Runs program t _ _ _ (store v3) at h3
  have h4:=cleanup_run v3
  change Runs program (cleanupMass v3+9) _ _ _
    (store (base cat width frames ((row (vectorBits fields.reverse)).reverse++hist) out)) at h4
  refine ⟨1+((5*(vectorBits fields).length+4)+(scanBudget fields+(t+(cleanupMass v3+9)))),?_,
    join h0 (join h1 (join h2 (join h3 h4)))⟩
  have hs:=scan_length_le fields
  have hr:=vector_reverse_length fields
  have hm:cleanupMass v3=R+(vectorBits fields).length+(vectorBits fields.reverse).length:=by
    simp only [cleanupMass,v3,v2,scanned,v,base,unary_length,List.length_nil,Nat.zero_add,Nat.add_zero]
  rw [hm]
  omega
end RiemannGaussian.SemiprimeD1StackWeightedModeEmit
