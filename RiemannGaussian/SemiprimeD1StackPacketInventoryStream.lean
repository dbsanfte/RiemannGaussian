/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryView
/-! # Actual selected-key Field parser and physical validity consumption
A prior real vector-tag pop exposes the framed raw key. The parser consumes
that actual frame, restores scratch and physically pops its true validity byte.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryStream
open SemiprimeD1StackPacketInventory SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventoryView SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl"=>Label.local
/-- One complete real raw-key Field source, including its actual call/return and singleton true validity. -/
theorem field_run (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (key tail:List Bool)
    (hr:f.reader=frame key tail) (ho:f.raw=[]) (hs:f.fieldScratch=[]) (hv:f.valid=[]):
    Runs program (8*key.length+7) (ctl .parse) (view f r o) (ctl .valid)
      (view {f with reader:=tail,raw:=key,valid:=[true]} r o) :=by
  let start:=SemiprimeD1TensorTapeFieldBytecode.initial (frame key tail) []
  let stop:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] key) (fun _=>[true])⟩
  have hin:Link.DataRel fieldStack (view f r o) start.store (view f r o):=by
    constructor
    · intro k;rcases k with k|k
      · cases k
        · exact hr
        · exact hs
        · exact ho
      · cases k;exact hv
    · intro k _;rfl
  have h0:=Link.data_update fieldStack field_injective (view f r o) start.store (view f r o) hin (.inl .input) tail
  have h1:=Link.data_update fieldStack field_injective (view f r o) _ _ h0 (.inl .output) key
  have h2:=Link.data_update fieldStack field_injective (view f r o) _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update start.store (.inl .input) tail) (.inl .output) key)
      (.inr ()) [true]=stop.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  change Link.DataRel fieldStack (view f r o) stop.store (Function.update (Function.update (Function.update
    (view f r o) (frequencyStack (F.aux .reader)) tail) (frequencyStack (F.aux .raw)) key)
      (frequencyStack (F.lookupStack (.inr .valid))) [true]) at h2
  rw [update_reader,update_raw,update_valid] at h2
  exact included_call program fieldStack Label.field field_injective Field.code (Field.active .tagPop (none,false))
    (fun _=>rfl) (ctl .parse) (ctl .valid) rfl (8*key.length+6) start stop (view f r o) _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run key tail []) hin h2
/-- Actual true-valid pop completes the raw-key read and preserves every other physical word, including OLD-j. -/
theorem parse_run (f:W.Words) (r:R.Stack→List Bool) (o:O.Stack→List Bool) (key tail:List Bool)
    (hr:f.reader=frame key tail) (ho:f.raw=[]) (hs:f.fieldScratch=[]) (hv:f.valid=[]):
    Runs program (8*key.length+8) (ctl .parse) (view f r o) (ctl .encodeClass)
      (view {f with reader:=tail,raw:=key,valid:=[]} r o) :=by
  have h0:=field_run f r o key tail hr ho hs hv
  have h1:=pop_run .valid (ctl .abort) (ctl .abort) (ctl .encodeClass) (lookupStack (.inr .valid))
    (view {f with reader:=tail,raw:=key,valid:=[true]} r o) [true] rfl rfl
  change Runs program 1 _ _ _ (Function.update (view {f with reader:=tail,raw:=key,valid:=[true]} r o)
    (frequencyStack (F.lookupStack (.inr .valid))) []) at h1
  rw [update_valid] at h1
  have h:=join h0 h1
  simpa only [Nat.add_assoc,SemiprimeD1StackBytecode.choose,List.head?_cons] using h
end RiemannGaussian.SemiprimeD1StackPacketInventoryStream
