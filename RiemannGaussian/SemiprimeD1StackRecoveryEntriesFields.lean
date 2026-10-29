/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives
/-! # All five canonical-row fields are physically parsed and retained
Actual node/index words feed the two binary readers; actual sign/magnitude/D
bytes feed the output logger. No field is supplied separately from the row tape.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesFields
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryDenominatorEncoding (Row)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- One actual source Field call, with its own physical validity bit and real return. -/
theorem field_call (part:Fin 5) (children:List Bool) (w:Aux → List Bool) (word tail:List Bool)
    (hi:w .reader=frame word tail) (ho:w (fieldAux part)=[]) (hv:w .valid=[]):
    Runs program (8*word.length+7) (.local (.field part)) (data children w) (.local (.valid part))
      (data children (Function.update (Function.update (Function.update w .reader tail) (fieldAux part) word) .valid [true])):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) (data children w) before.store (data children w):=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>exact hi
        | scratch=>exact data_scratch children w
        | output=>change data children w (fieldTarget part)=[];rw [field_address,data_aux,ho]
      · cases k;exact hv
    · intro k _;rfl
  simp only [data_update]
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part)) rfl
    (8*word.length+6) before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack part) (field_injective part) (data children w) before.store (data children w) hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) (data children w) _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) (data children w) _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack,field_address] using h2
/-- The actual true validity pop clears its physical field and leaves exactly parsed payloads. -/
theorem field_read (part:Fin 5) (children:List Bool) (w:Aux → List Bool) (word tail:List Bool)
    (hi:w .reader=frame word tail) (ho:w (fieldAux part)=[]) (hv:w .valid=[]):
    Runs program (8*word.length+8) (.local (.field part)) (data children w) (nextField part)
      (data children (Function.update (Function.update w .reader tail) (fieldAux part) word)):=by
  have h0:=field_call part children w word tail hi ho hv
  let v:=Function.update (Function.update (Function.update w .reader tail) (fieldAux part) word) .valid [true]
  have h1:=pop_run (.local (.valid part)) (.local .abort) (.local .abort) (nextField part) .valid children v [true] rfl (Function.update_self _ _ _)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  have he:Function.update v .valid []=Function.update (Function.update w .reader tail) (fieldAux part) word:=by
    dsimp [v]
    rw [Function.update_idem,Function.update_comm (by fin_cases part <;> decide:fieldAux part≠.valid),
      Function.update_comm (by decide:Aux.reader≠.valid)]
    have hz:Function.update w .valid []=w:=by rw [←hv];exact Function.update_eq_self _ _
    rw [hz]
  rw [he] at h1
  have h:=join h0 h1
  exact h
/-- Only already parsed fields are nonempty in the actual acquisition invariant. -/
def parsed (n:Nat) (r:Row):Fin 5 → List Bool:=fun part=>if part.val<n then r part else []
/-- Literal actual unread suffix at each of the five finite parser sites. -/
def suffix (r:Row) (n:Nat) (tail:List Bool):List Bool:=
  if n=0 then RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding.fields r tail
  else if n=1 then frame (r 1) (frame (r 2) (frame (r 3) (frame (r 4) tail)))
  else if n=2 then frame (r 2) (frame (r 3) (frame (r 4) tail))
  else if n=3 then frame (r 3) (frame (r 4) tail) else if n=4 then frame (r 4) tail else tail
/-- The next actual parser input is exactly its acquired source field and unread physical suffix. -/
theorem suffix_step (r:Row) (part:Fin 5) (tail:List Bool):suffix r part.val tail=frame (r part) (suffix r (part.val+1) tail):=by fin_cases part <;> rfl
/-- Physical write advances the actual finite five-field partial cache. -/
theorem parsed_step (r:Row) (part:Fin 5):Function.update (parsed part.val r) part (r part)=parsed (part.val+1) r:=by
  funext k;fin_cases part <;> fin_cases k <;> rfl
/-- Unparsed next-field output is genuinely empty before its actual parser call. -/
theorem parsed_current (r:Row) (part:Fin 5):parsed part.val r part=[]:=by simp only [parsed,Nat.lt_irrefl,ite_false]
/-- One real parser call advances the exact actual row cache. -/
theorem parse_one (part:Fin 5) (children rows reader:List Bool) (r:Row) (tail row child history buffer out:List Bool)
    (hr:reader=suffix r part.val tail):
    Runs program (8*(r part).length+8) (.local (.field part))
      (data children (words rows reader (parsed part.val r) row child [] history buffer out)) (nextField part)
      (data children (words rows (suffix r (part.val+1) tail) (parsed (part.val+1) r) row child [] history buffer out)):=by
  have h:=field_read part children (words rows reader (parsed part.val r) row child [] history buffer out)
    (r part) (suffix r (part.val+1) tail) (by change reader=_;rw [hr,suffix_step])
    (by rw [words_field,parsed_current]) rfl
  rw [update_reader,update_field,parsed_step] at h
  exact h
/-- Exact own clock of the five actual source-field calls and validity pops. -/
def time (r:Row):Nat:=8*((r 0).length+(r 1).length+(r 2).length+(r 3).length+(r 4).length)+40
/-- Complete real five-field source acquisition, with every byte preserved exactly. -/
theorem parse_run (children rows reader:List Bool) (r:Row) (tail row child history buffer out:List Bool)
    (hr:reader=RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding.fields r tail):
    Runs program (time r) (.local (.field 0))
      (data children (words rows reader (fun _=>[]) row child [] history buffer out)) (.local .outer)
      (data children (words rows tail r row child [] history buffer out)):=by
  have h0:=parse_one 0 children rows reader r tail row child history buffer out hr
  have h1:=parse_one 1 children rows (suffix r 1 tail) r tail row child history buffer out rfl
  have h2:=parse_one 2 children rows (suffix r 2 tail) r tail row child history buffer out rfl
  have h3:=parse_one 3 children rows (suffix r 3 tail) r tail row child history buffer out rfl
  have h4:=parse_one 4 children rows (suffix r 4 tail) r tail row child history buffer out rfl
  have h:=join h0 (join h1 (join h2 (join h3 h4)))
  have hp0:parsed 0 r=fun _=>[]:=by funext k;exact ite_eq_right (Nat.not_lt_zero _)
  have hp5:parsed 5 r=r:=by funext k;exact ite_eq_left k.isLt
  change Runs program _ (.local (.field 0))
    (data children (words rows reader (parsed 0 r) row child [] history buffer out)) (.local .outer)
    (data children (words rows tail (parsed 5 r) row child [] history buffer out)) at h
  rw [hp0,hp5] at h
  convert h using 1
  unfold time
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesFields
