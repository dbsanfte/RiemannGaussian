/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorPrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding
/-! # Five actual framed row fields, including every discarded byte
The source parses and drains the first four fields, then physically parses the
actual denominator into the real multiplier's first operand. No selected word
or denominator list is provided separately from the actual row tape.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorFields
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackRecoveryDenominatorPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryDenominatorEncoding (Row fields)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual live word receiving a physical field parse. -/
def target (part:Fin 5):Slot:=if part=4 then .mul M.input else .aux .discard
/-- Parser output is exactly its declared live address. -/
theorem target_address (part:Fin 5):fieldTarget part=address (target part):=by fin_cases part <;> rfl
/-- One real field call includes every parse/reverse bit and its actual return symbol. -/
theorem field_call (part:Fin 5) (v:Values) (word tail:List Bool)
    (hi:v (.aux .reader)=frame word tail) (ho:v (target part)=[])
    (hs:v (.mul M.copyScratch)=[]) (hv:v (.aux .valid)=[]):
    Runs program (8*word.length+7) (.local (.field part)) (data v) (.local (.valid part))
      (data (Function.update (Function.update (Function.update v (.aux .reader) tail) (target part) word) (.aux .valid) [true])):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) (data v) before.store (data v):=by
    constructor
    · intro k;rcases k with k|k
      · cases k with
        | input=>exact (data_get v (.aux .reader)).trans hi
        | scratch=>exact (data_get v (.mul M.copyScratch)).trans hs
        | output=>change data v (fieldTarget part)=[];rw [target_address,data_get,ho]
      · cases k;exact (data_get v (.aux .valid)).trans hv
    · intro k _;rfl
  simp only [data_update]
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part))
    rfl (8*word.length+6) before after _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack part) (field_injective part) (data v) before.store (data v) hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) (data v) _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) (data v) _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack,target_address,address] using h2
/-- Restoring the actually popped valid field returns the original live state outside parsed words. -/
theorem valid_restore (v:Values) (part:Fin 5) (word tail:List Bool) (hv:v (.aux .valid)=[]):
    Function.update (Function.update (Function.update (Function.update v (.aux .reader) tail)
      (target part) word) (.aux .valid) [true]) (.aux .valid) []=
        Function.update (Function.update v (.aux .reader) tail) (target part) word:=by
  rw [Function.update_idem]
  have hn:target part≠.aux .valid:=by fin_cases part <;> decide
  rw [Function.update_comm hn,Function.update_comm (by decide:Slot.aux Aux.reader≠.aux .valid)]
  have he:Function.update v (.aux .valid) []=v:=by rw [←hv];exact Function.update_eq_self _ _
  rw [he]
/-- One actual validity pop consumes its physically produced true bit. -/
theorem valid_call (part:Fin 5) (v:Values) (word tail:List Bool) (hv:v (.aux .valid)=[]):
    Runs program 1 (.local (.valid part))
      (data (Function.update (Function.update (Function.update v (.aux .reader) tail) (target part) word) (.aux .valid) [true]))
      (if part=4 then .local .multiply else .local (.clearField part))
      (data (Function.update (Function.update v (.aux .reader) tail) (target part) word)):=by
  have h:=pop_view (.local (.valid part)) (.local .abort) (.local .abort)
    (if part=4 then .local .multiply else .local (.clearField part)) (.aux .valid)
    (Function.update (Function.update (Function.update v (.aux .reader) tail) (target part) word) (.aux .valid) [true]) [true] rfl
    (Function.update_self _ _ _)
  simpa only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose,valid_restore v part word tail hv] using h
/-- Static actual next-field suffix. -/
def suffix (r:Row) (n:Nat) (tail:List Bool):List Bool:=
  if n=0 then fields r tail else if n=1 then frame (r 1) (frame (r 2) (frame (r 3) (frame (r 4) tail)))
  else if n=2 then frame (r 2) (frame (r 3) (frame (r 4) tail))
  else if n=3 then frame (r 3) (frame (r 4) tail) else if n=4 then frame (r 4) tail else tail
/-- Every actual field frame starts at exactly the next physical payload. -/
theorem suffix_step (r:Row) (part:Fin 5) (tail:List Bool):
    suffix r part.val tail=frame (r part) (suffix r (part.val+1) tail):=by fin_cases part <;> rfl
/-- First four field parses and physical drains leave only their actual unread suffix. -/
theorem discard_call (part:Fin 4) (v:Values) (word tail:List Bool)
    (hi:v (.aux .reader)=frame word tail) (ho:v (.aux .discard)=[])
    (hs:v (.mul M.copyScratch)=[]) (hv:v (.aux .valid)=[]):
    Runs program (9*word.length+9) (.local (.field part.castSucc)) (data v)
      (.local (.field ⟨part.val+1,by omega⟩)) (data (Function.update v (.aux .reader) tail)):=by
  have ht:target part.castSucc=.aux .discard:=by fin_cases part <;> rfl
  have hp:part.castSucc≠(4:Fin 5):=by fin_cases part <;> decide
  have h0:=field_call part.castSucc v word tail hi (by rw [ht];exact ho) hs hv
  rw [ht] at h0
  have h1:=valid_call part.castSucc v word tail hv
  rw [ite_eq_right hp,ht] at h1
  let w:=Function.update (Function.update v (.aux .reader) tail) (.aux .discard) word
  have h2:=drain_view (.local (.clearField part.castSucc)) (nextField part.castSucc) (.aux .discard) w rfl
  have hw:w (.aux .discard)=word:=Function.update_self _ _ _
  rw [hw] at h2
  have he:Function.update w (.aux .discard) []=Function.update v (.aux .reader) tail:=by
    dsimp [w]
    rw [Function.update_idem,Function.update_comm (by decide:Slot.aux Aux.reader≠.aux .discard)]
    have hh:Function.update v (.aux .discard) []=v:=by rw [←ho];exact Function.update_eq_self _ _
    rw [hh]
  rw [he] at h2
  have hn:nextField part.castSucc=.local (.field ⟨part.val+1,by omega⟩):=by fin_cases part <;> rfl
  rw [hn] at h2
  have h:=(join (join h0 h1) h2)
  simpa only [show (8*word.length+7+1)+(word.length+1)=9*word.length+9 by omega] using h
/-- Final actual denominator parse reaches the real multiplier's first input. -/
theorem denominator_call (v:Values) (word tail:List Bool)
    (hi:v (.aux .reader)=frame word tail) (ho:v (.mul M.input)=[])
    (hs:v (.mul M.copyScratch)=[]) (hv:v (.aux .valid)=[]):
    Runs program (8*word.length+8) (.local (.field 4)) (data v) (.local .multiply)
      (data (Function.update (Function.update v (.aux .reader) tail) (.mul M.input) word)):=by
  have h0:=field_call 4 v word tail hi ho hs hv
  have h1:=valid_call 4 v word tail hv
  have h:=join h0 h1
  simpa only [target,ite_true,show (8*word.length+7)+1=8*word.length+8 by omega] using h
/-- Paid complete parser/drain clock for all five physical fields of one row. -/
def time (r:Row):Nat:=9*((r 0).length+(r 1).length+(r 2).length+(r 3).length)+8*(r 4).length+44
/-- Complete actual five-field acquisition, retaining no discarded answer or metadata field. -/
theorem parse_run (v:Values) (r:Row) (tail:List Bool)
    (hi:v (.aux .reader)=fields r tail) (hd:v (.aux .discard)=[])
    (hm:v (.mul M.input)=[]) (hs:v (.mul M.copyScratch)=[]) (hv:v (.aux .valid)=[]):
    Runs program (time r) (.local (.field 0)) (data v) (.local .multiply)
      (data (Function.update (Function.update v (.aux .reader) tail) (.mul M.input) (r 4))):=by
  let view (n:Nat):Values:=Function.update v (.aux .reader) (suffix r n tail)
  have h0:=discard_call 0 v (r 0) (suffix r 1 tail) hi hd hs hv
  have h1:=discard_call 1 (view 1) (r 1) (suffix r 2 tail) rfl hd hs hv
  have h2:=discard_call 2 (view 2) (r 2) (suffix r 3 tail) rfl hd hs hv
  have h3:=discard_call 3 (view 3) (r 3) (suffix r 4 tail) rfl hd hs hv
  have h4:=denominator_call (view 4) (r 4) tail rfl hm hs hv
  simp only [view,Function.update_idem] at h1 h2 h3 h4
  have h:=join h0 (join h1 (join h2 (join h3 h4)))
  convert h using 1 <;> first | rfl | (unfold time;omega)
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorFields
