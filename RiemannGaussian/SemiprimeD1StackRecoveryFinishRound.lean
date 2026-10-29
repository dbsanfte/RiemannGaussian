/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators
/-! # Actual arbitrary negative floor correction, before modular reduction
The source reads its physically stored sign and lost-one flag. A negative
nonintegral quotient executes the full raw binary increment; it is never
identified with a magnitude shift by an unstated divisibility premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishRound
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinishProjection SemiprimeD1StackRecoveryFinishOperators SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Exact raw magnitude correction specified by the two actual Boolean source flags. -/
def roundWord (negative lost:Bool) (word:List Bool):List Bool:=
  if negative&&lost then (SemiprimeBitArithmetic.addBits word [true] false).bits else word
/-- Exact actual raw-increment source clock, including its real caller invocation. -/
def rawClock (word:List Bool):Nat:=
  3*(max word.length 1+1)+2*(SemiprimeBitArithmetic.addBits word [true] false).bits.length+3
/-- Own exact actual increment branch clock: real move, constant one, raw adder, real result move. -/
def incrementTime (word:List Bool):Nat:=
  (6*word.length+7)+1+rawClock word+(6*(SemiprimeBitArithmetic.addBits word [true] false).bits.length+7)
/-- Actual finite sign/loss tests and chosen branch have this same-program source clock. -/
def roundTime (negative lost:Bool) (word:List Bool):Nat:=
  1+(if negative then 1 else 0)+(if negative&&lost then incrementTime word else 6*word.length+7)
/-- Exact floor boundary: consumed numerator work, actual full corrected magnitude in real reducer input. -/
def rounded (v:Values) (word:List Bool):Values:=
  Function.update (Function.update v (.aux .numeratorWork) []) .reduceInput word
/-- Plain physical quotient transfer has no arithmetic assumption. -/
theorem plain_run (v:Values) (hs:v (.aux .copyScratch)=[]) (hi:v .reduceInput=[]):
    Runs program (6*(v (.aux .numeratorWork)).length+7) (ctl .plain) (data v) (ctl .qWidth)
      (data (rounded v (v (.aux .numeratorWork)))):=by
  have h:=move_call .plain (ctl .plain) (ctl .qWidth) v rfl hs
  have he:moved v .plain=rounded v (v (.aux .numeratorWork)):=by
    simp only [moved,moveFrom,moveTo,hi,List.append_nil,rounded]
    rw [Function.update_comm (by decide:Slot.reduceInput≠.aux .numeratorWork)]
  rw [he] at h
  exact h
/-- Actual negative-floor branch performs the real full unsigned increment and physically transfers its output. -/
theorem increment_run (v:Values) (hs:v (.aux .copyScratch)=[]) (hi:v .reduceInput=[])
    (hl:v .addLeft=[]) (hr:v .addRight=[]) (ho:v .addOutput=[]):
    Runs program (incrementTime (v (.aux .numeratorWork))) (ctl .increment) (data v) (ctl .qWidth)
      (data (rounded v (SemiprimeBitArithmetic.addBits (v (.aux .numeratorWork)) [true] false).bits)):=by
  let word:=v (.aux .numeratorWork)
  let result:=(SemiprimeBitArithmetic.addBits word [true] false).bits
  let v1:=moved v .roundingInput
  let v2:=Function.update v1 .addRight [true]
  let v3:=added v2 result
  have h0:=move_call .roundingInput (ctl .increment) (ctl .rawOne) v rfl hs
  change Runs program (6*word.length+7) _ _ _ (data v1) at h0
  have h1:=push_view (ctl .rawOne) (ctl .rawAdd) .addRight true v1 rfl
  have hz1:v1 .addRight=[]:=by simp [v1,moved,moveFrom,moveTo,hr]
  simp only [hz1] at h1
  change Runs program 1 _ _ _ (data v2) at h1
  have hout:v2 .addOutput=[]:=by simp [v2,v1,moved,moveFrom,moveTo,ho]
  have h2:=raw_call (ctl .rawAdd) (ctl .rounded) v2 rfl hout
  have hword:rawWord v2=result:=by simp [rawWord,v2,v1,moved,moveFrom,moveTo,hl,word,result]
  have htime:rawTime v2=rawClock word:=by
    unfold rawTime rawClock
    rw [hword]
    simp [v2,v1,moved,moveFrom,moveTo,hl,word,result]
  rw [hword,htime] at h2
  change Runs program (rawClock word) _ _ _ (data v3) at h2
  have hscratch:v3 (.aux .copyScratch)=[]:=by simp [v3,added,v2,v1,moved,moveFrom,moveTo,hs]
  have h3:=move_call .rounded (ctl .rounded) (ctl .qWidth) v3 rfl hscratch
  have hout3:v3 .addOutput=result:=by simp [v3,added]
  change Runs program (6*(v3 .addOutput).length+7) _ _ _ _ at h3
  rw [hout3] at h3
  have he:moved v3 .rounded=rounded v result:=by
    funext s
    cases s with
    | aux a=>cases a <;> simp [moved,v3,added,v2,v1,moveFrom,moveTo,rounded,hi,hl]
    | _=>simp [moved,v3,added,v2,v1,moveFrom,moveTo,rounded,hi,hl,hr,ho]
  rw [he] at h3
  exact join (join (join h0 h1) h2) h3
/-- Actual sign/loss reads select exactly the real floor branch, with every source call and return charged. -/
theorem round_run (v:Values) (negative lost:Bool) (hn:v (.aux .sign)=[negative]) (hd:v (.aux .lost)=[lost])
    (hs:v (.aux .copyScratch)=[]) (hi:v .reduceInput=[])
    (hl:v .addLeft=[]) (hr:v .addRight=[]) (ho:v .addOutput=[]):
    Runs program (roundTime negative lost (v (.aux .numeratorWork))) (ctl .signFloor) (data v) (ctl .qWidth)
      (data (rounded v (roundWord negative lost (v (.aux .numeratorWork))))) :=by
  have h0:=peek_view (ctl .signFloor) (ctl .abort) (ctl .plain) (ctl .negativeFloor) (.aux .sign) v rfl
  rw [hn] at h0
  cases negative with
  | false=>
    have h1:=plain_run v hs hi
    have h:=join h0 h1
    simpa only [roundTime,roundWord,Bool.false_and,Bool.false_eq_true,ite_false,Nat.add_zero] using h
  | true=>
    have h1:=peek_view (ctl .negativeFloor) (ctl .abort) (ctl .plain) (ctl .increment) (.aux .lost) v rfl
    rw [hd] at h1
    cases lost with
    | false=>
      have h2:=plain_run v hs hi
      have h:=join (join h0 h1) h2
      simpa only [roundTime,roundWord,Bool.true_and,Bool.false_eq_true,ite_true,ite_false] using h
    | true=>
      have h2:=increment_run v hs hi hl hr ho
      have h:=join (join h0 h1) h2
      simpa only [roundTime,roundWord,Bool.true_and,ite_true] using h
end RiemannGaussian.SemiprimeD1StackRecoveryFinishRound
