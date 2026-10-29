/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionConvert
/-! # Literal binary D/h/r shifts and physically copied original precision -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionShifts
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionPrimitives SemiprimeD1StackProcedureTrace
/-- One actual shift marker writes one low bit to EACH binary D/h word. -/
theorem shift_step (old : M.Stack→List Bool) (l power : List Bool) (n : Nat) :
    Runs program 3 .shift (data old l [] [] [] [] [] [] (List.replicate (n+1) true) power)
      .shift (data old (false::l) [] [] [] [] [] [] (List.replicate n true) (false::power)) :=by
  have h0:Runs program 1 .shift (data old l [] [] [] [] [] [] (List.replicate (n+1) true) power)
      .shiftPower (data old l [] [] [] [] [] [] (List.replicate n true) power):=by
    apply one_base program .shift .shiftPower (.pop (aux .shiftTodo) (.leftShift 0) .shiftPower .shiftPower) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 .shiftPower (data old l [] [] [] [] [] [] (List.replicate n true) power)
      .shiftHeight (data old l [] [] [] [] [] [] (List.replicate n true) (false::power)):=by
    apply one_base program .shiftPower .shiftHeight (.push (aux .power) false .shiftHeight) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2:Runs program 1 .shiftHeight (data old l [] [] [] [] [] [] (List.replicate n true) (false::power))
      .shift (data old (false::l) [] [] [] [] [] [] (List.replicate n true) (false::power)):=by
    apply one_base program .shiftHeight .shift (.push (aux .left) false .shift) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  exact join (join h0 h1) h2
/-- Physical low-zero shift commutes with the proof-side repeated-zero prefix. -/
theorem shift_front (n : Nat) (xs : List Bool) : shift n (false::xs)=shift (n+1) xs :=by
  unfold shift
  rw [List.replicate_succ']
  simp only [List.append_assoc,List.singleton_append]
/-- The actual shared shift loop constructs binary D and h*D, without unary powers. -/
theorem shift_run (old : M.Stack→List Bool) (l power : List Bool) (n : Nat) :
    Runs program (3*n+1) .shift (data old l [] [] [] [] [] [] (List.replicate n true) power)
      (.leftShift 0) (data old (shift n l) [] [] [] [] [] [] [] (shift n power)) :=by
  induction n generalizing l power with
  | zero=>
    apply one_base program .shift (.leftShift 0) (.pop (aux .shiftTodo) (.leftShift 0) .shiftPower .shiftPower) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  | succ n ih=>
    have hh:=join (shift_step old l power n) (ih (false::l) (false::power))
    rw [shift_front,shift_front] at hh
    convert hh using 1
    omega
/-- Three actual finite literal writes supply the h-term factor8. -/
theorem left_three (old : M.Stack→List Bool) (l power : List Bool) :
    Runs program 3 (.leftShift 0) (data old l [] [] [] [] [] [] [] power)
      .copyPrecision (data old (shift 3 l) [] [] [] [] [] [] [] power) :=by
  have h0:Runs program 1 (.leftShift 0) (data old l [] [] [] [] [] [] [] power)
      (.leftShift 1) (data old (false::l) [] [] [] [] [] [] [] power):=by
    apply one_base program (.leftShift 0) (.leftShift 1) (.push (aux .left) false (.leftShift 1)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (.leftShift 1) (data old (false::l) [] [] [] [] [] [] [] power)
      (.leftShift 2) (data old (false::false::l) [] [] [] [] [] [] [] power):=by
    apply one_base program (.leftShift 1) (.leftShift 2) (.push (aux .left) false (.leftShift 2)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2:Runs program 1 (.leftShift 2) (data old (false::false::l) [] [] [] [] [] [] [] power)
      .copyPrecision (data old (shift 3 l) [] [] [] [] [] [] [] power):=by
    apply one_base program (.leftShift 2) .copyPrecision (.push (aux .left) false .copyPrecision) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  exact join (join h0 h1) h2
/-- Original arbitrary-precision p is copied physically and restored as the identical BINARY word. -/
theorem copy_precision (old : M.Stack→List Bool) (l power p : List Bool)
    (hp : old (M.aux .precision)=p) :
    Runs program (5*p.length+4) .copyPrecision (data old l [] [] [] [] [] [] [] power)
      (.add false) (data old l p [] [] [] [] [] [] power) :=by
  have h:=copy_call 8 .copyPrecision (.add false) rfl (data old l [] [] [] [] [] [] [] power) rfl rfl
  have hs:data old l [] [] [] [] [] [] [] power (copySource 8)=p:=hp
  rw [hs] at h
  have he:Function.update (data old l [] [] [] [] [] [] [] power) (copyTarget 8) p=
      data old l p [] [] [] [] [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h
  exact h
/-- Complete binary D/h/p preparation uses only ACTUALLY acquired delta and original p. -/
theorem left_run (old : M.Stack→List Bool) (h delta : Nat) (p : List Bool)
    (hd : old (M.aux .delta)=List.replicate delta true) (hp : old (M.aux .precision)=p) :
    Runs program (8*delta+5*p.length+13) .copyDelta
      (data old (counterWord h) [] [] [] [] [] [] [] []) (.add false)
      (data old (heightTerm h delta) p [] [] [] [] [] [] (shift delta [true])) :=by
  have h0:=copy_call 7 .copyDelta .seedPower rfl (data old (counterWord h) [] [] [] [] [] [] [] []) rfl rfl
  have hs:data old (counterWord h) [] [] [] [] [] [] [] [] (copySource 7)=List.replicate delta true:=hd
  rw [hs,List.length_replicate] at h0
  have he0:Function.update (data old (counterWord h) [] [] [] [] [] [] [] []) (copyTarget 7) (List.replicate delta true)=
      data old (counterWord h) [] [] [] [] [] [] (List.replicate delta true) []:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he0] at h0
  have h1:Runs program 1 .seedPower (data old (counterWord h) [] [] [] [] [] [] (List.replicate delta true) [])
      .shift (data old (counterWord h) [] [] [] [] [] [] (List.replicate delta true) [true]):=by
    apply one_base program .seedPower .shift (.push (aux .power) true .shift) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2:=shift_run old (counterWord h) [true] delta
  have h3:=left_three old (shift delta (counterWord h)) (shift delta [true])
  have h4:=copy_precision old (heightTerm h delta) (shift delta [true]) p hp
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  convert hh using 1
  omega
/-- Three physically executed writes supply the r-term factor8. -/
theorem right_three (old : M.Stack→List Bool) (r out power : List Bool) :
    Runs program 3 (.rightShift 0) (data old [] r out [] [] [] [] [] power)
      .copyPartial (data old [] (shift 3 r) out [] [] [] [] [] power) :=by
  have h0:Runs program 1 (.rightShift 0) (data old [] r out [] [] [] [] [] power)
      (.rightShift 1) (data old [] (false::r) out [] [] [] [] [] power):=by
    apply one_base program (.rightShift 0) (.rightShift 1) (.push (aux .right) false (.rightShift 1)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h1:Runs program 1 (.rightShift 1) (data old [] (false::r) out [] [] [] [] [] power)
      (.rightShift 2) (data old [] (false::false::r) out [] [] [] [] [] power):=by
    apply one_base program (.rightShift 1) (.rightShift 2) (.push (aux .right) false (.rightShift 2)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  have h2:Runs program 1 (.rightShift 2) (data old [] (false::false::r) out [] [] [] [] [] power)
      .copyPartial (data old [] (shift 3 r) out [] [] [] [] [] power):=by
    apply one_base program (.rightShift 2) .copyPartial (.push (aux .right) false .copyPartial) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  exact join (join h0 h1) h2
/-- The actual first sum is paid-copied into the second adder and its old word is erased. -/
theorem copy_partial (old : M.Stack→List Bool) (r out power : List Bool) :
    Runs program ((5*out.length+4)+(out.length+1)) .copyPartial (data old [] r out [] [] [] [] [] power)
      (.add true) (data old out r [] [] [] [] [] [] power) :=by
  have h0:=copy_call 9 .copyPartial .clearPartial rfl (data old [] r out [] [] [] [] [] power) rfl rfl
  have he:Function.update (data old [] r out [] [] [] [] [] power) (copyTarget 9)
      (data old [] r out [] [] [] [] [] power (copySource 9))=data old out r out [] [] [] [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h0
  have h1:=SemiprimeD1StackPhysicalLoops.drain program .clearPartial (.add true) (aux .output)
    rfl (data old out r out [] [] [] [] [] power) out
  have hi:Function.update (data old out r out [] [] [] [] [] power) (aux .output) out=
      data old out r out [] [] [] [] [] power:=Function.update_eq_self _ _
  have ho:Function.update (data old out r out [] [] [] [] [] power) (aux .output) []=
      data old out r [] [] [] [] [] [] power:=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [hi,ho] at h1
  exact join h0 h1
/-- Complete r-term/second-adder preparation preserves BINARY D and the whole metadata cache. -/
theorem right_run (old : M.Stack→List Bool) (r : Nat) (out power : List Bool) :
    Runs program (6*out.length+8) (.rightShift 0) (data old [] (counterWord r) out [] [] [] [] [] power)
      (.add true) (data old out (productTerm r) [] [] [] [] [] [] power) :=by
  have hh:=join (right_three old (counterWord r) out power) (copy_partial old (productTerm r) out power)
  convert hh using 1
  omega
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionShifts
