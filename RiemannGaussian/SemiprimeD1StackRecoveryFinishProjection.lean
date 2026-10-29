/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
/-! # Exact complete real scalar-operator views at recovery boundaries
The reused raw-adder and reducer roles are literal subsets of the already
allocated real operators. The unused add WIDTH shadow remains empty and counted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishProjection
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
/-- All eleven actual multiplier roles, including every private copy/work field. -/
theorem data_main (v:Values) (k:M.Stack):data v (main k)=
    M.store (v .mulLeft) (v .mulRight) [] (v .reduceWidth) (v .reduceInput) [] (v .output) [] [] (v .width) [] k:=by
  rcases k with k|b
  · rcases k with k|k
    · cases k <;> rfl
    · rcases k with k|b
      · fin_cases k <;> rfl
      · cases b <;> rfl
  · cases b <;> rfl
/-- The real scalar-adder receives the SAME actual WIDTH, with every other real field literal. -/
theorem data_add (v:Values) (k:A.Stack):data v (addStack k)=
    A.store (v .addLeft) (v .addRight) [] (v .addOutput) (v .width) [] k:=by
  rcases k with k|b
  · cases k <;> rfl
  · cases b <;> rfl
/-- Raw floor increment uses precisely the real four scalar-add operand/work/result words. -/
theorem data_raw (v:Values) (k:Raw.Stack):data v (rawStack k)=
    SemiprimeD1StackAdder.store (v .addLeft) (v .addRight) [] (v .addOutput) k:=by
  cases k <;> rfl
/-- Real direct reduction uses precisely the existing multiplier's four binary fields. -/
theorem data_reduce (v:Values) (k:Raw.Stack):data v (reduceStack k)=
    SemiprimeD1StackAdder.store (v .reduceInput) (v .reduceWidth) [] (v .output) k:=by
  cases k <;> rfl
/-- The allocated unused scalar-add WIDTH shadow is always counted and empty. -/
theorem add_width_shadow (v:Values):data v (addWork (.inr false))=[]:=rfl
/-- Consuming scalar multiplication clears both real operands and writes only its actual result. -/
def multiplied (v:Values) (word:List Bool):Values:=
  Function.update (Function.update (Function.update v .mulLeft []) .mulRight []) .output word
/-- Consuming scalar addition or raw increment clears both real operands and writes its actual result. -/
def added (v:Values) (word:List Bool):Values:=
  Function.update (Function.update (Function.update v .addLeft []) .addRight []) .addOutput word
/-- Consuming direct reduction clears both its real word/counter inputs and writes its actual result. -/
def reduced (v:Values) (word:List Bool):Values:=
  Function.update (Function.update (Function.update v .reduceInput []) .reduceWidth []) .output word
/-- Every multiplier input/output update retains all actual foreign words. -/
theorem multiplied_other (v:Values) (word:List Bool) (k:Stack) (hk:∀j,main j≠k):
    data (multiplied v word) k=data v k:=by
  rw [multiplied,data_update,data_update,data_update]
  have h0:address .mulLeft≠k:=hk (.inl SemiprimeD1StackMultiplier.input)
  have h1:address .mulRight≠k:=hk (.inl SemiprimeD1StackMultiplier.factor)
  have h2:address .output≠k:=hk (M.reduceStack .output)
  rw [Function.update_of_ne h2.symm,Function.update_of_ne h1.symm,Function.update_of_ne h0.symm]
/-- Every scalar-add input/output update retains all actual foreign words, including the allocated WIDTH shadow. -/
theorem added_other (v:Values) (word:List Bool) (k:Stack) (hk:∀j,addStack j≠k):
    data (added v word) k=data v k:=by
  rw [added,data_update,data_update,data_update]
  have h0:address .addLeft≠k:=hk (.inl .left)
  have h1:address .addRight≠k:=hk (.inl .right)
  have h2:address .addOutput≠k:=hk (.inl .output)
  rw [Function.update_of_ne h2.symm,Function.update_of_ne h1.symm,Function.update_of_ne h0.symm]
/-- Every raw increment input/output update retains all actual foreign source/cache words. -/
theorem raw_other (v:Values) (word:List Bool) (k:Stack) (hk:∀j,rawStack j≠k):
    data (added v word) k=data v k:=by
  rw [added,data_update,data_update,data_update]
  have h0:address .addLeft≠k:=hk .left
  have h1:address .addRight≠k:=hk .right
  have h2:address .addOutput≠k:=hk .output
  rw [Function.update_of_ne h2.symm,Function.update_of_ne h1.symm,Function.update_of_ne h0.symm]
/-- Every real direct reduction input/output update retains all actual foreign source/cache words. -/
theorem reduced_other (v:Values) (word:List Bool) (k:Stack) (hk:∀j,reduceStack j≠k):
    data (reduced v word) k=data v k:=by
  rw [reduced,data_update,data_update,data_update]
  have h0:address .reduceInput≠k:=hk .left
  have h1:address .reduceWidth≠k:=hk .right
  have h2:address .output≠k:=hk .output
  rw [Function.update_of_ne h2.symm,Function.update_of_ne h1.symm,Function.update_of_ne h0.symm]
end RiemannGaussian.SemiprimeD1StackRecoveryFinishProjection
