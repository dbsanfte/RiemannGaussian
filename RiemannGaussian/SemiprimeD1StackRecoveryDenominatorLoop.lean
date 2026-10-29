/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorView
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorFields
/-! # Actual finite row-loop source with full denominator-first products
Every row marker, all five fields, all discarded bytes, the raw-product copy
and every real component call/return belong to this single actual trace.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorLoop
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackRecoveryDenominatorPrimitives SemiprimeD1StackRecoveryDenominatorView
open SemiprimeD1StackRecoveryDenominatorEncoding SemiprimeD1StackProcedureTrace
namespace F
export SemiprimeD1StackRecoveryDenominatorFields (time parse_run)
end F
namespace O
export SemiprimeD1StackRecoveryDenominatorOperators (multiply_call multiplyTime fit_call)
end O
/-- Actual preserving copy and physical accumulator drain prepare the real second operand. -/
theorem load_run (original reader widthTemplate acc:List Bool):
    Runs program (6*acc.length+5) (.local .load) (data (bank original reader widthTemplate [] [] acc []))
      (.local (.field 0)) (data (bank original reader widthTemplate [] acc [] [])):=by
  have h0:=copy_view false (.local .load) (.local .clearAccumulator)
    (bank original reader widthTemplate [] [] acc []) rfl rfl
  change Runs program (5*acc.length+4) (.local .load) (data (bank original reader widthTemplate [] [] acc []))
    (.local .clearAccumulator) (data (Function.update (bank original reader widthTemplate [] [] acc []) (.mul M.factor) (acc++[]))) at h0
  rw [List.append_nil,update_factor] at h0
  have h1:=drain_view (.local .clearAccumulator) (.local (.field 0)) (.mul (.inl .right))
    (bank original reader widthTemplate [] acc acc []) rfl
  rw [update_accumulator] at h1
  change Runs program (acc.length+1) (.local .clearAccumulator) (data (bank original reader widthTemplate [] acc acc []))
    (.local (.field 0)) (data (bank original reader widthTemplate [] acc [] [])) at h1
  have h:=join h0 h1
  convert h using 1;omega
/-- Complete actually executed row-step clock. -/
def rowTime (r:Row) (acc:List Bool):Nat:=1+(6*acc.length+5)+F.time r+O.multiplyTime (r 4) acc
/-- One true row marker acquires all five real fields, then executes the full real denominator-first multiplier. -/
theorem row_run (seen:Bool) (r:Row) (rs:List Row) (original widthTemplate acc:List Bool):
    Runs program (rowTime r acc) (.local (.loop seen)) (data (bank original (tape (r::rs)) widthTemplate [] [] acc []))
      (.local (.loop true)) (data (bank original (tape rs) widthTemplate [] [] (SemiprimeBitArithmetic.mulBits (r 4) acc).bits [])):=by
  have h0:=pop_view (.local (.loop seen)) (.local .abort)
    (if seen then .local .fit else .local .emptyPop) (.local .load) (.aux .reader)
    (bank original (tape (r::rs)) widthTemplate [] [] acc []) (true::fields r (tape rs)) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=load_run original (fields r (tape rs)) widthTemplate acc
  have h2:=F.parse_run (bank original (fields r (tape rs)) widthTemplate [] acc [] []) r (tape rs) rfl rfl rfl rfl rfl
  rw [update_reader,update_input] at h2
  have h3:=O.multiply_call (bank original (tape rs) widthTemplate (r 4) acc [] []) (r 4) acc (fun _=>rfl)
  rw [multiplied_bank] at h3
  exact join (join (join h0 h1) h2) h3
/-- The first false marker returns the old literal one rather than a width-padded one. -/
theorem empty_run (original widthTemplate:List Bool):
    Runs program 3 (.local (.loop false)) (data (bank original [false] widthTemplate [] [] [true] []))
      (.local .done) (data (bank original [] widthTemplate [] [] [] [true])):=by
  have h0:=pop_view (.local (.loop false)) (.local .abort) (.local .emptyPop) (.local .load) (.aux .reader)
    (bank original [false] widthTemplate [] [] [true] []) [false] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=pop_view (.local .emptyPop) (.local .abort) (.local .abort) (.local .emptyPush) (.mul (.inl .right))
    (bank original [] widthTemplate [] [] [true] []) [true] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  rw [update_accumulator] at h1
  have h2:=push_view (.local .emptyPush) (.local .done) (.aux .output) true
    (bank original [] widthTemplate [] [] [] []) rfl
  rw [update_output] at h2
  exact join (join h0 h1) h2
/-- Every nonempty row stream ends with one actual full WordFit call. -/
theorem finish_run (original widthTemplate acc:List Bool):
    Runs program (SemiprimeD1StackWordFitExecution.totalTime acc widthTemplate+2)
      (.local (.loop true)) (data (bank original [false] widthTemplate [] [] acc []))
      (.local .done) (data (bank original [] widthTemplate [] [] [] (SemiprimeD1StackWordFitExecution.result acc widthTemplate))):=by
  have h0:=pop_view (.local (.loop true)) (.local .abort) (.local .fit) (.local .load) (.aux .reader)
    (bank original [false] widthTemplate [] [] acc []) [false] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  rw [update_reader] at h0
  have h1:=O.fit_call (bank original [] widthTemplate [] [] acc []) rfl rfl rfl
  rw [fitted_bank] at h1
  change Runs program (SemiprimeD1StackWordFitExecution.totalTime acc widthTemplate+1)
    (.local .fit) (data (bank original [] widthTemplate [] [] acc [])) (.local .done)
    (data (bank original [] widthTemplate [] [] [] (SemiprimeD1StackWordFitExecution.result acc widthTemplate))) at h1
  have h:=join h0 h1
  convert h using 1;omega
/-- Actual source clock over the physical row traversal; proof recursion is not a runtime operand. -/
def budget (widthTemplate:List Bool):Bool → List Row → List Bool → Nat
  | seen,[],acc=>if seen then SemiprimeD1StackWordFitExecution.totalTime acc widthTemplate+2 else 3
  | _,r::rs,acc=>rowTime r acc+budget widthTemplate true rs (SemiprimeBitArithmetic.mulBits (r 4) acc).bits
/-- Mathematical actual-byte answer, preserving the original empty-row exception. -/
def answer (widthTemplate:List Bool) (seen:Bool) (rs:List Row) (acc:List Bool):List Bool:=
  if seen || !rs.isEmpty then SemiprimeD1StackWordFitExecution.result (raw rs acc) widthTemplate else [true]
/-- Complete physical row-loop induction, including every actual field/product/fit call and real return. -/
theorem loop_run (seen:Bool) (rs:List Row) (original widthTemplate acc:List Bool)
    (hseed:seen=false →acc=[true]):
    Runs program (budget widthTemplate seen rs acc) (.local (.loop seen))
      (data (bank original (tape rs) widthTemplate [] [] acc [])) (.local .done)
      (data (bank original [] widthTemplate [] [] [] (answer widthTemplate seen rs acc))):=by
  induction rs generalizing seen acc with
  | nil=>
    cases seen with
    | false=>rw [hseed rfl];exact empty_run original widthTemplate
    | true=>exact finish_run original widthTemplate acc
  | cons r rs ih=>
    have h0:=row_run seen r rs original widthTemplate acc
    have h1:=ih true (SemiprimeBitArithmetic.mulBits (r 4) acc).bits (by intro h;cases h)
    have h:=join h0 h1
    simpa only [budget,answer,List.isEmpty_cons,Bool.not_false,Bool.or_true,Bool.true_or,ite_true,raw,List.foldl_cons] using h
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorLoop
