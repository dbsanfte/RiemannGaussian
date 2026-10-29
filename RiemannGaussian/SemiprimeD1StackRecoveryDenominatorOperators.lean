/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorPrimitives
/-! # Real whole multiplier and final width-fit component calls
Both traces are the frozen physical source traces with actual call/return cells.
All caller words and allocated shadows outside each actual image are preserved.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOperators
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackProcedureTrace
namespace ME
export SemiprimeD1StackMultiplierExecution (source_run loopClock source_time timeBound)
end ME
namespace FE
export SemiprimeD1StackWordFitExecution (source_run totalTime done result)
end FE
/-- Exact wholesale actual multiplier bank replacement, retaining all foreign words. -/
def replaceMul (v:Values) (bank:M.Stack → List Bool):Values
  | .mul k=>bank k | .template=>v .template | .counter=>v .counter
  | .fitScratch=>v .fitScratch | .aux k=>v (.aux k)
/-- Complete actual full-product result, with all nine multiplier work words cleared. -/
def multiplied (v:Values) (xs ys:List Bool):Values:=
  replaceMul v (M.payload [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])
/-- Every full-product caller tape outside the actual multiplier image is unchanged. -/
theorem replace_foreign (v:Values) (bank:M.Stack → List Bool) (k:Stack)
    (hk:∀m,k≠main m):data (replaceMul v bank) k=data v k:=by
  rcases k with k|k
  · exact (hk k rfl).elim
  · rcases k with k|k
    · fin_cases k <;> rfl
    · cases k <;> rfl
/-- SAME actual full multiplier elapsed count, including the real outer call/return. -/
def multiplyTime (xs ys:List Bool):Nat:=2*xs.length+1+ME.loopClock ys xs.reverse []+1
/-- Current denominator FIRST, running product SECOND: actual whole9-role source call. -/
theorem multiply_call (v:Values) (xs ys:List Bool)
    (hv:∀k,v (.mul k)=M.payload xs ys [] [] [] [] [] [] [] k):
    Runs program (multiplyTime xs ys) (.local .multiply) (data v) (.local (.loop true)) (data (multiplied v xs ys)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program main Label.multiply (Sum.inl_injective) M.code (.control .start)
    (fun _=>rfl) (.local .multiply) (.local (.loop true)) rfl
    (2*xs.length+1+ME.loopClock ys xs.reverse [])
    (SemiprimeD1StackMultiplier.state (some (.control .start)) none none xs ys [] [] [] [] [] [] [])
    (SemiprimeD1StackMultiplier.state none none none [] [] [] [] (SemiprimeBitArithmetic.mulBits xs ys).bits [] [] [] [])
    _ _ rfl rfl rfl rfl (ME.source_run xs ys)
  · constructor
    · intro k;exact hv k
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      exact replace_foreign v _ k (by simpa only [ne_eq,eq_comm] using hk)
/-- Exact final width-fit result writes only the real consumed accumulator and actual output. -/
def fitted (v:Values):Values:=Function.update (Function.update v (.mul (.inl .right)) []) (.aux .output)
  (FE.result (v (.mul (.inl .right))) (v .template))
/-- Actual final fit call preserves the physical template and both unused fit shadows. -/
theorem fit_call (v:Values) (hc:v .counter=[]) (hs:v .fitScratch=[]) (ho:v (.aux .output)=[]):
    Runs program (FE.totalTime (v (.mul (.inl .right))) (v .template)+1)
      (.local .fit) (data v) (.local .done) (data (fitted v)):=by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program fitStack Label.fit fit_injective Fit.program .start (fun _=>rfl)
    (.local .fit) (.local .done) rfl (FE.totalTime (v (.mul (.inl .right))) (v .template))
    (SemiprimeD1StackWordFit.initial (v (.mul (.inl .right))) (v .template))
    (FE.done (v (.mul (.inl .right))) (v .template)) _ _ rfl rfl rfl rfl (FE.source_run _ _)
  · constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact (data_get v .counter).trans hc
      · exact (data_get v .fitScratch).trans hs
      · exact (data_get v (.aux .output)).trans ho
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · rfl
      · rfl
      · exact (data_get (fitted v) .counter).trans hc
      · exact (data_get (fitted v) .fitScratch).trans hs
      · rfl
    · intro k hk
      have ha:k≠address (.mul (.inl .right)):=fun h=>hk 0 (by exact h.symm)
      have ho':k≠address (.aux .output):=fun h=>hk 4 (by exact h.symm)
      simp only [fitted,data_update,Function.update_of_ne ho',Function.update_of_ne ha]
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOperators
