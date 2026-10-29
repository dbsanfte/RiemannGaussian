/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedPrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedSpec
/-! # Real numeric equality and real full binary ordinal increments
The complete four-role arithmetic bank is shared sequentially. Every copied
address digit, comparator cleanup, adder digit and actual call/return is paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedOperators
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackRecoveryEntriesIndexedState
open SemiprimeD1StackRecoveryEntriesIndexedPrimitives SemiprimeD1StackRecoveryEntriesIndexedSpec
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
/-- Real numeric WordEqual includes its actual outer call/return. -/
theorem equal_call (cache query counter reader value:List Bool):
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime query counter+1) (.local .compare)
      (store query counter [] [] cache query counter reader [] value [] []) (.local .compared)
      (store [] [] [] [decide (bitValue query=bitValue counter)] cache query counter reader [] value [] []):=by
  apply included_call program arithmetic Label.equal Sum.inl_injective E.code .loop (fun _=>rfl)
    (.local .compare) (.local .compared) rfl (SemiprimeD1StackWordEqualExecution.executionTime query counter)
    (E.state (some .loop) none query counter []) (E.state none none [] [] [decide (bitValue query=bitValue counter)])
    _ _ rfl rfl (SemiprimeD1StackWordEqualExecution.source_run query counter none)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
/-- Exact full real adder-plus-return clock for adding literal binary one. -/
def addTime (counter:List Bool):Nat:=3*(max counter.length 1+1)+2*(increment counter).length+3
/-- Actual raw increment, including full carry propagation, with no fixed-width wrap. -/
theorem add_call (cache query counter reader value:List Bool):
    Runs program (addTime counter) (.local .add)
      (store counter [true] [] [] cache query [] reader [] value [] []) (.local .result)
      (store [] [] [] (increment counter) cache query [] reader [] value [] []):=by
  apply included_call program arithmetic Label.add Sum.inl_injective A.code (.start false) (fun _=>rfl)
    (.local .add) (.local .result) rfl
    (3*(max counter.length 1+1)+2*(increment counter).length+2)
    (A.state (some (.start false)) none counter [true] [] [])
    (A.state none none [] [] [] (increment counter)) _ _ rfl rfl (SemiprimeD1StackAdderExecution.source_run counter [true] false)
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
/-- Exact actually executed address/counter comparison pipeline clock. -/
def compareTime (query counter:List Bool):Nat:=
  ((5*query.length+4)+(5*counter.length+4))+(SemiprimeD1StackWordEqualExecution.executionTime query counter+1)+1
/-- Actual numeric comparison of copied raw address and acquired binary ordinal, preserving both originals. -/
theorem compare_run (cache query counter reader:List Bool):
    Runs program (compareTime query counter) (.local .query) (view cache query counter reader [])
      (.local (.field (decide (bitValue query=bitValue counter)))) (view cache query counter reader []):=by
  have h0:=copy_call .query (.local .query) (.local .ordinal) (view cache query counter reader []) query [] rfl rfl rfl rfl
  simp only [List.append_nil] at h0
  dsimp only [view,copyTarget,arithmetic] at h0
  rw [update_left] at h0
  have h1:=copy_call .ordinal (.local .ordinal) (.local .compare)
    (store query [] [] [] cache query counter reader [] [] [] []) counter [] rfl rfl rfl rfl
  simp only [List.append_nil] at h1
  dsimp only [copyTarget,arithmetic] at h1
  rw [update_right] at h1
  have h2:=equal_call cache query counter reader []
  let answer:=decide (bitValue query=bitValue counter)
  have h3:=pop_run (.local .compared) (.local .abort) (.local (.field false)) (.local (.field true)) (arithmetic .output)
    (store [] [] [] [answer] cache query counter reader [] [] [] []) [answer] rfl rfl
  have hc:SemiprimeD1StackBytecode.choose (.local .abort) (.local (.field false)) (.local (.field true)) [answer].head?=
      Label.local (.field answer):=by cases answer <;> rfl
  dsimp only [arithmetic] at h3
  rw [hc,List.tail_cons,update_sum] at h3
  exact join (join (join h0 h1) h2) h3
/-- Every real copy/drain/seed/adder/result-transfer instruction of an ordinal increment. -/
def incrementTime (counter:List Bool):Nat:=
  (((((5*counter.length+4)+(counter.length+1))+1)+addTime counter)+(5*(increment counter).length+4))+((increment counter).length+1)
/-- Physically acquired binary counter increases only after an actually skipped vector field. -/
theorem increment_run (cache query counter reader:List Bool):
    Runs program (incrementTime counter) (.local .increment) (view cache query counter reader [])
      (.local .loop) (view cache query (increment counter) reader []):=by
  have h0:=copy_call .increment (.local .increment) (.local .clearCounterForAdd)
    (view cache query counter reader []) counter [] rfl rfl rfl rfl
  simp only [List.append_nil] at h0
  dsimp only [view,copyTarget,arithmetic] at h0
  rw [update_left] at h0
  have h1:=drain_run (.local .clearCounterForAdd) (.local .seed) (aux .counter)
    (store counter [] [] [] cache query counter reader [] [] [] []) counter rfl rfl
  dsimp only [aux] at h1
  rw [update_counter] at h1
  have h2:=push_run (.local .seed) (.local .add) (arithmetic .right) true
    (store counter [] [] [] cache query [] reader [] [] [] []) rfl
  dsimp only [arithmetic] at h2
  rw [update_right] at h2
  have h3:=add_call cache query counter reader []
  have h4:=copy_call .result (.local .result) (.local .clearResult)
    (store [] [] [] (increment counter) cache query [] reader [] [] [] []) (increment counter) [] rfl rfl rfl rfl
  simp only [List.append_nil] at h4
  dsimp only [copyTarget,aux] at h4
  rw [update_counter] at h4
  have h5:=drain_run (.local .clearResult) (.local .loop) (arithmetic .output)
    (store [] [] [] (increment counter) cache query (increment counter) reader [] [] [] []) (increment counter) rfl rfl
  dsimp only [arithmetic] at h5
  rw [update_sum] at h5
  exact join (join (join (join (join h0 h1) h2) h3) h4) h5
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedOperators
