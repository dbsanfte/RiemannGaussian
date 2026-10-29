/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextSteps
/-! # Physical guard/q routing and complete actual child-context ready trace -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextComponents
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContextArithmetic SemiprimeD1StackProcedureTrace
namespace S
export SemiprimeD1StackPhaseChildContextSteps (waiting acquired acquireBound)
end S
/-- Final physically acquired old/new caches, with an explicit true/false context-presence flag. -/
def result (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (phase a u edges t p)
    (if good a u edges t then contextResult axes p else oldInput (header axes))
    (if good a u edges t then contextResult (count a u edges t::axes) (precision a u edges t p) else emptyContext)
    [good a u edges t] []
/-- Actual ready cost includes both context suppliers and all numerical width/rank expansion. -/
def readyBound (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=if good a u edges t then S.acquireBound a u edges t p axes+10 else 4
/-- The acquired original phase verdict is read by ONE actual physical peek. -/
theorem guard_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program 1 .guard (S.waiting a u edges t p axes)
      (if accepted a u t then .positive else .reject) (S.waiting a u edges t p axes) :=by
  apply one_base program .guard _ (.peek guard .reject .reject .positive) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.reject Label.reject Label.positive
      ([accepted a u t].head?))=some _
    cases accepted a u t <;> rfl
  · rfl
/-- Actual q-empty guard is physical and protects context positivity even outside the original family. -/
theorem positive_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (ha : accepted a u t=true) :
    Runs program 1 .positive (S.waiting a u edges t p axes)
      (if 0<count a u edges t then .copyOldPrecision else .reject) (S.waiting a u edges t p axes) :=by
  apply one_base program .positive _ (.peek blocks .reject .copyOldPrecision .copyOldPrecision) _ _ rfl
  · have hs:S.waiting a u edges t p axes blocks=SemiprimeD1StackUnaryDivmod.unary (count a u edges t):=count_word a u edges t p ha
    change some (SemiprimeD1StackBytecode.choose Label.reject Label.copyOldPrecision Label.copyOldPrecision
      ((S.waiting a u edges t p axes blocks).head?))=some _
    rw [hs]
    cases hn:count a u edges t with
    | zero=>rfl
    | succ n=>rfl
  · rfl
/-- Explicit true/false context-presence flag is physically written, never native advice. -/
theorem emit (bit : Bool) (ph : P.Stack→List Bool) (old child : J.Stack→List Bool) :
    Runs program 1 (if bit then .accept else .reject) (store ph old child [] []) .done (store ph old child [bit] []) :=by
  apply one_base program _ .done (.push (aux .valid) bit .done) _ _ (by cases bit <;> rfl)
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k <;> rfl
/-- Complete ready trace uses ACTUALLY acquired P48 data and acquires all old/new context fields itself. -/
theorem ready_trace (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q,q+1≤ readyBound a u edges t p axes ∧ Runs program q .guard (S.waiting a u edges t p axes)
      .done (result a u edges t p axes) :=by
  have h0:=guard_run a u edges t p axes
  have hb:4≤ readyBound a u edges t p axes:=by unfold readyBound;split <;> omega
  cases ha:accepted a u t with
  | false=>
    rw [ha] at h0
    have h1:=emit false (phase a u edges t p) (oldInput (header axes)) emptyContext
    have hh:=join h0 h1
    have hg:good a u edges t=false:=by simp only [good,ha,Bool.false_eq_true,ite_false]
    refine ⟨2,by omega,?_⟩
    simpa only [result,hg,Bool.false_eq_true,ite_false,SemiprimeD1StackPhaseChildContextSteps.waiting] using hh
  | true=>
    rw [ha] at h0
    have h1:=positive_run a u edges t p axes ha
    by_cases hq:0<count a u edges t
    · simp only [hq,ite_true] at h1
      obtain ⟨b,hb,h2⟩:=SemiprimeD1StackPhaseChildContextSteps.source_run a u edges t p axes hp ha hq
      have h3:=emit true (phase a u edges t p) (contextResult axes p)
        (contextResult (count a u edges t::axes) (precision a u edges t p))
      have hh:=join (join (join h0 h1) h2) h3
      have hg:good a u edges t=true:=(good_true a u edges t).mpr ⟨ha,hq⟩
      refine ⟨1+1+b+1,?_,?_⟩
      · simp only [readyBound,hg,ite_true]
        omega
      · simpa only [result,hg,ite_true,SemiprimeD1StackPhaseChildContextSteps.acquired] using hh
    · simp only [hq,ite_false] at h1
      have h2:=emit false (phase a u edges t p) (oldInput (header axes)) emptyContext
      have hh:=join (join h0 h1) h2
      have hg:good a u edges t=false:=by simp only [good,ha,ite_true,hq,decide_false]
      refine ⟨3,by omega,?_⟩
      simpa only [result,hg,Bool.false_eq_true,ite_false,SemiprimeD1StackPhaseChildContextSteps.waiting] using hh
end RiemannGaussian.SemiprimeD1StackPhaseChildContextComponents
