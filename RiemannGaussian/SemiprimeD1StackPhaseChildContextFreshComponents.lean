/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshLoops
/-! # Actual cache peeks, paid acquired-rank copies and the whole fresh allocation trace -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshComponents
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackPhaseChildContextFreshArithmetic
open SemiprimeD1StackPhaseChildContextFreshPrimitives SemiprimeD1StackProcedureTrace
namespace Old
export SemiprimeD1StackPhaseChildContextPrimitives (count precision header)
export SemiprimeD1StackPhaseChildContextArithmetic (good)
export SemiprimeD1StackPhaseChildContextComponents (result)
end Old
/-- EXACT80-role stopped cache from the actual whole original source. -/
def cache (a u edges : Nat) (t p : List Bool) (axes : List Nat) : H.Stack→List Bool :=Old.result a u edges t p axes
/-- Actual old/new ranks, described only in proof invariants, not control parameters. -/
def rank (a u edges : Nat) (t : List Bool) (axes : List Nat) : Nat :=(Old.count a u edges t::axes).prod
/-- Exact coefficient-vector output when a child context physically exists; rejection is EMPTY. -/
def output (a u edges : Nat) (t p : List Bool) (axes : List Nat) : List Bool :=
  if Old.good a u edges t then SemiprimeD1TensorTapeCodec.vectorBits
    (words (rank a u edges t axes) axes.prod (decide (0<SemiprimeBitArithmetic.bitValue (Old.precision a u edges t p)))) else []
/-- Entire actual context/P48 bank retained, every allocator work word consumed. -/
def result (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (cache a u edges t p axes) [] [] [] (output a u edges t p axes) []
/-- Own paid allocator clock charges both acquired rank VALUES and every emitted byte. -/
def readyBound (a u edges : Nat) (t : List Bool) (axes : List Nat) : Nat :=
  if Old.good a u edges t then 30*(rank a u edges t axes+axes.prod+1) else 2
/-- Physical width-empty peek is exactly original reduced-unit precision positivity. -/
theorem positive_cache (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=true) :
    positive (cache a u edges t p axes)=decide (0<SemiprimeBitArithmetic.bitValue (Old.precision a u edges t p)) :=by
  have hw:cache a u edges t p axes (H.childStack H.J.widthCache)=
      List.replicate (SemiprimeBitArithmetic.bitValue (Old.precision a u edges t p)) true:=by
    change (if Old.good a u edges t then SemiprimeD1StackPhaseChildContextPrimitives.contextResult (Old.count a u edges t::axes) (Old.precision a u edges t p)
      else SemiprimeD1StackPhaseChildContext.emptyContext) _=_
    rw [hg]
    rfl
  unfold positive
  rw [hw]
  cases hv:SemiprimeBitArithmetic.bitValue (Old.precision a u edges t p) <;> rfl
/-- Actual context-present flag is physically peeked before allocation or any rank copy. -/
theorem guard_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program 1 .guard (store (cache a u edges t p axes) [] [] [] [] [])
      (if Old.good a u edges t then .copyNew else .done) (store (cache a u edges t p axes) [] [] [] [] []) :=by
  apply one_base program .guard _ (.peek valid .done .done .copyNew) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.done Label.done Label.copyNew ([Old.good a u edges t].head?))=some _
    cases Old.good a u edges t <;> rfl
  · rfl
/-- The new-rank VALUE reaches a fresh physical counter only through a real preserving copy. -/
theorem copy_new (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=true) :
    Runs program (5*rank a u edges t axes+4) .copyNew (store (cache a u edges t p axes) [] [] [] [] [])
      .copyOld (store (cache a u edges t p axes) (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) [] [] [] []) :=by
  let ph:=cache a u edges t p axes
  have hs:ph (H.childStack H.J.rankCache)=SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes):=by
    change (if Old.good a u edges t then SemiprimeD1StackPhaseChildContextPrimitives.contextResult (Old.count a u edges t::axes) (Old.precision a u edges t p)
      else SemiprimeD1StackPhaseChildContext.emptyContext) _=_
    rw [hg];rfl
  have h:=copy_call false .copyNew .copyOld rfl (store ph [] [] [] [] []) rfl rfl
  change Runs program (5*(ph (H.childStack H.J.rankCache)).length+4) .copyNew _ .copyOld _ at h
  rw [hs,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] at h
  change Runs program (5*rank a u edges t axes+4) .copyNew (store ph [] [] [] [] []) .copyOld
    (Function.update (store ph [] [] [] [] []) (aux .remaining) (ph (H.childStack H.J.rankCache))) at h
  rw [hs] at h
  convert h using 1
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- The old-rank skip VALUE is likewise derived from the actual old-header context source. -/
theorem copy_old (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=true) :
    Runs program (5*axes.prod+4) .copyOld
      (store (cache a u edges t p axes) (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) [] [] [] []) .before
      (store (cache a u edges t p axes) (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) (SemiprimeD1StackUnaryDivmod.unary axes.prod) [] [] []) :=by
  let ph:=cache a u edges t p axes
  have hs:ph (H.oldStack H.J.rankCache)=SemiprimeD1StackUnaryDivmod.unary axes.prod:=by
    change (if Old.good a u edges t then SemiprimeD1StackPhaseChildContextPrimitives.contextResult axes p
      else SemiprimeD1StackPhaseChildContext.oldInput (Old.header axes)) _=_
    rw [hg];rfl
  have h:=copy_call true .copyOld .before rfl
    (store ph (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) [] [] [] []) rfl rfl
  change Runs program (5*(ph (H.oldStack H.J.rankCache)).length+4) .copyOld _ .before _ at h
  rw [hs,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] at h
  change Runs program (5*axes.prod+4) .copyOld
    (store ph (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) [] [] [] []) .before
    (Function.update (store ph (SemiprimeD1StackUnaryDivmod.unary (rank a u edges t axes)) [] [] [] []) (aux .skip) (ph (H.oldStack H.J.rankCache))) at h
  rw [hs] at h
  convert h using 1
  funext k;rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Complete SAME-program ready trace has no phase/context/rank reacquisition or answer payload. -/
theorem ready_trace (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    ∃q,q+1≤ readyBound a u edges t axes ∧ Runs program q .guard
      (store (cache a u edges t p axes) [] [] [] [] []) .done (result a u edges t p axes) :=by
  have h0:=guard_run a u edges t p axes
  cases hg:Old.good a u edges t with
  | false=>
    rw [hg] at h0
    refine ⟨1,?_,?_⟩
    · simp only [readyBound,hg,Bool.false_eq_true,ite_false];omega
    · simpa only [result,output,hg,Bool.false_eq_true,ite_false] using h0
  | true=>
    rw [hg] at h0
    have h1:=copy_new a u edges t p axes hg
    have h2:=copy_old a u edges t p axes hg
    obtain ⟨b,hb,h3⟩:=SemiprimeD1StackPhaseChildContextFreshLoops.allocate (cache a u edges t p axes) (rank a u edges t axes) axes.prod
    rw [positive_cache a u edges t p axes hg] at h3
    have hh:=join (join (join h0 h1) h2) h3
    refine ⟨1+(5*rank a u edges t axes+4)+(5*axes.prod+4)+b,?_,?_⟩
    · simp only [readyBound,hg,ite_true];omega
    · simpa only [result,output,hg,ite_true] using hh
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshComponents
