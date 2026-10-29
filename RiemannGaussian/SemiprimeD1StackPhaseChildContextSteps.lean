/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextArithmetic
/-! # Paid original/header/precision copies and actual old/new context acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextSteps
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContextArithmetic SemiprimeD1StackProcedureTrace
/-- Actual P48 done-cache plus the original old header; every other context field clear. -/
def waiting (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (phase a u edges t p) (oldInput (header axes)) emptyContext [] []
/-- Original p has physically reached the old context source input. -/
def oldPrepared (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (phase a u edges t p) (J.initial (header axes) p).data emptyContext [] []
/-- The old rank/width are ACTUALLY acquired before any new context construction. -/
def oldAcquired (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (phase a u edges t p) (contextResult axes p) emptyContext [] []
/-- Physical child-header and precision-input tapes, with all child work/rank/width still clear. -/
def childPrepared (a u edges : Nat) (t p : List Bool) (axes : List Nat) (newHeader newP : List Bool) : Stack→List Bool :=
  store (phase a u edges t p) (contextResult axes p) (J.initial newHeader newP).data [] []
/-- Exact fully acquired old/new contexts before the actual success flag write. -/
def acquired (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Stack→List Bool :=
  store (phase a u edges t p) (contextResult axes p)
    (contextResult (count a u edges t::axes) (precision a u edges t p)) [] []
/-- One real original-p copy precedes the actual old-context source. -/
theorem old_precision (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program (5*p.length+4) .copyOldPrecision (waiting a u edges t p axes)
      .oldContext (oldPrepared a u edges t p axes) :=by
  have h:=copy_call 0 .copyOldPrecision .oldContext rfl (waiting a u edges t p axes) rfl rfl
  have hs:waiting a u edges t p axes (copySource 0)=p:=original_precision_word a u edges t p
  rw [hs] at h
  have he:Function.update (waiting a u edges t p axes) (copyTarget 0) p=oldPrepared a u edges t p axes:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · fin_cases k <;> rfl
      · rcases k with k|k <;> rfl
  rw [he] at h
  exact h
/-- Whole old-context source derives oldrank from the caller's ACTUAL positive old header. -/
theorem old_context (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x) :
    ∃q≤SemiprimeD1StackJetContextCorrectness.budget axes p+1,
      Runs program q .oldContext (oldPrepared a u edges t p axes) .copyHeader (oldAcquired a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=context_call false axes hp p (oldPrepared a u edges t p axes)
  have hi:withContext false (oldPrepared a u edges t p axes) (J.initial (header axes) p).data=oldPrepared a u edges t p axes:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
  have ho:withContext false (oldPrepared a u edges t p axes) (contextResult axes p)=oldAcquired a u edges t p axes:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
  rw [hi,ho] at hr
  exact ⟨q,hq,hr⟩
/-- The old UNARY-axes header is really copied before q is framed onto it. -/
theorem header_copy (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program (5*(header axes).length+4) .copyHeader (oldAcquired a u edges t p axes)
      .frame (childPrepared a u edges t p axes (header axes) []) :=by
  have h:=copy_call 1 .copyHeader .frame rfl (oldAcquired a u edges t p axes) rfl rfl
  have hs:oldAcquired a u edges t p axes (copySource 1)=header axes:=rfl
  rw [hs] at h
  have he:Function.update (oldAcquired a u edges t p axes) (copyTarget 1) (header axes)=
      childPrepared a u edges t p axes (header axes) []:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · rfl
            · fin_cases k <;> rfl
        · rfl
  rw [he] at h
  exact h
/-- Real framing restores ACTUAL unary q and writes its literal field ahead of the copied header. -/
theorem frame_q (a u edges : Nat) (t p : List Bool) (axes : List Nat) (ha : accepted a u t=true) :
    Runs program (6*count a u edges t+5) .frame (childPrepared a u edges t p axes (header axes) [])
      .cons (childPrepared a u edges t p axes
        (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary (count a u edges t)) (header axes)) []) :=by
  let d:=childPrepared a u edges t p axes (header axes) []
  have h:=frame_call d rfl
  have hs:d blocks=SemiprimeD1StackUnaryDivmod.unary (count a u edges t):=count_word a u edges t p ha
  have hh:d (childStack J.axesCache)=header axes:=rfl
  rw [hs,hh,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] at h
  have he:Function.update d (childStack J.axesCache)
      (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary (count a u edges t)) (header axes))=
      childPrepared a u edges t p axes
        (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary (count a u edges t)) (header axes)) []:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · rfl
            · fin_cases k <;> rfl
        · rfl
  change Runs program (6*count a u edges t+5) .frame d .cons
    (Function.update d (childStack J.axesCache)
      (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary (count a u edges t)) (header axes))) at h
  rw [he] at h
  exact h
/-- One actual constructor-tag push completes the EXACT existing UNARY-axis header. -/
theorem cons_q (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program 1 .cons (childPrepared a u edges t p axes
      (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary (count a u edges t)) (header axes)) [])
      .copyPrecision (childPrepared a u edges t p axes (header (count a u edges t::axes)) []) :=by
  apply one_base program .cons .copyPrecision (.push (childStack J.axesCache) true .copyPrecision) _ _ rfl
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · rfl
            · fin_cases k <;> rfl
        · rfl
/-- The ACTUAL new BINARY P word is paid-copied into the child context source. -/
theorem precision_copy (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    Runs program (5*(precision a u edges t p).length+4) .copyPrecision
      (childPrepared a u edges t p axes (header (count a u edges t::axes)) []) .childContext
      (childPrepared a u edges t p axes (header (count a u edges t::axes)) (precision a u edges t p)) :=by
  have h:=copy_call 2 .copyPrecision .childContext rfl
    (childPrepared a u edges t p axes (header (count a u edges t::axes)) []) rfl rfl
  have hs:childPrepared a u edges t p axes (header (count a u edges t::axes)) [] (copySource 2)=precision a u edges t p:=rfl
  rw [hs] at h
  have he:Function.update (childPrepared a u edges t p axes (header (count a u edges t::axes)) [])
      (copyTarget 2) (precision a u edges t p)=
      childPrepared a u edges t p axes (header (count a u edges t::axes)) (precision a u edges t p):=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rfl
          · rcases k with k|k
            · rfl
            · fin_cases k <;> rfl
        · rfl
  rw [he] at h
  exact h
/-- The NEW actual context source acquires unary q*oldrank and P-VALUE precision markers. -/
theorem child_context (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (hq : 0<count a u edges t) :
    ∃q≤SemiprimeD1StackJetContextCorrectness.budget (count a u edges t::axes) (precision a u edges t p)+1,
      Runs program q .childContext
        (childPrepared a u edges t p axes (header (count a u edges t::axes)) (precision a u edges t p))
        .accept (acquired a u edges t p axes) :=by
  let before:=childPrepared a u edges t p axes (header (count a u edges t::axes)) (precision a u edges t p)
  obtain ⟨q,hq,hr⟩:=context_call true (count a u edges t::axes) (child_positive axes hp _ hq)
    (precision a u edges t p) before
  have hi:withContext true before (J.initial (header (count a u edges t::axes)) (precision a u edges t p)).data=before:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
  have ho:withContext true before (contextResult (count a u edges t::axes) (precision a u edges t p))=
      acquired a u edges t p axes:=by
    funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> rfl
  rw [hi,ho] at hr
  exact ⟨q,hq,hr⟩
/-- Complete actual copy/frame/context call budget, with BOTH precision/rank VALUE costs explicit. -/
def acquireBound (a u edges : Nat) (t p : List Bool) (axes : List Nat) : Nat :=
  SemiprimeD1StackJetContextCorrectness.budget axes p+
  SemiprimeD1StackJetContextCorrectness.budget (count a u edges t::axes) (precision a u edges t p)+
  6*(p.length+(header axes).length+count a u edges t+(precision a u edges t p).length+1)+20
/-- Every accepted context header/cache is built by one literal paid source, with no q/P/rank advice. -/
theorem source_run (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (ha : accepted a u t=true) (hq : 0<count a u edges t) :
    ∃q≤acquireBound a u edges t p axes,Runs program q .copyOldPrecision (waiting a u edges t p axes)
      .accept (acquired a u edges t p axes) :=by
  have h0:=old_precision a u edges t p axes
  obtain ⟨b,hb,h1⟩:=old_context a u edges t p axes hp
  have h2:=header_copy a u edges t p axes
  have h3:=frame_q a u edges t p axes ha
  have h4:=cons_q a u edges t p axes
  have h5:=precision_copy a u edges t p axes
  obtain ⟨c,hc,h6⟩:=child_context a u edges t p axes hp hq
  refine ⟨_,?_,join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6⟩
  unfold acquireBound
  omega
end RiemannGaussian.SemiprimeD1StackPhaseChildContextSteps
