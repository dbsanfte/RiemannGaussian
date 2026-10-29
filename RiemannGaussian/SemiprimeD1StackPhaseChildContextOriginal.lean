/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextBounds
/-! # Exact original fresh-child context on the physical whole/ready source
This theorem acquires context headers/caches. Fresh coefficient allocation is a
separate physical stage; it is not claimed by the header result alone.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextOriginal
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
open SemiprimeD1StackPhaseChildContextArithmetic SemiprimeD1StackPhaseChildContextComponents
open SemiprimeD1StackPhaseChildContextExecution
open SemiprimeBitArithmetic
namespace Old
export SemiprimeD1StackPhaseWorkingPrecisionOriginal (originalOrder accepted_original precision_original blocks_retained)
end Old
/-- The caller's physical old header and binary p name exactly this original context. -/
def oldContext (axes : List Nat) (p : List Bool) : SemiprimeD1JetAxes.Context :=⟨axes,bitValue p⟩
/-- Original fresh-child context whose new dimension/precision are acquired by P48. -/
def childContext (a u edges : Nat) (t p : List Bool) (axes : List Nat) : SemiprimeD1JetAxes.Context :=
  SemiprimeD1FreshJetBits.context (oldContext axes p) (count a u edges t) (bitValue (precision a u edges t p))
/-- All48 actual phase/cache fields survive both context suppliers and all paid copies. -/
theorem phase_retained (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : P.Stack) :
    result a u edges t p axes (phaseStack k)=phase a u edges t p k :=rfl
/-- Original arbitrary-precision p remains BINARY and literally identical in the retained phase bank. -/
theorem original_precision_retained (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    result a u edges t p axes originalPrecision=p :=rfl
/-- Exact context-presence flag is written by physical guard/q peeks and actual accept/reject push. -/
theorem presence (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    result a u edges t p axes (aux .valid)=[good a u edges t] :=rfl
/-- BOTH complete15-role caches are the exact outputs of their real context suppliers. -/
theorem acquired_caches (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : good a u edges t=true) :
    (∀k,result a u edges t p axes (oldStack k)=contextResult axes p k) ∧
    (∀k,result a u edges t p axes (childStack k)=
      contextResult (count a u edges t::axes) (precision a u edges t p) k) :=by
  constructor <;> intro k <;> simp only [result,hg,ite_true,store,oldStack,childStack,Sum.elim_inl,Sum.elim_inr]
/-- Exact original child axes header, binary P, unary acquired rank and physical width length. -/
theorem child_fields (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : good a u edges t=true) :
    result a u edges t p axes (childStack J.axesCache)=header (childContext a u edges t p axes).axes ∧
    result a u edges t p axes (childStack J.precisionBits)=precision a u edges t p ∧
    result a u edges t p axes (childStack J.rankCache)=SemiprimeD1StackUnaryDivmod.unary (childContext a u edges t p axes).rank ∧
    (result a u edges t p axes (childStack J.widthCache)).length=(childContext a u edges t p axes).precision :=by
  have hc:∀k,result a u edges t p axes (childStack k)=contextResult (count a u edges t::axes) (precision a u edges t p) k:=
    (acquired_caches a u edges t p axes hg).2
  rw [hc,hc,hc,hc]
  exact ⟨rfl,rfl,rfl,SemiprimeD1StackJetContextCorrectness.width_value _ _⟩
/-- Oldrank derives from the original physical axes and is retained for coefficient allocation. -/
theorem old_fields (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : good a u edges t=true) :
    result a u edges t p axes (oldStack J.axesCache)=header axes ∧
    result a u edges t p axes (oldStack J.precisionBits)=p ∧
    result a u edges t p axes (oldStack J.rankCache)=SemiprimeD1StackUnaryDivmod.unary (oldContext axes p).rank ∧
    (result a u edges t p axes (oldStack J.widthCache)).length=bitValue p :=by
  have hc:= (acquired_caches a u edges t p axes hg).1
  rw [hc,hc,hc,hc]
  exact ⟨rfl,rfl,rfl,SemiprimeD1StackJetContextCorrectness.width_value _ _⟩
/-- Exact new context rank is q*oldrank, with BOTH ranks acquired from actual headers. -/
theorem child_rank (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    (childContext a u edges t p axes).rank=count a u edges t*(oldContext axes p).rank :=rfl
/-- Rejection leaves ALL15 child fields EMPTY and does not acquire oldrank/width/precision. -/
theorem rejected_caches (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : good a u edges t=false) :
    (∀k,result a u edges t p axes (childStack k)=[]) ∧
    result a u edges t p axes (oldStack J.axesCache)=header axes ∧
    result a u edges t p axes (oldStack J.precisionBits)=[] ∧
    result a u edges t p axes (oldStack J.rankCache)=[] ∧
    result a u edges t p axes (oldStack J.widthCache)=[] :=by
  constructor
  · intro k
    change (if good a u edges t then contextResult (count a u edges t::axes) (precision a u edges t p) else emptyContext) k=[]
    rw [hg];exact SemiprimeD1StackPhaseChildContextBounds.empty_context k
  · simp only [result,hg,Bool.false_eq_true,ite_false]
    exact ⟨rfl,rfl,rfl,rfl⟩
/-- Every original active phase has positive actual q under the parent's actual u≤ M fact. -/
theorem good_original (a u edges : Nat) (t : List Bool) (ht : bitValue t<2^(a+1)) (hu : u≤ edges) :
    good a u edges t=true ↔ SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t :=by
  rw [good_true]
  constructor
  · exact fun h=>(Old.accepted_original a u t ht).mp h.1
  · intro h
    have ha:accepted a u t=true:=(Old.accepted_original a u t ht).mpr h
    exact ⟨ha,count_positive a u edges t ha hu⟩
/-- The literal acquired unary q has exactly the original height*(u-orderFuel) value. -/
theorem count_original (a u edges : Nat) (t p : List Bool) (ht : bitValue t<2^(a+1))
    (h : SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    count a u edges t=SemiprimeD1ModeRate.jetHeight edges u*(u-Old.originalOrder a t) :=by
  have ha:accepted a u t=true:=(Old.accepted_original a u t ht).mpr h
  have h0:=count_word a u edges t p ha
  have h1:=Old.blocks_retained a u edges t p ht h
  change phase a u edges t p (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .q))=_ at h1
  rw [h0] at h1
  have hl:=congrArg List.length h1
  simpa only [SemiprimeD1StackUnaryDivmod.unary,List.length_replicate] using hl
/-- Acquired new context is EXACTLY original FreshJetBits.context, including original workingPrecision. -/
theorem child_context_original (a u edges : Nat) (t p : List Bool) (axes : List Nat) (ht : bitValue t<2^(a+1))
    (h : SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    childContext a u edges t p axes=SemiprimeD1FreshJetBits.context (oldContext axes p)
      (SemiprimeD1ModeRate.jetHeight edges u*(u-Old.originalOrder a t))
      (SemiprimeD1ModeRate.workingPrecision edges u a (Old.originalOrder a t) (bitValue p)) :=by
  unfold childContext
  rw [count_original a u edges t p ht h]
  have hv:=Old.precision_original a u edges t p ht h
  change bitValue (precision a u edges t p)=_ at hv
  rw [hv]
/-- SAME whole program, its own VALUE-charged clock, and exact original acquired context hold together. -/
theorem source_run_original (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (ht : bitValue t<2^(a+1)) (hu : u≤ edges)
    (h : SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    ∃q≤ 1000000000000000*(SemiprimeD1StackPhaseChildContextBounds.resource a u edges t p axes+1)^4,
      SemiprimeD1StackCalls.run program q (initial a u edges t p (header axes))=some (done a u edges t p axes) ∧
      (done a u edges t p axes).data (aux .valid)=[true] ∧
      (done a u edges t p axes).data (childStack J.axesCache)=header (childContext a u edges t p axes).axes ∧
      (done a u edges t p axes).data (childStack J.rankCache)=SemiprimeD1StackUnaryDivmod.unary (childContext a u edges t p axes).rank :=by
  obtain ⟨q,hq,hr⟩:=source_run a u edges t p axes hp
  have hg:good a u edges t=true:=(good_original a u edges t ht hu).mpr h
  have hc:=child_fields a u edges t p axes hg
  exact ⟨q,hq.trans (SemiprimeD1StackPhaseChildContextBounds.run_polynomial a u edges t p axes hp),hr,
    by change [good a u edges t]=[true];rw [hg],hc.1,hc.2.2.1⟩
end RiemannGaussian.SemiprimeD1StackPhaseChildContextOriginal
