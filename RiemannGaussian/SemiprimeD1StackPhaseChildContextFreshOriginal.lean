/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshBounds
/-! # Full ORIGINAL FreshJetBits.acquireFresh word-vector acquisition
Every vector constructor, field delimiter and coefficient bit is physically
written by the SAME original-only source. The q=1 axis is exactly all-zero.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshOriginal
open SemiprimeD1StackPhaseChildContextFresh SemiprimeD1StackPhaseChildContextFreshArithmetic
open SemiprimeD1StackPhaseChildContextFreshComponents SemiprimeD1StackPhaseChildContextFreshExecution
open SemiprimeBitArithmetic
namespace Context
export SemiprimeD1StackPhaseChildContextOriginal (oldContext childContext good_original count_original child_context_original)
end Context
/-- Exact original dense words, with q/P acquired from actual original fields by the source. -/
def freshWords (a u edges : Nat) (t p : List Bool) (axes : List Nat) : List (List Bool) :=
  (SemiprimeD1FreshJetBits.acquireFresh (Context.oldContext axes p) (Old.count a u edges t)
    (bitValue (Old.precision a u edges t p))).words
/-- ENTIRE80-role context/P48 bank is retained literally through fresh coefficient allocation. -/
theorem context_retained (a u edges : Nat) (t p : List Bool) (axes : List Nat) (k : H.Stack) :
    result a u edges t p axes (contextStack k)=cache a u edges t p axes k :=rfl
/-- Exact original fresh vector including all framing/delimiters, with no encoded-answer copy. -/
theorem output_original (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=true) :
    result a u edges t p axes (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits (freshWords a u edges t p axes) :=by
  change output a u edges t p axes=_
  simp only [output,hg,ite_true]
  change SemiprimeD1TensorTapeCodec.vectorBits
    (words (Old.count a u edges t*(Context.oldContext axes p).rank) (Context.oldContext axes p).rank
      (decide (0<bitValue (Old.precision a u edges t p))))=_
  rw [words_original]
  rfl
/-- Fresh source retains EXACT context/header/rank/precision from original context acquisition. -/
theorem child_fields (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=true) :
    result a u edges t p axes (contextStack (H.childStack H.J.axesCache))=Old.header (Context.childContext a u edges t p axes).axes ∧
    result a u edges t p axes (contextStack (H.childStack SemiprimeD1StackJetContext.precisionBits))=Old.precision a u edges t p ∧
    result a u edges t p axes (contextStack (H.childStack H.J.rankCache))=SemiprimeD1StackUnaryDivmod.unary (Context.childContext a u edges t p axes).rank ∧
    (result a u edges t p axes (contextStack (H.childStack H.J.widthCache))).length=(Context.childContext a u edges t p axes).precision :=
  SemiprimeD1StackPhaseChildContextOriginal.child_fields a u edges t p axes hg
/-- At q=1, actual allocation has EXACTLY oldrank empty words and no out-of-range unit. -/
theorem one_axis_zero (a u edges : Nat) (t p : List Bool) (axes : List Nat)
    (hg : Old.good a u edges t=true) (hq : Old.count a u edges t=1) :
    result a u edges t p axes (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits (List.replicate axes.prod []) :=by
  rw [output_original a u edges t p axes hg]
  unfold freshWords
  rw [hq,SemiprimeD1FreshJetBits.acquireFresh_one_words]
  rfl
/-- Physical guard/q rejection returns EMPTY fresh-vector output and preserves every actual cache field. -/
theorem rejected_output (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hg : Old.good a u edges t=false) :
    result a u edges t p axes (aux .output)=[] :=by
  change output a u edges t p axes=[]
  simp only [output,hg,Bool.false_eq_true,ite_false]
/-- Both rank copies, byte history and restoration workspace are physically clear at halt. -/
theorem work_clear (a u edges : Nat) (t p : List Bool) (axes : List Nat) :
    result a u edges t p axes (aux .remaining)=[] ∧ result a u edges t p axes (aux .skip)=[] ∧
    result a u edges t p axes (aux .history)=[] ∧ result a u edges t p axes (aux .scratch)=[] :=⟨rfl,rfl,rfl,rfl⟩
/-- Entire fresh vector agrees with the ORIGINAL native phase q/workingPrecision family. -/
theorem output_phase_original (a u edges : Nat) (t p : List Bool) (axes : List Nat)
    (ht : bitValue t<2^(a+1)) (hu : u≤ edges)
    (h : SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    result a u edges t p axes (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1FreshJetBits.acquireFresh (Context.oldContext axes p)
        (SemiprimeD1ModeRate.jetHeight edges u*(u-SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder a t))
        (SemiprimeD1ModeRate.workingPrecision edges u a (SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder a t) (bitValue p))).words :=by
  have hg:Old.good a u edges t=true:=(Context.good_original a u edges t ht hu).mpr h
  rw [output_original a u edges t p axes hg]
  unfold freshWords
  rw [Context.count_original a u edges t p ht h]
  have hP:=SemiprimeD1StackPhaseWorkingPrecisionOriginal.precision_original a u edges t p ht h
  change bitValue (Old.precision a u edges t p)=_ at hP
  rw [hP]
/-- Exact acquired dense words represent the original fresh generator, including q=1's zero element. -/
theorem fresh_value (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (hg : Old.good a u edges t=true) :
    SemiprimeD1JetInterpretation.interpret (Context.childContext a u edges t p axes) (freshWords a u edges t p axes)=
      SemiprimeD1JetAlgebra.generator (SemiprimeD1JetBoxIndex.dims (Old.count a u edges t::axes)) 0 :=by
  exact SemiprimeD1FreshJetBits.fresh_value (Context.oldContext axes p) (Old.count a u edges t)
    (bitValue (Old.precision a u edges t p)) hp ((SemiprimeD1StackPhaseChildContextArithmetic.good_true a u edges t).mp hg).2
/-- SAME whole actual source and entire original fresh vector, with its own VALUE-charged fixed polynomial. -/
theorem source_run_original (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (ht : bitValue t<2^(a+1)) (hu : u≤ edges)
    (h : SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    ∃q≤ 1000000000000000000*(SemiprimeD1StackPhaseChildContextFreshBounds.resource a u edges t p axes+1)^4,
      SemiprimeD1StackCalls.run program q (initial a u edges t p (Old.header axes))=some (done a u edges t p axes) ∧
      (done a u edges t p axes).data (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits (freshWords a u edges t p axes) ∧
      (∀k,(done a u edges t p axes).data (contextStack k)=cache a u edges t p axes k) :=by
  obtain ⟨q,hq,hr⟩:=source_run a u edges t p axes hp
  have hg:Old.good a u edges t=true:=(Context.good_original a u edges t ht hu).mpr h
  exact ⟨q,hq.trans (SemiprimeD1StackPhaseChildContextFreshBounds.run_polynomial a u edges t p axes hp),hr,
    output_original a u edges t p axes hg,fun _=>rfl⟩
/-- SAME actual P48cache continuation produces the entire original fresh vector without phase replay. -/
theorem phase_ready_original (a u edges : Nat) (t p : List Bool) (axes : List Nat) (hp : ∀x∈axes,0<x)
    (hg : Old.good a u edges t=true) :
    ∃q≤ phaseReadyBound a u edges t p axes,
      SemiprimeD1StackCalls.run program q (phaseReady a u edges t p (Old.header axes))=some (done a u edges t p axes) ∧
      (done a u edges t p axes).data (aux .output)=SemiprimeD1TensorTapeCodec.vectorBits (freshWords a u edges t p axes) :=by
  obtain ⟨q,hq,hr⟩:=phase_ready_run a u edges t p axes hp
  exact ⟨q,hq,hr,output_original a u edges t p axes hg⟩
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshOriginal
