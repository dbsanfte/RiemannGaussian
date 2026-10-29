/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseCacheFreshBounds
/-! # Exact original fresh generator from actual serialized phase-cache bytes
The caller supplies physical allocator/header words only. These proofs identify
the actual selected record as a stopped P48 cache and conclude exact original
fresh coefficient/context output on the SAME literal restore→Fresh program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPhaseCacheFreshOriginal
open SemiprimeD1StackPhaseCacheFresh SemiprimeD1StackPhaseCacheFreshComponents
open SemiprimeD1StackPhaseCacheFreshExecution
open SemiprimeBitArithmetic
namespace Old
export SemiprimeD1StackPhaseChildContextFreshOriginal (freshWords output_original one_axis_zero rejected_output output_phase_original)
export SemiprimeD1StackPhaseChildContextArithmetic (good)
end Old
/-- All85 actually USED Fresh role projections equal the exact actual frozen ready-source result. -/
theorem fresh_result (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (k:F.Stack) :
    (done banks i a u edges t p axes).data (freshStack k)=
      SemiprimeD1StackPhaseChildContextFreshComponents.result a u edges t p axes k :=fresh_data _ _ k
/-- The restored complete48-role phase bank is retained, with no extra physical cache copy. -/
theorem phase_retained (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hbank:banks[i.val]=phase a u edges t p) (k:P.Stack) :
    (done banks i a u edges t p axes).data (restoreStack (R.phaseStack k))=banks[i.val] k :=by
  rw [hbank]
  rfl
/-- Every actual heap/count/reference word survives, and ALL10reader work/output/flags are clear. -/
theorem heap_retained (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (k:Heap.Stack) :
    (done banks i a u edges t p axes).data (restoreStack (R.heapStack k))=
      Heap.input (heap banks) (List.replicate banks.length true) (List.replicate i.val true) k :=rfl
/-- ALL48allocated private P48 shadow words remain EMPTY; the actualbank is directly shared. -/
theorem shadows_empty (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (k:P.Stack) :
    (done banks i a u edges t p axes).data (.inr (F.contextStack (H.phaseStack k)))=[] :=rfl
/-- Entire original acquireFresh coefficient vector and codec, not merely a context header. -/
theorem output_original (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hg:Old.good a u edges t=true) :
    (done banks i a u edges t p axes).data output=
      SemiprimeD1TensorTapeCodec.vectorBits (Old.freshWords a u edges t p axes) :=by
  rw [show output=freshStack (F.aux .output) from rfl,fresh_result]
  exact Old.output_original a u edges t p axes hg
/-- Exact q=1 edge case physically emits oldrank zero coefficients and no out-of-range unit. -/
theorem one_axis_zero (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hg:Old.good a u edges t=true)
    (hq:SemiprimeD1StackPhaseChildContextPrimitives.count a u edges t=1) :
    (done banks i a u edges t p axes).data output=
      SemiprimeD1TensorTapeCodec.vectorBits (List.replicate axes.prod []) :=by
  rw [show output=freshStack (F.aux .output) from rfl,fresh_result]
  exact Old.one_axis_zero a u edges t p axes hg hq
/-- Precision-zero scalar reduction is exact: every actual coefficient word is EMPTY. -/
theorem precision_zero (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hg:Old.good a u edges t=true)
    (hP:bitValue (SemiprimeD1StackPhaseChildContextPrimitives.precision a u edges t p)=0) :
    (done banks i a u edges t p axes).data output=
      SemiprimeD1TensorTapeCodec.vectorBits
        (List.replicate (SemiprimeD1StackPhaseChildContextFreshComponents.rank a u edges t axes) []) :=by
  rw [output_original banks i a u edges t p axes hg]
  unfold Old.freshWords
  rw [hP]
  simp only [SemiprimeD1FreshJetBits.acquireFresh,show (SemiprimeD1JetScalarBits.reduce 0 [true]).bits=[] from rfl,
    ite_self,List.map_const',List.length_range]
  rfl
/-- Physical verdict/q rejection produces an EMPTY vector and no fresh allocation/context work. -/
theorem rejected_output (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hg:Old.good a u edges t=false) :
    (done banks i a u edges t p axes).data output=[] :=by
  rw [show output=freshStack (F.aux .output) from rfl,fresh_result]
  exact Old.rejected_output a u edges t p axes hg
/-- All actual context/header/rank/P48/original-binary-precision caches are retained identically. -/
theorem context_retained (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (k:H.Stack) :
    (done banks i a u edges t p axes).data (freshStack (F.contextStack k))=
      SemiprimeD1StackPhaseChildContextFreshComponents.cache a u edges t p axes k :=by
  rw [fresh_result]
  rfl
/-- Exact original workingPrecision/orderFuel/q family on the complete same-program vector output. -/
theorem output_phase_original (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (ht:bitValue t<2^(a+1)) (hu:u≤ edges)
    (h:SemiprimeD1StackPhaseGeometryGuardOriginal.originalGuard a u t) :
    (done banks i a u edges t p axes).data output=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1FreshJetBits.acquireFresh (SemiprimeD1StackPhaseChildContextOriginal.oldContext axes p)
        (SemiprimeD1ModeRate.jetHeight edges u*(u-SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder a t))
        (SemiprimeD1ModeRate.workingPrecision edges u a (SemiprimeD1StackPhaseWorkingPrecisionOriginal.originalOrder a t) (bitValue p))).words :=by
  rw [show output=freshStack (F.aux .output) from rfl,fresh_result]
  exact Old.output_phase_original a u edges t p axes ht hu h
/-- Full SAME actual consumer starts with heap/count/reference/header ONLY and emits the entire fresh vector. -/
theorem source_run_original (banks:List (P.Stack→List Bool)) (i:Fin banks.length)
    (a u edges:Nat) (t p:List Bool) (axes:List Nat) (hp:∀x∈axes,0<x)
    (hbank:banks[i.val]=phase a u edges t p) (hg:Old.good a u edges t=true) :
    ∃q≤ 1000000000000*(SemiprimeD1StackPhaseCacheFreshBounds.resource banks i a u edges t p axes+1)^2,
      SemiprimeD1StackCalls.run program q (source banks i axes)=some (done banks i a u edges t p axes) ∧
      (done banks i a u edges t p axes).data output=SemiprimeD1TensorTapeCodec.vectorBits (Old.freshWords a u edges t p axes) ∧
      (∀k,(done banks i a u edges t p axes).data (restoreStack (R.phaseStack k))=banks[i.val] k) ∧
      (∀k,(done banks i a u edges t p axes).data (.inr (F.contextStack (H.phaseStack k)))=[]) :=by
  obtain ⟨q,hq,hr⟩:=source_run banks i a u edges t p axes hp hbank
  exact ⟨q,hq.trans (SemiprimeD1StackPhaseCacheFreshBounds.run_polynomial banks i a u edges t p axes hp),hr,
    output_original banks i a u edges t p axes hg,phase_retained banks i a u edges t p axes hbank,fun _=>rfl⟩
end RiemannGaussian.SemiprimeD1StackPhaseCacheFreshOriginal
