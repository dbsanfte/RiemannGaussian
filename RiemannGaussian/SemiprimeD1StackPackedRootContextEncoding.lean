/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootContext
/-! # Exact whole28-role metadata/context boundaries -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPackedRootContextEncoding
open SemiprimeD1StackPackedRootContext
/-- Exact cache-ready entry, following the real metadata source. -/
def ready (bits : List Bool) : C.State Stack Label :=
  ⟨some (.inl .copyPrecision),none,none,data (M.result bits) (fun _ => []),[]⟩
/-- Actual state after the preserving copy of the derived binary precision. -/
def copied (bits : List Bool) : Stack→List Bool :=
  data (M.result bits) (J.initial [] (M.precisionWord bits.length)).data
/-- Actual FALSE-terminated empty-axis header, not a supplied context cache. -/
def prepared (bits : List Bool) : Stack→List Bool :=
  data (M.result bits) (J.initial [false] (M.precisionWord bits.length)).data
/-- Entire retained metadata source and ALL15 actually acquired context words. -/
def result (bits : List Bool) : Stack→List Bool :=
  data (M.result bits) (SemiprimeD1StackJetContextCorrectness.finalData [] (M.precisionWord bits.length))
/-- Genuine clean halt after both actual acquisitions. -/
def done (bits : List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Actual metadata update retains all15 context allocations. -/
theorem data_metadata (m : M.Stack→List Bool) (j : J.Stack→List Bool) (k : M.Stack) (xs : List Bool) :
    Function.update (data m j) (metadata k) xs=data (Function.update m k xs) j := by
  funext p
  rcases p with p|p
  · simp only [data,metadata,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Every actual context update retains the entire physically acquired metadata. -/
theorem data_context (m : M.Stack→List Bool) (j : J.Stack→List Bool) (k : J.Stack) (xs : List Bool) :
    Function.update (data m j) (context k) xs=data m (Function.update j k xs) := by
  funext p
  rcases p with p|p
  · rfl
  · simp only [data,context,Function.update_apply,Sum.elim_inr,Sum.inr.injEq]
/-- The empty actual context source contains no prepared rank or precision. -/
theorem empty_context : (J.initial [] []).data=(fun _ => []) := by
  funext k
  rcases k with k|k|k
  · cases k <;> rfl
  · cases k <;> rfl
  · fin_cases k <;> rfl
/-- Real binary-precision copy changes only the actual source-input cache. -/
theorem context_precision (axes p xs : List Bool) :
    Function.update (J.initial axes p).data J.precisionBits xs=(J.initial axes xs).data := by
  funext k
  rcases k with k|k|k
  · rfl
  · rfl
  · fin_cases k <;> rfl
/-- The literal FALSE push changes only the axis source header. -/
theorem context_axes (axes p xs : List Bool) :
    Function.update (J.initial axes p).data J.axesCache xs=(J.initial xs p).data := by
  funext k
  rcases k with k|k|k
  · rfl
  · rfl
  · fin_cases k <;> rfl
/-- The precision came from the actual width-driven binary counter. -/
theorem metadata_precision (bits : List Bool) :
    M.result bits (M.aux .precision)=M.precisionWord bits.length := rfl
/-- The borrowed copy scratch is empty at the actual metadata halt. -/
theorem metadata_scratch (bits : List Bool) : M.result bits (M.aux .copyScratch)=[] := rfl
end RiemannGaussian.SemiprimeD1StackPackedRootContextEncoding
