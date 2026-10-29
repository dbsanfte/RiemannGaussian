/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueModes

/-! # Actual derived limit caches
R+1 and digitCount-1 use real Copy plus push/pop. The three finite limits use
six literal pushes. All metadata and all cached digit fields survive exactly.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueCaches
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents
open SemiprimeD1StackVertexCatalogueView SemiprimeD1StackVertexCataloguePrepare
open SemiprimeD1StackVertexCatalogueModes
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeMacroParameters
open SemiprimeD1VertexCatalogueModes (Role dimension)

/-- Original physically counted digit-record count, not an algorithm input. -/
def digitCountValue (bits:List Bool) : ℕ := (SemiprimeD1StackDigitCountBounds.originalWords bits).length
/-- Reached store after the actual R copy. -/
def radiusCopy (bits:List Bool) : Stack→List Bool :=
  Function.update (afterCount bits) (cacheStack 4) (List.replicate (transformLength bits.length) true)
/-- Reached store after the actual successor push. -/
def radiusReady (bits:List Bool) : Stack→List Bool :=
  Function.update (afterCount bits) (cacheStack 4) (List.replicate (transformLength bits.length+1) true)
/-- Reached store after the actual acquired digit-count copy. -/
def predCopy (bits:List Bool) : Stack→List Bool :=
  Function.update (radiusReady bits) (cacheStack 3) (List.replicate (digitCountValue bits) true)
/-- Reached store after its one physical predecessor pop (EOF is permitted). -/
def predReady (bits:List Bool) : Stack→List Bool :=
  Function.update (radiusReady bits) (cacheStack 3) (List.replicate (digitCountValue bits-1) true)
/-- Actual one-limit cache. -/
def oneReady (bits:List Bool) : Stack→List Bool := Function.update (predReady bits) (cacheStack 0) [true]
/-- Actual two-limit cache after two pushes. -/
def twoReady (bits:List Bool) : Stack→List Bool := Function.update (oneReady bits) (cacheStack 1) [true,true]
/-- Actual fully initialized readonly base before constructor-tag acquisition. -/
def base (bits:List Bool) : Stack→List Bool := Function.update (twoReady bits) (cacheStack 2) [true,true,true]

/-- Literal push onto an actually updated physical word, with no free replacement. -/
theorem push_updated (pc next:Label) (stack:Stack) (bit:Bool) (data:Stack→List Bool) (word:List Bool)
    (hc:program pc=.base (.push stack bit next)) :
    Runs program 1 pc (Function.update data stack word) next (Function.update data stack (bit::word)) := by
  have h:=push_run pc next stack bit (Function.update data stack word) hc
  rw [Function.update_self] at h
  change Runs program 1 _ _ _ (Function.update (Function.update data stack word) stack (bit::word)) at h
  rw [Function.update_idem] at h
  exact h

/-- The actual radius supplier is copied, not encoded from a desired natural answer. -/
theorem radius_copy (bits:List Bool) :
    Runs program (5*transformLength bits.length+4) (.inl .copyRadiusSucc) (afterCount bits)
      (.inl .incRadiusSucc) (radiusCopy bits) := by
  have h:=copy_call .radiusSucc (afterCount bits) rfl (.inl .copyRadiusSucc) (.inl .incRadiusSucc) rfl
  have hs:afterCount bits (copyInput .radiusSucc)=List.replicate (transformLength bits.length) true:=rfl
  have hd:afterCount bits (copyOutput .radiusSucc)=[]:=rfl
  rw [hs,hd,List.append_nil,List.length_replicate] at h
  exact h

/-- One actual allocated marker acquires R+1. -/
theorem radius_push (bits:List Bool) :
    Runs program 1 (.inl .incRadiusSucc) (radiusCopy bits) (.inl .copyDigitsPred) (radiusReady bits) := by
  have h:=push_updated (.inl .incRadiusSucc) (.inl .copyDigitsPred) (cacheStack 4) true (afterCount bits)
    (List.replicate (transformLength bits.length) true) rfl
  simpa only [radiusCopy,radiusReady,List.replicate_succ] using h

/-- The actual parser-produced digit counter is copied, never supplied by a quotient oracle. -/
theorem pred_copy (bits:List Bool) :
    Runs program (5*digitCountValue bits+4) (.inl .copyDigitsPred) (radiusReady bits)
      (.inl .popDigitsPred) (predCopy bits) := by
  have h:=copy_call .digitsPred (radiusReady bits) rfl (.inl .copyDigitsPred) (.inl .popDigitsPred) rfl
  have hs:radiusReady bits (copyInput .digitsPred)=List.replicate (digitCountValue bits) true:=rfl
  have hd:radiusReady bits (copyOutput .digitsPred)=[]:=rfl
  rw [hs,hd,List.append_nil,List.length_replicate] at h
  exact h

/-- One physical pop acquires the original predecessor, including its exact zero branch. -/
theorem pred_pop (bits:List Bool) :
    Runs program 1 (.inl .popDigitsPred) (predCopy bits) (.inl (.constants 0)) (predReady bits) := by
  have h:=pop_run (.inl .popDigitsPred) (.inl (.constants 0)) (cacheStack 3) (predCopy bits) rfl
  change Runs program 1 _ _ _ (Function.update (Function.update (radiusReady bits) (cacheStack 3)
    (List.replicate (digitCountValue bits) true)) (cacheStack 3) (List.replicate (digitCountValue bits) true).tail) at h
  rw [List.tail_replicate,Function.update_idem] at h
  exact h

/-- All finite limits are physically built by the six displayed literal pushes. -/
theorem constants_run (bits:List Bool) :
    Runs program 6 (.inl (.constants 0)) (predReady bits) (.inl (.initTag 0)) (base bits) := by
  have h0:=push_run (.inl (.constants 0)) (.inl (.constants 1)) (cacheStack 0) true (predReady bits) rfl
  change Runs program 1 _ _ _ (oneReady bits) at h0
  have h1:=push_run (.inl (.constants 1)) (.inl (.constants 2)) (cacheStack 1) true (oneReady bits) rfl
  change Runs program 1 _ _ _ (Function.update (oneReady bits) (cacheStack 1) [true]) at h1
  have h2:=push_updated (.inl (.constants 2)) (.inl (.constants 3)) (cacheStack 1) true (oneReady bits) [true] rfl
  have h3:=push_run (.inl (.constants 3)) (.inl (.constants 4)) (cacheStack 2) true (twoReady bits) rfl
  change Runs program 1 _ _ _ (Function.update (twoReady bits) (cacheStack 2) [true]) at h3
  have h4:=push_updated (.inl (.constants 4)) (.inl (.constants 5)) (cacheStack 2) true (twoReady bits) [true] rfl
  have h5:=push_updated (.inl (.constants 5)) (.inl (.initTag 0)) (cacheStack 2) true (twoReady bits) [true,true] rfl
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

/-- Complete actual derived-cache construction retains all earlier source work and values. -/
theorem caches_run (bits:List Bool) :
    Runs program (5*transformLength bits.length+5*digitCountValue bits+16)
      (.inl .copyRadiusSucc) (afterCount bits) (.inl (.initTag 0)) (base bits) := by
  have h:=(radius_copy bits).trans ((radius_push bits).trans ((pred_copy bits).trans ((pred_pop bits).trans (constants_run bits))))
  simpa only [show (5*transformLength bits.length+4)+(1+((5*digitCountValue bits+4)+(1+6)))=
    5*transformLength bits.length+5*digitCountValue bits+16 by omega] using h

/-- Every kernel role is actually untouched and empty before tag initialization. -/
theorem base_kernel (bits:List Bool) (k:Kernel.Stack) : base bits (kernelStack k)=[] := rfl
/-- The outer-copy scratch really is empty after the actual cache constructor. -/
theorem base_scratch (bits:List Bool) : base bits scratchStack=[] := rfl
/-- The mathematical kernel view equals the actually constructed entire base store. -/
theorem base_view (bits:List Bool) : view (base bits) (fun _=>[]) [] []=base bits := by
  funext k
  rcases k with k|k|k|k|k
  · rfl
  · rfl
  · change view (base bits) (fun _=>[]) [] [] (kernelStack k)=base bits (kernelStack k)
    rw [view_kernel,base_kernel]
    rcases k with k|k|k
    · rfl
    · rfl
    · fin_cases k <;> rfl
  · rfl
  · rfl

/-- All source formats are derived from physical Root/cache-count/copy/push acquisition. -/
theorem base_format (bits:List Bool) :
    RoleFormat (firstAxis bits.length) (secondAxis bits.length) (digitCountValue bits) (base bits) := by
  intro role
  cases role with
  | one => rfl
  | two => rfl
  | three => rfl
  | radius =>
    change List.replicate (transformLength bits.length) true=List.replicate (firstAxis bits.length*secondAxis bits.length) true
    rw [axes_product]
  | firstAxis => rfl
  | secondAxis => rfl
  | digits => rfl
  | digitsPred => rfl
  | radiusSucc =>
    change List.replicate (transformLength bits.length+1) true=List.replicate (firstAxis bits.length*secondAxis bits.length+1) true
    rw [axes_product]
end RiemannGaussian.SemiprimeD1StackVertexCatalogueCaches
