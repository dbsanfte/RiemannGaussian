/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScalePrimitives
/-! # Physical public scale acquisition phase views
All functions below describe reached stack contents for proofs. They are not
fields of executing finite control or supplied data/evaluator/oracle arguments.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleState
open SemiprimeD1StackPublicScale
/-- The real original root-source acquisition's complete physical cache. -/
def roots (bits : List Bool) : R.Stack→List Bool := (SemiprimeD1StackRootSourceExecution.done bits).data
/-- Actual acquired modulus WORD, never an input modulus answer. -/
def cached (bits : List Bool) : List Bool := roots bits (.inl R.modulusKey)
/-- Actual retained original forward/inverse source bytes, selected by physical Bool. -/
def baseCode (bits : List Bool) (inverse : Bool) : List Bool :=
  roots bits (.inr (if inverse then .root else .forwardRoot))
/-- Physical prepared whole-dot input; proof view only. -/
def dotInput (raw base stride frequency count cached : List Bool) : I.Stack→List Bool :=
  (I.initial raw ⟨base,stride,frequency,count⟩ cached []).data
/-- Reached whole store after original root acquisition, before physical selection. -/
def acquired (bits raw stride frequency : List Bool) (inverse : Bool) : Stack→List Bool :=
  store (roots bits) (dotInput [] [] stride frequency [] []) raw [inverse] [] [] [] [] []
/-- Same reached physical selector store after its actual singleton pop. -/
def selected (bits raw stride frequency : List Bool) : Stack→List Bool :=
  store (roots bits) (dotInput [] [] stride frequency [] []) raw [] [] [] [] [] []
/-- Full physical prefix of zero cells, one per acquired modulus word cell. -/
def paddedRaw (bits raw : List Bool) : List Bool := List.replicate (cached bits).length false++raw
/-- ACTUAL prepared cache after paid source/M/raw copies, zero padding, literal2. -/
def prepared (bits raw stride frequency : List Bool) (inverse : Bool) : Stack→List Bool :=
  store (roots bits) (dotInput (paddedRaw bits raw) (baseCode bits inverse) stride frequency
    [true,true] (cached bits)) raw [] [] [] [] [] []
private theorem update_left {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A→List Bool) (g : B→List Bool) (a : A) (v : List Bool) :
    Function.update (Sum.elim f g) (.inl a) v=Sum.elim (Function.update f a v) g := by
  funext k;rcases k with k|k
  · by_cases h : k=a <;> simp [Function.update,h]
  · rfl
private theorem update_right {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A→List Bool) (g : B→List Bool) (b : B) (v : List Bool) :
    Function.update (Sum.elim f g) (.inr b) v=Sum.elim f (Function.update g b v) := by
  funext k;rcases k with k|k
  · rfl
  · by_cases h : k=b <;> simp [Function.update,h]
/-- Exact full-store update when an included dot role is physically written. -/
theorem store_dot_update (root : R.Stack→List Bool) (dot : I.Stack→List Bool)
    (raw selector padding scratch count word output : List Bool) (k : I.Stack) (v : List Bool) :
    Function.update (store root dot raw selector padding scratch count word output) (dotStack k) v=
      store root (Function.update dot k v) raw selector padding scratch count word output := by
  unfold store dotStack
  rw [update_right,update_left]
/-- Literal source-code cache update; no native source transport is executed. -/
theorem dot_base (raw base stride frequency count cached next : List Bool) :
    Function.update (dotInput raw base stride frequency count cached) baseRole next=
      dotInput raw next stride frequency count cached := by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> rfl
      · rfl
    · rfl
  · rfl
/-- Literal modulus cache update after an ACTUAL preserving copy. -/
theorem dot_modulus (raw base stride frequency count cached next : List Bool) :
    Function.update (dotInput raw base stride frequency count cached)
      (.inl SemiprimeD1StackInputDotEvaluate.modulusRole) next=
      dotInput raw base stride frequency count next := by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
    · rfl
  · rfl
/-- The actual raw-copy/zero-padding writes affect only the original raw role. -/
theorem dot_raw (raw base stride frequency count cached next : List Bool) :
    Function.update (dotInput raw base stride frequency count cached) I.rawRole next=
      dotInput next base stride frequency count cached := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k <;> fin_cases k <;> rfl
/-- The two literal pushes populate the actual shared producer/dot count role. -/
theorem dot_count (raw base stride frequency count cached next : List Bool) :
    Function.update (dotInput raw base stride frequency count cached) countRole next=
      dotInput raw base stride frequency next cached := by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> rfl
      · rfl
    · rfl
  · rfl
/-- Generic reached setup phase, used solely to expose actual physical writes. -/
def stage (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count : List Bool) : Stack→List Bool :=
  store root (dotInput work base stride frequency count cached) raw selector padding [] [] [] []
/-- Actual private padding update is a literal whole-store update. -/
theorem stage_padding (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count) (auxRole .padding) next=
      stage root raw stride frequency selector base cached work next count := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Actual selector pop affects no other original/cache bytes. -/
theorem stage_selector (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count) (auxRole .selector) next=
      stage root raw stride frequency next base cached work padding count := by
  funext k;rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Literal cached-base update within a reached complete stage. -/
theorem stage_base (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count) (dotStack baseRole) next=
      stage root raw stride frequency selector next cached work padding count := by
  rw [stage,store_dot_update,dot_base];rfl
/-- Literal actual-modulus copy update within the complete stage. -/
theorem stage_modulus (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count)
      (dotStack (.inl SemiprimeD1StackInputDotEvaluate.modulusRole)) next=
      stage root raw stride frequency selector base next work padding count := by
  rw [stage,store_dot_update,dot_modulus];rfl
/-- Literal raw-word update within the complete stage. -/
theorem stage_raw (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count) (dotStack I.rawRole) next=
      stage root raw stride frequency selector base cached next padding count := by
  rw [stage,store_dot_update,dot_raw];rfl
/-- Literal shared count-cache update within the complete stage. -/
theorem stage_count (root : R.Stack→List Bool) (raw stride frequency selector base cached work padding count next : List Bool) :
    Function.update (stage root raw stride frequency selector base cached work padding count) (dotStack countRole) next=
      stage root raw stride frequency selector base cached work padding next := by
  rw [stage,store_dot_update,dot_count];rfl
end RiemannGaussian.SemiprimeD1StackPublicScaleState
