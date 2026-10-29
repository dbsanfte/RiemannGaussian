/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueComponents

/-! # Exact physical frontend store views and literal instruction effects
The base is the actually acquired readonly payload. These are proof views,
not supplied state/storage answers or runtime native array operations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueView
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1VertexCatalogueModes (Mode Role)

/-- Exact global store with actual cleared kernel work and explicit limit/tag/output words. -/
def view (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool) : Stack→List Bool
  | .inr (.inr (.inl k)) => SemiprimeD1StackCartesian4Components.store limits
      SemiprimeD1StackCartesian4Bounds.emptyIndices tag output k
  | k => base k

/-- The physical kernel substore is read literally. -/
theorem view_kernel (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool) (k:Kernel.Stack) :
    view base limits tag output (kernelStack k)=SemiprimeD1StackCartesian4Components.store limits
      SemiprimeD1StackCartesian4Bounds.emptyIndices tag output k := rfl
/-- All source-role words are the actual readonly base words. -/
theorem view_role (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool) (role:Role) :
    view base limits tag output (roleStack role)=base (roleStack role) := by cases role <;> rfl
/-- The separate outer-copy scratch is retained exactly. -/
theorem view_scratch (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output:List Bool) :
    view base limits tag output scratchStack=base scratchStack := rfl

/-- An actual kernel-limit write changes only that physical limit. -/
theorem view_limit (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output word:List Bool) (axis:Fin 4) :
    Function.update (view base limits tag output) (kernelStack (Kernel.limitStack axis)) word=
      view base (Function.update limits axis word) tag output := by
  funext k
  rcases k with k|k|k|k|k
  · simp [view,kernelStack,Kernel.limitStack,Function.update]
  · simp [view,kernelStack,Kernel.limitStack,Function.update]
  · rcases k with k|k|k
    · by_cases h:k=axis
      · subst k;simp [view,kernelStack,Kernel.limitStack,SemiprimeD1StackCartesian4Components.store,Function.update]
      · simp [view,kernelStack,Kernel.limitStack,SemiprimeD1StackCartesian4Components.store,Function.update,h]
    · simp [view,kernelStack,Kernel.limitStack,SemiprimeD1StackCartesian4Components.store,Function.update]
    · simp [view,kernelStack,Kernel.limitStack,SemiprimeD1StackCartesian4Components.store,Function.update]
  · simp [view,kernelStack,Kernel.limitStack,Function.update]
  · simp [view,kernelStack,Kernel.limitStack,Function.update]

/-- An actual record-output update preserves every readonly source and limit. -/
theorem view_output (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output word:List Bool) :
    Function.update (view base limits tag output) (kernelStack (Kernel.aux 2)) word=view base limits tag word := by
  funext k
  rcases k with k|k|k|k|k
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · rcases k with k|k|k
    · simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
    · simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
    · fin_cases k <;> simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]

/-- An actual constructor-tag update preserves its complete physical surroundings. -/
theorem view_tag (base:Stack→List Bool) (limits:Fin 4→List Bool) (tag output word:List Bool) :
    Function.update (view base limits tag output) (kernelStack (Kernel.aux 3)) word=view base limits word output := by
  funext k
  rcases k with k|k|k|k|k
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · rcases k with k|k|k
    · simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
    · simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
    · fin_cases k <;> simp [view,kernelStack,Kernel.aux,SemiprimeD1StackCartesian4Components.store,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]
  · simp [view,kernelStack,Kernel.aux,Function.update]

/-- A literal global push, including its actual data-cell allocation. -/
theorem push_run (pc next:Label) (stack:Stack) (bit:Bool) (data:Stack→List Bool)
    (hc:program pc=.base (.push stack bit next)) :
    Runs program 1 pc data next (Function.update data stack (bit::data stack)) := by
  exact one_base program pc next (.push stack bit next) data _ hc rfl rfl

/-- A literal global pop with one continuation, including actual EOF. -/
theorem pop_run (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hc:program pc=.base (.pop stack next next next)) :
    Runs program 1 pc data next (Function.update data stack (data stack).tail) := by
  apply one_base program pc next (.pop stack next next next) data _ hc
  · cases h:(data stack).head? with
    | none => simp [B.execute,SemiprimeD1StackBytecode.choose,h]
    | some bit => cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,h]
  · rfl

/-- Every old limit byte is physically cleared; no stale field is discarded for free. -/
theorem clear_run (word:List Bool) (pc next:Label) (stack:Stack) (data:Stack→List Bool)
    (hw:data stack=word) (hc:program pc=.base (.pop stack next pc pc)) :
    Runs program (word.length+1) pc data next (Function.update data stack []) := by
  induction word generalizing data with
  | nil =>
    apply one_base program pc next (.pop stack next pc pc) data _ hc
    · simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
    · change Function.update data stack (data stack).tail=_
      rw [hw,List.tail_nil]
  | cons bit word ih =>
    have h0:Runs program 1 pc data pc (Function.update data stack word):=by
      apply one_base program pc pc (.pop stack next pc pc) data _ hc
      · cases bit <;> simp [B.execute,SemiprimeD1StackBytecode.choose,hw]
      · change Function.update data stack (data stack).tail=_
        rw [hw,List.tail_cons]
    have h1:=ih (Function.update data stack word) (Function.update_self _ _ _)
    have h:=h0.trans h1
    rw [Function.update_idem] at h
    simpa only [List.length_cons,show 1+(word.length+1)=word.length+1+1 by omega] using h
end RiemannGaussian.SemiprimeD1StackVertexCatalogueView
