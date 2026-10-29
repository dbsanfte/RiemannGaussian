/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhase
/-! # Full actual238-role component boundaries and literal physical updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseView
open SemiprimeD1StackCachePhase
/-- A physical restore-bank update preserves all other component words. -/
theorem data_restore (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch xs:List Bool) (k:Restore.Stack) :
    Function.update (data restored fold blocks scratch) (restoreStack k) xs=
      data (Function.update restored k xs) fold blocks scratch :=by
  funext j;rcases j with j|j
  · simp only [data,restoreStack,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- A physical fold-bank update preserves the complete restored cache and block bank. -/
theorem data_fold (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch xs:List Bool) (k:Fold.Stack) :
    Function.update (data restored fold blocks scratch) (foldStack k) xs=
      data restored (Function.update fold k xs) blocks scratch :=by
  funext j;rcases j with j|j
  · rfl
  · rcases j with j|j
    · simp only [data,foldStack,Function.update_apply,Sum.elim_inr,Sum.elim_inl,Sum.inr.injEq,Sum.inl.injEq]
    · rfl
/-- A physical block-bank update preserves both complete prior source banks. -/
theorem data_blocks (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch xs:List Bool) (k:Blocks.Stack) :
    Function.update (data restored fold blocks scratch) (blockStack k) xs=
      data restored fold (Function.update blocks k xs) scratch :=by
  funext j;rcases j with j|j
  · rfl
  · rcases j with j|j
    · rfl
    · rcases j with j|j
      · simp only [data,blockStack,Function.update_apply,Sum.elim_inr,Sum.elim_inl,Sum.inr.injEq,Sum.inl.injEq]
      · rfl
/-- The single actual copy scratch is charged and isolated from every component role. -/
theorem data_scratch (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch xs:List Bool) :
    Function.update (data restored fold blocks scratch) copyScratch xs=data restored fold blocks xs :=by
  funext j;rcases j with j|j
  · rfl
  · rcases j with j|j
    · rfl
    · rcases j with j|j
      · rfl
      · cases j;rfl
/-- All actual restored words remain directly available between real component calls. -/
theorem restored_word (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch:List Bool) (k:Restore.Stack) :
    data restored fold blocks scratch (restoreStack k)=restored k :=rfl
/-- All actual fold words remain directly available, including its physically computed output. -/
theorem fold_word (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch:List Bool) (k:Fold.Stack) :
    data restored fold blocks scratch (foldStack k)=fold k :=rfl
/-- All actual block words remain directly available, including all15 retained OLD context roles. -/
theorem block_word (restored:Restore.Stack→List Bool) (fold:Fold.Stack→List Bool)
    (blocks:Blocks.Stack→List Bool) (scratch:List Bool) (k:Blocks.Stack) :
    data restored fold blocks scratch (blockStack k)=blocks k :=rfl
end RiemannGaussian.SemiprimeD1StackCachePhaseView
