/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
/-! # Actual byte-index countdown and physical array terminator -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadCount
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineReadBuffers SemiprimeD1StackProcedureTrace
/-- Only physically materialized byte markers steer array traversal. -/
def unary (n:Nat):List Bool:=List.replicate n true
/-- Empty actual index chooses the current physical row. -/
theorem zero_run (part:Part) (w:Words) (reader:List Bool):
    Runs program 1 (.local (.readCount part)) (bank (buffers w reader []))
      (.local (.readTag part true)) (bank (buffers w reader [])):=by
  have h:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local (.readCount part))
    (.local (.readTag part true)) (.local .abort) (.local (.readTag part false))
    (aux .readTodo) (bank (buffers w reader [])) [] rfl rfl
  rw [update_todo] at h
  exact h
/-- Each actual TRUE marker consumes one later array row rather than expanding a binary numeric address. -/
theorem succ_run (part:Part) (w:Words) (reader:List Bool) (n:Nat):
    Runs program 1 (.local (.readCount part)) (bank (buffers w reader (unary (n+1))))
      (.local (.readTag part false)) (bank (buffers w reader (unary n))):=by
  have h:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local (.readCount part))
    (.local (.readTag part true)) (.local .abort) (.local (.readTag part false))
    (aux .readTodo) (bank (buffers w reader (unary (n+1)))) (true::unary n) rfl
    (by simp [buffers,bank,aux,unary,List.replicate_succ])
  change Runs program 1 _ _ (.local (.readTag part false))
    (Function.update (bank (buffers w reader (unary (n+1)))) (aux .readTodo) (unary n)) at h
  rw [update_todo] at h
  exact h
/-- The actual FALSE vector terminator triggers zero extension while retaining all unrelated words. -/
theorem eof_run (part:Part) (take:Bool) (w:Words) (todo:List Bool):
    Runs program 1 (.local (.readTag part take)) (bank (buffers w (vector []) todo))
      (.local (.missingReader part)) (bank (buffers w [] todo)):=by
  have h:=SemiprimeD1StackRecoveryAffinePrimitives.pop_run (.local (.readTag part take))
    (.local .abort) (.local (.missingReader part)) (.local (.field (.coefficient part take false)))
    (aux .reader) (bank (buffers w (vector []) todo)) [false] rfl rfl
  change Runs program 1 _ _ (.local (.missingReader part))
    (Function.update (bank (buffers w (vector []) todo)) (aux .reader) []) at h
  rw [update_reader] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadCount
