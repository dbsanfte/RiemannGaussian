/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInversePrimitives
import RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
/-! # Actual unary-index and physical array-tag branches -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadHeads
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInversePrimitives
open SemiprimeD1StackProcedureTrace
/-- The actual zero query counter selects this physical array row. -/
theorem count_zero (part : ReadSite) (w : Words) (reader : List Bool) :
    Runs program 1 (.read part .count) (store (buffers w reader []))
      (.read part (.tag true)) (store (buffers w reader [])) := by
  have h:=pop_run (.read part .count) (.read part (.tag true)) (.read part .failed)
    (.read part (.tag false)) (aux .readTodo) (store (buffers w reader [])) [] rfl rfl
  rw [update_todo] at h
  exact h
/-- One paid actual TRUE marker skips one actual row and retains the remaining unary query. -/
theorem count_succ (part : ReadSite) (w : Words) (reader : List Bool) (n : ℕ) :
    Runs program 1 (.read part .count) (store (buffers w reader (unary (n+1))))
      (.read part (.tag false)) (store (buffers w reader (unary n))) := by
  have h:=pop_run (.read part .count) (.read part (.tag true)) (.read part .failed)
    (.read part (.tag false)) (aux .readTodo) (store (buffers w reader (unary (n+1))))
    (true::unary n) rfl (by simp only [store,bank,aux,buffers,unary,List.replicate_succ];rfl)
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
  rw [update_todo] at h
  exact h
/-- A real TRUE row tag exposes its two actual framed fields. -/
theorem tag_row (part : ReadSite) (take : Bool) (w : Words) (reader todo : List Bool) :
    Runs program 1 (.read part (.tag take)) (store (buffers w (true::reader) todo))
      (.read part (.field take false)) (store (buffers w reader todo)) := by
  have h:=pop_run (.read part (.tag take)) (.read part .missingReader) (.read part .missingReader)
    (.read part (.field take false)) (aux .reader) (store (buffers w (true::reader) todo))
    (true::reader) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
  rw [update_reader] at h
  exact h
/-- The actual FALSE array EOF enters the missing-entry literal-zero branch. -/
theorem tag_eof (part : ReadSite) (take : Bool) (w : Words) (todo : List Bool) :
    Runs program 1 (.read part (.tag take)) (store (buffers w [false] todo))
      (.read part .missingReader) (store (buffers w [] todo)) := by
  have h:=pop_run (.read part (.tag take)) (.read part .missingReader) (.read part .missingReader)
    (.read part (.field take false)) (aux .reader) (store (buffers w [false] todo))
    [false] rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h
  rw [update_reader] at h
  exact h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadHeads
