/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductState
/-! # Actual physical buffer copies and cleanup in the vertex-product caller -/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackVertexProductMoves
open SemiprimeD1StackVertexProduct SemiprimeD1StackVertexProductState
open SemiprimeD1StackProcedureTrace (Runs one_base runs_trans)

/-- Real buffer-drain loop at a literal caller location. -/
theorem drain (v : Values) (s : Slot) (pc next : Label)
    (hcode : program pc=.base (.pop (address s) next pc pc)) (he : v s=[]) (word : List Bool) :
    Runs program (word.length+1) pc (data (Function.update v s word)) next (data v) := by
  induction word with
  | nil =>
    have hd : Function.update v s []=v := Function.update_eq_self_iff.mpr he.symm
    rw [hd]
    apply one_base program pc next (.pop (address s) next pc pc) _ _ hcode
    · simp only [SemiprimeD1StackBytecode.execute,data_get,he,List.head?_nil,SemiprimeD1StackBytecode.choose]
    · change Function.update (data v) (address s) ((data v (address s)).tail)=data v
      rw [data_get,he,List.tail_nil,←data_update,hd]
  | cons bit word ih =>
    have h1 : Runs program 1 pc (data (Function.update v s (bit::word))) pc (data (Function.update v s word)) := by
      apply one_base program pc pc (.pop (address s) next pc pc) _ _ hcode
      · simp only [SemiprimeD1StackBytecode.execute,data_get,Function.update_self,List.head?_cons]
        cases bit <;> rfl
      · change Function.update (data (Function.update v s (bit::word))) (address s)
          ((data (Function.update v s (bit::word)) (address s)).tail)=_
        rw [data_get,Function.update_self,List.tail_cons,←data_update,Function.update_idem]
    have hh:=runs_trans program _ _ _ _ _ _ _ _ h1 ih
    simpa only [List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

/-- Physical cleanup from the actual current buffer value, not a projected-away field. -/
theorem drain_current (v : Values) (s : Slot) (pc next : Label)
    (hcode : program pc=.base (.pop (address s) next pc pc)) :
    Runs program ((v s).length+1) pc (data v) next (data (Function.update v s [])) := by
  have h:=drain (Function.update v s []) s pc next hcode (by simp) (v s)
  simpa only [Function.update_idem,Function.update_eq_self] using h

/-- Fixed source slot of each actual source-copy inclusion. -/
def copySource (vertices : Bool) : Slot := if vertices then .vertices else .result
/-- Fixed destination slot of each actual source-copy inclusion. -/
def copyTarget (vertices : Bool) : Slot := if vertices then .reader else .product

/-- Copy source is the actual named live register. -/
theorem copy_source_address (vertices : Bool) : copyStack vertices 0=address (copySource vertices) := by cases vertices <;> rfl
/-- Copy target is the actual named live register. -/
theorem copy_target_address (vertices : Bool) : copyStack vertices 1=address (copyTarget vertices) := by cases vertices <;> rfl
/-- Copy restoration work is not a hidden live value in the state invariant. -/
theorem copy_work_other : ∀s,aux .copyWork ≠ address s := by decide

/-- Real literal copy-call adapter. No copied word, input count or cost answer
is supplied: both operands are the actual reached physical register contents. -/
theorem copy_call (v : Values) (vertices : Bool) (pc next : Label)
    (hcode : program pc=.call (.copy vertices 0) next) :
    Runs program (5*(v (copySource vertices)).length+4) pc (data v) next
      (data (Function.update v (copyTarget vertices) ((v (copySource vertices))++(v (copyTarget vertices))))) := by
  let source:=copySource vertices
  let target:=copyTarget vertices
  have hne : source ≠ target := by cases vertices <;> decide
  apply SemiprimeD1StackProcedureTrace.included_call program (copyStack vertices) (Label.copy vertices)
    (copyStack_injective vertices) SemiprimeD1StackCopy.code (0:Fin 9) (fun _=>rfl) pc next hcode _
    (SemiprimeD1StackCopy.state 0 none (v source) (v target) [])
    (SemiprimeD1StackCopy.done (v source) ((v source)++(v target)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words (v source) (v target) none
  · constructor
    · intro k
      fin_cases k
      · change data v (copyStack vertices 0)=v source
        rw [copy_source_address,data_get]
      · change data v (copyStack vertices 1)=v target
        rw [copy_target_address,data_get]
      · exact data_other v (aux .copyWork) copy_work_other
    · intro k hk
      rfl
  · constructor
    · intro k
      fin_cases k
      · change data (Function.update v target (v source++v target)) (copyStack vertices 0)=v source
        rw [copy_source_address,data_get,Function.update_of_ne hne]
      · change data (Function.update v target (v source++v target)) (copyStack vertices 1)=v source++v target
        rw [copy_target_address,data_get,Function.update_self]
      · exact data_other _ (aux .copyWork) copy_work_other
    · intro k hk
      have hn : k ≠ address target := fun he=>hk 1 ((copy_target_address vertices).trans he.symm)
      rw [data_update]
      exact Function.update_of_ne hn _ _

end RiemannGaussian.SemiprimeD1StackVertexProductMoves
