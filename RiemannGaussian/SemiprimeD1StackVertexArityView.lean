/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArityComponents

/-! # Physical arity source and working stores -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityView
open SemiprimeD1StackVertexArity SemiprimeD1StackVertexArityComponents
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Literal source-counter representation, later tied to the original-N cache. -/
def header (tag index radius first second digits:ℕ) : Source→List Bool
  | .tag => unary tag
  | .index => unary index
  | .radiusSucc => unary radius
  | .firstAxis => unary first
  | .secondAxis => unary second
  | .digits => unary digits
/-- Exact physical words at all procedure boundaries; scratch and compare-left are empty. -/
def work (arity tag multiplier right limit result:List Bool) : Aux→List Bool
  | .arity => arity
  | .tagReader => tag
  | .multiplier => multiplier
  | .compareRight => right
  | .compareLimit => limit
  | .compareResult => result
  | _ => []
/-- The complete physical fifteen-stack boundary store. -/
def store (h:Source→List Bool) (arity tag multiplier right limit result:List Bool) : Stack→List Bool :=
  data h (work arity tag multiplier right limit result)
/-- Actual writes do not change any source metadata word. -/
theorem update_aux (h:Source→List Bool) (w:Aux→List Bool) (key:Aux) (word:List Bool) :
    Function.update (data h w) (aux key) word=data h (Function.update w key word) := by
  funext k
  rcases k with k|k
  · simp [data,aux,Function.update]
  · by_cases hk:k=key
    · subst k;simp [data,aux,Function.update]
    · simp [data,aux,Function.update,hk]
/-- Physical arity update preserves the other working words. -/
theorem work_arity (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.arity word=work word tag multiplier right limit result := by
  funext k
  cases k <;> rfl
/-- Physical tagReader update preserves the other working words. -/
theorem work_tagReader (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.tagReader word=work arity word multiplier right limit result := by
  funext k
  cases k <;> rfl
/-- Physical multiplier update preserves the other working words. -/
theorem work_multiplier (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.multiplier word=work arity tag word right limit result := by
  funext k
  cases k <;> rfl
/-- Physical compareRight update preserves the other working words. -/
theorem work_compareRight (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.compareRight word=work arity tag multiplier word limit result := by
  funext k
  cases k <;> rfl
/-- Physical compareLimit update preserves the other working words. -/
theorem work_compareLimit (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.compareLimit word=work arity tag multiplier right word result := by
  funext k
  cases k <;> rfl
/-- Physical compareResult update preserves the other working words. -/
theorem work_compareResult (arity tag multiplier right limit result word:List Bool) :
    Function.update (work arity tag multiplier right limit result) Aux.compareResult word=work arity tag multiplier right limit word := by
  funext k
  cases k <;> rfl
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
end RiemannGaussian.SemiprimeD1StackVertexArityView
