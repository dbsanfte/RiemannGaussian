/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeComponents
/-! # Literal physically retained stores of the one-pass scope-record join -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeView
open SemiprimeD1StackPortScopeRecords
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- Nine actually cached words; functions here are finite store specifications only. -/
abbrev Record := Fin 9→List Bool
/-- Literal shared source, nine parsed fields and physical work stacks. -/
def store (base:S.Stack→List Bool) (words:Record) (work:Aux→List Bool) : Stack→List Bool :=
  Sum.elim base (Sum.elim words work)
/-- Actual clean loop work: two source suffixes and reverse output accumulator. -/
def cleanWork (ports ids raw:List Bool) : Aux→List Bool
  | .readerPorts => ports | .readerIds => ids | .reversed => raw | _ => []
/-- Whole loop store with every original source cache retained literally. -/
def clean (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw:List Bool) : Stack→List Bool :=
  store base words (cleanWork ports ids raw)
/-- Actual field writes modify only their finite cache slot. -/
theorem update_cache (base:S.Stack→List Bool) (words:Record) (work:Aux→List Bool)
    (part:Fin 9) (word:List Bool) :
    Function.update (store base words work) (cache part) word=
      store base (Function.update words part word) work := by
  funext k
  by_cases hk:k=cache part
  · subst k
    rw [Function.update_self]
    change word=(Function.update words part word) part
    rw [Function.update_self]
  · rw [Function.update_of_ne hk]
    cases k with
    | inl old => rfl
    | inr fresh =>
      cases fresh with
      | inl j =>
        have hj:j≠part:=by intro he;subst j;exact hk rfl
        change words j=(Function.update words part word) j
        rw [Function.update_of_ne hj]
      | inr role => rfl
/-- Actual work writes modify precisely one physical private role. -/
theorem update_aux (base:S.Stack→List Bool) (words:Record) (work:Aux→List Bool)
    (role:Aux) (word:List Bool) :
    Function.update (store base words work) (aux role) word=
      store base words (Function.update work role word) := by
  funext k
  by_cases hk:k=aux role
  · subst k
    rw [Function.update_self]
    change word=(Function.update work role word) role
    rw [Function.update_self]
  · rw [Function.update_of_ne hk]
    cases k with
    | inl old => rfl
    | inr fresh =>
      cases fresh with
      | inl j => rfl
      | inr other =>
        have hj:other≠role:=by intro he;subst other;exact hk rfl
        change work other=(Function.update work role word) other
        rw [Function.update_of_ne hj]
/-- Physically acquired port suffix update. -/
theorem clean_ports (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw next:List Bool) :
    Function.update (clean base ports ids words raw) (aux .readerPorts) next=clean base next ids words raw := by
  unfold clean
  rw [update_aux]
  apply congrArg (store base words)
  funext k
  cases k <;> rfl
/-- Physically acquired ID-vector suffix update. -/
theorem clean_ids (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw next:List Bool) :
    Function.update (clean base ports ids words raw) (aux .readerIds) next=clean base ports next words raw := by
  unfold clean
  rw [update_aux]
  apply congrArg (store base words)
  funext k
  cases k <;> rfl
/-- Every reversed emitted bit is an actual output allocation. -/
theorem clean_raw (base:S.Stack→List Bool) (ports ids:List Bool) (words:Record) (raw next:List Bool) :
    Function.update (clean base ports ids words raw) (aux .reversed) next=clean base ports ids words next := by
  unfold clean
  rw [update_aux]
  apply congrArg (store base words)
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
end RiemannGaussian.SemiprimeD1StackPortScopeView
