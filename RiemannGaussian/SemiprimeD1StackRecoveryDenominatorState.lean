/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominator
/-! # Exact live physical word views for all19 denominator roles
Seventeen slots can be live at real component boundaries. Both allocated fit
shadows are always explicitly empty and remain included in prefix accounting.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackRecoveryDenominator
/-- Finite proof-side names of actual live words, never runtime operands. -/
inductive Slot where
  | mul (k:M.Stack) | template | counter | fitScratch | aux (k:Aux)
  deriving DecidableEq,Fintype
/-- Literal physical role occupied by each live word. -/
def address:Slot → Stack
  | .mul k=>main k | .template=>template | .counter=>fitWork Fit.counter
  | .fitScratch=>fitWork Fit.scratch | .aux k=>aux k
/-- All17 live roles are distinct from each other and both counted shadows. -/
theorem address_injective:Function.Injective address:=by decide
/-- Word views are mathematical notation; the actual source input remains two tapes. -/
abbrev Values:=Slot → List Bool
/-- Complete all19-role physical store, explicitly empty at both fit shadows. -/
def data (v:Values) (k:Stack):List Bool:=
  if k=address .template then v .template else if k=address .counter then v .counter else
  if k=address .fitScratch then v .fitScratch else
  match k with | .inl m=>v (.mul m) | .inr (.inr a)=>v (.aux a) | _=>[]
/-- Each live word reads exactly its actual physical value. -/
theorem data_get (v:Values) (s:Slot):data v (address s)=v s:=by cases s <;> rfl
/-- Both unlisted allocated fit shadows are physically empty. -/
theorem data_other (v:Values) (k:Stack) (hk:∀s,k≠address s):data v k=[]:=by
  simp only [data,ite_eq_right (hk .template),ite_eq_right (hk .counter),ite_eq_right (hk .fitScratch)]
  rcases k with k|k
  · exact (hk (.mul k) rfl).elim
  · rcases k with k|k
    · rfl
    · exact (hk (.aux k) rfl).elim
/-- Every live-word update equals its actual physical store update. -/
theorem data_update (v:Values) (s:Slot) (word:List Bool):
    data (Function.update v s word)=Function.update (data v) (address s) word:=by
  funext k
  by_cases hex:∃t,k=address t
  · obtain ⟨t,rfl⟩:=hex
    rw [data_get]
    by_cases he:t=s
    · subst t;simp
    · have hn:address t≠address s:=fun h=>he (address_injective h)
      simp only [Function.update_of_ne he,Function.update_of_ne hn,data_get]
  · have hk:∀s,k≠address s:=by simpa only [not_exists] using hex
    rw [data_other _ _ hk,Function.update_of_ne (hk s),data_other _ _ hk]
/-- The empty live view is the complete19-role empty store. -/
theorem data_zero:data (fun _=>[])=fun _=>[]:=by
  funext k
  by_cases hex:∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex;exact data_get (fun _=>[]) s
  · exact data_other (fun _=>[]) k (by simpa only [not_exists] using hex)
/-- Exactly the two physical input words, with no acquired answer or row count. -/
def initialValues (rows widthTemplate:List Bool):Values:=
  Function.update (Function.update (fun _=>[]) (.aux .rows) rows) .template widthTemplate
/-- Actual initial physical store equals the two-input view. -/
theorem initial_data (rows widthTemplate:List Bool):
    (initial rows widthTemplate).data=data (initialValues rows widthTemplate):=by
  simp only [initialValues,data_update,data_zero,initial,input,address]
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorState
