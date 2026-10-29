/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinish
/-! # Exact live-word boundaries for all35 physical recovery roles
Twenty-seven original/cache/operand words may be live at real-call boundaries.
The remaining eight allocated private/shadow words are explicitly empty there;
all35 remain counted during every actual component execution.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinish
/-- Finite proof-side names of the actual live source/cache/operand roles. -/
inductive Slot where
  | width | mulLeft | mulRight | reduceWidth | reduceInput | output | addLeft | addRight | addOutput | aux (k:Aux)
  deriving DecidableEq,Fintype
/-- Literal actual address of each live word. -/
def address:Slot→Stack
  | .width=>width | .mulLeft=>mulLeft | .mulRight=>mulRight | .reduceWidth=>reduceStack .right
  | .reduceInput=>reduceStack .left | .output=>output
  | .addLeft=>rawStack .left | .addRight=>rawStack .right | .addOutput=>rawStack .output | .aux k=>aux k
/-- All27 live addresses are distinct; the allocated shadow/private roles remain separate. -/
theorem address_injective:Function.Injective address:=by decide
/-- Proof notation for physical source words only, never a runtime operand. -/
abbrev Values:=Slot→List Bool
/-- Exact all35-role bank at an actual source-call boundary. -/
def data (v:Values) (k:Stack):List Bool:=
  if k=address .width then v .width else if k=address .mulLeft then v .mulLeft else
  if k=address .mulRight then v .mulRight else if k=address .reduceWidth then v .reduceWidth else
  if k=address .reduceInput then v .reduceInput else if k=address .output then v .output else
  if k=address .addLeft then v .addLeft else if k=address .addRight then v .addRight else
  if k=address .addOutput then v .addOutput else
  match k with | .inr (.inr a)=>v (.aux a) | _=>[]
/-- Every live address reads its exact physical word. -/
theorem data_get (v:Values) (s:Slot):data v (address s)=v s:=by
  cases s <;> rfl
/-- Every unlisted allocated private/shadow role is physically empty at a boundary. -/
theorem data_other (v:Values) (k:Stack) (hk:∀s,k≠address s):data v k=[]:=by
  simp only [data,ite_eq_right (hk .width),ite_eq_right (hk .mulLeft),ite_eq_right (hk .mulRight),
    ite_eq_right (hk .reduceWidth),ite_eq_right (hk .reduceInput),ite_eq_right (hk .output),ite_eq_right (hk .addLeft),
    ite_eq_right (hk .addRight),ite_eq_right (hk .addOutput)]
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · exact (hk (.aux k) rfl).elim
/-- A live-word update is exactly the corresponding physical data-store update. -/
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
/-- Empty proof bank is the actual all35-role empty store. -/
theorem data_zero:data (fun _=>[])=fun _=>[]:=by
  funext k
  by_cases hex:∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex
    exact data_get (fun _=>[]) s
  · exact data_other (fun _=>[]) k (by simpa only [not_exists] using hex)
/-- The actual three source operands occupy only their literal physical roles. -/
def initialValues (numerator denominator widthWord:List Bool):Values:=
  Function.update (Function.update (Function.update (fun _=>[]) (.aux .numerator) numerator) (.aux .denominator) denominator) .width widthWord
/-- No intermediate, quotient, inverse or answer is supplied by initial bank notation. -/
theorem initial_data (numerator denominator widthWord:List Bool):
    (initial numerator denominator widthWord).data=data (initialValues numerator denominator widthWord):=by
  simp only [initialValues,data_update,data_zero,initial,input,address]
end RiemannGaussian.SemiprimeD1StackRecoveryFinishState
