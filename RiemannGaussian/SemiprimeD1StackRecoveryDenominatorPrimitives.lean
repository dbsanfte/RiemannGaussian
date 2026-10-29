/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorState
/-! # Paid actual copies, source-bit steps and physical drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryDenominatorPrimitives
open SemiprimeD1StackRecoveryDenominator SemiprimeD1StackRecoveryDenominatorState
open SemiprimeD1StackProcedureTrace
/-- Exact composition of actual caller traces. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack → List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Static source word for either actual preserving copy. -/
def copyFrom (site:Bool):Slot:=if site then .aux .rows else .mul (.inl .right)
/-- Static destination word for either actual preserving copy. -/
def copyTo (site:Bool):Slot:=if site then .aux .reader else .mul M.factor
/-- Actual source role equals its live word address. -/
theorem copy_source (site:Bool):copyStack site 0=address (copyFrom site):=by cases site <;> rfl
/-- Actual destination role equals its live word address. -/
theorem copy_target (site:Bool):copyStack site 1=address (copyTo site):=by cases site <;> rfl
/-- Each actual copy has distinct source and destination. -/
theorem copy_ne (site:Bool):address (copyFrom site)≠address (copyTo site):=by
  rw [←copy_source,←copy_target]
  exact fun h=>(by decide:(0:Fin 3)≠1) ((copy_injective site) h)
/-- Shared restoring scratch is separate from each actual target. -/
theorem copy_work_ne (site:Bool):scratch≠address (copyTo site):=by
  rw [←copy_target]
  change copyStack site 2≠copyStack site 1
  exact fun h=>(by decide:(2:Fin 3)≠1) ((copy_injective site) h)
/-- Every real preserving copy pays its physical call, cells and return. -/
theorem copy_view (site:Bool) (pc next:Label) (v:Values)
    (hc:program pc=.call (.copy site 0) next) (hs:v (.mul M.copyScratch)=[]):
    Runs program (5*(v (copyFrom site)).length+4) pc (data v) next
      (data (Function.update v (copyTo site) (v (copyFrom site)++v (copyTo site)))):=by
  rw [data_update]
  apply included_call program (copyStack site) (Label.copy site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*(v (copyFrom site)).length+3)
    (SemiprimeD1StackCopy.state 0 none (v (copyFrom site)) (v (copyTo site)) [])
    (SemiprimeD1StackCopy.done (v (copyFrom site)) (v (copyFrom site)++v (copyTo site))) _ _ rfl rfl
    (SemiprimeD1StackCopy.copy_words _ _ none)
  · constructor
    · intro k;fin_cases k
      · change data v (copyStack site 0)=v (copyFrom site)
        rw [copy_source,data_get]
      · change data v (copyStack site 1)=v (copyTo site)
        rw [copy_target,data_get]
      · change data v (address (.mul M.copyScratch))=[]
        rw [data_get,hs]
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (data v) (address (copyTo site)) _ (copyStack site 0)=v (copyFrom site)
        rw [copy_source,Function.update_of_ne (copy_ne site),data_get]
      · change Function.update (data v) (address (copyTo site)) _ (copyStack site 1)=_
        rw [copy_target,Function.update_self]
        rfl
      · change Function.update (data v) (address (copyTo site)) _ (scratch)=[]
        rw [Function.update_of_ne (copy_work_ne site)]
        exact (data_get v (.mul M.copyScratch)).trans hs
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 (by rw [copy_target];exact he.symm)) _ _
/-- One physical push writes exactly one actual Boolean cell. -/
theorem push_view (pc next:Label) (s:Slot) (b:Bool) (v:Values)
    (hc:program pc=.base (.push (address s) b next)):
    Runs program 1 pc (data v) next (data (Function.update v s (b::v s))):=by
  rw [data_update]
  exact one_base program _ _ _ _ _ hc rfl (by rw [←data_get v s];rfl)
/-- One physical pop branches solely on the actual leading cell and exposes the actual tail. -/
theorem pop_view (pc empty low high:Label) (s:Slot) (v:Values) (word:List Bool)
    (hc:program pc=.base (.pop (address s) empty low high)) (hx:v s=word):
    Runs program 1 pc (data v) (SemiprimeD1StackBytecode.choose empty low high word.head?)
      (data (Function.update v s word.tail)):=by
  rw [data_update]
  apply one_base program _ _ _ _ _ hc
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hx]
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hx]
/-- Every drain bit, including its final EOF test, is actually executed. -/
theorem drain_view (pc next:Label) (s:Slot) (v:Values)
    (hc:program pc=.base (.pop (address s) next pc pc)):
    Runs program ((v s).length+1) pc (data v) next (data (Function.update v s [])):=by
  generalize hw:v s=word
  induction word generalizing v with
  | nil=>simpa only [hw,List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_view pc next pc pc s v [] hc hw
  | cons b word ih=>
    have h0:=pop_view pc next pc pc s v (b::word) hc hw
    have h1:=ih (Function.update v s word) (Function.update_self _ _ _)
    have h:=join (by cases b <;> exact h0) h1
    simpa only [hw,Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryDenominatorPrimitives
