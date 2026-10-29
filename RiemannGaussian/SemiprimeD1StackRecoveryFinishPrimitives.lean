/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishState
/-! # Actual copy, pop, push, drain and nested-return traces
Every preservation/restoration loop and every actual return symbol is charged.
Only finite literal roles/sites appear in instructions; live-bank functions
below describe physical words in proofs and are never accepted by the program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState SemiprimeD1StackProcedureTrace
/-- Exact composition of actual traces for this one fixed recovery source. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Literal proof-side live source slot for each consuming transfer. -/
def moveFrom:MoveSite→Slot
  | .plain|.roundingInput=>.aux .numeratorWork
  | .rounded|.correction=>.addOutput
  | _=>.output
/-- Literal proof-side live destination for each consuming transfer. -/
def moveTo:MoveSite→Slot
  | .plain|.rounded=>.reduceInput | .roundingInput=>.addLeft | .residue=>.aux .numeratorResidue
  | .inverseInput=>.aux .inverseInput | .two=>.aux .two | .one|.update=>.aux .current
  | .product=>.aux .product | .opposite=>.aux .opposite | .signed=>.aux .signedResidue | .correction=>.aux .correction
/-- Actual cached left multiplier operand slot. -/
def multiplyFromLeft:MulSite→Slot
  | .product=>.aux .inverseInput | .opposite|.signed=>.aux .negative
  | .update=>.aux .current | .final=>.aux .signedResidue
/-- Actual cached right multiplier operand slot. -/
def multiplyFromRight:MulSite→Slot
  | .product|.final=>.aux .current | .opposite=>.aux .product | .update=>.aux .correction | .signed=>.aux .numeratorResidue
/-- Literal proof-side source slot of each actual preserving copy. -/
def copyFrom:Copy→Slot
  | .numerator=>.aux .numerator | .denominator=>.aux .denominator | .width|.negative|.todo=>.width
  | .odd=>.aux .denominatorWork | .addLeft=>.aux .two | .addRight=>.aux .opposite | .positive=>.aux .numeratorResidue
  | .mulLeft site=>multiplyFromLeft site | .mulRight site=>multiplyFromRight site | .move site=>moveFrom site
/-- Literal proof-side target slot of each actual preserving copy. -/
def copyTo:Copy→Slot
  | .numerator=>.aux .numeratorWork | .denominator=>.aux .denominatorWork | .width=>.reduceWidth
  | .negative=>.aux .negative | .todo=>.aux .todo | .odd=>.reduceInput | .addLeft=>.addLeft | .addRight=>.addRight
  | .positive=>.aux .signedResidue | .mulLeft _=>.mulLeft | .mulRight _=>.mulRight | .move site=>moveTo site
/-- Actual copy source is its named physical live address. -/
theorem copy_source (site:Copy):copyStack site 0=address (copyFrom site):=by
  cases site with
  | mulLeft site=>cases site <;> rfl
  | mulRight site=>cases site <;> rfl
  | move site=>cases site <;> rfl
  | _=>rfl
/-- Actual copy destination is its named physical live address. -/
theorem copy_target (site:Copy):copyStack site 1=address (copyTo site):=by
  cases site with
  | move site=>cases site <;> rfl
  | _=>rfl
/-- Every real copy's source and destination are separate. -/
theorem copy_ne (site:Copy):address (copyFrom site)≠address (copyTo site):=by
  rw [←copy_source,←copy_target]
  exact fun h=>(by decide:(0:Fin 3)≠1) ((copy_injective site) h)
/-- Real restoring-copy scratch is separate from every actual destination. -/
theorem copy_work_ne (site:Copy):aux .copyScratch≠address (copyTo site):=by
  rw [←copy_target]
  change copyStack site 2≠copyStack site 1
  exact fun h=>(by decide:(2:Fin 3)≠1) ((copy_injective site) h)
/-- Every real preserving copy pays its physical call, cells and return. -/
theorem copy_view (site:Copy) (pc next:Label) (v:Values)
    (hc:program pc=.call (.copy site 0) next) (hs:v (.aux .copyScratch)=[]):
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
      · change data v (address (.aux .copyScratch))=[]
        rw [data_get,hs]
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (data v) (address (copyTo site)) _ (copyStack site 0)=v (copyFrom site)
        rw [copy_source,Function.update_of_ne (copy_ne site),data_get]
      · change Function.update (data v) (address (copyTo site)) _ (copyStack site 1)=_
        rw [copy_target,Function.update_self]
        rfl
      · change Function.update (data v) (address (copyTo site)) _ (aux .copyScratch)=[]
        rw [Function.update_of_ne (copy_work_ne site)]
        exact (data_get v (.aux .copyScratch)).trans hs
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
/-- A real nested call pushes and later pops its finite return symbol; no saved frame is supplied. -/
theorem returning_call (pc entry next:Label) (before after:Stack→List Bool) (time:Nat)
    (hc:program pc=.call entry next)
    (hr:Runs program time entry before (.local .returning) after):
    Runs program (time+2) pc before next after:=by
  intro frames target h
  rcases h with ⟨hp,hd,hf⟩
  let mid:=SemiprimeD1StackCalls.execute (.call entry next) target
  have hm:SemiprimeD1StackCalls.run program 1 target=some mid:=by
    change SemiprimeD1StackCalls.step program target=some mid
    simp only [SemiprimeD1StackCalls.step,hp,Option.map_some,hc,mid]
  obtain ⟨finish,hRun,hAt⟩:=hr (next::frames) mid (by
    simp only [At,mid,SemiprimeD1StackCalls.execute,hd,hf,and_self])
  let last:=SemiprimeD1StackCalls.execute .ret finish
  have hl:SemiprimeD1StackCalls.run program 1 finish=some last:=by
    change SemiprimeD1StackCalls.step program finish=some last
    simp only [SemiprimeD1StackCalls.step,hAt.1,Option.map_some,program,last]
  refine ⟨last,?_,?_,?_,?_⟩
  · rw [show time+2=1+(time+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hRun,Option.bind_some]
    exact hl
  · simp only [last,SemiprimeD1StackCalls.execute,hAt.2.2]
  · simpa only [last,SemiprimeD1StackCalls.execute,hAt.2.2] using hAt.2.1
  · simp only [last,SemiprimeD1StackCalls.execute,hAt.2.2]
/-- A real drain subcall charges both its true call/return and every consumed cell. -/
theorem drain_call (pc next:Label) (s:Slot) (v:Values)
    (hc:program pc=.call (.drain (address s)) next):
    Runs program ((v s).length+3) pc (data v) next (data (Function.update v s [])):=by
  have h:=drain_view (.drain (address s)) (.local .returning) s v rfl
  exact returning_call pc (.drain (address s)) next _ _ _ hc h
end RiemannGaussian.SemiprimeD1StackRecoveryFinishPrimitives
