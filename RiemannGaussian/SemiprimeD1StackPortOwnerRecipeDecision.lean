/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRecipeEmit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRecipeDecision
open SemiprimeD1StackPortOwnerRecipe SemiprimeD1StackPortOwnerRecipeSpec SemiprimeD1StackPortOwnerRecipeEmit
open SemiprimeD1StackProcedureTrace (Runs one_base runs_refl runs_trans)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Literal original constructor tag number, fixed before all input. -/
def tagCode : Tag→Fin 18
  | .input=>10 | .first=>11 | .twiddle=>12 | .second=>13
  | .product=>14 | .carry=>15 | .digit=>16 | .orOut=>17
/-- Proof-only description of the branch actually selected by physical tests. -/
def selected (p:Counters) (tag:Tag) : Recipe :=
  match tag,p.half with
  | .input,false=>.inputSource | .input,true=>.inputFirst
  | .first,false=>.firstFirst | .first,true=>.firstScale
  | .twiddle,false=>.twiddleScale | .twiddle,true=>.twiddleSecond
  | .second,false=>.secondSecond
  | .second,true=>if p.a<2 then .secondProduct else .secondCarry
  | .product,false=>.productProduct | .product,true=>.productFirst
  | .carry,false=>if p.a=0 then .carryInitial else .carryOut
  | .carry,true=>if p.a<p.r*p.t then .carryPrevious else .carryTerminal
  | .digit,false=>.digitInput
  | .digit,true=>if p.b=0 then if p.digits=1 then .digitCheck else .digitOrFirst else .digitOrNew
  | .orOut,false=>.orSource
  | .orOut,true=>if p.b+1<p.digits-1 then .orNext else .orCheck
/-- Fixed jump target of the original constructor/half dispatch. -/
def branchStart : Tag→Bool→Label
  | .input,false=>.local (.begin .inputSource) | .input,true=>.local (.begin .inputFirst)
  | .first,false=>.local (.begin .firstFirst) | .first,true=>.local (.begin .firstScale)
  | .twiddle,false=>.local (.begin .twiddleScale) | .twiddle,true=>.local (.begin .twiddleSecond)
  | .second,false=>.local (.begin .secondSecond) | .second,true=>.local .secondLimit
  | .product,false=>.local (.begin .productProduct) | .product,true=>.local (.begin .productFirst)
  | .carry,false=>.local .carryZero | .carry,true=>.local .carryLimit
  | .digit,false=>.local (.begin .digitInput) | .digit,true=>.local .digitZero
  | .orOut,false=>.local (.begin .orSource) | .orOut,true=>.local .orLimit
/-- One real peek retains the actual physical store and branches on its actual head byte. -/
theorem peek_run (pc:Label) (role:Stack) (empty low high:Label) (data:Stack→List Bool)
    (hc:program pc=.base (.peek role empty low high)) :
    Runs program 1 pc data (SemiprimeD1StackBytecode.choose empty low high (data role).head?) data := by
  apply one_base program pc _ (.peek role empty low high) data data hc rfl rfl
/-- Unary zero/nonzero branch is a literal EOF or true-byte read. -/
theorem choose_unary (empty low high:Label) (n:ℕ) :
    SemiprimeD1StackBytecode.choose empty low high (unary n).head?=if n=0 then empty else high := by
  cases n <;> rfl
/-- A computed comparison bit selects only its two fixed literal branches. -/
theorem choose_decide (empty low high:Label) (p:Prop) [Decidable p] :
    SemiprimeD1StackBytecode.choose empty low high [decide p].head?=if p then high else low := by
  by_cases h:p <;> simp [h,SemiprimeD1StackBytecode.choose]
/-- The actual half marker is read before the static constructor/half jump. -/
theorem half_run (p:Counters) (tag:Tag) :
    Runs program 1 (.local (.half tag)) (ready p) (.local (.choose tag p.half)) (ready p) := by
  have h:=peek_run (.local (.half tag)) (arg .half) (.local (.choose tag false))
    (.local (.choose tag true)) (.local (.choose tag true)) (ready p) rfl
  have he:SemiprimeD1StackBytecode.choose (Label.local (.choose tag false))
      (.local (.choose tag true)) (.local (.choose tag true)) ((ready p) (arg .half)).head?=
      .local (.choose tag p.half):=by
    cases hh:p.half <;> simp [ready,prepared,atStage,words,arg,reg,Function.update,hh,SemiprimeD1StackBytecode.choose]
  rw [he] at h
  exact h
/-- The actual constructor/half stage executes its real finite jump. -/
theorem branch_start_run (p:Counters) (tag:Tag) (half:Bool) :
    Runs program 1 (.local (.choose tag half)) (ready p) (branchStart tag half) (ready p) := by
  have hc:program (.local (.choose tag half))=.base (.jump (branchStart tag half)):=by
    cases tag <;> cases half <;> rfl
  apply one_base program _ _ (.jump (branchStart tag half)) _ _ hc rfl rfl
/-- Every additional recipe test reads its physically acquired unary word or comparison bit. -/
theorem branch_run (p:Counters) (tag:Tag) (hd:0<p.digits) :
    ∃time≤2,Runs program time (branchStart tag p.half) (ready p)
      (.local (.begin (selected p tag))) (ready p) := by
  cases tag with
  | input=>cases hh:p.half <;> exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin _)) (ready p)⟩
  | first=>cases hh:p.half <;> exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin _)) (ready p)⟩
  | twiddle=>cases hh:p.half <;> exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin _)) (ready p)⟩
  | product=>cases hh:p.half <;> exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin _)) (ready p)⟩
  | second=>
    cases hh:p.half with
    | false=>exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin .secondSecond)) (ready p)⟩
    | true=>
      have h:=peek_run (.local .secondLimit) (reg .smallA) (.local .abort)
        (.local (.begin .secondCarry)) (.local (.begin .secondProduct)) (ready p) rfl
      have hv:ready p (reg .smallA)=[decide (p.a<2)]:=by rfl
      rw [hv,choose_decide] at h
      refine ⟨1,by omega,?_⟩
      by_cases he:p.a<2 <;> simpa only [branchStart,selected,hh,he,ite_true,ite_false] using h
  | carry=>
    cases hh:p.half with
    | false=>
      have h:=peek_run (.local .carryZero) (arg .a) (.local (.begin .carryInitial))
        (.local (.begin .carryOut)) (.local (.begin .carryOut)) (ready p) rfl
      have hv:ready p (arg .a)=unary p.a:=by rfl
      rw [hv,choose_unary] at h
      refine ⟨1,by omega,?_⟩
      by_cases he:p.a=0 <;> simpa only [branchStart,selected,hh,he,ite_true,ite_false] using h
    | true=>
      have h:=peek_run (.local .carryLimit) (reg .ltArt) (.local .abort)
        (.local (.begin .carryTerminal)) (.local (.begin .carryPrevious)) (ready p) rfl
      have hv:ready p (reg .ltArt)=[decide (p.a<p.r*p.t)]:=by rfl
      rw [hv,choose_decide] at h
      refine ⟨1,by omega,?_⟩
      by_cases he:p.a<p.r*p.t <;> simpa only [branchStart,selected,hh,he,ite_true,ite_false] using h
  | digit=>
    cases hh:p.half with
    | false=>exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin .digitInput)) (ready p)⟩
    | true=>
      have h:=peek_run (.local .digitZero) (arg .b) (.local .digitSize)
        (.local (.begin .digitOrNew)) (.local (.begin .digitOrNew)) (ready p) rfl
      have hv:ready p (arg .b)=unary p.b:=by rfl
      rw [hv,choose_unary] at h
      by_cases hb:p.b=0
      · simp only [hb,ite_true] at h
        have hs:=peek_run (.local .digitSize) (reg .dminus) (.local (.begin .digitCheck))
          (.local (.begin .digitOrFirst)) (.local (.begin .digitOrFirst)) (ready p) rfl
        have hvalue:ready p (reg .dminus)=unary (p.digits-1):=by rfl
        rw [hvalue,choose_unary] at hs
        have he:p.digits-1=0 ↔ p.digits=1:=by omega
        simp only [he] at hs
        have hboth:=runs_trans program _ _ _ _ _ _ _ _ h hs
        refine ⟨2,by omega,?_⟩
        by_cases hd1:p.digits=1 <;> simpa only [branchStart,selected,hh,hb,hd1,ite_true,ite_false] using hboth
      · refine ⟨1,by omega,?_⟩
        simpa only [branchStart,selected,hh,hb,ite_false] using h
  | orOut=>
    cases hh:p.half with
    | false=>exact ⟨0,by omega,by simpa only [branchStart,selected,hh] using runs_refl program (.local (.begin .orSource)) (ready p)⟩
    | true=>
      have h:=peek_run (.local .orLimit) (reg .ltNext) (.local .abort)
        (.local (.begin .orCheck)) (.local (.begin .orNext)) (ready p) rfl
      have hv:ready p (reg .ltNext)=[decide (p.b+1<p.digits-1)]:=by rfl
      rw [hv,choose_decide] at h
      refine ⟨1,by omega,?_⟩
      by_cases he:p.b+1<p.digits-1 <;> simpa only [branchStart,selected,hh,he,ite_true,ite_false] using h
/-- All actual half/branch instructions are counted; the computed recipe never enters runtime as advice. -/
theorem decision_run (p:Counters) (tag:Tag) (hd:0<p.digits) :
    ∃time≤4,Runs program time (.local (.half tag)) (ready p)
      (.local (.begin (selected p tag))) (ready p) := by
  obtain ⟨time,ht,hr⟩:=branch_run p tag hd
  have h:=runs_trans program _ _ _ _ _ _ _ _ (half_run p tag)
    (runs_trans program _ _ _ _ _ _ _ _ (branch_start_run p tag p.half) hr)
  exact ⟨1+(1+time),by omega,h⟩
end RiemannGaussian.SemiprimeD1StackPortOwnerRecipeDecision
