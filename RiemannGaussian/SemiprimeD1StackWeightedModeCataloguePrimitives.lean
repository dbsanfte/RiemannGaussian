/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueView
/-! # Actual paid metadata catalogue primitive calls -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCataloguePrimitives
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => (Sum.inl :Control→Label)
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Literal target address of either actual metadata copy. -/
def copyTarget (site:Bool):Stack:=copyStack site 1
/-- Literal readonly source of either actual metadata copy. -/
def copySource (site:Bool):Stack:=copyStack site 0
theorem copy_ne (site:Bool):copySource site≠copyTarget site:=by cases site <;> decide
theorem copy_scratch_ne (site:Bool):aux .copyScratch≠copyTarget site:=by cases site <;> decide
theorem copy_call (site:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (copyLabel site 0) (ctl next))
    (s:Stack→List Bool) (xs ys:List Bool)
    (hx:s (copySource site)=xs) (hy:s (copyTarget site)=ys) (hz:s (aux .copyScratch)=[]) :
    Runs program (5*xs.length+4) (ctl pc) s (ctl next)
      (Function.update s (copyTarget site) (xs++ys)):=by
  apply included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) s _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update s (copyTarget site) (xs++ys) (copySource site)=xs
        rw [Function.update_of_ne (copy_ne site),hx]
      · exact Function.update_self _ _ _
      · change Function.update s (copyTarget site) (xs++ys) (aux .copyScratch)=[]
        rw [Function.update_of_ne (copy_scratch_ne site),hz]
    · intro k hk;exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Literal current slot/order field selected for real framing. -/
def frameSource (site:Bool):Stack:=frameStack site 0
/-- Literal common two-field label assembly destination. -/
def frameTarget:Stack:=aux .word
theorem frame_ne (site:Bool):frameSource site≠frameTarget:=by cases site <;> decide
theorem frame_call (site:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (frameLabel site 0) (ctl next))
    (s:Stack→List Bool) (xs ys:List Bool)
    (hx:s (frameSource site)=xs) (hy:s frameTarget=ys) (hz:s (aux .frameScratch)=[]) :
    Runs program (6*xs.length+5) (ctl pc) s (ctl next)
      (Function.update s frameTarget (frame xs ys)):=by
  apply included_call program (frameStack site) (frameLabel site) (frame_injective site)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (6*xs.length+4)
    (SemiprimeD1StackFrame.state 0 none xs ys []) (SemiprimeD1StackFrame.done xs (frame xs ys)) s _
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update s frameTarget (frame xs ys) (frameSource site)=xs
        rw [Function.update_of_ne (frame_ne site),hx]
      · exact Function.update_self _ _ _
      · change Function.update s frameTarget (frame xs ys) (aux .frameScratch)=[]
        rw [Function.update_of_ne (by decide:aux .frameScratch≠frameTarget),hz]
    · intro k hk;exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Literal weight or complete mode-label word copied by the actual logger. -/
def bodyWord (site:Bool):Stack:=bodyStack site .word
/-- Literal chronological log destination of either logger inclusion. -/
def bodyHistory (site:Bool):Stack:=bodyStack site .history
theorem body_ne (site:Bool):bodyWord site≠bodyHistory site:=by cases site <;> decide
theorem body_scratch_ne (site:Bool):aux .copyScratch≠bodyHistory site:=by cases site <;> decide
theorem body_call (site:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (bodyLabel site Body.entry) (ctl next))
    (s:Stack→List Bool) (word hist:List Bool)
    (hw:s (bodyWord site)=word) (hs:s (aux .copyScratch)=[]) (hh:s (bodyHistory site)=hist) :
    ∃t ≤6*(2*word.length+3)+1,Runs program t (ctl pc) s (ctl next)
      (Function.update s (bodyHistory site) ((true::frame word []).reverse++hist)):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackAssignmentBody.body_run word hist
  refine ⟨t+1,by omega,?_⟩
  apply included_call program (bodyStack site) (bodyLabel site) (body_injective site) Body.code Body.entry
    (fun _=>rfl) (ctl pc) (ctl next) hc t
    (⟨some Body.entry,none,SemiprimeD1StackAssignmentBody.contents word [] hist⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label)
    (⟨none,none,SemiprimeD1StackAssignmentBody.contents word [] ((true::frame word []).reverse++hist)⟩:
      SemiprimeD1StackBytecode.State Body.Stack Body.Label) s _ rfl rfl hr
  · constructor
    · intro k;cases k <;> first | exact hw | exact hs | exact hh
    · intro k _;rfl
  · constructor
    · intro k;cases k
      · exact (Function.update_of_ne (body_ne site) _ _).trans hw
      · exact (Function.update_of_ne (body_scratch_ne site) _ _).trans hs
      · exact Function.update_self _ _ _
    · intro k hk;exact Function.update_of_ne (fun he=>hk .history he.symm) _ _
theorem push_run (pc next:Control) (k:Stack) (b:Bool) (s:Stack→List Bool)
    (hc:program (ctl pc)=.base (.push k b (ctl next))) :
    Runs program 1 (ctl pc) s (ctl next) (Function.update s k (b::s k)):=
  one_base program _ _ _ _ _ hc rfl rfl
theorem pop_run (pc empty low high:Control) (k:Stack) (s:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.pop k (ctl empty) (ctl low) (ctl high))) (hx:s k=xs) :
    Runs program 1 (ctl pc) s (SemiprimeD1StackBytecode.choose (ctl empty) (ctl low) (ctl high) xs.head?)
      (Function.update s k xs.tail):=by
  apply one_base program _ _ _ _ _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
theorem drain_loop (pc next:Control) (k:Stack)
    (hc:program (ctl pc)=.base (.pop k (ctl next) (ctl pc) (ctl pc)))
    (s:Stack→List Bool) (xs:List Bool) (hx:s k=xs) :
    Runs program (xs.length+1) (ctl pc) s (ctl next) (Function.update s k []):=by
  induction xs generalizing s with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_run pc next pc pc k s [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next pc pc k s (b::xs) hc hx
    have h1:=ih (Function.update s k xs) (Function.update_self _ _ _)
    have h:=runs_trans program 1 (xs.length+1) _ _ _ s (Function.update s k xs) _
      (by cases b <;> exact h0) h1
    simpa only [Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackWeightedModeCataloguePrimitives
