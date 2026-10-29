/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCleanup
/-! # Actual complete54-word final sweep: retain only three inputs and chronological output -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFinalCleanup
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseInventory SemiprimeD1StackNormalizedInverseCalls
open SemiprimeD1StackNormalizedInverseCleanup SemiprimeD1StackProcedureTrace
/-- Precisely the physical original array/q/W words and the actually emitted output survive. -/
def retained (k : Stack) : Prop := k=template ∨ k=aux .denominator ∨ k=aux .originalQ ∨ k=aux .output
/-- Exact endpoint of the actual fixed literal54-word sweep. -/
noncomputable def cleanStore (data : Stack→List Bool) : Stack→List Bool := by
  classical
  exact fun k=>if retained k then data k else []
/-- No uncounted field or shadow is omitted from the real successful cleanup. -/
theorem work_mem_iff (k : Stack) : k∈roles workRole ↔ ¬retained k := by
  constructor
  · intro h
    obtain ⟨i,_,hi⟩:=List.mem_map.mp h
    intro hk
    rcases hk with hk|hk|hk|hk
    · exact workRole_not_template i (hi.trans hk)
    · exact workRole_not_denominator i (hi.trans hk)
    · exact workRole_not_q i (hi.trans hk)
    · exact workRole_not_output i (hi.trans hk)
  · intro h
    have ht : k≠template := fun he=>h (Or.inl he)
    have ha : k≠aux .denominator := fun he=>h (Or.inr (Or.inl he))
    have hq : k≠aux .originalQ := fun he=>h (Or.inr (Or.inr (Or.inl he)))
    have ho : k≠aux .output := fun he=>h (Or.inr (Or.inr (Or.inr he)))
    obtain ⟨i,hi⟩:=workRole_complete k ht ha hq ho
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,hi⟩
/-- Mathematical equality specifies the endpoint of THIS actual sweep; no execution clock is transported. -/
theorem final_cleared (data : Stack→List Bool) : cleared workRole data 54=cleanStore data := by
  classical
  funext k
  rw [cleared_full,work_mem_iff]
  by_cases h:retained k <;> simp only [cleanStore,h,not_true_eq_false,not_false_eq_true,ite_true,ite_false]
/-- ALL54 real drain loops execute through actual EOF before the single final halt. -/
theorem final_run (data : Stack→List Bool) :
    ∃q≤54*(mass data+1),Runs program q (ctl (.clearFinal 0)) data (ctl .done) (cleanStore data) := by
  have hc : ∀i:Fin 54,program (ctl (.clearFinal i))=.base
      (.pop (workRole i) (next (fun j=>ctl (.clearFinal j)) (ctl .done) i)
        (ctl (.clearFinal i)) (ctl (.clearFinal i))) := by
    intro i
    have hh:i.val+1<54 ↔ i.val<54-1 := by omega
    simp only [program,ctl,finalNext,next,hh]
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<54) workRole (fun j=>ctl (.clearFinal j)) (ctl .done) hc 53 0 rfl data
  refine ⟨q,by omega,?_⟩
  simpa only [cleared_zero,final_cleared,show (⟨0,by decide⟩:Fin 54)=0 from Fin.ext rfl] using hr
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFinalCleanup
