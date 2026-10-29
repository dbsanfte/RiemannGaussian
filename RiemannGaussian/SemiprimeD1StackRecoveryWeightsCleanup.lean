/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsInventory
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRegisterClear
/-! # Actual dedicated finite cleanup sweeps on THIS60-role program
Old cleared-store/list identities are mathematical only. Every pop/EOF and its
clock below executes THIS fixed program, retaining the immutable power tape.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsCleanup
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackProcedureTrace
namespace Old
export SemiprimeD1StackNormalizedInverseView (store)
export SemiprimeD1StackNormalizedInverseCleanup (mass cleared cleared_zero cleared_succ cleared_le)
end Old
/-- Exact mathematical actual-old-store view after fixed literal cleanup positions. -/
noncomputable def cleared {n:Nat} (slot:Fin n→I.Stack) (w:Words) (position:Nat):Stack→List Bool:=
  Sum.elim (Old.cleared slot (SemiprimeD1StackNormalizedInverseView.store w.toWords) position) w.scalarInputs
/-- An actual original-word write preserves every added caller tape. -/
theorem update_lift (before:I.Stack→List Bool) (added:Scalar→List Bool) (slot:I.Stack) (xs:List Bool) :
    Function.update (Sum.elim before added) (helper slot) xs=Sum.elim (Function.update before slot xs) added:=by
  funext role
  rcases role with role|role
  · simp only [helper,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Before real cleanup, the entire60-word bank is unchanged. -/
theorem cleared_zero {n:Nat} (slot:Fin n→I.Stack) (w:Words):cleared slot w 0=bank w:=by
  unfold cleared
  rw [Old.cleared_zero]
  rfl
/-- One real old-role EOF drain advances the literal position and preserves all59 other words. -/
theorem cleared_succ {n:Nat} (slot:Fin n→I.Stack) (w:Words) (i:Fin n):
    Function.update (cleared slot w i.val) (helper (slot i)) []=cleared slot w (i.val+1):=by
  unfold cleared
  rw [update_lift,Old.cleared_succ]
/-- Any actual word being drained has its own existing physical-cell mass cap. -/
theorem word_le {n:Nat} (slot:Fin n→I.Stack) (w:Words) (position:Nat) (i:Fin n):
    (cleared slot w position (helper (slot i))).length≤ Old.mass (Old.store w.toWords):=
  Old.cleared_le slot _ position (slot i)
/-- The next static finite cleanup label, before all original dimensions. -/
def next {n:Nat} (pc:Fin n→Label) (stopped:Label) (i:Fin n):Label:=
  if h:i.val<n-1 then pc ⟨i.val+1,by omega⟩ else stopped
/-- Every literal cleanup loop is executed on THIS60-role program, with all bytes and empty branches paid. -/
theorem sweep {n:Nat} (hn:0<n) (slot:Fin n→I.Stack) (pc:Fin n→Label) (stopped:Label)
    (hc:∀i,program (pc i)=.base (.pop (helper (slot i)) (next pc stopped i) (pc i) (pc i)))
    (remaining position:Nat) (hp:position+remaining=n-1) (w:Words):
    ∃q≤(remaining+1)*(Old.mass (Old.store w.toWords)+1),
      Runs program q (pc ⟨position,by omega⟩) (cleared slot w position) stopped (cleared slot w n):=by
  induction remaining generalizing position with
  | zero=>
    have hpos:position=n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=stopped:=by simp only [next,i,hpos,Nat.lt_irrefl,dite_false]
    have h0:=P.drain_loop (pc i) stopped (helper (slot i)) (by rw [hc,hnext])
      (cleared slot w position) ((cleared slot w position) (helper (slot i))) rfl
    have he:=cleared_succ slot w i
    change Function.update (cleared slot w position) (helper (slot i)) []=cleared slot w (position+1) at he
    rw [he,show position+1=n by omega] at h0
    refine ⟨_,?_,h0⟩
    have hw:=word_le slot w position i
    omega
  | succ remaining ih=>
    have hpos:position<n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=pc ⟨position+1,by omega⟩:=by simp only [next,i,dite_eq_left hpos]
    have h0:=P.drain_loop (pc i) (pc ⟨position+1,by omega⟩) (helper (slot i)) (by rw [hc,hnext])
      (cleared slot w position) ((cleared slot w position) (helper (slot i))) rfl
    have he:=cleared_succ slot w i
    change Function.update (cleared slot w position) (helper (slot i)) []=cleared slot w (position+1) at he
    rw [he] at h0
    obtain ⟨q,hq,h1⟩:=ih (position+1) (by omega)
    refine ⟨_,?_,P.join h0 h1⟩
    have hw:=word_le slot w position i
    nlinarith
/-- Six actual parsed/product field drains, retaining the entire old suffix and all six inputs. -/
theorem pair_run (w:Words):
    ∃time ≤ 6*(Old.mass (Old.store w.toWords)+1),
      Runs program time (.local (.clearPair 0)) (bank w) (.local .decrementA)
        (bank (replace w (SemiprimeD1StackNormalizedInverseRegisterClear.pairClear w.toWords))):=by
  let slot:Fin 6→I.Stack:=SemiprimeD1StackNormalizedInverseRegisterClear.pairSlot
  have hc:∀i:Fin 6,program (.local (.clearPair i))=.base (.pop (helper (slot i))
      (next (fun j=>Label.local (.clearPair j)) (.local .decrementA) i) (.local (.clearPair i)) (.local (.clearPair i))):=by
    intro i;rfl
  obtain ⟨time,ht,hr⟩:=sweep (by decide:0<6) slot (fun i=>Label.local (.clearPair i)) (.local .decrementA) hc 5 0 rfl w
  refine ⟨time,by omega,?_⟩
  simpa only [cleared_zero,cleared,Old.cleared_zero,slot,SemiprimeD1StackNormalizedInverseRegisterClear.pair_cleared,
    show (⟨0,by decide⟩:Fin 6)=0 from Fin.ext rfl,bank,replace] using hr
/-- All8 actual cache fields are drained after the output row has been framed. -/
theorem registers_run (w:Words):
    ∃time ≤ 8*(Old.mass (Old.store w.toWords)+1),
      Runs program time (.local (.clearCoefficient 0)) (bank w) (.local .outer)
        (bank {w with registers:=fun _=>[]}):=by
  have hc:∀i:Fin 8,program (.local (.clearCoefficient i))=.base (.pop (helper (SemiprimeD1StackNormalizedInverse.regRole i))
      (next (fun j=>Label.local (.clearCoefficient j)) (.local .outer) i) (.local (.clearCoefficient i)) (.local (.clearCoefficient i))):=by
    intro i;rfl
  obtain ⟨time,ht,hr⟩:=sweep (by decide:0<8) SemiprimeD1StackNormalizedInverse.regRole
    (fun i=>Label.local (.clearCoefficient i)) (.local .outer) hc 7 0 rfl w
  refine ⟨time,by omega,?_⟩
  simpa only [cleared_zero,cleared,Old.cleared_zero,SemiprimeD1StackNormalizedInverseRegisterClear.registers_cleared,
    show (⟨0,by decide⟩:Fin 8)=0 from Fin.ext rfl,bank] using hr
/-- Final output and five actual helper inputs are retained; all other helper roles are empty. -/
noncomputable def cleanStore (w:Words):Stack→List Bool:=by
  classical
  exact Sum.elim (fun k=>if SemiprimeD1StackRecoveryWeightsInventory.kept k then Old.store w.toWords k else []) w.scalarInputs
/-- THIS cleanup image excludes immutable powers while including every other private helper/shadow. -/
theorem work_mem_iff (k:I.Stack):
    k∈SemiprimeD1StackNormalizedInverseCleanup.roles (fun i:Fin 53=>SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩) ↔
      ¬SemiprimeD1StackRecoveryWeightsInventory.kept k:=by
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp h
    exact SemiprimeD1StackRecoveryWeightsInventory.work_not_kept i
  · intro hk
    obtain ⟨i,hi⟩:=SemiprimeD1StackRecoveryWeightsInventory.work_complete k hk
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,hi⟩
/-- Exact endpoint of THIS program's53 actual physical drains, not the inverse whole-source54 sweep. -/
theorem final_cleared (w:Words):
    cleared (fun i:Fin 53=>SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩) w 53=cleanStore w:=by
  classical
  funext role
  rcases role with role|role
  · change SemiprimeD1StackNormalizedInverseCleanup.cleared _ (Old.store w.toWords) 53 role=_
    rw [SemiprimeD1StackNormalizedInverseCleanup.cleared_full,work_mem_iff]
    by_cases h:SemiprimeD1StackRecoveryWeightsInventory.kept role <;> simp only [cleanStore,h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,Sum.elim_inl]
  · rfl
/-- All53 actual drains and EOF branches execute before final halt, retaining all six inputs and the output. -/
theorem final_run (w:Words):
    ∃time ≤ 53*(Old.mass (Old.store w.toWords)+1),
      Runs program time (.local (.clean false 0)) (bank w) (.local .done) (cleanStore w):=by
  have hc:∀i:Fin 53,program (.local (.clean false i))=.base
      (.pop (helper (SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩))
        (next (fun j=>Label.local (.clean false j)) (.local .done) i)
        (.local (.clean false i)) (.local (.clean false i))):=by intro i;rfl
  obtain ⟨time,ht,hr⟩:=sweep (by decide:0<53) (fun i:Fin 53=>SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩)
    (fun i=>Label.local (.clean false i)) (.local .done) hc 52 0 rfl w
  refine ⟨time,by omega,?_⟩
  simpa only [cleared_zero,final_cleared,show (⟨0,by decide⟩:Fin 53)=0 from Fin.ext rfl] using hr
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsCleanup
