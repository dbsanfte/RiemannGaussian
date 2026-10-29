/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCalls
/-! # Actual finite cleanup sweeps preserve every original and added caller word
The old cleared-store equalities reused below are mathematical update/list
identities only. Every clock here is proved from THIS program's actual drains;
no old execution or semantic report clock is transported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCleanup
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineCalls SemiprimeD1StackProcedureTrace
namespace Old
export SemiprimeD1StackRecoveryGridCleanup (mass cleared cleared_zero cleared_succ cleared_le)
end Old
/-- Exact mathematical actual-old-store view after fixed literal cleanup positions. -/
noncomputable def cleared {n:Nat} (slot:Fin n→Q.Stack) (w:Words) (position:Nat):Stack→List Bool:=
  Sum.elim (Old.cleared slot (SemiprimeD1StackRecoveryGridView.bank w.toWords) position) w.added
/-- An actual original-word write preserves every added caller tape. -/
theorem update_lift (before:Q.Stack→List Bool) (added:Aux→List Bool) (slot:Q.Stack) (xs:List Bool) :
    Function.update (Sum.elim before added) (grid slot) xs=Sum.elim (Function.update before slot xs) added:=by
  funext role
  rcases role with role|role
  · simp only [grid,Function.update_apply,Sum.elim_inl,Sum.inl.injEq]
  · rfl
/-- Before real cleanup, the entire112-word bank is unchanged. -/
theorem cleared_zero {n:Nat} (slot:Fin n→Q.Stack) (w:Words):cleared slot w 0=bank w:=by
  unfold cleared
  rw [Old.cleared_zero]
  rfl
/-- One real old-role EOF drain advances the literal position and preserves all111 other words. -/
theorem cleared_succ {n:Nat} (slot:Fin n→Q.Stack) (w:Words) (i:Fin n):
    Function.update (cleared slot w i.val) (grid (slot i)) []=cleared slot w (i.val+1):=by
  unfold cleared
  rw [update_lift,Old.cleared_succ]
/-- Any actual word being drained has its own existing physical-cell mass cap. -/
theorem word_le {n:Nat} (slot:Fin n→Q.Stack) (w:Words) (position:Nat) (i:Fin n):
    (cleared slot w position (grid (slot i))).length≤ Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords):=
  Old.cleared_le slot _ position (slot i)
/-- The next static finite cleanup label, before all original dimensions. -/
def next {n:Nat} (pc:Fin n→Label) (stopped:Label) (i:Fin n):Label:=
  if h:i.val<n-1 then pc ⟨i.val+1,by omega⟩ else stopped
/-- Every literal cleanup loop is executed on THIS112-role program, with all bytes and empty branches paid. -/
theorem sweep {n:Nat} (hn:0<n) (slot:Fin n→Q.Stack) (pc:Fin n→Label) (stopped:Label)
    (hc:∀i,program (pc i)=.base (.pop (grid (slot i)) (next pc stopped i) (pc i) (pc i)))
    (remaining position:Nat) (hp:position+remaining=n-1) (w:Words):
    ∃q≤(remaining+1)*(Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords)+1),
      Runs program q (pc ⟨position,by omega⟩) (cleared slot w position) stopped (cleared slot w n):=by
  induction remaining generalizing position with
  | zero=>
    have hpos:position=n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=stopped:=by simp only [next,i,hpos,Nat.lt_irrefl,dite_false]
    have h0:=PTrace.drain_loop (pc i) stopped (grid (slot i)) (by rw [hc,hnext])
      (cleared slot w position) ((cleared slot w position) (grid (slot i))) rfl
    have he:=cleared_succ slot w i
    change Function.update (cleared slot w position) (grid (slot i)) []=cleared slot w (position+1) at he
    rw [he,show position+1=n by omega] at h0
    refine ⟨_,?_,h0⟩
    have hw:=word_le slot w position i
    omega
  | succ remaining ih=>
    have hpos:position<n-1:=by omega
    let i:Fin n:=⟨position,by omega⟩
    have hnext:next pc stopped i=pc ⟨position+1,by omega⟩:=by simp only [next,i,dite_eq_left hpos]
    have h0:=PTrace.drain_loop (pc i) (pc ⟨position+1,by omega⟩) (grid (slot i)) (by rw [hc,hnext])
      (cleared slot w position) ((cleared slot w position) (grid (slot i))) rfl
    have he:=cleared_succ slot w i
    change Function.update (cleared slot w position) (grid (slot i)) []=cleared slot w (position+1) at he
    rw [he] at h0
    obtain ⟨q,hq,h1⟩:=ih (position+1) (by omega)
    refine ⟨_,?_,PTrace.join h0 h1⟩
    have hw:=word_le slot w position i
    nlinarith
/-- All35 non-template real arithmetic fields are physically drained and helper-return is reached. -/
theorem rational_run (site:Site) (w:Words):
    ∃q≤35*(Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords)+1),
      Runs program q (.operation site (.clear 0)) (bank w) (.operation site .done)
        (cleared (fun i:Fin 35=>Q.rationalStack (Q.rationalRole i)) w 35):=by
  have hc:∀i:Fin 35,program (.operation site (.clear i))=.base
      (.pop (grid (Q.rationalStack (Q.rationalRole i))) (next (fun j=>Label.operation site (.clear j)) (.operation site .done) i)
        (.operation site (.clear i)) (.operation site (.clear i))):=by intro i;rfl
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<35) (fun i:Fin 35=>Q.rationalStack (Q.rationalRole i))
    (fun i=>Label.operation site (.clear i)) (.operation site .done) hc 34 0 rfl w
  refine ⟨q,by omega,?_⟩
  simpa only [cleared_zero,show (⟨0,by decide⟩:Fin 35)=0 from Fin.ext rfl] using hr
/-- Mathematical endpoint of THIS actual arithmetic sweep retains W and all76 foreign words literally. -/
theorem rational_cleared (w:Words):
    cleared (fun i:Fin 35=>Q.rationalStack (Q.rationalRole i)) w 35=
      bank {w with rational:=fun role=>if role=SemiprimeD1StackRationalOperation.aux .template then w.rational role else []}:=by
  unfold cleared
  rw [SemiprimeD1StackRecoveryGridCleanup.rational_cleared]
  rfl
/-- All ten actual geometry/shadow roles are physically cleared before originalt scratch is drained. -/
theorem geometry_run (w:Words):
    ∃q≤10*(Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords)+1),
      Runs program q (.local (.clearGeometry 0)) (bank w) (.local .clearQ)
        (cleared (fun i:Fin 10=>Q.geometryAux (Q.geometryRole i)) w 10):=by
  have hc:∀i:Fin 10,program (.local (.clearGeometry i))=.base
      (.pop (grid (Q.geometryAux (Q.geometryRole i))) (next (fun j=>Label.local (.clearGeometry j)) (.local .clearQ) i)
        (.local (.clearGeometry i)) (.local (.clearGeometry i))):=by intro i;rfl
  obtain ⟨q,hq,hr⟩:=sweep (by decide:0<10) (fun i:Fin 10=>Q.geometryAux (Q.geometryRole i))
    (fun i=>Label.local (.clearGeometry i)) (.local .clearQ) hc 9 0 rfl w
  refine ⟨q,by omega,?_⟩
  simpa only [cleared_zero,show (⟨0,by decide⟩:Fin 10)=0 from Fin.ext rfl] using hr
/-- Exact actual geometry cleanup endpoint; all Grid retained caches and all added words survive. -/
theorem geometry_cleared (w:Words):
    cleared (fun i:Fin 10=>Q.geometryAux (Q.geometryRole i)) w 10=bank {w with geometry:=fun _=>[]}:=by
  unfold cleared
  rw [SemiprimeD1StackRecoveryGridGeometry.geometry_cleared]
  rfl
/-- Actual mass includes ALL112 physical data words, including every added array/count buffer. -/
def mass (data:Stack→List Bool):Nat:=∑slot,(data slot).length
/-- Every actual initialized/cache/output byte belongs to the existing physical bank. -/
theorem word_le_mass (data:Stack→List Bool) (slot:Stack):(data slot).length≤ mass data:=
  Finset.single_le_sum (f:=fun slot:Stack=>(data slot).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ slot)
/-- The complete old Grid mass is a physical subset of the complete112-word bank. -/
theorem old_mass_le (w:Words):Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords)≤ mass (bank w):=by
  have he:mass (bank w)=Old.mass (SemiprimeD1StackRecoveryGridView.bank w.toWords)+(∑slot:Aux,(w.added slot).length):=by
    simp only [mass,bank,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Old.mass]
  omega
/-- A fixed inventory sum charges every one of the112 allocated physical tapes. -/
theorem word_sum (data:Stack→List Bool) (cap:Nat) (h:∀slot,(data slot).length≤ cap):mass data≤112*cap:=by
  unfold mass
  calc
    _≤∑_slot:Stack,cap:=Finset.sum_le_sum (fun slot _=>h slot)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
/-- SAME actual executed fragment bounds physical stopped-byte mass; no report clock is transported. -/
theorem trace_mass (time:Nat) (pc stopped:Label) (before after:Stack→List Bool)
    (hr:Runs program time pc before stopped after):mass after≤112*(mass before+time):=by
  let start:C.State Stack Label:=⟨some pc,none,none,before,[]⟩
  obtain ⟨finish,hfinish,hAt⟩:=hr [] start ⟨rfl,rfl,rfl⟩
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program time (mass before) start finish (word_le_mass before) hfinish
  rw [hAt.2.1] at hd
  exact word_sum after (mass before+time) hd
/-- Actual scalar-prefix plus all35 physical cleanup drains has its own complete bound, including real foreign retained bytes. -/
theorem rational_after_trace (site:Site) (time:Nat) (pc:Label) (before middle:Words)
    (hr:Runs program time pc (bank before) (.operation site (.clear 0)) (bank middle)):
    ∃q≤4000*(mass (bank before)+time+1),Runs program q pc (bank before) (.operation site .done)
      (cleared (fun i:Fin 35=>Q.rationalStack (Q.rationalRole i)) middle 35):=by
  obtain ⟨q,hq,hclear⟩:=rational_run site middle
  have hsub:=old_mass_le middle
  have hm:=trace_mass time pc (.operation site (.clear 0)) (bank before) (bank middle) hr
  refine ⟨time+q,?_,PTrace.join hr hclear⟩
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCleanup
