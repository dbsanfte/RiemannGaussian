/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsBounds
/-! # Every140 physical word and actual saved return at whole/ready compiled prefixes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsStorage
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsEncoding
open SemiprimeD1StackRecoveryNodeInputsBounds SemiprimeD1StackRecoveryNodeInputsResource
/-- All140 words are counted, including every allocated otherwise-unused private address. -/
theorem word_sum (data : Stack→List Bool) (cap : ℕ) (h : ∀role,(data role).length≤cap) :
    (∑role : Stack,(data role).length)≤140*cap := by
  classical
  calc
    _≤∑_k : Stack,cap:=Finset.sum_le_sum (fun role _=>h role)
    _=140*cap:=by rw [Finset.sum_const,Finset.card_univ,stack_card];rfl
/-- A prefix cannot continue past a proved true halt of the SAME program/state. -/
theorem prefix_fuel (start stop : C.State Stack Label) (bound : ℕ)
    (hstop : stop.pc=none) (h : ∃s≤bound,SemiprimeD1StackCalls.run program s start=some stop)
    (fuel : ℕ) (out : C.State Stack Label) (hr : SemiprimeD1StackCalls.run program fuel start=some out) :
    fuel≤bound := by
  obtain ⟨s,hs,hh⟩:=h
  have hbefore:fuel ≤ s :=by
    by_contra hn
    have he:fuel=s+(1+(fuel-(s+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have heof:SemiprimeD1StackCalls.run program 1 stop=none:=by
      cases stop with
      | mk pc focus flag data frames=>cases pc <;> first | rfl | cases hstop
    rw [heof,Option.bind_none] at hr
    cases hr
  exact hbefore.trans hs
/-- Generic SAME-source prefix capacity counts all140 tapes and the real none-label stack. -/
theorem prefix_cap (start stop : C.State Stack Label) (cap bound : ℕ)
    (hstop : stop.pc=none) (hframes : start.frames=[])
    (hstart : ∀role,(start.data role).length≤cap)
    (h : ∃s≤bound,SemiprimeD1StackCalls.run program s start=some stop)
    (fuel : ℕ) (out : C.State Stack Label) (hr : SemiprimeD1StackCalls.run program fuel start=some out) :
    (∑role : Stack,(out.data role).length)+out.frames.length≤141*(cap+bound) := by
  have hf:=prefix_fuel start stop bound hstop h fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel cap start out hstart hr
  have hm:=word_sum out.data (cap+fuel) hd
  have hret:=SemiprimeD1StackCalls.run_frame_bound program fuel start out hr
  rw [hframes,List.length_nil] at hret
  omega
/-- The actual five source words and every other initially empty address have their original physical-byte cap. -/
theorem initial_bound (a M u : ℕ) (t width : List Bool) (role : Stack) :
    ((initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width).data role).length≤R.resource a M u t width := by
  rcases role with role|role
  · exact SemiprimeD1StackRecoveryAffineStorage.initial_role_bound a M u t width role
  · rcases role with role|role <;> exact Nat.zero_le _
/-- The actual retained Grid104 bank, not a supplied array/rank answer, has a semantic cubic ready-byte cap. -/
theorem ready_initial_bound (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (role : Stack) :
    ((gridReady a M u selected t width).data role).length≤10^9*(R.resource a M u t width)^3 := by
  rcases role with role|role
  · rcases role with role|role
    · exact (SemiprimeD1StackRecoveryAffineInitialCaps.original_caps a M u selected t width ht).2 role
    · exact Nat.zero_le _
  · rcases role with role|role <;> exact Nat.zero_le _
/-- Fixed physical-space coefficient and degree precede every original phase/template. -/
def cellsPolynomial (a M u : ℕ) (t width : List Bool) : ℕ :=10^153*(R.resource a M u t width)^30
/-- Both whole and already-acquired-Grid ready boundaries fit this one all140-plus-returns envelope. -/
theorem cells_le (a M u : ℕ) (t width : List Bool) :
    141*(10^9*(R.resource a M u t width)^3+polynomial a M u t width)≤cellsPolynomial a M u t width := by
  have h:=Nat.pow_le_pow_right (R.resource_pos a M u t width) (by decide:3≤30)
  unfold polynomial cellsPolynomial
  omega
/-- EVERY actual source prefix includes all140 words and genuine call-stack cells. -/
theorem prefix_cells (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some out) :
    (∑role : Stack,(out.data role).length)+out.frames.length≤cellsPolynomial a M u t width := by
  have hb:∀role,((initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width).data role).length≤10^9*(R.resource a M u t width)^3:=by
    intro role
    have h:=initial_bound a M u t width role
    have hp:R.resource a M u t width≤(R.resource a M u t width)^3:=Nat.le_pow (by decide:0<3)
    omega
  exact (prefix_cap _ _ _ _ rfl rfl hb (source_run_bounded a M u selected t width ht) fuel out hr).trans (cells_le a M u t width)
/-- SAME ready source counts retained Grid fields and all new/private words, with no replay. -/
theorem ready_prefix_cells (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (fuel : ℕ) (out : C.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (gridReady a M u selected t width)=some out) :
    (∑role : Stack,(out.data role).length)+out.frames.length≤cellsPolynomial a M u t width :=
  (prefix_cap _ _ _ _ rfl rfl (ready_initial_bound a M u selected t width ht)
    (ready_run_bounded a M u selected t width ht) fuel out hr).trans (cells_le a M u t width)
/-- Generic exact compiled-state bridge applies to BOTH actual entries of this SAME machine. -/
theorem machine_cap (start : C.State Stack Label) (bound : ℕ)
    (h : ∀fuel out,SemiprimeD1StackCalls.run program fuel start=some out→
      (∑role : Stack,(out.data role).length)+out.frames.length≤bound)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start))=some cfg) :
    (∑role : Stack,(cfg.stk (some role)).length)+(cfg.stk none).length≤bound := by
  have he:=SemiprimeD1StackCalls.run_correct (affine (A.oldAux .originalA)) inverseOutput (ctl .start) program fuel start
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel start with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:cfg=SemiprimeD1StackCalls.configuration out:=(Option.some.inj hh).symm
    subst cfg
    exact h fuel out hout
/-- All140 data alphabets plus actual return cells at EVERY genuine compiled whole prefix. -/
theorem machine_prefix_cells (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)))=some cfg) :
    (∑role : Stack,(cfg.stk (some role)).length)+(cfg.stk none).length≤cellsPolynomial a M u t width :=
  machine_cap _ _ (prefix_cells a M u selected t width ht) fuel cfg hp
/-- SAME compiled ready entry retains all old caches, counting every actual data and return cell. -/
theorem machine_ready_prefix_cells (a M u : ℕ) (selected : Fin (2^(a+1))) (t width : List Bool)
    (ht : SemiprimeBitArithmetic.bitValue t=selected.val) (fuel : ℕ) (cfg : machine.Cfg)
    (hp : (fun c=>c.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (gridReady a M u selected t width)))=some cfg) :
    (∑role : Stack,(cfg.stk (some role)).length)+(cfg.stk none).length≤cellsPolynomial a M u t width :=
  machine_cap _ _ (ready_prefix_cells a M u selected t width ht) fuel cfg hp
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsStorage
