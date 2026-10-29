/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridBounds
/-! # All104 actual tapes, allocated shadows and genuine return cells at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridStorage
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridBounds
namespace Exec
export SemiprimeD1StackRecoveryGridExecution (source_run done runBound)
end Exec
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos a_le M_le u_le t_le width_le)
end R
/-- Only five actual original words are populated, and every allocated tape is counted. -/
theorem initial_role_bound (a M u:Nat) (t width:List Bool) (k:Stack) :
    ((initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width).data k).length≤R.resource a M u t width:=by
  rcases k with k|k
  · change (if k=SemiprimeD1StackRationalOperation.aux .template then width else []).length≤_
    split
    · exact R.width_le a M u t width
    · exact Nat.zero_le _
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · exact Nat.zero_le _
      · rcases k with k|k
        · exact Nat.zero_le _
        · rcases k with k|k
          · exact Nat.zero_le _
          · cases k <;> first
              | exact Nat.zero_le _
              | exact R.t_le a M u t width
              | change (List.replicate _ _).length≤_;rw [List.length_replicate];first | exact R.a_le a M u t width | exact R.M_le a M u t width | exact R.u_le a M u t width
/-- Any successful prefix ends no later than the SAME actual source's true halt; the generous own budget need not be an exact halt time. -/
theorem prefix_fuel (a M u:Nat) (t width:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some out) :
    fuel≤Exec.runBound a M u t width:=by
  obtain ⟨q,hq,hfinal⟩:=Exec.source_run a M u t width
  have ht:fuel≤q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (Exec.done a M u t width)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- A literal inventory sum includes all104 physical roles, including displaced Geometry shadows and shared arithmetic. -/
theorem word_sum (words:Stack→List Bool) (cap:Nat) (h:∀k,(words k).length≤cap) :
    (∑k:Stack,(words k).length)≤104*cap:=by
  calc
    _≤∑_k:Stack,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
attribute [local irreducible] Exec.runBound
/-- Every prefix uses actual source-clock and input-cell bounds, with the real none-labelled return stack included. -/
theorem prefix_cells (a M u:Nat) (t width:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤105*(R.resource a M u t width+Exec.runBound a M u t width+1):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (R.resource a M u t width) _ _ (initial_role_bound a M u t width) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:=word_sum out.data (R.resource a M u t width+fuel) hd
  have ht:=prefix_fuel a M u t width fuel out hr
  omega
/-- The fixed whole-source storage polynomial pays N and W by VALUE, all retained inputs/outputs and every real return cell. -/
theorem polynomial_space (a M u:Nat) (t width:List Bool) :
    105*(R.resource a M u t width+Exec.runBound a M u t width+1)≤10^63*(R.resource a M u t width)^12:=by
  have ht:=runBound_le a M u t width
  have hR:=R.resource_pos a M u t width
  have hp:R.resource a M u t width≤(R.resource a M u t width)^12:=Nat.le_pow (by decide:0<12)
  unfold polynomial at ht
  norm_num1 at ht ⊢
  omega
/-- Genuine compiled104-role prefixes count all data tapes and the actual none-labelled saved-return tape. -/
theorem machine_prefix_cells (a M u:Nat) (t width:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^63*(R.resource a M u t width)^12:=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .originalA) (aux .slopes) (.local .start) program fuel
    (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact (prefix_cells a M u t width fuel out hout).trans (polynomial_space a M u t width)
end RiemannGaussian.SemiprimeD1StackRecoveryGridStorage
