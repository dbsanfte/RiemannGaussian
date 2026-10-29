/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationClock
/-! # Every actual orientation data role and real return cell at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationStorage
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationExecution
open SemiprimeD1StackPacketOrientationClock
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All three retained physical inputs and all sixteen initially empty helper/output words are counted. -/
theorem initial_role_bound (left right index:List Bool) (k:Stack):
    ((initial left right index).data k).length ≤ inputSize left right index :=by
  rcases k with k|k
  · exact Nat.zero_le _
  · cases k <;> dsimp only [initial,input,Sum.elim_inr,List.length_nil] <;> unfold inputSize <;> omega
/-- No reached prefix passes the actual same-program successful final halt. -/
theorem prefix_fuel (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (vectorBits left) (vectorBits right) index)=some out):
    fuel ≤ polynomial (vectorBits left) (vectorBits right) index :=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded left right index hlen
  have hf:fuel ≤ t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hp
    have hh:SemiprimeD1StackCalls.run program 1 (done left right index)=none:=rfl
    rw [hh,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- SAME source trace counts all19 actual Bool stacks and every genuine nested return frame. -/
theorem prefix_cells (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (vectorBits left) (vectorBits right) index)=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      1000000*inputSize (vectorBits left) (vectorBits right) index :=by
  let S:=inputSize (vectorBits left) (vectorBits right) index
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ out (initial_role_bound _ _ _) hp
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hp
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 19*(S+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(S+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel left right index hlen fuel out hp
  change fuel ≤ 10000*S at ht
  change _ ≤ 1000000*S
  omega
/-- Every genuine compiled prefix includes the physical none-labelled return stack in the same linear byte cap. -/
theorem machine_prefix_cells (left right:List (List Bool)) (index:List Bool) (hlen:left.length=right.length)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits left) (vectorBits right) index)))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000*inputSize (vectorBits left) (vectorBits right) index :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .leftInput) (aux .keyOutput) (SemiprimeD1StackPacketOrientation.Label.local .start)
    program fuel (initial (vectorBits left) (vectorBits right) index)
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (vectorBits left) (vectorBits right) index) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells left right index hlen fuel out hout
end RiemannGaussian.SemiprimeD1StackPacketOrientationStorage
