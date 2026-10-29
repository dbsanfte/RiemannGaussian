/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsClock
/-! # All nineteen physical row-reader roles and real return cells at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsStorage
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsExecution SemiprimeD1StackPacketRowsClock
open SemiprimeD1StackPacketRowsAcquire SemiprimeD1StackPacketRowsEncoding
open SemiprimeSourceHistogramKeyBits (frame)
namespace Map
export SemiprimeD1StackOwnerLookup (records)
end Map
/-- Both actual initial words, and every initially empty helper role, share the same input-size cap. -/
theorem initial_role_bound (key cat:List Bool) (k:Stack) :((initial key cat).data k).length ≤ inputSize key cat :=by
  rcases k with k|k
  · exact Nat.zero_le _
  · cases k <;> dsimp only [initial,input,Sum.elim_inr,List.length_nil] <;> unfold inputSize <;> omega
/-- A successful prefix cannot pass the actual final halt of this same program. -/
theorem prefix_fuel (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (frame owner factor) (Map.records rows []))=some out) :
    fuel ≤ polynomial (frame owner factor) (Map.records rows []) :=by
  obtain ⟨t,ht,hstop⟩:=source_run_bounded owner factor rows left right hl hr hleft hright hlen
  have hf:fuel ≤ t:=by
    by_contra hn
    have he:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hp
    have hh:SemiprimeD1StackCalls.run program 1 (done (frame owner factor) (Map.records rows []) left right)=none:=rfl
    rw [hh,Option.bind_none] at hp
    cases hp
  exact hf.trans ht
/-- Every actual data role and every real nested return address is counted on the same whole-source prefix. -/
theorem prefix_cells (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length)
    (fuel:Nat) (out:C.State Stack Label)
    (hp:SemiprimeD1StackCalls.run program fuel (initial (frame owner factor) (Map.records rows []))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      10000000*(inputSize (frame owner factor) (Map.records rows []))^2 :=by
  let S:=inputSize (frame owner factor) (Map.records rows [])
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ out (initial_role_bound _ _) hp
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hp
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 19*(S+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(S+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel owner factor rows left right hl hr hleft hright hlen fuel out hp
  have hS:1 ≤ S:=by dsimp [S,inputSize];omega
  change fuel ≤ 100000*S^2 at ht
  change _ ≤ 10000000*S^2
  nlinarith
/-- Genuine compiled prefixes count all nineteen Bool stacks plus the physical none-labelled return stack. -/
theorem machine_prefix_cells (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length)
    (fuel:Nat) (cfg:machine.Cfg)
    (hp:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (frame owner factor) (Map.records rows []))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      10000000*(inputSize (frame owner factor) (Map.records rows []))^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .key) (output false) (.local .start) program fuel
    (initial (frame owner factor) (Map.records rows []))
  have hh:=he.trans hp
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (frame owner factor) (Map.records rows [])) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells owner factor rows left right hl hr hleft hright hlen fuel out hout
end RiemannGaussian.SemiprimeD1StackPacketRowsStorage
