/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyExecution
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBytes
/-! # Whole actual key-only clock is a fixed polynomial in acquired vector bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBounds
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyBytes SemiprimeD1StackSourceKeyFrequencyExecution
open SemiprimeD1StackSourceKeyFrequencyRead SemiprimeD1StackSourceKeyFrequencyMaximum
open SemiprimeD1StackSourceKeyFrequencyStore
/-- Strict comparison's optional replacement still has a linear physical byte bound. -/
theorem maximumClock_le (a b:List Bool) :maximumClock a b≤12*a.length+16*b.length+27 :=by
  have ht:=SemiprimeD1StackWordLessExecution.totalTime_le a b
  unfold maximumClock
  split_ifs <;> omega
/-- One exact row pays every old dictionary record and the actual unread suffix. -/
theorem rowTime_le (S m:Nat) (s:Summary) (raw:List Bool) (hS:1≤ S) (hm:m+1≤ S)
    (hs:Sized m S s) (hr:raw.length≤ S) :rowTime s raw≤100000*S^3 :=by
  have hm':m≤ S:=by omega
  have hc:(read s.rows raw).length≤ m:=read_length_le s.rows raw m (fun r h=>(hs.words r h).2)
  have hn:(nextCount s.rows raw).length≤ S:=
    (SemiprimeD1StackSourceEnvironmentEncoding.successor_length _).trans (by omega)
  have hd:=dictionary_length m S s hs
  have hprod:=Nat.mul_le_mul hm' (show 2*(S+1+m)+3≤4*S+5 by omega)
  have hD:(dictionary s.rows).length≤10*S^2:=by nlinarith only [hd,hprod,hS]
  have hu:=(unread_length_le s.rows raw).trans hD
  have he:(encoded raw).length≤ S+1:=by simp only [encoded,List.length_append,List.length_singleton];omega
  have hl:SemiprimeD1StackOwnerLookupBounds.runBound (encoded raw) (coded s.rows)≤100*(S+2)*(10*S^2+1):=by
    unfold SemiprimeD1StackOwnerLookupBounds.runBound
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by change (dictionary s.rows).length+1≤_;omega)
  have hmClock:=maximumClock_le s.maximum (nextCount s.rows raw)
  have h1:S≤ S^2:=Nat.le_pow (by decide:0<(2:Nat))
  have h2:S^2≤ S^3:=by calc
    _=S^2*1:=by omega
    _≤ S^2*S:=Nat.mul_le_mul_left _ hS
    _=S^3:=by ring
  have hp:(100*(S+2)*(10*S^2+1))≤3300*S^3:=by nlinarith only [hS,h1,h2]
  have hl':SemiprimeD1StackOwnerLookupBounds.runBound (encoded raw) (coded s.rows)≤3300*S^3:=hl.trans hp
  have ha:s.maximum.length≤ S:=hs.maximum.trans hm'
  unfold rowTime lookupClock storeClock
  omega
/-- The exact same chronological row loop remains polynomial with every duplicate and historical record retained. -/
theorem scanTime_le (S m:Nat) (keys:List (List Bool)) (s:Summary) (hS:1≤ S)
    (hm:m+keys.length≤ S) (hs:Sized m S s) (hr:∀raw∈keys,raw.length≤ S) :
    scanTime keys s≤ keys.length*(100000*S^3)+1 :=by
  induction keys generalizing m s with
  | nil=>simp only [scanTime,List.length_nil,Nat.zero_mul,Nat.zero_add];exact le_rfl
  | cons raw keys ih=>
    have hraw:=hr raw List.mem_cons_self
    have hrow:=rowTime_le S m s raw hS (by simp only [List.length_cons] at hm;omega) hs hraw
    have hnext:=ih (m+1) (step s raw) (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm)
      (step_sized m S s raw hs hraw) (fun raw h=>hr raw (List.mem_cons_of_mem _ h))
    simp only [scanTime,List.length_cons]
    nlinarith only [hrow,hnext]
/-- Conservative fixed fifth-degree clock for the SAME actual21-role source. -/
def polynomial (keys:List (List Bool)) :Nat :=1000000000*(inputSize keys)^5
/-- No histogram report clock or native maximum clock is used in this whole-source bound. -/
theorem runBound_le (keys:List (List Bool)) :runBound keys≤ polynomial keys :=by
  let S:=inputSize keys
  have hS:1≤ S:=(input_bounds keys).1
  have hM:keys.length≤ S:=(input_bounds keys).2.1
  have hscan:=scanTime_le S 0 keys empty hS (by omega) (empty_sized S) (input_bounds keys).2.2
  have hmul:=Nat.mul_le_mul_right (100000*S^3) hM
  have hscan':scanTime keys empty≤100000*S^4+1:=by nlinarith only [hscan,hmul]
  have hv:(SemiprimeD1TensorTapeCodec.vectorBits keys).length≤ S:=by dsimp [S,inputSize];omega
  have h15:S≤ S^5:=Nat.le_pow (by decide:0<(5:Nat))
  have h45:S^4≤ S^5:=by calc
    _=S^4*1:=by omega
    _≤ S^4*S:=Nat.mul_le_mul_left _ hS
    _=S^5:=by ring
  change runBound keys≤1000000000*S^5
  unfold runBound
  nlinarith only [hscan',hv,hS,h15,h45]
/-- Whole actual run acquires all frequencies and maximum from key vector bytes within the fixed polynomial. -/
theorem source_run_bounded (keys:List (List Bool)) :
    ∃q≤ polynomial keys,SemiprimeD1StackCalls.run program q (source keys)=some (done keys) :=by
  obtain ⟨q,hq,hr⟩:=source_run keys
  exact ⟨q,hq.trans (runBound_le keys),hr⟩
/-- Same genuinely compiled machine has the same whole-source polynomial elapsed clock. -/
noncomputable def machineSource (keys:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source keys))
      (some (SemiprimeD1StackCalls.configuration (done keys))) (polynomial keys) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .maximum) .start program
  let h:=source_run_bounded keys
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBounds
