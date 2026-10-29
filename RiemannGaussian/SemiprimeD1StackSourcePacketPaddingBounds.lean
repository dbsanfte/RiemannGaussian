/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingExecution
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingMeaning
/-! # Same whole source has a fixed physical-input polynomial bit clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBounds
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingExecution SemiprimeD1StackSourcePacketPaddingMeaning
open SemiprimeD1StackSourcePacketPaddingSetup SemiprimeD1StackSourcePacketPaddingFinish
namespace FB
export SemiprimeD1StackSourceKeyFrequencyBytes (Sized step_sized empty_sized input_bounds)
end FB
/-- The actual whole frequency fold has one retained override and at most one added counter bit per occurrence. -/
theorem fold_sized (keys:List (List Bool)) (m W:Nat) (s:FE.Summary) (hs:FB.Sized m W s)
    (hr:∀raw∈keys,raw.length≤ W) :
    FB.Sized (m+keys.length) W (keys.foldl SemiprimeD1StackSourceKeyFrequencyEncoding.step s) :=by
  induction keys generalizing m s with
  | nil=>simpa only [List.foldl_nil,List.length_nil,Nat.add_zero] using hs
  | cons raw keys ih=>
    have hraw:=hr raw List.mem_cons_self
    simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (m+1) (SemiprimeD1StackSourceKeyFrequencyEncoding.step s raw) (FB.step_sized m W s raw hs hraw)
        (fun raw hh=>hr raw (List.mem_cons_of_mem _ hh))
/-- Actual acquired maximum width comes from the executed binary increments, with no supplied counter Fits premise. -/
theorem maximum_length (keys:List (List Bool)) :(FE.acquire keys).maximum.length≤ keys.length :=by
  have h:=fold_sized keys 0 (FE.inputSize keys) SemiprimeD1StackSourceKeyFrequencyEncoding.empty
    (FB.empty_sized _) (FB.input_bounds keys).2.2
  simpa only [Nat.zero_add,SemiprimeD1StackSourceKeyFrequencyEncoding.acquire] using h.maximum
/-- The separately paid adapter is linear in actual unary exponent bytes and binary maximum bytes. -/
theorem roundTime_le (a:Nat) (bits:List Bool) :roundTime a bits≤1000*(a+bits.length+1) :=by
  have hp:=prefixed_length a bits
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le (prefixed a bits).reverse
  rw [List.length_reverse] at ht
  unfold roundTime setupTime finishTime
  omega
/-- Conservative fifth-degree clock for the whole two-input actual frequency-and-padding program. -/
def polynomial (keys:List (List Bool)) (a:Nat) :Nat:=100000000000*(inputSize keys a)^5
/-- Every old dictionary record, exponent marker, actual low read and returned bit belongs to this SAME physical clock. -/
theorem runBound_le (keys:List (List Bool)) (a:Nat) :runBound keys a≤ polynomial keys a :=by
  let S:=inputSize keys a
  have hF:FE.inputSize keys≤ S:=by dsimp [S,inputSize];omega
  have hS:1≤ S:=(FB.input_bounds keys).1.trans hF
  have ha:a≤ S:=by dsimp [S,inputSize];omega
  have hm:(FE.acquire keys).maximum.length≤ S:=
    (maximum_length keys).trans ((FB.input_bounds keys).2.1.trans hF)
  have ht:=SemiprimeD1StackSourceKeyFrequencyBounds.runBound_le keys
  unfold SemiprimeD1StackSourceKeyFrequencyBounds.polynomial at ht
  have hp:(FE.inputSize keys)^5≤ S^5:=Nat.pow_le_pow_left hF 5
  have hfreq:SemiprimeD1StackSourceKeyFrequencyExecution.runBound keys≤1000000000*S^5:=
    ht.trans (Nat.mul_le_mul_left _ hp)
  have hround:=roundTime_le a (FE.acquire keys).maximum
  have h15:S≤ S^5:=Nat.le_pow (by decide:0<(5:Nat))
  change runBound keys a≤100000000000*S^5
  unfold runBound
  nlinarith only [hfreq,hround,ha,hm,hS,h15]
/-- Complete actual source produces its exact compact output within the fixed whole physical-input clock. -/
theorem source_run_bounded (keys:List (List Bool)) (a:Nat) :
    ∃q≤ polynomial keys a,SemiprimeD1StackCalls.run program q (source keys a)=some (done keys a) :=by
  obtain ⟨q,hq,hr⟩:=source_run keys a
  exact ⟨q,hq.trans (runBound_le keys a),hr⟩
/-- The genuine25-role finite machine has the SAME polynomial whole-source certificate. -/
noncomputable def machineSource (keys:List (List Bool)) (a:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source keys a))
      (some (SemiprimeD1StackCalls.configuration (done keys a))) (polynomial keys a) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (frequencyStack (F.aux .source)) (aux .padding) .start program
  let h:=source_run_bounded keys a
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingBounds
