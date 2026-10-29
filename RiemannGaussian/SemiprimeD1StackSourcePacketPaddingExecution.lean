/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingSetup
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingRaise
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingFinish
/-! # Whole two-input physical frequency/padding source and its own actual clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingExecution
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingPrimitives SemiprimeD1StackSourcePacketPaddingCalls
open SemiprimeD1StackSourcePacketPaddingSetup SemiprimeD1StackSourcePacketPaddingRaise
open SemiprimeD1StackSourcePacketPaddingBits SemiprimeD1StackSourcePacketPaddingFinish
open SemiprimeD1StackProcedureTrace
/-- Same-program adapter clock pays copies, finite OR cut, optional actual increment, literal zero bits, reverse and trim. -/
def roundTime (a:Nat) (bits:List Bool) :Nat:=setupTime a bits+(2*a+1)+50*(bits.length+1)+finishTime a bits
/-- Real prepared adapter from the actual stopped21-role frequency bank; no computed maximum/cache is injected into its program. -/
theorem round_run (src:List Bool) (s:FE.Summary) (a:Nat) :
    ∃q≤ roundTime a s.maximum,Runs program q .copyCut (bank (readyWords src s a)) .done
      (bank {readyWords src s a with padding:=rounded a s.maximum}) :=by
  have h0:=setup_run src s a
  have h1:=cut_run a s.maximum false {readyWords src s a with prefixTodo:=List.replicate a true}
  simp only [Bool.false_or] at h1
  obtain ⟨q,hq,h2⟩:=raise_run src s a
  have h3:=finish_run src s a
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold roundTime
  omega
/-- Same physical source calls Frequency21 ONCE and includes every subsequent adapter transition and literal halt. -/
def runBound (keys:List (List Bool)) (a:Nat) :Nat:=
  SemiprimeD1StackSourceKeyFrequencyExecution.runBound keys+1+roundTime a (FE.acquire keys).maximum+1
/-- Whole entry has only acquired raw-key vector and unary exponent; every frequency/maximum/output bit is produced inside. -/
theorem source_trace (keys:List (List Bool)) (a:Nat) :
    ∃q≤ runBound keys a-1,Runs program q .start (source keys a).data .done (result keys a) :=by
  obtain ⟨q,hq,h0⟩:=frequency_call (source keys a).data keys (fun _=>rfl)
  have he:Sum.elim (SemiprimeD1StackSourceKeyFrequencyEncoding.done keys).data
      (fun k=>(source keys a).data (aux k))=bank (readyWords (SemiprimeD1TensorTapeCodec.vectorBits keys) (FE.acquire keys) a):=by
    funext k;rcases k with k|k
    · rfl
    · cases k <;> rfl
  rw [he] at h0
  obtain ⟨u,hu,h1⟩:=round_run (SemiprimeD1TensorTapeCodec.vectorBits keys) (FE.acquire keys) a
  refine ⟨q+u,?_,join h0 h1⟩
  unfold runBound
  omega
/-- Actual final halt clears both flags; the SAME trace clock includes the real last step. -/
theorem source_run (keys:List (List Bool)) (a:Nat) :
    ∃q≤ runBound keys a,SemiprimeD1StackCalls.run program q (source keys a)=some (done keys a) :=by
  obtain ⟨q,hq,hr⟩:=source_trace keys a
  obtain ⟨finish,hfin,hAt⟩:=hr [] (source keys a) ⟨rfl,rfl,rfl⟩
  have hp:0<runBound keys a:=by unfold runBound;omega
  refine ⟨q+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  exact halt_run program .done rfl (result keys a) [] finish hAt
/-- Genuine fixed25-role machine has the same whole two-field source clock and exact compact output. -/
noncomputable def paddingInTime (keys:List (List Bool)) (a:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source keys a))
      (some (SemiprimeD1StackCalls.configuration (done keys a))) (runBound keys a) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (frequencyStack (F.aux .source)) (aux .padding) .start program
  let h:=source_run keys a
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingExecution
