/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTarget
/-! # Original input to actual preprocess target bytes, including out-of-bank zero -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPublicTargetExecution
open SemiprimeD1StackPublicTarget SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic SemiprimeMacroParameters
/-- The ACTUAL producer's complete ordered original radix digit list. -/
def digits (bits : List Bool) : List (List Bool) :=
  SemiprimeD1StackDigitBankSpec.blocks (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) bits.length bits
/-- The actual selected word, with the physical reader's literal empty default. -/
def target (bits index : List Bool) : List Bool := ((digits bits)[index.length]?).getD []
/-- Actual reached acquired preprocess data plus the still physical unary index. -/
def acquired (bits index : List Bool) : Stack→List Bool :=
  store (SemiprimeD1BinaryPublicAcquisitionComponents.result bits) (R.store [] [] index [] [] [] [] [])
/-- Final acquired preprocess data is retained, including digit cache; only the
query/index work is consumed and replaced by the actual binary target bytes. -/
def finalData (bits index : List Bool) : Stack→List Bool :=
  store (SemiprimeD1BinaryPublicAcquisitionComponents.result bits) (R.store [] [] [] [] [] (target bits index) [] [])
/-- Actual completed source halt. -/
def done (bits index : List Bool) : C.State Stack Label := ⟨none,none,none,finalData bits index,[]⟩
/-- The N-only preprocess preprocessing procedure is really called, retaining the
separately physical query outside its private bank. -/
theorem acquire_call (bits index : List Bool) (hb : bits≠[]) :
    ∃time ≤ SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+1,
      Runs program time .start (input bits index) .read (acquired bits index) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.preprocess Sum.inl_injective
    P.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl) .start .read rfl t
    (P.initial bits) (⟨none,none,none,SemiprimeD1BinaryPublicAcquisitionComponents.result bits,[]⟩:C.State P.Stack P.Label)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- Actual cache-preserving scan reads ONLY the acquired preprocess digit bytes. -/
theorem read_call (bits index : List Bool) :
    Runs program (SemiprimeD1StackJetReadExecution.totalTime index (digits bits)+1) .read
      (acquired bits index) .done (finalData bits index) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program readStack Label.reader read_injective
    R.program .start (fun _=>rfl) .read .done rfl (SemiprimeD1StackJetReadExecution.totalTime index (digits bits))
    (R.state (some .start) none none (SemiprimeD1TensorTapeCodec.vectorBits (digits bits)) [] index [] [] [] [] [])
    (R.state none none none (SemiprimeD1TensorTapeCodec.vectorBits (digits bits)) [] [] [] [] (target bits index) [] [])
    _ _ rfl rfl rfl rfl (SemiprimeD1StackJetReadExecution.source_run index (digits bits))
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (hk .index rfl).elim | exact (hk .output rfl).elim
/-- Literal whole original-binary acquisition/read execution; no target answer,
cache, digit list or digit count is supplied. Unary query acquisition is separate. -/
theorem source_run (bits index : List Bool) (hb : bits≠[]) :
    ∃time ≤ SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
      SemiprimeD1StackJetReadExecution.timeBound (SemiprimeD1TensorTapeCodec.vectorBits (digits bits)).length index.length+3,
      C.run program time (initial bits index)=some (done bits index) := by
  obtain ⟨t,ht,h0⟩:=acquire_call bits index hb
  have h1:=read_call bits index
  obtain ⟨finish,hfinish,hout⟩:=(runs_trans program _ _ _ _ _ _ _ _ h0 h1) [] (initial bits index) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (finalData bits index) [] finish hout
  refine ⟨t+(SemiprimeD1StackJetReadExecution.totalTime index (digits bits)+1)+1,?_,?_⟩
  · have hr:=SemiprimeD1StackJetReadExecution.totalTime_le index (digits bits)
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
/-- EVERY physical query index has the original targetDigit value, not merely
indices inside the bank. Missing bank cells are zero by digitCount_covers and
N<2^ell, through the frozen targetDigit_zero theorem. -/
theorem target_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    bitValue (target bits index)=targetDigit (bitLength (bitValue bits)) (bitValue bits) index.length := by
  by_cases hi : index.length<digitCount (bitLength (bitValue bits))
  · obtain ⟨digit,hd,hv⟩:=SemiprimeD1BinaryPublicAcquisitionBounds.original_digit bits hc hN index.length hi
    change bitValue (((digits bits)[index.length]?).getD [])=_
    change (digits bits)[index.length]?=some digit at hd
    rw [hd]
    exact hv
  · have he:=SemiprimeD1BinaryPublicAcquisitionBounds.original_count bits hc hN
    change (digits bits).length=digitCount (bitLength (bitValue bits)) at he
    have ho : (digits bits)[index.length]?=none := List.getElem?_eq_none (by omega)
    have hz:=targetDigit_zero (bitLength_pos hN) (input_lt_bitLength_power (bitValue bits)) (by omega : digitCount (bitLength (bitValue bits)) ≤ index.length)
    change bitValue (((digits bits)[index.length]?).getD [])=_
    rw [ho,hz]
    rfl
/-- The actual halted output is the original preprocess digit for every physical index. -/
theorem output_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) :
    bitValue ((done bits index).data (.inr .output))=
      targetDigit (bitLength (bitValue bits)) (bitValue bits) index.length := target_original bits index hc hN
/-- Every actually acquired metadata/cache role survives this actual target scan. -/
theorem retained_public (bits index : List Bool) (k : P.Stack) :
    (done bits index).data (.inl k)=SemiprimeD1BinaryPublicAcquisitionComponents.result bits k := rfl
/-- All private reader/index/work roles except output are empty at completion. -/
theorem cleanup (bits index : List Bool) (k : R.Stack) (hk : k≠.output) :
    (done bits index).data (.inr k)=[] := by
  cases k <;> simp_all [done,finalData,store,R.store]
end RiemannGaussian.SemiprimeD1StackPublicTargetExecution
