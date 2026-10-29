/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBoundaryRecordExecution
/-! # Closed boundary record clock and every actual physical prefix cell -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBoundaryRecordBounds
open SemiprimeD1StackBoundaryRecord SemiprimeD1StackBoundaryRecordExecution
/-- Initial storage accounts for original N, the acquired bank and both accumulators. -/
def inputSize (bits bank hist out : List Bool) : Nat := bits.length+bank.length+hist.length+out.length
/-- Every initial role, including both unused shadows, has an actual input-byte bound. -/
theorem initial_data_bound (bits bank hist out : List Bool) (k : Stack) :
    ((initial bits bank hist out).data k).length≤ inputSize bits bank hist out := by
  have hz (j : Z.Stack) : ((Z.initial bits).data j).length≤bits.length := by
    rcases j with j|j
    · change (SemiprimeD1StackZeroBoundaryTable.P.input bits j).length≤bits.length
      rw [SemiprimeD1StackZeroBoundaryTableBounds.public_input]
      split <;> simp
    · cases j <;> exact Nat.zero_le _
  have hs (j : S.Stack) : ((S.initial bank).data j).length≤bank.length := by
    change (if j=SemiprimeD1StackPortOrdinalStream.Stack.bank then bank else []).length≤_
    split <;> simp
  rcases k with k|k
  · have h:=hz k;change ((Z.initial bits).data k).length≤_;unfold inputSize;omega
  · cases k with
    | inl k => have h:=hs k;change ((S.initial bank).data k).length≤_;unfold inputSize;omega
    | inr k => cases k <;> simp [initial,data,R.data,inputSize];omega
/-- A real successful whole-source halt bounds all possible executed prefixes. -/
theorem prefix_fuel_le (bits : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some finish) :
    fuel≤timeBound bits words := by
  obtain ⟨t,ht,he⟩:=source_run bits hb words hist out
  have hf:fuel≤t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits words hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All48 roles, both unused alias shadows and all real nested return cells are counted. -/
theorem prefix_cells (bits : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      49*(inputSize bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+timeBound bits words+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (inputSize bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) _ finish
    (initial_data_bound bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length)≤
      48*(inputSize bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+fuel) := by
    calc
      _≤∑_k:Stack,(inputSize bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb words hist out fuel finish hr
  omega
/-- Same complete prefix inventory in the actual compiled finite-control machine. -/
theorem machine_prefix_cells (bits : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      49*(inputSize bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+timeBound bits words+1) := by
  have he:=SemiprimeD1StackCalls.run_correct original output (.inl .start) program fuel
    (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)
  change (C.run program fuel (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)).map
    SemiprimeD1StackCalls.configuration=
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel]
        (some (SemiprimeD1StackCalls.configuration
          (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))) at he
  have hh:(C.run program fuel (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)).map
      SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run program fuel (initial bits (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) with
  | none => rw [hrun] at hh;cases hh
  | some finish =>
    rw [hrun] at hh
    have hc:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb words hist out fuel finish hrun
/-- Actual internal flags, including remembered return labels, are finite. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite original output (.inl .start) program
/-- Every actual alphabet is finite, including the real return-stack alphabet. -/
theorem all_alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (.inl .start) program k
/-- At most four fundamental commands implement each actually compiled instruction. -/
theorem compile_depth (pc : Label) :
    SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  (SemiprimeD1StackCalls.compile_depth (.inl .start : Label) (program pc))
/-- Every whole-table byte is acquired by the real writer. -/
theorem table_length (bits : List Bool) :
    (table bits).length+1≤7*2^(SemiprimeD1StackZeroBoundaryTable.cached bits).length :=
  (SemiprimeD1BooleanTreeStream.bytes_length _ _).2
/-- The old unary field is bounded only by actual metadata values, including ID zero. -/
theorem ports_length (words : List (List Bool)) (M : Nat)
    (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    (S.result words).length≤words.length*(2*M+2)+1 := by
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length
    (SemiprimeD1StackPortOrdinalStreamExecution.unaryWords words) M (by
      intro w hw
      obtain ⟨v,hv',rfl⟩:=List.mem_map.mp hw
      simpa only [List.length_replicate] using hv v hv')
  simpa only [S.result,SemiprimeD1StackPortOrdinalStreamExecution.unaryWords,List.length_map] using h
/-- Whole real clock: public acquisition once, full table output, binary padding,
actual unary metadata conversion and every record framing bit. -/
theorem timeBound_le (bits : List Bool) (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound bits words≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+
      61*2^(SemiprimeD1StackZeroBoundaryTable.cached bits).length+
      110*(words.length+1)*(M+1)+20 := by
  have hs:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words M hl hv
  have hp:=ports_length words M hv
  have ht:=table_length bits
  unfold timeBound SemiprimeD1StackZeroBoundaryTableExecution.timeBound R.recordTime
  nlinarith
end RiemannGaussian.SemiprimeD1StackBoundaryRecordBounds
