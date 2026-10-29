/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanRecordExecution
/-! # Closed Boolean record clock and every actual physical prefix cell -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBooleanRecordBounds
open SemiprimeD1StackBooleanRecord SemiprimeD1StackBooleanRecordExecution
/-- Initial storage accounts for the acquired bank and both accumulators. -/
def inputSize (bank hist out : List Bool) : Nat := bank.length+hist.length+out.length
/-- Every initial role, including both unused shadows, has an actual input-byte bound. -/
theorem initial_data_bound (mode : SemiprimeD1StackBooleanEntry.Mode) (bank hist out : List Bool) (k : Stack) :
    ((initial mode bank hist out).data k).length≤ inputSize bank hist out := by
  have hs (j : S.Stack) : ((S.initial bank).data j).length≤bank.length := by
    change (if j=SemiprimeD1StackPortOrdinalStream.Stack.bank then bank else []).length≤_
    split <;> simp
  rcases k with k|k
  · change 0≤_;exact Nat.zero_le _
  · cases k with
    | inl k => have h:=hs k;change ((S.initial bank).data k).length≤_;unfold inputSize;omega
    | inr k => cases k <;> simp [initial,data,R.data,inputSize];omega
/-- A real successful whole-source halt bounds all possible executed prefixes. -/
theorem prefix_fuel_le (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some finish) :
    fuel≤timeBound mode words := by
  obtain ⟨t,ht,he⟩:=source_run mode words hist out
  have hf:fuel≤t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done mode words hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All17 roles, both unused alias shadows and all real nested return cells are counted. -/
theorem prefix_cells (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      18*(inputSize (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+timeBound mode words+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (inputSize (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) _ finish
    (initial_data_bound mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length)≤
      17*(inputSize (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+fuel) := by
    calc
      _≤∑_k:Stack,(inputSize (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le mode words hist out fuel finish hr
  omega
/-- Same complete prefix inventory in the actual compiled finite-control machine. -/
theorem machine_prefix_cells (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool))
    (hist out : List Bool) (fuel : Nat) (cfg : (machine mode).Cfg)
    (hr : (fun q=>q.bind (machine mode).step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      18*(inputSize (SemiprimeD1TensorTapeCodec.vectorBits words) hist out+timeBound mode words+1) := by
  have he:=SemiprimeD1StackCalls.run_correct original output (.inl (.start mode)) program fuel
    (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)
  change (C.run program fuel (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)).map
    SemiprimeD1StackCalls.configuration=
      (fun q:Option (machine mode).Cfg=>q.bind (machine mode).step)^[fuel]
        (some (SemiprimeD1StackCalls.configuration
          (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out))) at he
  have hh:(C.run program fuel (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out)).map
      SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run program fuel (initial mode (SemiprimeD1TensorTapeCodec.vectorBits words) hist out) with
  | none => rw [hrun] at hh;cases hh
  | some finish =>
    rw [hrun] at hh
    have hc:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells mode words hist out fuel finish hrun
/-- Actual internal flags, including remembered return labels, are finite. -/
theorem control_finite (mode : SemiprimeD1StackBooleanEntry.Mode) : Finite (machine mode).σ :=
  SemiprimeD1StackCalls.control_finite original output (.inl (.start mode)) program
/-- Every alphabet is finite, including the real return-stack alphabet. -/
theorem all_alphabets_finite (mode : SemiprimeD1StackBooleanEntry.Mode) (k : (machine mode).K) :
    Finite ((machine mode).Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite original output (.inl (.start mode)) program k
/-- Each compiled transition uses at most four fundamental commands. -/
theorem compile_depth (mode : SemiprimeD1StackBooleanEntry.Mode) (pc : Label) :
    SemiprimeD1StackBytecode.statementDepth ((machine mode).m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.inl (.start mode) : Label) (program pc)
/-- Every complete literal table has at most 47 actual bytes. -/
theorem table_length (mode : SemiprimeD1StackBooleanEntry.Mode) : (table mode).length≤47 :=
  SemiprimeD1StackBooleanTableSource.bytes_le mode
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
/-- Whole real clock includes the literal table, preserving scope conversion,
all unary framing bytes and every real nested call/return. -/
theorem timeBound_le (mode : SemiprimeD1StackBooleanEntry.Mode) (words : List (List Bool)) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound mode words≤110*(words.length+1)*(M+1)+210 := by
  have hs:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words M hl hv
  have hp:=ports_length words M hv
  have ht:=table_length mode
  unfold timeBound R.recordTime
  nlinarith
end RiemannGaussian.SemiprimeD1StackBooleanRecordBounds
