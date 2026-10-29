/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordExecution
/-! # Whole owner-record bound and ALL34 roles and real return cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 32768
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordBounds
open SemiprimeD1StackOwnerRecord SemiprimeD1StackOwnerRecordExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)
/-- Actual initial key, prefix, binary bank and accumulator byte allowance. -/
def inputSize (key prefixBytes bank hist out : List Bool) : Nat :=
  key.length+prefixBytes.length+bank.length+hist.length+out.length
theorem initial_data_bound (key prefixBytes bank hist out : List Bool) (k : Stack) :
    ((initial key prefixBytes bank hist out).data k).length≤ inputSize key prefixBytes bank hist out := by
  fin_cases k <;>
    simp [initial,data,T.initial,T.data,SemiprimeD1StackOwnerPrefix.data,
      SemiprimeD1StackAdder.store,SemiprimeD1StackDigitCount.data,S.initial,R.data,inputSize] <;> omega
/-- Actual completed halt bounds every successful prefix of this SAME program. -/
theorem prefix_fuel_le (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) (fuel : Nat)
    (finish : C.State Stack Label)
    (hr : C.run program fuel (initial key (records rows tail) (vectorBits words) hist out)=some finish) :
    fuel≤ timeBound key rows words hs := by
  obtain ⟨t,ht,he⟩:=source_run key rows tail words hs hist out
  have hf:fuel≤t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done key rows tail words hs hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All34 roles, three unused shadows and every nested return cell are charged. -/
theorem prefix_cells (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) (hist out : List Bool) (fuel : Nat)
    (finish : C.State Stack Label)
    (hr : C.run program fuel (initial key (records rows tail) (vectorBits words) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      35*(inputSize key (records rows tail) (vectorBits words) hist out+timeBound key rows words hs) := by
  let I:=inputSize key (records rows tail) (vectorBits words) hist out
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ finish
    (initial_data_bound key (records rows tail) (vectorBits words) hist out) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hi:(∑k:Stack,(finish.data k).length)≤34*(I+fuel) := by
    calc
      _≤∑_k:Stack,(I+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le key rows tail words hs hist out fuel finish hr
  change _≤35*(I+timeBound key rows words hs)
  omega
/-- Literal complete table ALWAYS has at most23 bytes, including conflicting prefixes. -/
theorem table_length (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (words : List (List Bool)) (hs : words.length≤2) :
    (table key rows tail words hs).length≤23 :=
  SemiprimeD1OwnerTablePalette.bytes_le _ _ _
/-- The old unary tape grows only with bounded occurrence ordinals, never N. -/
theorem ports_length (words : List (List Bool)) (M : Nat)
    (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    (S.result words).length≤words.length*(2*M+2)+1 := by
  have h:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length
    (SemiprimeD1StackPortOrdinalStreamExecution.unaryWords words) M (by
      intro w hw
      obtain ⟨v,hv',rfl⟩:=List.mem_map.mp hw
      simpa only [List.length_replicate] using hv v hv')
  simpa only [S.result,SemiprimeD1StackPortOrdinalStreamExecution.unaryWords,List.length_map] using h
/-- Closed bound in actual key/prefix bytes and acquired width/value metadata. -/
theorem timeBound_le (key : List Bool) (rows : List (List Bool×Bool))
    (words : List (List Bool)) (hs : words.length≤2) (M : Nat)
    (hl : ∀w∈words,w.length≤M) (hv : ∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound key rows words hs≤
      200*(words.length+1)*(M+1)+100*(key.length+1)*((records rows []).length+1)+300 := by
  have ht:=SemiprimeD1StackOwnerTableBounds.traceTime_le key rows words hs
  have hb:=SemiprimeD1StackPortOrdinalStreamBounds.bank_length words M hl
  have he:=SemiprimeD1StackPortOrdinalStreamBounds.timeBound_le words M hl hv
  have hp:=ports_length words M hv
  have hlit:=table_length key rows [] words hs
  unfold SemiprimeD1StackOwnerTableBounds.runBound SemiprimeD1StackOwnerPrefixBounds.runBound at ht
  unfold timeBound R.recordTime
  nlinarith
end RiemannGaussian.SemiprimeD1StackOwnerRecordBounds
