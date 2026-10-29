/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordExecution
/-! # Linear descriptor overhead and every actual data/return prefix cell -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordBounds
open SemiprimeD1StackBooleanDescriptorRecord SemiprimeD1StackBooleanDescriptorRecordEncoding
open SemiprimeD1StackBooleanDescriptorRecordExecution
/-- All loaded source bytes and caller accumulators are explicitly retained. -/
def inputSize (descriptor bank hist out : List Bool) : Nat :=
  descriptor.length+bank.length+hist.length+out.length
/-- Every actual initial role has a bound in the real loaded byte inventory. -/
theorem initial_data_bound (descriptor bank hist out : List Bool) (k : Stack) :
    ((initial descriptor bank hist out).data k).length ≤ inputSize descriptor bank hist out := by
  rcases k with k|k
  · have h:=SemiprimeD1StackBooleanRecordBounds.initial_data_bound .equality bank hist out k
    change ((R.initial .equality bank hist out).data k).length ≤ _
    unfold inputSize SemiprimeD1StackBooleanRecordBounds.inputSize at *
    omega
  · rcases k with k|k
    · change 0 ≤ _;exact Nat.zero_le _
    · cases k <;> simp [initial,clean,data,inputSize]
      omega
/-- Constructor selection costs only a fixed linear number of actual descriptor bytes. -/
theorem timeBound_le_descriptor (code : Fin 18) (w : Record)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (scope : List (List Bool))
    (htag:w 0=List.replicate code.val true) :
    timeBound code w mode scope ≤ SemiprimeD1StackBooleanRecordExecution.timeBound mode scope+
      7*(record w []).length+12 := by
  have ht:=tag_length_le_mass w
  rw [htag,List.length_replicate] at ht
  rw [record_length]
  unfold timeBound
  simp only [List.length_nil]
  omega
/-- Actual padded-binary scope conversion remains paid; no decoded scope is supplied. -/
theorem timeBound_le (code : Fin 18) (w : Record)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (scope : List (List Bool)) (M : Nat)
    (htag:w 0=List.replicate code.val true)
    (hl:∀s∈scope,s.length ≤ M) (hv:∀s∈scope,SemiprimeBitArithmetic.bitValue s ≤ M) :
    timeBound code w mode scope ≤ 110*(scope.length+1)*(M+1)+7*(record w []).length+222 := by
  have hd:=timeBound_le_descriptor code w mode scope htag
  have hs:=SemiprimeD1StackBooleanRecordBounds.timeBound_le mode scope M hl hv
  omega
/-- A completed actual source run bounds every successfully reached prefix. -/
theorem prefix_fuel_le (code : Fin 18) (w : Record) (tail : List Bool)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (htag:w 0=List.replicate code.val true)
    (hm:dispatch code=.local (.record mode)) (scope : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (finish : C.State Stack Label)
    (hr:C.run program fuel (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)=some finish) :
    fuel ≤ timeBound code w mode scope := by
  obtain ⟨t,ht,he⟩:=source_run code w tail mode htag hm scope hist out
  have hf:fuel ≤ t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done mode w tail scope hist out)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every one of27 Boolean data roles and every real return cell is counted. -/
theorem prefix_cells (code : Fin 18) (w : Record) (tail : List Bool)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (htag:w 0=List.replicate code.val true)
    (hm:dispatch code=.local (.record mode)) (scope : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (finish : C.State Stack Label)
    (hr:C.run program fuel (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length ≤
      28*(inputSize (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out+
        timeBound code w mode scope+1) := by
  let I:=inputSize (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ finish
    (initial_data_bound (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length) ≤ 27*(I+fuel) := by
    calc
      _ ≤ ∑_k:Stack,(I+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le code w tail mode htag hm scope hist out fuel finish hr
  change (∑k:Stack,(finish.data k).length)+finish.frames.length ≤ 28*(I+timeBound code w mode scope+1)
  omega
/-- Identical full prefix inventory in the actually compiled finite machine. -/
theorem machine_prefix_cells (code : Fin 18) (w : Record) (tail : List Bool)
    (mode : SemiprimeD1StackBooleanEntry.Mode) (htag:w 0=List.replicate code.val true)
    (hm:dispatch code=.local (.record mode)) (scope : List (List Bool)) (hist out : List Bool)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      28*(inputSize (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out+
        timeBound code w mode scope+1) := by
  have he:=SemiprimeD1StackCalls.run_correct (aux .reader) (.inl R.history) (.local (.field 0)) program fuel
    (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)
  change (C.run program fuel (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)).map
    SemiprimeD1StackCalls.configuration=
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel]
        (some (SemiprimeD1StackCalls.configuration
          (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out))) at he
  have hh:(C.run program fuel
      (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out)).map
        SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run program fuel (initial (record w tail) (SemiprimeD1TensorTapeCodec.vectorBits scope) hist out) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have hc:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells code w tail mode htag hm scope hist out fuel finish hrun
/-- Each compiled transition uses at most four fundamental finite-machine commands. -/
theorem compile_depth (pc : Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤ 4 :=
  SemiprimeD1StackCalls.compile_depth (.local (.field 0) : Label) (program pc)
end RiemannGaussian.SemiprimeD1StackBooleanDescriptorRecordBounds
