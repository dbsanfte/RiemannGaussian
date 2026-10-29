/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamExecution
/-! # Actual metadata-bounded port serialization cost and finite-machine time -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalStreamBounds
open SemiprimeD1StackPortOrdinalStream SemiprimeD1StackPortOrdinalStreamExecution
open SemiprimeD1StackDigitBankSpec (entries)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- All emitted unary cells come from bounded occurrence ordinals only. -/
theorem entries_length (words:List (List Bool)) (M:Nat)
    (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    (entries (unaryWords words)).length≤words.length*(2*M+2) := by
  induction words with
  | nil => simp [unaryWords,entries]
  | cons w ws ih =>
    have h:=ih (fun v hm=>hv v (List.mem_cons_of_mem w hm))
    have hw:=hv w (List.mem_cons_self)
    simp only [unaryWords,List.map_cons,entries,List.length_append,List.length_cons,
      SemiprimeSourceHistogramKeyBits.frame_length,List.length_replicate,List.length_nil]
    simp only [unaryWords] at h
    nlinarith
/-- The actual binary bank width, including all high-zero padding, is paid. -/
theorem bank_length (words:List (List Bool)) (M:Nat) (hl:∀w∈words,w.length≤M) :
    (vectorBits words).length≤words.length*(2*M+2)+1 := by
  induction words with
  | nil => simp [vectorBits]
  | cons w ws ih =>
    have h:=ih (fun v hm=>hl v (List.mem_cons_of_mem w hm))
    have hw:=hl w List.mem_cons_self
    simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith
/-- Actual per-record trace has a linear bound in both binary and unary bytes. -/
theorem loopBudget_le (words:List (List Bool)) (M:Nat)
    (hl:∀w∈words,w.length≤M) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    loopBudget words≤words.length*(35*M+40)+1 := by
  induction words with
  | nil => simp [loopBudget]
  | cons w ws ih =>
    have h:=ih (fun v hm=>hl v (List.mem_cons_of_mem w hm))
      (fun v hm=>hv v (List.mem_cons_of_mem w hm))
    have hw:=hl w List.mem_cons_self
    have hvw:=hv w List.mem_cons_self
    simp only [loopBudget,List.length_cons]
    nlinarith
/-- Closed polynomial actual time, with no decoded-index or cost supplier. -/
theorem timeBound_le (words:List (List Bool)) (M:Nat)
    (hl:∀w∈words,w.length≤M) (hv:∀w∈words,SemiprimeBitArithmetic.bitValue w≤M) :
    timeBound words≤100*(words.length+1)*(M+1) := by
  have hb:=bank_length words M hl
  have he:=entries_length words M hv
  have ht:=loopBudget_le words M hl hv
  unfold timeBound
  nlinarith
/-- Actual standalone input contains only the binary vector bank. -/
theorem initial_eq (bank:List Bool) :
    Turing.initList machine bank=SemiprimeD1StackCalls.configuration (initial bank) := by
  exact (SemiprimeD1StackCalls.initial_correct Stack.bank Stack.output
    (.control .start) program bank).symm
/-- Genuine complete compiled-machine execution, including all real calls. -/
noncomputable def portTapeInTime (words:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (vectorBits words))
      (some (SemiprimeD1StackCalls.configuration (done words))) (timeBound words) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect Stack.bank Stack.output (.control .start) program
  let h:=source_run words
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  exact ⟨⟨t,ht.2⟩,ht.1⟩


/-- The actual halt bounds every real executed prefix. -/
theorem prefix_fuel_le (words:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (vectorBits words))=some out) :
    fuel≤timeBound words := by
  obtain ⟨t,ht,he⟩:=source_run words
  have hf:fuel≤t := by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))) := by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:SemiprimeD1StackCalls.run program 1 (done words)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every one of twelve data roles and all real return cells is counted. -/
theorem prefix_cells (words:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (vectorBits words))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      13*((vectorBits words).length+timeBound words+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (vectorBits words).length _ out
    (by intro k;change (if k=Stack.bank then vectorBits words else []).length≤_;split <;> simp) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤12*((vectorBits words).length+fuel) := by
    calc
      _≤∑_k:Stack,((vectorBits words).length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le words fuel out hr
  omega
/-- Same inventory bound for every prefix of the actual compiled machine. -/
theorem machine_prefix_cells (words:List (List Bool)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine (vectorBits words)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      13*((vectorBits words).length+timeBound words+1) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.bank Stack.output (.control .start) program fuel
    (initial (vectorBits words))
  change (SemiprimeD1StackCalls.run program fuel (initial (vectorBits words))).map
      SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits words)))) at he
  have hh:(SemiprimeD1StackCalls.run program fuel (initial (vectorBits words))).map
      SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start))
      (initial_eq (vectorBits words)).symm).trans hr)
  cases hrun:SemiprimeD1StackCalls.run program fuel (initial (vectorBits words)) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells words fuel out hrun
end RiemannGaussian.SemiprimeD1StackPortOrdinalStreamBounds
