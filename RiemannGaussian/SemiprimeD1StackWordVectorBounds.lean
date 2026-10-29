/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVectorExecution

/-! # Complete assignment-word acquisition cost and all-prefix storage
The source pays original/count copies, all actual raw block/log calls and one
physical reversal. Complete assignments give genuinely linear acquisition in
the physical input inventory; no prepared vector or selected-word advice enters.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordVectorBounds
open SemiprimeD1StackWordVector SemiprimeD1StackWordVectorExecution SemiprimeD1StackWordVectorSpec

/-- The actual original input and BOTH retained physical cache word lengths. -/
def inputSize (word width count : List Bool) : ℕ := word.length+width.length+count.length+1

/-- A fixed quadratic also pays all generated EOF padding on short raw input. -/
theorem timeBound_le_square (word width count : List Bool) :
    timeBound word width count ≤ 1000*(inputSize word width count)^2 := by
  unfold timeBound inputSize
  nlinarith [Nat.zero_le (word.length^2),Nat.zero_le (width.length^2),Nat.zero_le (count.length^2),
    Nat.zero_le (word.length*width.length),Nat.zero_le (word.length*count.length),
    Nat.zero_le (width.length*count.length)]

/-- For every complete original assignment, acquisition is LINEAR in the full
physical input inventory. No family cutoff or sampled success is involved. -/
theorem timeBound_le_linear (word width count : List Bool)
    (hfull : count.length*width.length ≤ word.length) :
    timeBound word width count ≤ 200*inputSize word width count := by
  unfold timeBound inputSize
  nlinarith

/-- Actual complete source certificate, retaining the output-sensitive budget. -/
noncomputable def sourceAcquire (word width count : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial word width count)
      (some (done word width count)) (timeBound word width count) := by
  let h:=source_run word width count
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  exact ⟨⟨m,hm.2⟩,hm.1⟩
/-- Genuine actual finite-machine acquisition; no grouping closure is supplied. -/
noncomputable def machineAcquire (word width count : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial word width count))
      (some (SemiprimeD1StackCalls.configuration (done word width count))) (timeBound word width count) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) original output (Label.control .start) program _ _ _
    (sourceAcquire word width count)
/-- Genuine finite-machine linear bound for ALL complete assignment tapes. -/
noncomputable def machineAcquireLinear (word width count : List Bool)
    (hfull : count.length*width.length ≤ word.length) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial word width count))
      (some (SemiprimeD1StackCalls.configuration (done word width count))) (200*inputSize word width count) := by
  let h:=source_run word width count
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) original output (Label.control .start) program
  exact ⟨⟨m,hm.2⟩,hm.1.trans (timeBound_le_linear word width count hfull)⟩

/-- Exact original-order vector of actual extracted fixed-width words. -/
theorem output_original (word width count : List Bool) :
    (done word width count).data output=
      SemiprimeD1TensorTapeCodec.vectorBits (blocks width count.length word) := rfl
/-- The actual original assignment cache survives every word acquisition. -/
theorem retained_original (word width count : List Bool) : (done word width count).data original=word := rfl
/-- Every unused source bit is still available for following words or flags. -/
theorem retained_suffix (word width count : List Bool) :
    (done word width count).data (.inl 0)=word.drop (count.length*width.length) := rfl
/-- Original physical width cache is retained without numeric decoding. -/
theorem retained_width (word width count : List Bool) : (done word width count).data (.inl 1)=width := rfl
/-- The complete original physical count cache survives the actual count copy. -/
theorem retained_count (word width count : List Bool) : (done word width count).data countCache=count := rfl

/-- Every successful source prefix ends by the proved actual whole acquisition. -/
theorem prefix_fuel_le (word width count : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word width count)=some out) : fuel ≤ timeBound word width count := by
  obtain ⟨m,hm,he⟩:=source_run word width count
  have hfm : fuel ≤ m := by
    by_contra h
    have hh : fuel=m+(1+(fuel-(m+1))) := by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done word width count)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfm.trans hm
/-- Every actual prefix includes all ten Boolean data stacks AND real return
tags, including raw input/cache copies, output framing and chronological log. -/
theorem prefix_cells (word width count : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word width count)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      11*(inputSize word width count+timeBound word width count) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize word width count) _ out
    (by
      intro k
      rcases k with k|k
      · fin_cases k <;> simp [initial,store,Block.store,inputSize];omega
      · fin_cases k <;> simp [initial,store,inputSize] <;> omega) hr
  have ht:=prefix_fuel_le word width count fuel out hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hsum : (∑k : Stack,(out.data k).length) ≤ 10*(inputSize word width count+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inputSize word width count+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega
/-- The identical inventory bound at EVERY actually reached finite-machine prefix. -/
theorem machine_prefix_cells (word width count : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word width count)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      11*(inputSize word width count+timeBound word width count) := by
  have he:=SemiprimeD1StackCalls.run_correct (K:=Stack) (L:=Label) original output (Label.control .start) program fuel (initial word width count)
  change (C.run program fuel (initial word width count)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word width count))) at he
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial word width count) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word width count fuel out hrun
/-- Every actual finite-machine prefix has a fixed quadratic bound even when
padding generates more data than a short raw assignment originally contained. -/
theorem machine_prefix_cells_square (word width count : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word width count)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 20000*(inputSize word width count)^2 := by
  have h:=machine_prefix_cells word width count fuel cfg hr
  have ht:=timeBound_le_square word width count
  have hp : inputSize word width count ≤ (inputSize word width count)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by unfold inputSize;omega : 1 ≤ inputSize word width count) (by decide : 1 ≤ 2)
  omega
/-- ALL actual storage is linear in the original complete assignment inventory,
with both caches, original source, unread suffix, output and returns included. -/
theorem machine_prefix_cells_linear (word width count : List Bool)
    (hfull : count.length*width.length ≤ word.length) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word width count)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 3000*inputSize word width count := by
  have h:=machine_prefix_cells word width count fuel cfg hr
  have ht:=timeBound_le_linear word width count hfull
  omega

end RiemannGaussian.SemiprimeD1StackWordVectorBounds
