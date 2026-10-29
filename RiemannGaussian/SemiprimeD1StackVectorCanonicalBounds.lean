/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorCanonicalExecution

/-! # Complete canonical-vector guard time and every-prefix space
Input byte lengths alone bound the actual parsing, fresh binary modulus
copies, all visited comparisons and rejected-suffix cleanup. No guard is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVectorCanonicalBounds
open SemiprimeD1StackVectorCanonical SemiprimeD1StackVectorCanonicalExecution
open SemiprimeD1TensorTapeCodec (vectorBits)

/-- Every physical word iteration has a derived linear instruction allowance. -/
theorem stepBudget_le (word cached : List Bool) :
    stepBudget word cached ≤ 14*word.length+11*cached.length+27 := by
  have h:=SemiprimeD1StackWordLessExecution.totalTime_le word cached
  unfold stepBudget
  omega
/-- The entire accepting or rejecting loop has one fixed quadratic bound. -/
theorem loopBudget_le (words : List (List Bool)) (cached : List Bool) :
    loopBudget cached words ≤ 100*((vectorBits words).length+cached.length+1)^2 := by
  induction words with
  | nil =>
    simp only [loopBudget,vectorBits,List.length_singleton]
    have h : 0<(1+cached.length+1)^2 := by positivity
    omega
  | cons word words ih =>
    have h:=stepBudget_le word cached
    simp only [loopBudget,vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
    nlinarith [Nat.zero_le (word.length^2),Nat.zero_le (word.length*cached.length),
      Nat.zero_le (word.length*(vectorBits words).length)]
/-- Actual whole-program instruction count, including input copy and halt. -/
theorem timeBound_le (words : List (List Bool)) (cached : List Bool) :
    timeBound words cached ≤ 200*((vectorBits words).length+cached.length+1)^2 := by
  have h:=loopBudget_le words cached
  let S:=(vectorBits words).length+cached.length+1
  have hp : 1 ≤ S := by dsimp [S];omega
  have hpow : S ≤ S^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hp (by decide : 1 ≤ 2)
  change timeBound words cached ≤ 200*S^2
  unfold timeBound
  change loopBudget cached words ≤ 100*S^2 at h
  have hS : S=(vectorBits words).length+cached.length+1 := rfl
  omega

/-- A completed actual guard certificate on arbitrary raw binary words/modulus. -/
noncomputable def sourceCheck (words : List (List Bool)) (cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial (vectorBits words) cached)
      (some (done words cached)) (200*((vectorBits words).length+cached.length+1)^2) := by
  let h:=source_run words cached
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  exact ⟨⟨m,hm.2⟩,hm.1.trans (timeBound_le words cached)⟩
/-- Genuine fixed finite-machine canonicality guard, with no canonicality premise. -/
noncomputable def machineCheck (words : List (List Bool)) (cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (vectorBits words) cached))
      (some (SemiprimeD1StackCalls.configuration (done words cached)))
      (200*((vectorBits words).length+cached.length+1)^2) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) Stack.cache Stack.output Label.start program _ _ _
    (sourceCheck words cached)
/-- Exact computed literal guard output. -/
theorem output_original (words : List (List Bool)) (cached : List Bool) :
    (done words cached).data .output=[answer cached words] := rfl
/-- The retained full vector can be consumed later by the actual dot source. -/
theorem retained_vector (words : List (List Bool)) (cached : List Bool) :
    (done words cached).data .cache=vectorBits words := rfl
/-- The original binary modulus is never replaced by a decoded or unary value. -/
theorem retained_modulus (words : List (List Bool)) (cached : List Bool) :
    (done words cached).data .modulus=cached := rfl
/-- For an original finite word family the computed guard is precisely every
original word's numerical canonicality, without a supplied solved predicate. -/
theorem finite_answer_true {n : ℕ} (input : Fin n→List Bool) (cached : List Bool) :
    answer cached (List.ofFn input)=true ↔
      ∀i,SemiprimeBitArithmetic.bitValue (input i)<SemiprimeBitArithmetic.bitValue cached := by
  rw [answer_true,List.forall_mem_ofFn_iff]

/-- Every successfully reached source prefix stops by its actual guard halt. -/
theorem prefix_fuel_le (words : List (List Bool)) (cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (vectorBits words) cached)=some out) :
    fuel ≤ 200*((vectorBits words).length+cached.length+1)^2 := by
  obtain ⟨m,hm,he⟩:=source_run words cached
  have hfm : fuel ≤ m := by
    by_contra h
    have hh : fuel=m+(1+(fuel-(m+1))) := by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done words cached)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfm.trans (hm.trans (timeBound_le words cached))
/-- ALL ten Boolean stacks and real return-label cells at every actual prefix,
including original caches, parser work, modulus copies and unread rejected tail. -/
theorem prefix_cells (words : List (List Bool)) (cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (vectorBits words) cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      3000*((vectorBits words).length+cached.length+1)^2 := by
  let I:=(vectorBits words).length+cached.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out
    (by intro k;cases k <;> simp [initial,store,I]) hr
  have hfuel:=prefix_fuel_le words cached fuel out hr
  have hframe:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframe
  have hsum : (∑k : Stack,(out.data k).length) ≤ 10*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have hp : I+1 ≤ (I+1)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ I+1) (by decide : 1 ≤ 2)
  change fuel ≤ 200*(I+1)^2 at hfuel
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 3000*(I+1)^2
  omega
/-- The identical all-prefix bound on the genuine finite machine. -/
theorem machine_prefix_cells (words : List (List Bool)) (cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits words) cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      3000*((vectorBits words).length+cached.length+1)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.cache Stack.output Label.start program fuel (initial (vectorBits words) cached)
  change (C.run program fuel (initial (vectorBits words) cached)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits words) cached))) at he
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial (vectorBits words) cached) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells words cached fuel out hrun

end RiemannGaussian.SemiprimeD1StackVectorCanonicalBounds
