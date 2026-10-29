/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBytecode

/-! # Actual Boolean-stack prefix bounds
These bounds follow from executed instructions, not from arithmetic reports.
For a fixed finite program the stack-cardinality factor is a fixed constant.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackBytecodeBounds
open SemiprimeD1StackBytecode

/-- A literal instruction allocates at most one bit on each physical stack. -/
theorem execute_length {K L : Type} [DecidableEq K]
    (instruction : Instruction K L) (state : State K L) (k : K) :
    ((execute instruction state).store k).length ≤ (state.store k).length+1 := by
  cases instruction with
  | push stack bit next =>
    simp only [execute]
    by_cases hk : k=stack
    · subst k
      simp only [Function.update_self,List.length_cons]
      exact le_rfl
    · simp only [Function.update_of_ne hk]
      omega
  | pop stack empty low high =>
    simp only [execute]
    by_cases hk : k=stack
    · subst k
      simp only [Function.update_self,List.length_tail]
      omega
    · simp only [Function.update_of_ne hk]
      omega
  | peek stack empty low high => simp only [execute];omega
  | jump next => simp only [execute];omega
  | halt => simp only [execute];omega

/-- An actual successful source step has the same physical allocation bound. -/
theorem step_length {K L : Type} [DecidableEq K]
    (code : L→Instruction K L) (a b : State K L) (h : step code a=some b) (k : K) :
    (b.store k).length ≤ (a.store k).length+1 := by
  cases a with
  | mk pc flag store =>
    cases pc with
    | none => cases h
    | some label =>
      have he : execute (code label) (⟨some label,flag,store⟩:State K L)=b := Option.some.inj h
      rw [←he]
      exact execute_length _ _ _

/-- Every successful executed prefix pays for all of its possible stack growth. -/
theorem run_length {K L : Type} [DecidableEq K]
    (code : L→Instruction K L) (fuel : ℕ) (a b : State K L)
    (h : run code fuel a=some b) (k : K) :
    (b.store k).length ≤ (a.store k).length+fuel := by
  induction fuel generalizing b with
  | zero =>
    have he : a=b := Option.some.inj h
    subst b
    exact le_rfl
  | succ fuel ih =>
    change ((fun q=>q.bind (step code))^[fuel+1] (some a))=some b at h
    rw [Function.iterate_succ_apply'] at h
    cases hr : run code fuel a with
    | none =>
      change (run code fuel a).bind (step code)=some b at h
      rw [hr] at h
      cases h
    | some c =>
      change (run code fuel a).bind (step code)=some b at h
      rw [hr] at h
      have hs : step code c=some b := h
      have hc := ih c hr
      have hh := step_length code c b hs k
      omega

/-- Literal occupied cells on all Boolean stacks. -/
def cells {K L : Type} [Fintype K] (state : State K L) : ℕ :=
  ∑k,(state.store k).length

/-- Fixed finite stack count gives a whole-configuration prefix memory bound. -/
theorem run_cells {K L : Type} [DecidableEq K] [Fintype K]
    (code : L→Instruction K L) (fuel : ℕ) (a b : State K L)
    (h : run code fuel a=some b) :
    cells b ≤ cells a+Fintype.card K*fuel := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun k _=>run_length code fuel a b h k)
  simpa only [cells,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    smul_eq_mul] using hh

/-- Halt is genuine: a positive further execution cannot return a state. -/
theorem run_after_halt {K L : Type} [DecidableEq K]
    (code : L→Instruction K L) (state : State K L) (h : state.pc=none) (n : ℕ) :
    run code (n+1) state=none := by
  have hs : step code state=none := by simp only [step,h,Option.map_none]
  unfold run
  rw [Function.iterate_succ_apply,Option.bind_some,hs]
  have hz (n : ℕ) : (fun q : Option (State K L)=>q.bind (step code))^[n] none=none := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih];rfl
  exact hz n

/-- A successful prefix cannot pass the proved actual halt transition. -/
theorem fuel_le_halt {K L : Type} [DecidableEq K]
    (code : L→Instruction K L) (a finish b : State K L) (time fuel : ℕ)
    (ht : run code time a=some finish) (hf : finish.pc=none)
    (hr : run code fuel a=some b) : fuel ≤ time := by
  by_contra hn
  have hlt : time<fuel := by omega
  obtain ⟨n,he⟩ := Nat.exists_eq_add_of_lt hlt
  have hs := run_after_halt code finish hf n
  have he' : fuel=(n+1)+time := by omega
  have heq : run code fuel a=none := by
    rw [he']
    unfold run at ht hs ⊢
    rw [Function.iterate_add_apply,ht]
    exact hs
  rw [heq] at hr
  cases hr

/-- Source memory estimates apply to the actual compiled machine prefix. -/
theorem machine_cells {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (input output : K) (main : L) (code : L→Instruction K L) (fuel : ℕ)
    (a : State K L) (cfg : (machine input output main code).Cfg)
    (h : (fun c=>c.bind (machine input output main code).step)^[fuel]
      (some (configuration a))=some cfg) :
    (∑k : K,(cfg.stk k).length) ≤ cells a+Fintype.card K*fuel := by
  have hh := run_correct input output main code fuel a
  rw [h] at hh
  cases hr : run code fuel a with
  | none => rw [hr] at hh;cases hh
  | some b =>
    rw [hr] at hh
    have hc : configuration b=cfg := Option.some.inj hh
    subst cfg
    exact run_cells code fuel a b hr

end RiemannGaussian.SemiprimeD1StackBytecodeBounds
