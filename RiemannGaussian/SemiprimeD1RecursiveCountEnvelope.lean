/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecursiveCallInventory

/-! # Exact finite-tree induction for summable original mode exponents
This internal numerical lemma is instantiated by the actual acquired branching
bounds. It does not supply a branching oracle to the executed controller.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1RecursiveCountEnvelope
open scoped BigOperators
open SemiprimeD1RecursiveCallTree SemiprimeD1RecursiveCallState

/-- A finite list sum is bounded by its actual length times a common bound. -/
theorem sum_map_le {α : Type*} (xs : List α) (f : α → ℝ) (B : ℝ)
    (h : ∀x∈xs,f x ≤ B) : (xs.map f).sum ≤ (xs.length:ℝ)*B := by
  have hh := List.sum_le_length_nsmul (xs.map f) B (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact h x hx)
  simpa only [List.length_map,nsmul_eq_mul] using hh

/-- The exact dyadic exponent remaining along a finite descendant path. -/
noncomputable def tail (depth : ℕ) : ℕ → ℝ
  | 0 => 0
  | fuel+1 => (1/4:ℝ)^depth+tail (depth+1) fuel

/-- Every finite path contribution is nonnegative. -/
theorem tail_nonneg (depth fuel : ℕ) : 0 ≤ tail depth fuel := by
  induction fuel generalizing depth with
  | zero => rfl
  | succ fuel ih => exact add_nonneg (by positivity) (ih _)

/-- A fixed geometric constant controls every actual remaining depth. -/
theorem tail_le (depth fuel : ℕ) : tail depth fuel ≤ 2*(1/4:ℝ)^depth := by
  induction fuel generalizing depth with
  | zero => dsimp only [tail];positivity
  | succ fuel ih =>
    have h := ih (depth+1)
    dsimp only [tail]
    rw [pow_succ] at h
    have hp : 0 ≤ (1/4:ℝ)^depth := by positivity
    linarith

/-- Exact call-count induction using actual child-list membership. The final
original-input theorem discharges this internal bound with the acquired menus. -/
theorem count_le (s : ℕ) (root : Call) (G A : ℝ) (hG : 1 ≤ G) (hA : 0 ≤ A)
    (hbranch : ∀ call, Reach s root call →
      ((children s call).length:ℝ) ≤ G*Real.exp (A*(1/4:ℝ)^call.depth))
    (fuel : ℕ) (call : Call) (hr : Reach s root call) :
    (count s fuel call:ℝ) ≤ ((fuel:ℝ)+1)*G^fuel*Real.exp (A*tail call.depth fuel) := by
  induction fuel generalizing call with
  | zero => simp only [count,tail,Nat.cast_one,Nat.cast_zero,zero_add,pow_zero,one_mul,mul_zero,Real.exp_zero,le_refl]
  | succ fuel ih =>
    let B := ((fuel:ℝ)+1)*G^fuel*Real.exp (A*tail (call.depth+1) fuel)
    have hB : 0 ≤ B := by dsimp only [B];positivity
    have hs : (((children s call).map (count s fuel)).sum:ℝ) ≤
        ((children s call).length:ℝ)*B := by
      rw [Nat.cast_list_sum]
      simp only [List.map_map,Function.comp_def]
      apply sum_map_le
      intro next hm
      have hh := ih next (Reach.step hr hm)
      rw [mem_children_depth s call next hm] at hh
      exact hh
    have hs' := hs.trans (mul_le_mul_of_nonneg_right (hbranch call hr) hB)
    let V := G^(fuel+1)*Real.exp (A*tail call.depth (fuel+1))
    have hV : 1 ≤ V := by
      have hp : 1 ≤ G^(fuel+1) := one_le_pow₀ hG
      have he := Real.one_le_exp (mul_nonneg hA (tail_nonneg call.depth (fuel+1)))
      exact one_le_mul_of_one_le_of_one_le hp he
    have heq : (G*Real.exp (A*(1/4:ℝ)^call.depth))*B = ((fuel:ℝ)+1)*V := by
      dsimp only [B,V,tail]
      rw [pow_succ,mul_add,Real.exp_add]
      ring
    rw [heq] at hs'
    rw [count,Nat.cast_add,Nat.cast_one]
    have hc : ((fuel+1:ℕ):ℝ)+1 = (fuel:ℝ)+2 := by push_cast;ring
    rw [hc]
    calc
      _ ≤ 1+((fuel:ℝ)+1)*V := add_le_add (le_refl (1:ℝ)) hs'
      _ ≤ ((fuel:ℝ)+2)*V := by nlinarith
      _ = _ := by dsimp only [V];ring

end RiemannGaussian.SemiprimeD1RecursiveCountEnvelope
