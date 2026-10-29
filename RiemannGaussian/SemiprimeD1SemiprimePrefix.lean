/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicAcquiredExecution

/-! # Fixed parent precision2 suffices for ALL semiprime prefix queries
Every original public accepted assignment corresponds to one ordinary ordered
factor pair. A semiprime has at most two such pairs, also when its two primes
coincide. Every prefix count is consequently recovered EXACTLY from ZMod4;
there is no parity-only or cancellation-based existence test.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1SemiprimePrefix
open SemiprimeCountRecovery SemiprimeCounterSearch
open SemiprimePublicFactorCount SemiprimePublicAcquiredExecution
open scoped BigOperators

/-- Every ordered nontrivial factor pair of a product of two primes has one of
the two actual prime values on its left. No distinct-prime premise is needed. -/
theorem left_factor_eq (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a*b = p*q) : a=p ∨ a=q := by
  have hpd : p ∣ a*b := by rw [hab]; exact dvd_mul_right p q
  rcases hp.dvd_mul.mp hpd with hpa | hpb
  · obtain ⟨k, hk⟩ := hpa
    have he : p*(k*b) = p*q := by rw [← Nat.mul_assoc, ← hk, hab]
    have hkb : k*b=q := Nat.eq_of_mul_eq_mul_left hp.pos he
    have hbd : b ∣ q := ⟨k, by rw [← hkb]; exact Nat.mul_comm _ _⟩
    have hbe : b=q := (hq.eq_one_or_self_of_dvd b hbd).resolve_left (by omega)
    rw [hbe] at hab
    exact Or.inl (Nat.eq_of_mul_eq_mul_right hq.pos hab)
  · obtain ⟨k, hk⟩ := hpb
    have he : p*(a*k) = p*q := by nlinarith [hab]
    have hak : a*k=q := Nat.eq_of_mul_eq_mul_left hp.pos he
    have had : a ∣ q := ⟨k, hak.symm⟩
    exact Or.inr ((hq.eq_one_or_self_of_dvd a had).resolve_left (by omega))

/-- The actual public ordinary factor-pair family has at most two members. -/
theorem ordinary_card_le_two (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hN : N=p*q) :
    Fintype.card (OrdinaryFactors N) ≤ 2 := by
  classical
  let key : OrdinaryFactors N → Bool := fun pair => decide (pair.val.1.val=p)
  have hinj : Function.Injective key := by
    intro x y hkey
    have hx := left_factor_eq p q x.val.1.val x.val.2.val hp hq x.property.1 x.property.2.1
      (x.property.2.2.trans hN)
    have hy := left_factor_eq p q y.val.1.val y.val.2.val hp hq y.property.1 y.property.2.1
      (y.property.2.2.trans hN)
    have he : x.val.1.val=y.val.1.val := by
      by_cases hxp : x.val.1.val=p
      · have hyp : y.val.1.val=p := by
          have hh : decide (y.val.1.val=p)=true := by simpa only [key,hxp,decide_true] using hkey.symm
          exact of_decide_eq_true hh
        exact hxp.trans hyp.symm
      · have hyp : y.val.1.val≠p := by
          intro hy'
          have hh : decide (x.val.1.val=p)=true := by simpa only [key,hy',decide_true] using hkey
          exact hxp (of_decide_eq_true hh)
        exact (hx.resolve_left hxp).trans (hy.resolve_left hyp).symm
    have hright : x.val.2.val=y.val.2.val := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < x.val.1.val by have := x.property.1; omega)
      rw [x.property.2.2, he, y.property.2.2]
    apply Subtype.ext
    exact Prod.ext (Fin.ext he) (Fin.ext hright)
  have hc := Fintype.card_le_of_injective key hinj
  simpa only [Fintype.card_bool] using hc

/-- Restricting the original witness space never increases its exact count. -/
theorem restricted_count_le {X I : Type*} [Fintype X] (bits : X → I → Bool) (P : X → Bool)
    (fixed : List (I×Bool)) : acceptedCount (restricted bits P fixed) ≤ acceptedCount P := by
  unfold acceptedCount
  apply Finset.sum_le_sum
  intro x _
  cases hx : P x
  · simp only [restricted,hx,Bool.false_and,Bool.false_eq_true,ite_false,Nat.le_refl]
  · simp only [restricted,hx,Bool.true_and,ite_true]
    split_ifs <;> omega

/-- EVERY actual public prefix has at most two accepted assignments for a semiprime. -/
theorem prefix_count_le_two (N p q : ℕ) (hpos : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hN : N=p*q) (fixed : List (Fin (wireCount N)×Bool)) :
    acceptedCount (restricted assignmentBit (indexedPredicate N hpos) fixed) ≤ 2 := by
  apply (restricted_count_le assignmentBit (indexedPredicate N hpos) fixed).trans
  rw [indexed_factor_count]
  exact ordinary_card_le_two N p q hp hq hN

/-- The canonical parent residue at precision2 is the EXACT natural prefix
count, not merely its parity or an existence heuristic. -/
theorem prefix_residue_exact (N p q : ℕ) (hpos : 0 < N) (hp : p.Prime) (hq : q.Prime)
    (hN : N=p*q) (fixed : List (Fin (wireCount N)×Bool)) :
    (acceptedCount (restricted assignmentBit (indexedPredicate N hpos) fixed) : ZMod 4).val =
      acceptedCount (restricted assignmentBit (indexedPredicate N hpos) fixed) := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (by have h := prefix_count_le_two N p q hpos hp hq hN fixed; omega)

end RiemannGaussian.SemiprimeD1SemiprimePrefix
