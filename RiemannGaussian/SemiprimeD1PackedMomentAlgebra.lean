/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Exact first-moment cancellation in a scalar square modulus
These are finite algebra identities. They do not supply a contraction value,
its coefficient acquisition or a runtime bound. Higher terms are discarded
only in the FINAL scalar ring, never in intermediate integer lifts.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PackedMomentAlgebra
open scoped BigOperators

/-- A square-zero marker retains the constant and the complete first moment. -/
theorem marked_product {E R : Type*} [CommSemiring R] (s : Finset E)
    (b : R) (hb : b*b=0) (w : E→R) :
    (∏ e ∈ s, (1+b*w e))=1+b*(∑ e ∈ s, w e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.prod_insert he,Finset.sum_insert he,ih]
    calc
      _ = 1+b*(w e+∑ j ∈ s, w j)+(b*b)*(w e*(∑ j ∈ s, w j)) := by ring
      _ = _ := by rw [hb]; simp

/-- Literal local checker zeros still reject an entire assignment. -/
theorem checked_product {E R : Type*} [Fintype E] [CommSemiring R]
    (test : E→Bool) (b : R) (hb : b*b=0) (w : E→R) :
    (∏e,if test e then 1+b*w e else 0)=
      if ∀e,test e=true then 1+b*(∑e,w e) else 0 := by
  classical
  by_cases h : ∀e,test e=true
  · rw [ite_eq_left h]
    simpa only [h,ite_true] using marked_product Finset.univ b hb w
  · rw [ite_eq_right h]
    obtain ⟨e,he⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right he)

/-- The public base itself is square-zero in the FINAL ring modulo its square. -/
theorem base_square_zero (B : ℕ) : (B : ZMod (B^2))*(B : ZMod (B^2))=0 := by
  rw [←Nat.cast_mul,←pow_two,ZMod.natCast_self]

/-- Count and first moment cannot carry into each other when each is below B. -/
theorem packed_lt (B c S : ℕ) (hc : c<B) (hS : S<B) : c+B*S<B^2 := by
  have hB : 0<B := by omega
  have hs : S+1≤B := by omega
  have hm := Nat.mul_le_mul_left B hs
  nlinarith only [hc,hm]

/-- Low and high base-B digits recover the exact count and first moment. -/
theorem unpack (B c S : ℕ) (hB : 0<B) (hc : c<B) :
    (c+B*S)%B=c ∧ (c+B*S)/B=S := by
  constructor
  · rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hc]
  · rw [Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt hc,Nat.zero_add]

/-- The canonical scalar residue has the same two exact digits; no oracle
for the count or sum is introduced by this readout identity. -/
theorem residue_unpack (B c S : ℕ) (hc : c<B) (hS : S<B) :
    ((c+B*S : ℕ) : ZMod (B^2)).val=c+B*S ∧
      ((c+B*S : ℕ) : ZMod (B^2)).val%B=c ∧
      ((c+B*S : ℕ) : ZMod (B^2)).val/B=S := by
  have hv : ((c+B*S : ℕ) : ZMod (B^2)).val=c+B*S := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (packed_lt B c S hc hS)]
  have h := unpack B c S (by omega) hc
  exact ⟨hv,by rw [hv];exact h.1,by rw [hv];exact h.2⟩

end RiemannGaussian.SemiprimeD1PackedMomentAlgebra
