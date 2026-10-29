/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentSemiprime

/-! # One packed scalar determines both semiprime factors
This is the exact arithmetic recovery specification. A physical binary
square-root/discriminant source and its bit-cost proof are still required.
No square-root value, satisfying assignment or factor is supplied to it.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PackedMomentRecovery
open SemiprimeMacroParameters SemiprimeD1PackedMomentSemiprime

/-- Recover from the exact two scalar channels; a square has one model and a
distinct semiprime has two. Natural square root reads the actual discriminant. -/
def fromMoments (N count sum : ℕ) : ℕ×ℕ :=
  if count=1 then (sum,sum) else
    let d := Nat.sqrt (sum^2-4*N)
    ((sum-d)/2,(sum+d)/2)

/-- Original-N-only arithmetic postprocessing of the single acquired scalar. -/
def recover (N value : ℕ) : ℕ×ℕ :=
  let B := 2^bitLength N
  fromMoments N (value%B) (value/B)

/-- Exact square recovery needs no prefix search or internal graph assignment. -/
theorem square (N p : ℕ) : fromMoments N 1 p=(p,p) := rfl

/-- The true discriminant is exactly the square of the ordered prime gap. -/
theorem discriminant (p q : ℕ) (hpq : p ≤ q) : (p+q)^2-4*(p*q)=(q-p)^2 := by
  have he : q-p+p=q := Nat.sub_add_cancel hpq
  have hsum : 4*(p*q)+(q-p)^2=(p+q)^2 := by nlinarith only [he]
  omega

/-- Distinct-case arithmetic works even when the two factors are equal;
the model count is used only to choose the public recovery branch. -/
theorem two_models (p q : ℕ) (hpq : p ≤ q) : fromMoments (p*q) 2 (p+q)=(p,q) := by
  unfold fromMoments
  rw [ite_eq_right (by decide : ¬(2:ℕ)=1),discriminant p q hpq,Nat.sqrt_eq']
  dsimp only
  have he : q-p+p=q := Nat.sub_add_cancel hpq
  have hl : p+q-(q-p)=2*p := by omega
  have hr : p+q+(q-p)=2*q := by omega
  rw [hl,hr,Nat.mul_div_right _ (by decide : 0<(2:ℕ)),Nat.mul_div_right _ (by decide : 0<(2:ℕ))]

/-- One exact marked contraction followed by arithmetic returns the ordered
factors. All model multiplicity and no-carry premises are discharged. -/
theorem ordered_recovery (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≤ q) :
    recover (p*q) (packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))=(p,q) := by
  have h := readout p q hp hq
  dsimp only [recover]
  rw [h.1,h.2]
  by_cases he : p=q
  · rw [ite_eq_left he,ite_eq_left he,square,he]
  · rw [ite_eq_right he,ite_eq_right he]
    exact two_models p q hpq

/-- Both original orientations give the same available factorization; an
ordering promise is not required by the public recovery function. -/
theorem recovery (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    recover (p*q) (packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))=(p,q) ∨
      recover (p*q) (packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))=(q,p) := by
  by_cases h : p ≤ q
  · exact Or.inl (ordered_recovery p q hp hq h)
  · have he := ordered_recovery q p hq hp (by omega)
    exact Or.inr (by simpa only [Nat.mul_comm q p] using he)

/-- Genuine nontrivial factorization of EVERY semiprime from the SINGLE
specified scalar. This is a semantic theorem, not its acquisition/cost proof. -/
theorem factorization (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    let f := recover (p*q) (packedValue (p*q) (Nat.mul_pos hp.pos hq.pos))
    2 ≤ f.1 ∧ 2 ≤ f.2 ∧ f.1*f.2=p*q := by
  rcases recovery p q hp hq with h|h
  · rw [h]
    exact ⟨hp.two_le,hq.two_le,rfl⟩
  · rw [h]
    exact ⟨hq.two_le,hp.two_le,Nat.mul_comm q p⟩

end RiemannGaussian.SemiprimeD1PackedMomentRecovery
