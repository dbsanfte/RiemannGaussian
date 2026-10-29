/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Exact reflected-grid cancellation in tapered Hermite recovery

Reflection pairs points of valuation i with their higher-valuation differences.
Lower levels cancel pointwise. This finite algebraic lemma is independent of
the original residue-grid count, which is supplied at the later D.10 join.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1InvolutionRegroup
open scoped BigOperators

/-- Reindexing by a genuine finite reflected-grid involution preserves sums. -/
theorem sum_reflect {A : Type*} (S : Finset A) (reflect : A→A)
    (hmem : ∀ x∈S,reflect x∈S) (hinv : ∀ x∈S,reflect (reflect x)=x)
    (f : A→ℤ) : (∑ x∈S,f (reflect x))=∑ x∈S,f x := by
  classical
  apply Finset.sum_bij (fun x _ => reflect x)
  · exact hmem
  · intro x hx y hy he
    exact (hinv x hx).symm.trans ((congrArg reflect he).trans (hinv y hy))
  · intro y hy
    exact ⟨reflect y,hmem y hy,hinv y hy⟩
  · intros;rfl

/-- The exact original raw valuation sum reduces to its high-level differences.
Only the actual valuation laws and reflection involution are required; no loss
bound or distribution of valuation levels is assumed. -/
theorem regroup {A : Type*} (S : Finset A) (reflect : A→A) (v : A→ℕ)
    (q : ℕ→ℤ) (i : ℕ)
    (hmem : ∀ x∈S,reflect x∈S) (hinv : ∀ x∈S,reflect (reflect x)=x)
    (hlow : ∀ x∈S,v x < i→v (reflect x)=v x)
    (hhigh : ∀ x∈S,i < v x→v (reflect x)=i) :
    (∑ x∈S,q (v x)*((v x:ℤ)-(v (reflect x):ℤ)))=
      ∑ x∈S,if i < v x then (q (v x)-q i)*((v x:ℤ)-(i:ℤ)) else 0 := by
  classical
  let positive : A→ℤ := fun x => if i < v x then q (v x)*((v x:ℤ)-(i:ℤ)) else 0
  let constant : A→ℤ := fun x => if i < v x then q i*((v x:ℤ)-(i:ℤ)) else 0
  have hlocal (x : A) (hx : x∈S) :
      q (v x)*((v x:ℤ)-(v (reflect x):ℤ))=positive x-constant (reflect x) := by
    rcases lt_trichotomy (v x) i with hlo|heq|hhi
    · have he := hlow x hx hlo
      simp only [positive,constant,he,show ¬i < v x by omega,ite_false,sub_self,mul_zero]
    · have hlower : i≤v (reflect x) := by
        by_contra hbad
        have he := hlow (reflect x) (hmem x hx) (by omega)
        rw [hinv x hx,heq] at he
        omega
      by_cases hb : i < v (reflect x)
      · simp only [positive,constant,heq,lt_self_iff_false,ite_false,hb,ite_true]
        ring
      · have he : v (reflect x)=i := by omega
        simp [positive,constant,heq,he]
    · have he := hhigh x hx hhi
      simp only [positive,constant,he,hhi,ite_true,lt_self_iff_false,ite_false,sub_zero]
  calc
    _ = ∑ x∈S,(positive x-constant (reflect x)) := Finset.sum_congr rfl hlocal
    _ = (∑ x∈S,positive x)-(∑ x∈S,constant (reflect x)) := by rw [Finset.sum_sub_distrib]
    _ = (∑ x∈S,positive x)-(∑ x∈S,constant x) := by rw [sum_reflect S reflect hmem hinv constant]
    _ = ∑ x∈S,(positive x-constant x) := by rw [Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [positive,constant]
      split_ifs <;> ring

end RiemannGaussian.SemiprimeD1InvolutionRegroup
