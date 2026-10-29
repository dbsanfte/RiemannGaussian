/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! # Exact coordinate fibres of the complete source-word alphabet
The bijections count actual finite functions, including singleton alphabets.
A coordinate argument enforces a nonempty coordinate domain.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHeadFibres
/-- Fixing one actual colour leaves exactly the other coordinates free. -/
def fibreEquiv (r Q : ℕ) (q : Fin Q) (c : Fin r) :
    {w : Fin Q → Fin r // w q = c} ≃ ({j : Fin Q // j ≠ q} → Fin r) where
  toFun w j := w.val j
  invFun f := ⟨fun j => if h : j = q then c else f ⟨j,h⟩, by simp⟩
  left_inv w := by
    apply Subtype.ext
    funext j
    by_cases h : j=q
    · subst j; simp [w.property]
    · simp [h]
  right_inv f := by funext j; simp [j.property]

theorem fibre_card (r Q : ℕ) (q : Fin Q) (c : Fin r) :
    Fintype.card {w : Fin Q → Fin r // w q = c} = r^(Q-1) := by
  rw [Fintype.card_congr (fibreEquiv r Q q c), Fintype.card_fun]
  have h : Fintype.card {j : Fin Q // j ≠ q} = Q-1 := by
    simp [Fintype.card_subtype_compl]
  rw [h, Fintype.card_fin]

/-- For two independent words the second word has one fixed colour. -/
def collisionEquiv (r Q : ℕ) (q : Fin Q) :
    {p : (Fin Q → Fin r) × (Fin Q → Fin r) // p.1 q = p.2 q} ≃
      ((Fin Q → Fin r) × ({j : Fin Q // j ≠ q} → Fin r)) where
  toFun p := ⟨p.val.1, fun j => p.val.2 j⟩
  invFun p := ⟨⟨p.1,fun j => if h : j=q then p.1 q else p.2 ⟨j,h⟩⟩,by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j
      by_cases h : j=q
      · subst j; simp [p.property]
      · simp [h]
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext j; simp [j.property]

theorem collision_card (r Q : ℕ) (q : Fin Q) :
    Fintype.card {p : (Fin Q → Fin r) × (Fin Q → Fin r) // p.1 q = p.2 q} =
      r^(2*Q-1) := by
  rw [Fintype.card_congr (collisionEquiv r Q q), Fintype.card_prod,
    Fintype.card_fun,Fintype.card_fun,Fintype.card_fin]
  have h : Fintype.card {j : Fin Q // j ≠ q} = Q-1 := by
    simp [Fintype.card_subtype_compl]
  rw [h, Fintype.card_fin, ← pow_add]
  congr 1
  have := q.isLt
  omega
end RiemannGaussian.SemiprimeSourceHeadFibres
