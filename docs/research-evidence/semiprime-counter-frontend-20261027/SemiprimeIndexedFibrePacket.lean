/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeIndexedNodeCertificate

/-! # The indexed scan summands are the existing native fibre packet -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeIndexedFibrePacket
open scoped BigOperators
open Polynomial SemiprimeCounterCompose SemiprimeLayoutCertificates
open SemiprimeIndexedNodeCertificate
noncomputable section
variable {A E : Type} [Fintype A] [DecidableEq A] [Fintype E]

/-- A finite sum does not depend on the choice of its exhaustive finite instance. -/
theorem sum_instance_irrel {α β : Type*} [AddCommMonoid β]
    (F G : Fintype α) (f g : α → β) (h : ∀ a, f a=g a) :
    Finset.sum (@Finset.univ α F) f = Finset.sum (@Finset.univ α G) g := by
  cases Subsingleton.elim F G
  apply Finset.sum_congr rfl
  intro a _
  exact h a

omit [Fintype A] [DecidableEq A] in
/-- Explicit summary types avoid any classical reindexing of the finite packet. -/
theorem packet_eq_sum {arity : E → ℕ} {rows : (e : E) → Fin (arity e) → A → ℚ}
    (d : Data arity rows) (T : (e : E) → (Fin (arity e) → Bool) → ℚ)
    (correction : (e : E) → Fin (arity e) → Polynomial ℚ) (S : Finset A) :
    fibrePacket arity T rows (certificate d) correction S =
      ∑ y : (g : Fin d.r) → Summary (Fin (d.h g)) (Fin (d.m g)) (d.W g),
        term d T correction S y := by
  unfold fibrePacket term
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro g _
  apply sum_instance_irrel
  intro a
  by_cases hc : (certificate d).measurement g a = y g ∧ localForced arity rows (certificate d) S g a
  · simp only [hc]
    rfl
  · simp only [hc, ↓reduceIte]
end
end RiemannGaussian.SemiprimeIndexedFibrePacket
