/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Exact separation by shared measurements

This proves the arbitrary-group fibre identity used by the streamed counter.
Representatives need only match measurements; they need not obey forced bits.
Empty fibres contribute zero automatically. The hypotheses concern actual
pointwise measurement invariance and representative validity, not a precomputed
contraction or a promised value of the sums.
-/

namespace RiemannGaussian.SemiprimeSharedSummary
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {V Y : G → Type*} [∀ g, Fintype (V g)]
variable {R : Type*} [CommSemiring R]

theorem fibre_factorization
    (measurement : (g : G) → V g → Y g)
    (forced : (g : G) → V g → Prop)
    (value : G → ((g : G) → V g) → R)
    (representative : ((g : G) → Y g) → (g : G) → V g)
    (hrep : ∀ y g, (∃ a, measurement g a = y g) →
      measurement g (representative y g) = y g)
    (hinvariant : ∀ g x z, x g = z g →
      (∀ h, h ≠ g → measurement h (x h) = measurement h (z h)) → value g x = value g z)
    (y : (g : G) → Y g) :
    (∑ x : (g : G) → V g,
      if ∀ g, measurement g (x g) = y g ∧ forced g (x g) then ∏ g, value g x else 0) =
      ∏ g, ∑ a : V g, if measurement g a = y g ∧ forced g a then
        value g (Function.update (representative y) g a) else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hvalid : ∀ g, measurement g (x g) = y g ∧ forced g (x g)
  · rw [ite_eq_left hvalid]
    apply Finset.prod_congr rfl
    intro g hg
    rw [ite_eq_left (hvalid g)]
    apply hinvariant g x (Function.update (representative y) g (x g))
    · simp
    · intro h hne
      rw [Function.update_of_ne hne]
      exact (hvalid h).1.trans (hrep y h ⟨x h, (hvalid h).1⟩).symm
  · rw [ite_eq_right hvalid]
    obtain ⟨g, hg⟩ := not_forall.mp hvalid
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ g) (ite_eq_right hg)

variable [∀ g, Fintype (Y g)]

/-- Full contraction with local forced bits, separated by all measurements.
This includes empty groups, empty fibres, and representatives violating forced
bits: forced conditions apply only to the actual local summation variable. -/
theorem shared_summary_contraction
    (measurement : (g : G) → V g → Y g)
    (forced : (g : G) → V g → Prop)
    (value : G → ((g : G) → V g) → R)
    (representative : ((g : G) → Y g) → (g : G) → V g)
    (hrep : ∀ y g, (∃ a, measurement g a = y g) →
      measurement g (representative y g) = y g)
    (hinvariant : ∀ g x z, x g = z g →
      (∀ h, h ≠ g → measurement h (x h) = measurement h (z h)) → value g x = value g z) :
    (∑ x : (g : G) → V g, if ∀ g, forced g (x g) then ∏ g, value g x else 0) =
      ∑ y : (g : G) → Y g,
        ∏ g, ∑ a : V g, if measurement g a = y g ∧ forced g a then
          value g (Function.update (representative y) g a) else 0 := by
  classical
  simp_rw [← fibre_factorization measurement forced value representative hrep hinvariant]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hsplit (y : (g : G) → Y g) :
      (∀ g, measurement g (x g) = y g ∧ forced g (x g)) ↔
        (fun g => measurement g (x g)) = y ∧ ∀ g, forced g (x g) := by
    constructor
    · intro h
      exact ⟨funext (fun g => (h g).1), fun g => (h g).2⟩
    · rintro ⟨h, hf⟩ g
      exact ⟨congrFun h g, hf g⟩
  simp_rw [hsplit]
  by_cases hf : ∀ g, forced g (x g) <;> simp [hf]

#print axioms fibre_factorization
#print axioms shared_summary_contraction
end RiemannGaussian.SemiprimeSharedSummary
