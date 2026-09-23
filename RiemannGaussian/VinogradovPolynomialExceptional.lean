/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovTypeMaximum
import RiemannGaussian.VinogradovMixedExceptional

/-!
# The unrestricted type count reduces to two distinct blocks

Select an attained maximizing polynomial system of the same type, then
absorb repeated tuples on both sides using its actual doubled-block mixed
count and diagonal reserve. This gives an unconditional factor-two
reduction for every original type system and every fixed tail, at the
explicit alphabet threshold. The retained system may differ from the
original one; the tail, degree, type parameter and endpoints do not.
-/

namespace RiemannGaussian.VinogradovPolynomialExceptional
noncomputable section
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovMixedMoments VinogradovTypeMaximum VinogradovMixedExceptional

/-- An attained type system dominates the original mixed count and loses
at most half its count when both polynomial blocks are required distinct. -/
theorem exists_distinct_reduction {κ : Type*} [Fintype κ]
    {m d T e P s : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      mixedMoment m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u ≤
        mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u ∧
      mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u ≤
        2 * (distinctCount m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u : ℝ) := by
  obtain ⟨e', G, hG, hdom, hdouble⟩ := exists_doubling_dominant hF P s u
  exact ⟨e', G, hG, hdom, mixedMoment_le_twice_distinct hm s _ u hdouble
    (by simpa only [Fintype.card_fin] using hP)⟩

/-- The complete original integer count is bounded by twice an actual
distinct-block count of the same type, with no supplied moment estimate. -/
theorem exists_count_reduction {κ : Type*} [Fintype κ]
    {m d T e P s : ℕ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      typeCount d P s F u ≤
        2 * distinctCount m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u := by
  obtain ⟨e', G, hG, hdom, hgood⟩ := exists_distinct_reduction hF hm hP u
  refine ⟨e', G, hG, ?_⟩
  have h := hdom.trans hgood
  rw [← typeCount_eq_mixedMoment] at h
  exact_mod_cast h

end
end RiemannGaussian.VinogradovPolynomialExceptional
