/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialConditionedDescent
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# An attained maximum over polynomial systems of fixed type

The binary exponent and all lower coefficients can vary without bound.
The literal mixed counts are nevertheless bounded natural numbers, so
their maximum is attained by an actual system. Doubling this maximizing
polynomial block stays in the family while the original tail is fixed.
No mixed-moment dilation invariance is assumed.
-/

namespace RiemannGaussian.VinogradovTypeMaximum
noncomputable section
open scoped BigOperators Classical
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovMixedMoments VinogradovShiftedMoment

/-- Doubling all active polynomials changes only the common binary exponent. -/
theorem hasType_double {m d T e : ℕ} {F : Fin m → ℤ[X]}
    (hF : HasType F d T e) : HasType (fun j => C 2 * F j) d T (e + 1) := by
  intro j
  refine ⟨?_, ?_⟩
  · simpa only [natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0)] using (hF j).1
  · rw [leadingCoeff_mul, leadingCoeff_C, (hF j).2, pow_succ]
    ring

/-- The literal complete mixed solution count, with the original tail unchanged. -/
def typeCount {κ : Type*} [Fintype κ] {m : ℕ} (d P s : ℕ)
    (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) : ℕ :=
  differenceCount
    (configurationFrequency m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u) 0

/-- The count is bounded uniformly in every polynomial coefficient and exponent. -/
theorem typeCount_le {κ : Type*} [Fintype κ] {m : ℕ} (d P s : ℕ)
    (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    typeCount d P s F u ≤ (P ^ m * Fintype.card κ ^ s) ^ 2 := by
  unfold typeCount differenceCount
  calc
    _ ≤ Fintype.card (((Fin m → Fin P) × (Fin s → κ)) ×
        ((Fin m → Fin P) × (Fin s → κ))) := Finset.card_le_univ _
    _ = _ := by simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_two]

/-- The type count is the actual mixed torus integral. -/
theorem typeCount_eq_mixedMoment {κ : Type*} [Fintype κ] {m : ℕ} (d P s : ℕ)
    (F : Fin m → ℤ[X]) (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    (typeCount d P s F u : ℝ) =
      mixedMoment m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u :=
  (mixedMoment_eq_count _ _ _ _).symm

/-- The supremum over this infinite family is attained, with no coefficient cutoff. -/
theorem exists_maximizer {κ : Type*} [Fintype κ] {m d T e : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (P s : ℕ)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      ∀ (e'' : ℕ) (H : Fin m → ℤ[X]), HasType H d T e'' →
        typeCount d P s H u ≤ typeCount d P s G u := by
  let S : Set ℕ := {a | ∃ (e' : ℕ) (G : Fin m → ℤ[X]),
    HasType G d T e' ∧ a = typeCount d P s G u}
  have hne : S.Nonempty := ⟨_, e, F, hF, rfl⟩
  have hfin : S.Finite := (Set.finite_Iic ((P ^ m * Fintype.card κ ^ s) ^ 2)).subset (by
    rintro a ⟨e', G, hG, rfl⟩
    exact typeCount_le d P s G u)
  obtain ⟨e', G, hG, heq⟩ := hne.csSup_mem hfin
  refine ⟨e', G, hG, ?_⟩
  intro e'' H hH
  rw [← heq]
  exact le_csSup hfin.bddAbove ⟨e'', H, hH, rfl⟩

/-- Select one actual system which dominates the given count and its own
doubled-block count while retaining the same fixed tail. -/
theorem exists_doubling_dominant {κ : Type*} [Fintype κ] {m d T e : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e) (P s : ℕ)
    (u : κ → (Fin d ⊕ Fin m) → ℤ) :
    ∃ (e' : ℕ) (G : Fin m → ℤ[X]), HasType G d T e' ∧
      mixedMoment m s (fun x : Fin P => fullFrequency d F (x.val + 1)) u ≤
        mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u ∧
      mixedMoment m s
        (fun x : Fin P => fun j => 2 * fullFrequency d G (x.val + 1) j) u ≤
        mixedMoment m s (fun x : Fin P => fullFrequency d G (x.val + 1)) u := by
  obtain ⟨e', G, hG, hmax⟩ := exists_maximizer hF P s u
  refine ⟨e', G, hG, ?_, ?_⟩
  · simpa only [← typeCount_eq_mixedMoment, Nat.cast_le] using hmax e F hF
  · have he : (fun x : Fin P => fullFrequency d (fun j => C 2 * G j) (x.val + 1)) =
        fun x : Fin P => fun j => 2 * fullFrequency d G (x.val + 1) j := by
      funext x j
      cases j <;> simp [fullFrequency]
    have h := hmax (e' + 1) (fun j => C 2 * G j) (hasType_double hG)
    have hr : (typeCount d P s (fun j => C 2 * G j) u : ℝ) ≤
        typeCount d P s G u := by exact_mod_cast h
    simpa only [typeCount_eq_mixedMoment, he] using hr

end
end RiemannGaussian.VinogradovTypeMaximum
