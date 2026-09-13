/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPrimePowerRigidity

/-!
# Signed moment reconstruction with the colour partition retained

The complete first-k signed power sums of a tuple with distinct entries
determine its entries and their signs. The fibre consists exactly of the
permutations within each sign class, with cardinality r₊! * r₋!.
The proof uses crossed multisets and Newton identities; it applies in every
domain where the first k natural coefficients are nonzero.
-/

namespace RiemannGaussian.VinogradovSignedRigidity
noncomputable section
open scoped BigOperators

/-- No entry of a nonsingular tuple can cancel with an opposite colour
from the same tuple in the crossed multiset identity. -/
theorem colour_permutation_of_crossed_multiset {R : Type*} {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (hv : Function.Injective v)
    (he : Finset.univ.val.map (fun i => if colour i then v i else u i) =
      Finset.univ.val.map (fun i => if colour i then u i else v i)) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, u j = v (σ j) ∧ colour j = colour (σ j) := by
  classical
  have hex (i) : ∃ j, u j = v i ∧ colour j = colour i := by
    cases hci : colour i with
    | false =>
      have hm : v i ∈ Finset.univ.val.map (fun j => if colour j then u j else v j) :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, by simp [hci]⟩
      rw [← he] at hm
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
      cases hcj : colour j with
      | false => exact ⟨j, by simpa [hcj] using hj, by simp [hcj]⟩
      | true =>
        have hji : j = i := hv (by simpa [hcj] using hj)
        subst j
        simp_all
    | true =>
      have hm : v i ∈ Finset.univ.val.map (fun j => if colour j then v j else u j) :=
        Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, by simp [hci]⟩
      rw [he] at hm
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
      cases hcj : colour j with
      | false =>
        have hji : j = i := hv (by simpa [hcj] using hj)
        subst j
        simp_all
      | true => exact ⟨j, by simpa [hcj] using hj, by simp [hcj]⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← (hf i).1, ← (hf j).1, hij]
  let e : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e.symm, ?_⟩
  intro j
  have hj := hf (e.symm j)
  have he : f (e.symm j) = j := e.apply_symm_apply j
  simpa only [he] using hj

/-- The complete signed equations are exactly the ordinary equations
for crossed tuples, preserving the original colour of every entry. -/
theorem crossed_power_sums {R : Type*} [CommRing R] {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (n : ℕ)
    (h : (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) =
      ∑ i, (if colour i then (1 : R) else -1) * u i ^ n) :
    (∑ i, (if colour i then v i else u i) ^ n) =
      ∑ i, (if colour i then u i else v i) ^ n := by
  apply sub_eq_zero.mp
  calc
    _ = (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) -
        ∑ i, (if colour i then (1 : R) else -1) * u i ^ n := by
      simp only [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      cases colour i <;> simp
      ring
    _ = 0 := by rw [h, sub_self]

/-- The full signed moment vector determines a nonsingular tuple up to
a permutation that respects the original positive and negative colours. -/
theorem signed_power_permutation {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (colour : Fin k → Bool) (v u : Fin k → R) (hv : Function.Injective v)
    (hchar : ∀ n, 1 ≤ n → n ≤ k → (n : R) ≠ 0)
    (h : ∀ n, 1 ≤ n → n ≤ k →
      (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) =
      ∑ i, (if colour i then (1 : R) else -1) * u i ^ n) :
    ∃ σ : Equiv.Perm (Fin k), ∀ j, u j = v (σ j) ∧ colour j = colour (σ j) := by
  apply colour_permutation_of_crossed_multiset colour v u hv
  apply VinogradovPowerSumRigidity.multiset_eq_of_power_sums_of_natCast_ne_zero
      _ _ hchar
  intro n hn hnk
  exact crossed_power_sums colour v u n (h n hn hnk)

/-- Permutations that retain a fixed partition of the index set. -/
abbrev PreservingPerm {ι : Type*} (P : ι → Prop) :=
  {σ : Equiv.Perm ι // ∀ i, P (σ i) ↔ P i}

/-- A partition-preserving permutation consists of independent permutations
of its two parts, with no freedom to exchange their colours. -/
def preservingPermEquiv {ι : Type*} (P : ι → Prop) [DecidablePred P] :
    PreservingPerm P ≃ (Equiv.Perm {i // P i} × Equiv.Perm {i // ¬ P i}) where
  toFun σ := (σ.val.subtypePerm σ.property,
    σ.val.subtypePerm (fun i => not_congr (σ.property i)))
  invFun pair := ⟨pair.1.subtypeCongr pair.2, by
    intro i
    by_cases hi : P i
    · simp only [hi, iff_true]
      rw [Equiv.Perm.subtypeCongr.left_apply _ _ hi]
      exact (pair.1 ⟨i, hi⟩).property
    · simp only [hi, iff_false]
      rw [Equiv.Perm.subtypeCongr.right_apply _ _ hi]
      exact (pair.2 ⟨i, hi⟩).property⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : P i
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hi]
      rfl
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hi]
      rfl
  right_inv pair := by
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.left_apply_subtype]
    · apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [Equiv.Perm.subtypePerm_apply, Equiv.Perm.subtypeCongr.right_apply_subtype]

/-- The exact permutation allowance for a retained two-colour partition. -/
theorem card_preservingPerm {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    Nat.card (PreservingPerm P) =
      (Fintype.card {i // P i}).factorial * (Fintype.card {i // ¬ P i}).factorial := by
  classical
  rw [Nat.card_congr (preservingPermEquiv P), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm]

/-- A complete signed moment fibre over any domain; the original tuple
provides an actual realization of the target. -/
abbrev SignedFibre {R : Type*} [CommRing R] {k : ℕ}
    (colour : Fin k → Bool) (v : Fin k → R) :=
  {u : Fin k → R // ∀ n, 1 ≤ n → n ≤ k →
    (∑ i, (if colour i then (1 : R) else -1) * v i ^ n) =
      ∑ i, (if colour i then (1 : R) else -1) * u i ^ n}

/-- Every permutation respecting the sign partition preserves every
signed moment, with all original variable colours retained. -/
def signedFibreOfPerm {R : Type*} [CommRing R] {k : ℕ}
    (colour : Fin k → Bool) (v : Fin k → R)
    (σ : PreservingPerm (fun i => colour i = true)) : SignedFibre colour v :=
  ⟨fun i => v (σ.val i), by
    intro n hn hnk
    have hc (i) : colour (σ.val i) = colour i := by
      have hh := σ.property i
      cases h₁ : colour (σ.val i) <;> cases h₂ : colour i <;> simp_all
    have he := Equiv.sum_comp σ.val
      (fun i => (if colour i then (1 : R) else -1) * v i ^ n)
    simpa only [hc] using he.symm⟩

/-- A nonsingular signed fibre is exactly the permutations of its two
colour classes. This proves finiteness even over an infinite domain. -/
theorem signedFibre_equiv {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (colour : Fin k → Bool) (v : Fin k → R) (hv : Function.Injective v)
    (hchar : ∀ n, 1 ≤ n → n ≤ k → (n : R) ≠ 0) :
    Nonempty (PreservingPerm (fun i => colour i = true) ≃ SignedFibre colour v) := by
  classical
  apply Nonempty.intro
  apply Equiv.ofBijective (signedFibreOfPerm colour v)
  constructor
  · intro σ τ hστ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact hv (congrArg (fun u : SignedFibre colour v => u.val i) hστ)
  · intro u
    obtain ⟨σ, hσ⟩ := signed_power_permutation colour v u.val hv hchar u.property
    let σ' : PreservingPerm (fun i => colour i = true) := ⟨σ, by
      intro i
      change colour (σ i) = true ↔ colour i = true
      rw [(hσ i).2]⟩
    refine ⟨σ', ?_⟩
    apply Subtype.ext
    funext i
    exact (hσ i).1.symm

/-- The exact signed-fibre cardinality is the product of the two colour
factorials, rather than the factorial obtained by forgetting the signs. -/
theorem signed_fibre_card {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}
    (colour : Fin k → Bool) (v : Fin k → R) (hv : Function.Injective v)
    (hchar : ∀ n, 1 ≤ n → n ≤ k → (n : R) ≠ 0) :
    Nat.card (SignedFibre colour v) =
      (Fintype.card {i // colour i = true}).factorial *
        (Fintype.card {i // colour i ≠ true}).factorial := by
  obtain ⟨e⟩ := signedFibre_equiv colour v hv hchar
  rw [← Nat.card_congr e, card_preservingPerm]

end
end RiemannGaussian.VinogradovSignedRigidity
