/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialDifferencing

/-!
# Exact colour products for polynomial-system conditioning

The complete residue-tuple energies sum to the power of the original
one-variable residue energy. A tuple restriction determined by its colour
does not change any admissible colour fibre. These are the product
identities used to pay the nonsingular conditioning bound by the literal
residue mixed integral.
-/

namespace RiemannGaussian.VinogradovColourProducts
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovMomentPartition VinogradovPartitionEnergy VinogradovProductEnergy
open VinogradovDifferenceEnergy

/-- Every original coordinate colour is retained. -/
def tupleLabel {ι κ : Type*} (m : ℕ) (label : ι → κ) (x : Fin m → ι) : Fin m → κ :=
  fun j => label (x j)

/-- The tuple colour mask is the product of the individual masks. -/
theorem tuple_targetWeight {ι κ : Type*} (m : ℕ) (label : ι → κ)
    (c : Fin m → κ) (x : Fin m → ι) :
    targetWeight (tupleLabel m label) (fun _ => 1) c x =
      ∏ j, targetWeight label (fun _ => 1) (c j) (x j) := by
  simp only [targetWeight, tupleLabel, funext_iff]
  by_cases hc : ∀ j, label (x j) = c j
  · simp [hc]
  · rw [if_neg hc]
    obtain ⟨j, hj⟩ := not_forall.mp hc
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- A fixed complete tuple colour has exactly the product of its
original single-variable residue polynomials. -/
theorem tuple_class_polynomial {ι κ a : Type*} [Fintype ι] [Fintype a]
    (m : ℕ) (v : ι → a → ℤ) (label : ι → κ) (c : Fin m → κ)
    (theta : UnitAddTorus a) :
    polynomial (tupleFrequency m v) (targetWeight (tupleLabel m label) (fun _ => 1) c) theta =
      ∏ j, polynomial v (targetWeight label (fun _ => 1) (c j)) theta := by
  unfold polynomial
  simp_rw [tuple_targetWeight]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, product_mFourier]
  rfl

/-- Summing every original tuple colour gives the exact power of the
one-variable colour energy. -/
theorem tuple_colour_energy {ι κ a : Type*} [Fintype ι] [Fintype κ] [Fintype a]
    (m : ℕ) (v : ι → a → ℤ) (label : ι → κ) (theta : UnitAddTorus a) :
    (∑ c : Fin m → κ, ‖polynomial (tupleFrequency m v)
      (targetWeight (tupleLabel m label) (fun _ => 1) c) theta‖ ^ 2) =
      colourEnergy label (fun i => mFourier (v i) theta) ^ m := by
  simp_rw [tuple_class_polynomial, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun _j : Fin m => fun c : κ =>
    ‖polynomial v (targetWeight label (fun _ => 1) c) theta‖ ^ 2)]
  simp only [polynomial, targetWeight, ite_mul, one_mul, zero_mul,
    colourEnergy, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Deleting zero coefficients through a subtype is an exact identity. -/
theorem polynomial_subtype_eq {ι a : Type*} [Fintype ι] [Fintype a]
    (good : ι → Prop) [Fintype {i // good i}] (v : ι → a → ℤ) (w : ι → ℂ)
    (hw : ∀ i, ¬good i → w i = 0) (theta : UnitAddTorus a) :
    polynomial (fun i : {i // good i} => v i.val) (fun i => w i.val) theta =
      polynomial v w theta := by
  unfold polynomial
  rw [← Finset.sum_subtype (Finset.univ.filter good) (by simp) (fun i => w i * mFourier (v i) theta)]
  apply Finset.sum_subset (Finset.filter_subset good Finset.univ)
  intro i hi hn
  have hg : ¬good i := by simpa only [Finset.mem_filter, hi, true_and] using hn
  rw [hw i hg, zero_mul]

/-- A restriction determined by the entire colour tuple does not
alter any admissible colour fibre. -/
theorem good_tuple_class_polynomial {ι κ a : Type*} [Fintype ι] [Fintype a]
    (m : ℕ) (v : ι → a → ℤ) (label : ι → κ) (good : (Fin m → κ) → Prop)
    (c : Fin m → κ) (hc : good c) (theta : UnitAddTorus a) :
    polynomial (fun x : {x : Fin m → ι // good (tupleLabel m label x)} => tupleFrequency m v x.val)
      (targetWeight (fun x => tupleLabel m label x.val) (fun _ => 1) c) theta =
      polynomial (tupleFrequency m v) (targetWeight (tupleLabel m label) (fun _ => 1) c) theta := by
  change polynomial (fun x : {x : Fin m → ι // good (tupleLabel m label x)} =>
    tupleFrequency m v x.val)
    (fun x => targetWeight (tupleLabel m label) (fun _ => 1) c x.val) theta = _
  apply polynomial_subtype_eq (fun x => good (tupleLabel m label x))
    (tupleFrequency m v) (targetWeight (tupleLabel m label) (fun _ => 1) c) ?_ theta
  intro x hx
  unfold targetWeight
  apply if_neg
  intro he
  exact hx (he.symm ▸ hc)

end
end RiemannGaussian.VinogradovColourProducts
