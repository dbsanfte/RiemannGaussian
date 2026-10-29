/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketPolynomialSupport
import RiemannGaussian.SemiprimeD1AcquiredModeSum

/-! # Dyadic weights of the ACTUAL physical packet row recipes
The actual coefficient branch supplies its same-bit test. Original D.12 then
proves divisibility by2^(order+1), including the negative Boolean complement.
Multiplication preserves this ideal content in the actual multijet ring; no
multiplicative valuation law or integral-domain assumption is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1PacketPolynomialWeight
open scoped BigOperators
open SemiprimeD1WeightedPolynomial SemiprimeD1PacketEntryBits
open SemiprimeD1PacketEntryValue SemiprimeD1PacketEntryComponents SemiprimeD1PacketEntryInputs
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation
noncomputable section

/-- The actual global-index mode weight, in acquired descriptor order. -/
def weights (cache : SemiprimeD1PacketModeMask.Cache) : List ℕ :=
  cache.items.map (fun item => item.mode.order+1)

/-- Each actual physical signed mode coefficient has its ORIGINAL dyadic weight. -/
theorem coefficient_weight (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (item : SemiprimeD1PacketModeMask.Item) (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val) :
    (2 : Carrier ctx)^(item.mode.order+1) ∣ interpret ctx (coefficient ctx z a i t row item).words := by
  rw [coefficient_value ctx z a i t row item hpos hp ht hi]
  dsimp only
  split_ifs with h
  · have hbit : row.slot.val.testBit i.val = (item.tile%2^a).testBit i.val :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    obtain ⟨c, hc⟩ := SemiprimeD1UniversalModeData.original_weight ctx.precision a i.val item.mode.order
      (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes))
      (interpret ctx z.words) t row.slot ⟨item.tile%2^a, Nat.mod_lt _ (by positivity)⟩
      ht hi i.isLt hbit
    rw [hc]
    simp only [map_ofNat]
    exact dvd_mul_right _ c
  · have hbit : row.slot.val.testBit i.val = (item.tile%2^a).testBit i.val :=
      beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
    obtain ⟨c, hc⟩ := SemiprimeD1UniversalModeData.original_weight ctx.precision a i.val item.mode.order
      (SemiprimeD1JetAlgebra.constants (SemiprimeD1JetBoxIndex.dims ctx.axes))
      (interpret ctx z.words) t row.slot ⟨item.tile%2^a, Nat.mod_lt _ (by positivity)⟩
      ht hi i.isLt hbit
    rw [hc]
    simp only [map_ofNat]
    exact dvd_neg.mpr (dvd_mul_right _ c)
  · exact dvd_zero _

/-- Literal finite mode-polynomial sums retain coefficientwise dyadic content. -/
theorem weighted_list_sum {R : Type*} [CommRing R] (w : ℕ → ℕ)
    (ps : List (MvPolynomial ℕ R)) (hp : ∀ p ∈ ps, Weighted w p) : Weighted w ps.sum := by
  induction ps with
  | nil => simpa only [List.sum_nil, map_zero] using weighted_C w (0 : R)
  | cons p ps ih =>
    exact weighted_add w _ _ (hp p List.mem_cons_self)
      (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

/-- Literal finite row-polynomial products preserve every dyadic mode weight. -/
theorem weighted_list_prod {R : Type*} [CommRing R] (w : ℕ → ℕ)
    (ps : List (MvPolynomial ℕ R)) (hp : ∀ p ∈ ps, Weighted w p) : Weighted w ps.prod := by
  induction ps with
  | nil => simpa only [List.prod_nil, map_one] using weighted_C w (1 : R)
  | cons p ps ih =>
    exact weighted_mul w _ _ (hp p List.mem_cons_self)
      (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

/-- An actual affine recipe is weighted once its actual acquired coefficients are. -/
theorem rowPolynomial_weighted {R : Type*} [CommRing R] (w : ℕ → ℕ) (K : ℕ)
    (row : SemiprimeD1AffineCoefficient.Row R)
    (hc : ∀ j < K, (2 : R)^w j ∣ row.coefficients.getD j 0) :
    Weighted w (SemiprimeD1AffineCoefficient.rowPolynomial K row) := by
  unfold SemiprimeD1AffineCoefficient.rowPolynomial
  apply weighted_add w _ _ (weighted_C w row.base)
  apply weighted_list_sum
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  rw [MvPolynomial.C_mul_X_eq_monomial]
  apply weighted_monomial
  simpa only [degree_single, Nat.mul_one] using hc j (List.mem_range.mp hj)

/-- Every actual row recipe, with its original complete descriptor cache, is weighted. -/
theorem recipe_weighted (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (row : Wire a)
    (columns : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache)
    (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val) :
    Weighted (SemiprimeD1AcquiredModeSum.weight (weights cache))
      (SemiprimeD1AffineCoefficient.rowPolynomial cache.items.length
        (SemiprimeD1JetAffineCoefficient.rowValue ctx (recipe ctx z a i t row columns cache.items).value)) := by
  apply rowPolynomial_weighted
  intro j hj
  have hw : SemiprimeD1AcquiredModeSum.weight (weights cache) j = cache.items[j].mode.order+1 := by
    unfold SemiprimeD1AcquiredModeSum.weight weights
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj), List.getElem_map]
  rw [hw]
  change (2 : Carrier ctx)^(cache.items[j].mode.order+1) ∣
    ((coefficients ctx z a i t row cache.items).value.map (interpret ctx)).getD j 0
  rw [coefficients_value, List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj), List.getElem_map]
  exact coefficient_weight ctx z a i t row cache.items[j] hpos hp ht hi

/-- The COMPLETE actual physical packet polynomial satisfies the weighted-menu
hypothesis, including every repeated row and all Boolean complements. -/
theorem packet_polynomial_weighted (ctx : Context) (z : SemiprimeD1JetAffineCoefficient.JetRun)
    (a : ℕ) (i : Fin a) (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (columns rows : List (Wire a)) (cache : SemiprimeD1PacketModeMask.Cache)
    (hpos : ctx.Positive) (hp : 0 < ctx.precision)
    (ht : SemiprimeD1WireKernelOriginal.point a t.val ≠ 0)
    (hi : padicValInt 2 (SemiprimeD1WireKernelOriginal.point a t.val) = i.val) :
    Weighted (SemiprimeD1AcquiredModeSum.weight (weights cache))
      (SemiprimeD1AffineCoefficient.polynomial cache.items.length
        ((recipes ctx z a i t columns cache.items rows).value.map
          (SemiprimeD1JetAffineCoefficient.rowValue ctx))) := by
  unfold SemiprimeD1AffineCoefficient.polynomial
  apply weighted_list_prod
  intro p hp'
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hp'
  rw [recipes_value, List.map_map] at hrow
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hrow
  exact recipe_weighted ctx z a i t original columns cache hpos hp ht hi

/-- Actual descriptor weights equal the ORIGINAL acquired catalogue weights. -/
theorem original_weights {n F r a : ℕ} {arity : Fin F → ℕ}
    (source : SemiprimeD1OriginalModeAcquisition.Acquired n F a arity)
    (packet : Fin source.packets.state.packets.length) (i : Fin a) (g : Fin r) :
    weights (SemiprimeD1PacketModeMask.fromModes source packet i g) =
      SemiprimeD1ModeCatalog.weights (source.packets.state.packets.length*2^(i.val+1))
        (source.precision-1) := by
  have hc := SemiprimeD1PacketModeMask.fromModes_catalogue source packet i g
  unfold weights SemiprimeD1ModeCatalog.weights
  rw [← hc, List.map_map]
  rfl

end
end RiemannGaussian.SemiprimeD1PacketPolynomialWeight
