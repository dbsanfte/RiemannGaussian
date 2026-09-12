/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteKuzminLandauPeriodic

/-!
# Exact finite blocks selected by a monotone phase increment

The indices of a monotone sequence lying in a half-open value interval
form a literal consecutive integer block. A positive separation lower
bound controls its actual cardinality. Applied to phase increments, this
retains the finite good blocks needed by a resonance decomposition and
gives their nonresonant cancellation bound.
-/

namespace RiemannGaussian.MonotonePhaseBlocks
noncomputable section
open PhaseIncrementInverse FiniteKuzminLandau
open scoped Classical

/-- The original indices whose values lie in the specified half-open
interval, with the original finite cutoff retained. -/
def band (d : ℕ → ℝ) (N : ℕ) (u v : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n ↦ u ≤ d n ∧ d n < v)

/-- Membership retains both the original index cutoff and both value
boundaries. -/
theorem mem_band (d : ℕ → ℝ) (N : ℕ) (u v : ℝ) (n : ℕ) :
    n ∈ band d N u v ↔ n < N ∧ u ≤ d n ∧ d n < v := by
  simp only [band, Finset.mem_filter, Finset.mem_range]

/-- A nonempty monotone value band is exactly a finite consecutive
integer interval; no boundary fibre is dropped. -/
theorem band_eq_Ico {d : ℕ → ℝ} {N : ℕ} {u v : ℝ}
    (hd : MonotoneOn d (Set.Iio N)) (hne : (band d N u v).Nonempty) :
    ∃ a b : ℕ, a < b ∧ b ≤ N ∧ band d N u v = Finset.Ico a b := by
  let T := band d N u v
  let a := T.min' hne
  let z := T.max' hne
  have ha : a ∈ T := Finset.min'_mem T hne
  have hz : z ∈ T := Finset.max'_mem T hne
  have haz : a ≤ z := Finset.min'_le T z hz
  have ha' := (mem_band d N u v a).mp ha
  have hz' := (mem_band d N u v z).mp hz
  refine ⟨a, z + 1, by omega, by omega, ?_⟩
  ext n
  constructor
  · intro hn
    have hl := Finset.min'_le T n hn
    have hu := Finset.le_max' T n hn
    simp only [Finset.mem_Ico]
    change a ≤ n ∧ n < z + 1
    exact ⟨hl, by omega⟩
  · intro hn
    have hn' := Finset.mem_Ico.mp hn
    have hnN : n < N := by omega
    apply (mem_band d N u v n).mpr
    exact ⟨hnN, ha'.2.1.trans (hd ha'.1 hnN hn'.1),
      (hd hnN hz'.1 (by omega)).trans_lt hz'.2.2⟩

/-- A positive separation of values controls the number of original
indices in any value interval, with the finite endpoint cost retained. -/
theorem band_card_le {d : ℕ → ℝ} {N : ℕ} {u v ℓ : ℝ} (hℓ : 0 < ℓ) (huv : u ≤ v)
    (hd : MonotoneOn d (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → ℓ * ((j : ℝ) - i) ≤ d j - d i) :
    ((band d N u v).card : ℝ) ≤ (v - u) / ℓ + 1 := by
  by_cases hne : (band d N u v).Nonempty
  · obtain ⟨a, b, hab, hbN, he⟩ := band_eq_Ico hd hne
    have ha : a ∈ band d N u v := by rw [he]; exact Finset.mem_Ico.mpr ⟨le_rfl, hab⟩
    have hz : b - 1 ∈ band d N u v := by rw [he]; simp only [Finset.mem_Ico]; omega
    have ha' := (mem_band d N u v a).mp ha
    have hz' := (mem_band d N u v (b - 1)).mp hz
    have hs := hsep a ha'.1 (b - 1) hz'.1 (by omega)
    have hc : ((band d N u v).card : ℝ) = (b : ℝ) - a := by
      rw [he, Nat.card_Ico, Nat.cast_sub (by omega : a ≤ b)]
    have hbcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
    rw [hbcast] at hs
    rw [hc]
    have heq : (v - u) / ℓ + 1 = (v - u + ℓ) / ℓ := by field_simp
    rw [heq, le_div_iff₀ hℓ]
    nlinarith [ha'.2.1, hz'.2.2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    have hwidth : 0 ≤ v - u := sub_nonneg.mpr huv
    positivity

/-- A complete nonresonant increment band inherits the periodic
Kuzmin--Landau estimate, retaining all original summands and boundaries. -/
theorem nonresonant_band_bound (φ : ℕ → ℝ) (N : ℕ) (m : ℤ) {η : ℝ} (hη : 0 < η)
    (hd : MonotoneOn (increment φ) (Set.Iio N)) :
    ‖∑ n ∈ band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
      ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), rotation (φ n)‖ ≤
        2 * Real.pi / η := by
  let T := band (increment φ) N ((m : ℝ) * (2 * Real.pi) + η)
    ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η)
  by_cases hne : T.Nonempty
  · obtain ⟨a, b, _, _, he⟩ := band_eq_Ico hd hne
    change T = _ at he
    change ‖∑ n ∈ T, rotation (φ n)‖ ≤ _
    rw [he]
    apply FiniteKuzminLandauPeriodic.bound_Ico φ a b m hη
    · intro n hn
      rw [← he] at hn
      have h := (mem_band _ _ _ _ n).mp hn
      exact ⟨h.2.1, h.2.2.le⟩
    · left
      intro i hi j hj hij
      have hi' : i ∈ T := by rw [he]; exact Finset.mem_Ico.mpr hi
      have hj' : j ∈ T := by rw [he]; exact Finset.mem_Ico.mpr hj
      exact hd ((mem_band _ _ _ _ i).mp hi').1 ((mem_band _ _ _ _ j).mp hj').1 hij
  · change ‖∑ n ∈ T, rotation (φ n)‖ ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]
    positivity

end
end RiemannGaussian.MonotonePhaseBlocks
