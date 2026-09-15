/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Continuity of reflected harmonic products

For every convergent complex array and every moving lower-half order selection, the centered harmonic product tends to zero. Both reflected marginals are paid by one Cesaro average; no special coefficient family is selected.
-/

namespace RiemannGaussian.HarmonicProductContinuity
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The centered product keeps its reference phase exactly; only the
two genuine perturbations are estimated. -/
theorem norm_product_sub_square {A B a : ℂ} {C : ℝ}
    (hB : ‖B‖ ≤ C) (ha : ‖a‖ ≤ C) :
    ‖A * B - a ^ 2‖ ≤ C * (‖A - a‖ + ‖B - a‖) := by
  have he : A * B - a ^ 2 = (A - a) * B + a * (B - a) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hB (norm_nonneg (A - a))
  have h2 := mul_le_mul_of_nonneg_right ha (norm_nonneg (B - a))
  nlinarith

/-- Each original and reflected order marginal is bounded by the same
complete finite prefix. Injectivity prevents any hidden multiplicity. -/
theorem order_marginal_sums_le (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (N : ℕ) (S : Finset ℕ) (hS : ∀ k ∈ S, 2 * k ≤ N + 1) :
    (∑ k ∈ S, e (k + 1)) ≤ ∑ j ∈ Finset.range (N + 3), e j ∧
    (∑ k ∈ S, e (N + 1 - k)) ≤ ∑ j ∈ Finset.range (N + 3), e j := by
  have hs : (S.image (fun k => k + 1)) ⊆ Finset.range (N + 3) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by have hh := hS k hk; omega)
  have hr : (S.image (fun k => N + 1 - k)) ⊆ Finset.range (N + 3) := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by omega)
  have his : Set.InjOn (fun k : ℕ => k + 1) S := by
    intro a _ b _ h
    dsimp only at h
    omega
  have hir : Set.InjOn (fun k : ℕ => N + 1 - k) S := by
    intro a ha b hb h
    have ha' := hS a ha
    have hb' := hS b hb
    dsimp only at h
    omega
  constructor
  · rw [← Finset.sum_image his]
    exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => he j)
  · rw [← Finset.sum_image hir]
    exact Finset.sum_le_sum_of_subset_of_nonneg hr (fun j _ _ => he j)

/-- A bound for every selected reflected harmonic product uses only
the Cesaro average of the centered array. The set may vary arbitrarily. -/
theorem norm_harmonic_product_error_le (a : ℕ → ℂ) (b : ℂ) (N : ℕ)
    (S : Finset ℕ) (hS : ∀ k ∈ S, 2 * k ≤ N + 1)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ k, ‖a k‖ ≤ C) (hb : ‖b‖ ≤ C) :
    ‖∑ k ∈ S, (a (k + 1) * a (N + 1 - k) - b ^ 2) / ((N + 1 - k : ℕ) : ℂ)‖ ≤
      12 * C * (((N + 3 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 3), ‖a j - b‖) := by
  let E : ℝ := ∑ j ∈ Finset.range (N + 3), ‖a j - b‖
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hT : (0 : ℝ) < ((N + 3 : ℕ) : ℝ) := by positivity
  have hterms (k : ℕ) (hk : k ∈ S) :
      ‖(a (k + 1) * a (N + 1 - k) - b ^ 2) / ((N + 1 - k : ℕ) : ℂ)‖ ≤
        (2 * C / ((N + 1 : ℕ) : ℝ)) * (‖a (k + 1) - b‖ + ‖a (N + 1 - k) - b‖) := by
    have hl : 0 < N + 1 - k := by have hh := hS k hk; omega
    have hlr : (0 : ℝ) < ((N + 1 - k : ℕ) : ℝ) := by exact_mod_cast hl
    have hc : ((N + 1 : ℕ) : ℝ) ≤ 2 * ((N + 1 - k : ℕ) : ℝ) := by
      exact_mod_cast (by have hh := hS k hk; omega : N + 1 ≤ 2 * (N + 1 - k))
    have hi : (1 : ℝ) / (N + 1 - k : ℕ) ≤ 2 / ((N + 1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hlr hM).mpr
      nlinarith
    rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
    have hh := mul_le_mul (norm_product_sub_square (A := a (k + 1)) (ha (N + 1 - k)) hb)
      (by simpa only [one_div] using hi) (by positivity) (by positivity)
    exact hh.trans_eq (by ring)
  have hm := order_marginal_sums_le (fun j => ‖a j - b‖) (fun _ => norm_nonneg _) N S hS
  have hcoef : 4 * C / ((N + 1 : ℕ) : ℝ) ≤ 12 * C / ((N + 3 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hM hT).mpr
    have hc : ((N + 3 : ℕ) : ℝ) ≤ 3 * ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N + 3 ≤ 3 * (N + 1))
    nlinarith [mul_le_mul_of_nonneg_left hc hC]
  calc
    _ ≤ ∑ k ∈ S, (2 * C / ((N + 1 : ℕ) : ℝ)) *
        (‖a (k + 1) - b‖ + ‖a (N + 1 - k) - b‖) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterms)
    _ = (2 * C / ((N + 1 : ℕ) : ℝ)) *
        ((∑ k ∈ S, ‖a (k + 1) - b‖) + ∑ k ∈ S, ‖a (N + 1 - k) - b‖) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (4 * C / ((N + 1 : ℕ) : ℝ)) * E := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add hm.1 hm.2)
        (by positivity : (0 : ℝ) ≤ 2 * C / ((N + 1 : ℕ) : ℝ))
      exact hh.trans_eq (by dsimp only [E]; ring)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcoef hE
      exact hh.trans_eq (by ring)

/-- Every moving selection in the lower half has the same centered
harmonic-product continuity law. Convergence of the full complex array
suffices; no special coefficient family or phase alignment is imposed. -/
theorem tendsto_harmonic_product_error (a : ℕ → ℂ) (b : ℂ)
    (ha : Tendsto a atTop (nhds b)) (S : ℕ → Finset ℕ)
    (hS : ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, 2 * k ≤ N + 1) :
    Tendsto (fun N : ℕ => ∑ k ∈ S N,
      (a (k + 1) * a (N + 1 - k) - b ^ 2) / ((N + 1 - k : ℕ) : ℂ))
        atTop (nhds 0) := by
  obtain ⟨R, hR, haR⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  let C : ℝ := R + ‖b‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have haC : ∀ k, ‖a k‖ ≤ C := by
    intro k
    have hh := haR (a k) (Set.mem_range_self k)
    dsimp only [C]
    linarith [norm_nonneg b]
  have hbC : ‖b‖ ≤ C := by dsimp only [C]; linarith
  have he : Tendsto (fun j : ℕ => ‖a j - b‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using (ha.sub_const b).norm
  have havg := he.cesaro.comp (tendsto_add_atTop_nat 3)
  apply squeeze_zero_norm' (by
    filter_upwards [hS] with N hSN
    exact norm_harmonic_product_error_le a b N (S N) hSN hC haC hbC)
  simpa only [Function.comp_def, mul_zero] using havg.const_mul (12 * C)

end
end RiemannGaussian.HarmonicProductContinuity
