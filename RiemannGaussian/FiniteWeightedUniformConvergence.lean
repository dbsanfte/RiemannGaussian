/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Uniform errors under arbitrary finite complex weights

Bounded total variation transports uniformly vanishing errors. For nonnegative weights with converging total mass, the limiting reference complex phase is retained exactly.
-/

namespace RiemannGaussian.FiniteWeightedUniformConvergence
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- Every moving complex weight family with bounded total variation
transports a uniformly vanishing selected error to a vanishing sum. -/
theorem tendsto_weighted_error {α : Type*} (S : ℕ → Finset α)
    (w E : ℕ → α → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ᶠ N : ℕ in atTop, (∑ k ∈ S N, ‖w N k‖) ≤ C)
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, ‖E N k‖ ≤ ε) :
    Tendsto (fun N : ℕ => ∑ k ∈ S N, w N k * E N k) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc : 0 < C + 1 := by linarith
  have hd : 0 < ε / (C + 1) := div_pos hε hc
  filter_upwards [hmass, hE (ε / (C + 1)) hd] with N hm he
  rw [dist_zero_right]
  calc
    _ ≤ ∑ k ∈ S N, ‖w N k * E N k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S N, ‖w N k‖ * (ε / (C + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (he k hk) (norm_nonneg _)
    _ = (∑ k ∈ S N, ‖w N k‖) * (ε / (C + 1)) := by rw [Finset.sum_mul]
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_right hm hd.le
    _ < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hc).mpr
      nlinarith

/-- Every convergent total mass of nonnegative finite weights transports
a uniformly converging complex array to its exact reference phase times
the limiting mass. The selected family and its moving support are arbitrary. -/
theorem tendsto_nonneg_weighted_sum {α : Type*} (S : ℕ → Finset α)
    (w : ℕ → α → ℝ) (a : ℕ → α → ℂ) {c : ℝ} {b : ℂ}
    (hw : ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, 0 ≤ w N k)
    (hmass : Tendsto (fun N : ℕ => ∑ k ∈ S N, w N k) atTop (nhds c))
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ k ∈ S N, ‖a N k - b‖ ≤ ε) :
    Tendsto (fun N : ℕ => ∑ k ∈ S N, (w N k : ℂ) * a N k)
      atTop (nhds ((c : ℂ) * b)) := by
  have hC : 0 ≤ |c| + 1 := by positivity
  have hmassBound : ∀ᶠ N : ℕ in atTop, (∑ k ∈ S N, ‖(w N k : ℂ)‖) ≤ |c| + 1 := by
    have hc : c < |c| + 1 := by linarith [le_abs_self c]
    filter_upwards [hw, hmass.eventually (eventually_lt_nhds hc)] with N hwN hmN
    calc
      _ = ∑ k ∈ S N, w N k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Complex.norm_real, Real.norm_of_nonneg (hwN k hk)]
      _ ≤ _ := hmN.le
  have he := tendsto_weighted_error S (fun N k => (w N k : ℂ))
    (fun N k => a N k - b) hC hmassBound ha
  have hr := ((Complex.continuous_ofReal.tendsto _).comp hmass).mul_const b
  have h := he.add hr
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end RiemannGaussian.FiniteWeightedUniformConvergence
