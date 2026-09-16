/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMassTransport

/-!
# Exact positive cancellation of three complex amplitudes

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszCycleCore
noncomputable section
open scoped BigOperators Classical

/-- The signed area of two actual complex amplitudes. -/
def area (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

/-- The exact planar dependence retains all signs and amplitudes. -/
theorem area_cycle_identity (z w v : ℂ) :
    area w v • z + area v z • w + area z w • v = 0 := by
  apply Complex.ext <;> simp only [area, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.zero_re, Complex.zero_im] <;> ring

/-- Positive oriented areas identify the cancellable branch. -/
def positiveCycle (z w v : ℂ) : Prop := 0 < area w v ∧ 0 < area v z ∧ 0 < area z w

/-- Scale the exact dependence to exhaust one available amplitude.
Outside the positive branch the scale is zero, so the step changes nothing. -/
def cycleScale (z w v : ℂ) : ℝ :=
  if positiveCycle z w v then (max (area w v) (max (area v z) (area z w)))⁻¹ else 0

/-- Every removed fraction lies between zero and one, including the
inactive branch. No positivity hypothesis remains on this bound. -/
theorem cycleScale_bounds (z w v : ℂ) :
    0 ≤ cycleScale z w v * area w v ∧ cycleScale z w v * area w v ≤ 1 ∧
    0 ≤ cycleScale z w v * area v z ∧ cycleScale z w v * area v z ≤ 1 ∧
    0 ≤ cycleScale z w v * area z w ∧ cycleScale z w v * area z w ≤ 1 := by
  by_cases h : positiveCycle z w v
  · have ha := h.1
    have hb := h.2.1
    have hc := h.2.2
    let M := max (area w v) (max (area v z) (area z w))
    have hM : 0 < M := ha.trans_le (le_max_left _ _)
    have hA : area w v ≤ M := le_max_left _ _
    have hB : area v z ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hC : area z w ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have bound (a : ℝ) (ha0 : 0 ≤ a) (haM : a ≤ M) : 0 ≤ M⁻¹ * a ∧ M⁻¹ * a ≤ 1 := by
      refine ⟨mul_nonneg (inv_nonneg.mpr hM.le) ha0, ?_⟩
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_one hM).mpr haM
    rw [cycleScale, if_pos h]
    exact ⟨(bound _ ha.le hA).1, (bound _ ha.le hA).2,
      (bound _ hb.le hB).1, (bound _ hb.le hB).2,
      (bound _ hc.le hC).1, (bound _ hc.le hC).2⟩
  · simp [cycleScale, h]

/-- The portions sent by every step cancel exactly, with no chord error. -/
theorem sent_cycle_eq_zero (z w v : ℂ) :
    (cycleScale z w v * area w v) • z +
      (cycleScale z w v * area v z) • w +
      (cycleScale z w v * area z w) • v = 0 := by
  rw [mul_smul, mul_smul, mul_smul, ← smul_add, ← smul_add, area_cycle_identity, smul_zero]

/-- The three unsent amplitudes retain their original directions and sum. -/
theorem sum_cycle_remainders (z w v : ℂ) :
    (1 - cycleScale z w v * area w v) • z +
      (1 - cycleScale z w v * area v z) • w +
      (1 - cycleScale z w v * area z w) • v = z + w + v := by
  have h := sent_cycle_eq_zero z w v
  simp only [sub_smul, one_smul]
  linear_combination -h

/-- The full amount removed from the absolute budget by one exact cycle. -/
def cycleSaving (z w v : ℂ) : ℝ :=
  cycleScale z w v * (area w v * ‖z‖ + area v z * ‖w‖ + area z w * ‖v‖)

/-- The saving is always nonnegative, with no sign assumption required. -/
theorem cycleSaving_nonneg (z w v : ℂ) : 0 ≤ cycleSaving z w v := by
  obtain ⟨ha, _, hb, _, hc, _⟩ := cycleScale_bounds z w v
  have hz := mul_nonneg ha (norm_nonneg z)
  have hw := mul_nonneg hb (norm_nonneg w)
  have hv := mul_nonneg hc (norm_nonneg v)
  unfold cycleSaving
  nlinarith

/-- The norm budget decreases by exactly the sent zero-cycle mass. -/
theorem sum_norm_cycle_remainders (z w v : ℂ) :
    ‖(1 - cycleScale z w v * area w v) • z‖ +
      ‖(1 - cycleScale z w v * area v z) • w‖ +
      ‖(1 - cycleScale z w v * area z w) • v‖ =
      ‖z‖ + ‖w‖ + ‖v‖ - cycleSaving z w v := by
  obtain ⟨_, ha, _, hb, _, hc⟩ := cycleScale_bounds z w v
  rw [norm_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg (sub_nonneg.mpr ha),
    Real.norm_of_nonneg (sub_nonneg.mpr hb),
    Real.norm_of_nonneg (sub_nonneg.mpr hc)]
  unfold cycleSaving
  ring

/-- A full triple has an independent exact-cancellation saving. -/
theorem norm_sum_three_le_sub_saving (z w v : ℂ) :
    ‖z + w + v‖ ≤ ‖z‖ + ‖w‖ + ‖v‖ - cycleSaving z w v := by
  rw [← sum_norm_cycle_remainders, ← sum_cycle_remainders]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))

end
end RiemannGaussian.ZetaRieszCycleCore
