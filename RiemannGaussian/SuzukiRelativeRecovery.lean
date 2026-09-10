/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiDampedDelayMoments

/-!
# Arbitrarily close relative recovery for the actual Suzuki signal

Variable damping concentrates the genuine signed gamma moments into any
fixed relative window. The finite positive delay span and integer rounding
are then absorbed into a strictly larger time ratio. Every sufficiently
late interval `[a, K*a]`, for any fixed `K > 1`, contains a positive value
of the original unaveraged arithmetic signal.

This sharpens the unconditional recovery time estimate. It does not bound
the depths of the negative excursions or prove the arithmetic RH floor.
-/

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

/-- Choosing damping to match a prescribed relative window gives actual
positive delayed values in that window at every sufficiently late order. -/
theorem exists_suzukiDamping_eventually_pos_in_relative_window {l u : ℝ}
    (hl : 0 < l) (hl1 : l < 1) (hu : 1 < u) :
    ∃ d : ℝ, 1 / 2 < d ∧ ∀ᶠ n : ℕ in atTop,
      ∃ t ∈ Icc (l * n / d) (u * n / d),
        0 < suzukiPositiveDelaySignal (suzukiZeroWindowDelayNodes (d + 1 / 4)) t := by
  obtain ⟨b, hb, hbu, hql, hqu⟩ := exists_gammaWindow_tail_allowance hl hl1 hu
  let d := 1 + 1 / b
  have hd : 1 / 2 < d := by
    dsimp [d]
    have : 0 < 1 / b := by positivity
    linarith
  have hbd : b * d = b + 1 := by dsimp [d]; field_simp
  have hsafe : 1 / 2 < b * d := by rw [hbd]; linarith
  refine ⟨d, hd, ?_⟩
  apply eventually_exists_pos_in_dampedGammaWindow (by linarith) hb.le hl hl1 hu hbu hql hqu
    (fun t ht => suzukiPositiveDelaySignal_eq_zero_of_nonpositive _ ht)
    (integrable_suzukiPositiveDelaySignal_real_laplace _ hsafe)
    (integrable_suzukiDampedDelayGammaMoment _ hd)
  exact tendsto_suzukiZeroWindowDampedGammaMoment_atTop hd le_rfl

/-- For every fixed ratio greater than one, every sufficiently late
interval with that ratio contains a positive value of the original Suzuki
signal. All delay spans, cutoffs, and rounding errors are discharged. -/
theorem eventually_exists_pos_suzukiSignal_between_arbitrary_time_multiples
    {K : ℝ} (hK : 1 < K) :
    ∀ᶠ a : ℝ in atTop, ∃ u ∈ Icc a (K * a),
      0 < suzukiChebyshevLogAverageLaplaceSignal u := by
  have hK0 : 0 < K := by linarith
  have hinv : 1 / K < (1 : ℝ) := (div_lt_one hK0).mpr hK
  obtain ⟨l, hlK, hl1⟩ := exists_between hinv
  have hl : 0 < l := (one_div_pos.mpr hK0).trans hlK
  have hKl : 1 < K * l := by simpa only [mul_comm] using (div_lt_iff₀ hK0).mp hlK
  obtain ⟨u, hu, huK⟩ := exists_between hKl
  have hu0 : 0 < u := by linarith
  have hratio : u / l < K := (div_lt_iff₀ hl).mpr (by simpa only [mul_comm] using huK)
  obtain ⟨d, hd, hpos⟩ := exists_suzukiDamping_eventually_pos_in_relative_window hl hl1 hu
  have hd0 : 0 < d := by linarith
  let L := suzukiZeroWindowDelayNodes (d + 1 / 4)
  let S := positiveDelaySpan L
  let C := (u / l) * S + u / d
  have hS : 0 ≤ S := positiveDelaySpan_nonneg L
  have hc : Tendsto (fun a : ℝ => Nat.ceil ((d / l) * (a + S))) atTop atTop :=
    tendsto_nat_ceil_atTop.comp
      ((tendsto_atTop_add_const_right atTop S tendsto_id).const_mul_atTop
        (by positivity : 0 < d / l))
  filter_upwards [hc.eventually hpos, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (C / (K - u / l))] with a ha ha0 haC
  let n := Nat.ceil ((d / l) * (a + S))
  obtain ⟨t, ht, hp⟩ := ha
  have hnlo : (d / l) * (a + S) ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < (d / l) * (a + S) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlo : a + S ≤ l * n / d := by
    apply (le_div_iff₀ hd0).mpr
    calc
      (a + S) * d = ((d / l) * (a + S)) * l := by field_simp
      _ ≤ (n : ℝ) * l := mul_le_mul_of_nonneg_right hnlo hl.le
      _ = _ := mul_comm _ _
  have hst : S < t := by linarith [ht.1]
  obtain ⟨v, hv, hsv⟩ := exists_suzukiSignal_ge_positiveDelay L hst
  have hup : u * n / d < (u / l) * a + C := by
    calc
      _ = (u / d) * n := by ring
      _ < (u / d) * ((d / l) * (a + S) + 1) :=
        mul_lt_mul_of_pos_left hnhi (by positivity)
      _ = _ := by dsimp [C]; field_simp; ring
  have hCa : C ≤ (K - u / l) * a := by
    simpa only [mul_comm] using (div_le_iff₀ (by linarith : 0 < K - u / l)).mp haC
  refine ⟨v, ⟨?_, ?_⟩, hp.trans_le hsv⟩
  · linarith [hv.1, ht.1]
  · linarith [hv.2, ht.2]

/-- The exact Legendre signal recovers above its affine correction in
every sufficiently late interval of any fixed ratio greater than one. -/
theorem eventually_exists_suzukiLegendre_recovery_between_arbitrary_time_multiples
    {K : ℝ} (hK : 1 < K) :
    ∀ᶠ a : ℝ in atTop, ∃ u ∈ Icc a (K * a),
      suzukiArchimedeanSlopeConstant * (K * a) + suzukiArchimedeanIntercept <
        suzukiLegendreSignal u := by
  filter_upwards [eventually_exists_pos_suzukiSignal_between_arbitrary_time_multiples hK,
    eventually_ge_atTop (0 : ℝ)] with a ha ha0
  obtain ⟨u, hu, hp⟩ := ha
  refine ⟨u, hu, ?_⟩
  rw [suzukiLegendreSignal_eq_laplace_add_affine (ha0.trans hu.1)]
  have hm := mul_le_mul_of_nonpos_left hu.2 suzukiArchimedeanSlopeConstant_neg.le
  linarith

/-- A deep signed value has a genuine balanced local minimum below it
at a time between `t/K` and `K*t`, for any fixed `K > 1`. The estimate is
unconditional and preserves the original signed value. -/
theorem eventually_suzukiLegendre_deep_value_has_relative_localMin
    {K : ℝ} (hK : 1 < K) :
    ∀ᶠ t : ℝ in atTop,
      suzukiLegendreSignal t <
        suzukiArchimedeanSlopeConstant * (K * t) + suzukiArchimedeanIntercept →
      ∃ r : ℝ, t / K < r ∧ r < K * t ∧
        IsLocalMin suzukiLegendreSignal r ∧ suzukiLegendreSignal r ≤ suzukiLegendreSignal t := by
  have hK0 : 0 < K := by linarith
  have hdiv : Tendsto (fun t : ℝ => t / K) atTop atTop := tendsto_id.atTop_div_const hK0
  have hrec := eventually_exists_suzukiLegendre_recovery_between_arbitrary_time_multiples hK
  filter_upwards [hrec, hdiv.eventually hrec, eventually_ge_atTop (0 : ℝ)] with t hr hl ht0
  intro hdeep
  obtain ⟨a, ha, hJa⟩ := hl
  obtain ⟨b, hb, hJb⟩ := hr
  have hcancel : K * (t / K) = t := by field_simp
  have hat : a ≤ t := by simpa only [hcancel] using ha.2
  have hbt : t ≤ b := hb.1
  have hscale : t ≤ K * t := by nlinarith
  have hcl : suzukiArchimedeanSlopeConstant * (K * t) ≤
      suzukiArchimedeanSlopeConstant * (K * (t / K)) := by
    rw [hcancel]
    exact mul_le_mul_of_nonpos_left hscale suzukiArchimedeanSlopeConstant_neg.le
  have hleft : suzukiLegendreSignal t < suzukiLegendreSignal a := by linarith
  have hright : suzukiLegendreSignal t < suzukiLegendreSignal b := hdeep.trans hJb
  obtain ⟨r, hrab, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a b).Nonempty from ⟨t, hat, hbt⟩) continuous_suzukiLegendreSignal.continuousOn
  have hrt : suzukiLegendreSignal r ≤ suzukiLegendreSignal t := hmin ⟨hat, hbt⟩
  have har : a < r := lt_of_le_of_ne hrab.1 (by intro he; subst r; linarith)
  have hrb : r < b := lt_of_le_of_ne hrab.2 (by intro he; subst r; linarith)
  exact ⟨r, ha.1.trans_lt har, hrb.trans_le hb.2,
    hmin.isLocalMin (Icc_mem_nhds har hrb), hrt⟩

end
end RiemannGaussian
