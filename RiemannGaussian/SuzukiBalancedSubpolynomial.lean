/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiControlledRecovery
import RiemannGaussian.SuzukiSubexponentialWork

/-!
# Subpolynomial allowances restricted to actual balanced cells

The unconditional recovery intervals trap each sufficiently deep signed
excursion between two higher endpoints. Its actual local minimum has a
controlled logarithmic time and hence a controlled physical cutoff.
This transports a bound by every positive cutoff power from balanced cells
to the whole signal. The independent arithmetic bound on balanced cells
remains a premise, not a result of the recovery argument.
-/

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

/-- Every sufficiently deep value has an actual local minimum below it
within fixed multiples of its own time. Both the signed value and the
local-minimum property survive the localization. -/
theorem eventually_suzukiLegendre_deep_value_has_controlled_localMin :
    ∀ᶠ t : ℝ in atTop,
      suzukiLegendreSignal t <
        suzukiArchimedeanSlopeConstant * (4096 * t) + suzukiArchimedeanIntercept →
      ∃ r : ℝ, t / 4096 < r ∧ r < 4096 * t ∧
        IsLocalMin suzukiLegendreSignal r ∧ suzukiLegendreSignal r ≤ suzukiLegendreSignal t := by
  have hdiv : Tendsto (fun t : ℝ => t / 4096) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hrec := eventually_exists_suzukiLegendre_recovery_between_time_multiples
  filter_upwards [hrec, hdiv.eventually hrec, eventually_ge_atTop (0 : ℝ)] with t hr hl ht0
  intro hdeep
  obtain ⟨a, ha, hJa⟩ := hl
  obtain ⟨b, hb, hJb⟩ := hr
  have hat : a ≤ t := by linarith [ha.2]
  have hbt : t ≤ b := hb.1
  have hcl : suzukiArchimedeanSlopeConstant * (4096 * t) ≤
      suzukiArchimedeanSlopeConstant * (4096 * (t / 4096)) := by
    apply mul_le_mul_of_nonpos_left _ suzukiArchimedeanSlopeConstant_neg.le
    linarith
  have hleft : suzukiLegendreSignal t < suzukiLegendreSignal a := by linarith
  have hright : suzukiLegendreSignal t < suzukiLegendreSignal b := hdeep.trans hJb
  obtain ⟨r, hrab, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a b).Nonempty from ⟨t, hat, hbt⟩) continuous_suzukiLegendreSignal.continuousOn
  have hrt : suzukiLegendreSignal r ≤ suzukiLegendreSignal t := hmin ⟨hat, hbt⟩
  have har : a < r := lt_of_le_of_ne hrab.1 (by intro he; subst r; linarith)
  have hrb : r < b := lt_of_le_of_ne hrab.2 (by intro he; subst r; linarith)
  exact ⟨r, ha.1.trans_lt har, hrb.trans_le hb.2,
    hmin.isLocalMin (Icc_mem_nhds har hrb), hrt⟩

private theorem affine_le_exp {ε : ℝ} (hε : 0 < ε) (A B : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    A * t + B ≤ (|A| / ε + |B|) * Real.exp (ε * t) := by
  have hlin : t ≤ Real.exp (ε * t) / ε := by
    rw [le_div_iff₀ hε]
    linarith [Real.add_one_le_exp (ε * t)]
  have he : 1 ≤ Real.exp (ε * t) := Real.one_le_exp_iff.mpr (mul_nonneg hε.le ht)
  calc
    A * t + B ≤ |A| * t + |B| :=
      add_le_add (mul_le_mul_of_nonneg_right (le_abs_self A) ht) (le_abs_self B)
    _ ≤ |A| * (Real.exp (ε * t) / ε) + |B| * Real.exp (ε * t) :=
      add_le_add (mul_le_mul_of_nonneg_left hlin (abs_nonneg A))
        (le_mul_of_one_le_right (abs_nonneg B) he)
    _ = _ := by ring

/-- A power floor on sufficiently late balanced cells controls every
sufficiently late signal value. The explicit exponent dilation is the
same fixed time dilation supplied by unconditional recovery. -/
theorem suzukiLegendre_eventually_exp_lower_of_balanced_power_floor
    {δ C : ℝ} (hδ : 0 < δ)
    (hb : ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      -(C * ((count + 2 : ℕ) : ℝ) ^ δ) ≤ suzukiMassLegendrePotential count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in atTop,
      -(D * Real.exp ((4096 * δ) * t)) ≤ suzukiLegendreSignal t := by
  obtain ⟨start, hs⟩ := eventually_atTop.mp hb
  let A := -(4096 * suzukiArchimedeanSlopeConstant)
  let B := -suzukiArchimedeanIntercept
  let D := |C| + |A| / (4096 * δ) + |B|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hδ' : 0 < 4096 * δ := by positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_suzukiLegendre_deep_value_has_controlled_localMin,
    eventually_gt_atTop (4096 * Real.log ((start + 3 : ℕ) : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hmin ht ht0
  by_cases hdeep : suzukiLegendreSignal t <
      suzukiArchimedeanSlopeConstant * (4096 * t) + suzukiArchimedeanIntercept
  · obtain ⟨r, htr, hrt, hlocal, hval⟩ := hmin hdeep
    have hrstart : Real.log ((start + 3 : ℕ) : ℝ) < r := by linarith
    have hr2 : Real.log 2 < r := lt_of_le_of_lt
      (Real.log_le_log (by norm_num) (by norm_cast; omega)) hrstart
    obtain ⟨count, hbal, hl, hu, _, heq⟩ := suzukiLegendreSignal_localMin_balanced hr2 hlocal
    have hc : start ≤ count := by
      have hlog := hrstart.trans_le hu
      have hn : (start + 3 : ℕ) < count + 3 := by
        exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
      omega
    have hpow : ((count + 2 : ℕ) : ℝ) ^ δ ≤ Real.exp ((4096 * δ) * t) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (hl.trans hrt.le) hδ.le]
    have hfloor := hs count hc hbal
    have hCpow := mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((count + 2 : ℕ) : ℝ)) δ)
    have hp := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    have hDge : |C| ≤ D := by
      dsimp [D]
      have hp : 0 ≤ |A| / (4096 * δ) := by positivity
      linarith [abs_nonneg B]
    have hd := mul_le_mul_of_nonneg_right hDge (Real.exp_pos ((4096 * δ) * t)).le
    rw [heq] at hval
    linarith
  · have haf := affine_le_exp hδ' A B ht0
    have hDge : |A| / (4096 * δ) + |B| ≤ D := by
      dsimp [D]
      linarith [abs_nonneg C]
    have hd := mul_le_mul_of_nonneg_right hDge (Real.exp_pos ((4096 * δ) * t)).le
    dsimp [A, B] at haf
    linarith

private theorem global_exp_floor_of_eventual {ε D : ℝ} (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (h : ∀ᶠ t : ℝ in atTop, -(D * Real.exp (ε * t)) ≤ suzukiLegendreSignal t) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 0 < t →
      -(E * Real.exp (ε * t)) ≤ suzukiLegendreSignal t := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  let U := max T 0
  have hU : 0 ≤ U := le_max_right _ _
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc 0 U).Nonempty from ⟨0, le_rfl, hU⟩) continuous_suzukiLegendreSignal.continuousOn
  refine ⟨D + |suzukiLegendreSignal u|, by positivity, fun t ht => ?_⟩
  have he : 1 ≤ Real.exp (ε * t) := Real.one_le_exp_iff.mpr (mul_nonneg hε ht.le)
  by_cases htU : t ≤ U
  · have hmin := hu (show t ∈ Icc 0 U from ⟨ht.le, htU⟩)
    change suzukiLegendreSignal u ≤ suzukiLegendreSignal t at hmin
    have habs := mul_le_mul_of_nonneg_left he (abs_nonneg (suzukiLegendreSignal u))
    nlinarith [neg_abs_le (suzukiLegendreSignal u), mul_nonneg hD (Real.exp_pos (ε * t)).le]
  · have hl := hT t ((le_max_left _ _).trans (le_of_not_ge htU))
    nlinarith [mul_nonneg (abs_nonneg (suzukiLegendreSignal u)) (Real.exp_pos (ε * t)).le]

/-- A subpolynomial lower allowance is needed only on the actual balanced
cells. Controlled recovery absorbs the fixed time dilation into a smaller
positive exponent; continuity absorbs the finite head. The balanced-cell
arithmetic lower bound remains the sole premise. -/
theorem riemannHypothesis_of_suzuki_balanced_potential_eventually_subpolynomial_lower_bound
    (hb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ count : ℕ in atTop,
      SuzukiMassBalancedCell count →
        -(C * ((count + 2 : ℕ) : ℝ) ^ ε) ≤ suzukiMassLegendrePotential count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound
    (a := 1) (by norm_num)
  intro ε hε
  obtain ⟨C, hC⟩ := hb (ε / 4096) (by positivity)
  obtain ⟨D, hD, hd⟩ := suzukiLegendre_eventually_exp_lower_of_balanced_power_floor
    (by positivity : 0 < ε / 4096) hC
  rw [show 4096 * (ε / 4096) = ε by ring] at hd
  obtain ⟨E, hE, he⟩ := global_exp_floor_of_eventual hε.le hD hd
  refine ⟨E + |suzukiArchimedeanIntercept|, by positivity, fun t ht => ?_⟩
  have hj := he t ht
  rw [suzukiLegendreSignal_eq_laplace_add_affine ht.le] at hj
  have he1 : 1 ≤ Real.exp (ε * t) := Real.one_le_exp_iff.mpr (mul_nonneg hε.le ht.le)
  have hc := mul_le_mul_of_nonneg_left he1 (abs_nonneg suzukiArchimedeanIntercept)
  have hs := mul_nonpos_of_nonpos_of_nonneg suzukiArchimedeanSlopeConstant_neg.le ht.le
  simp only [one_mul]
  nlinarith [le_abs_self suzukiArchimedeanIntercept]

/-- A hypothetical right-half zero forces some positive power of negative
excursions on balanced cells themselves. The bad values cannot escape to
unbalanced cutoffs or to uncontrolled recovery times. -/
theorem suzuki_balanced_potential_power_excursions_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, ∃ᶠ count : ℕ in atTop,
      SuzukiMassBalancedCell count ∧
        suzukiMassLegendrePotential count < -(C * ((count + 2 : ℕ) : ℝ) ^ ε) := by
  by_contra hn
  push Not at hn
  have hRH :=
    riemannHypothesis_of_suzuki_balanced_potential_eventually_subpolynomial_lower_bound hn
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

/-- The independent arithmetic task may be stated using the single
literal logarithmic-average error, only at balanced cutoffs. Its affine
centering and full entropy correction are absorbed into each positive
power's constant, without a second arithmetic hypothesis. -/
theorem riemannHypothesis_of_suzuki_balanced_logAverage_eventually_subpolynomial_upper
    (hA : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ count : ℕ in atTop,
      SuzukiMassBalancedCell count →
        suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) ≤
          C * ((count + 2 : ℕ) : ℝ) ^ ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_balanced_potential_eventually_subpolynomial_lower_bound
  intro ε hε
  obtain ⟨C, hC⟩ := hA ε hε
  let E := |-suzukiArchimedeanSlopeConstant| / ε + |-suzukiArchimedeanIntercept|
  refine ⟨C + E + 1, ?_⟩
  filter_upwards [hC] with count hc
  intro hbal
  have hN : (1 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by norm_cast; omega
  have hpow := Real.one_le_rpow hN hε.le
  have hroot : (1 : ℝ) ≤ Real.sqrt ((count + 2 : ℕ) : ℝ) := Real.one_le_sqrt.mpr hN
  have hden : 1 ≤ ((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ) := by nlinarith
  have hent : 1 / (((count + 2 : ℕ) : ℝ) * Real.sqrt ((count + 2 : ℕ) : ℝ)) ≤ 1 :=
    (div_le_one (by positivity)).mpr hden
  have he := affine_le_exp hε (-suzukiArchimedeanSlopeConstant) (-suzukiArchimedeanIntercept)
    (Real.log_nonneg hN)
  have hexp : Real.exp (ε * Real.log ((count + 2 : ℕ) : ℝ)) =
      ((count + 2 : ℕ) : ℝ) ^ ε := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [hexp] at he
  change _ ≤ E * ((count + 2 : ℕ) : ℝ) ^ ε at he
  have hlow := (suzuki_balanced_potential_endpoint_bounds hbal).1
  nlinarith [hc hbal]

end
end RiemannGaussian
