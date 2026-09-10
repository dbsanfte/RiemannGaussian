/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiRelativeRecovery
import RiemannGaussian.SuzukiBalancedSubpolynomial

/-!
# Balanced-cell transfer with arbitrarily small exponent loss

Unconditional relative recovery traps every deep signed value near an
actual balanced minimum. A floor of order `N^δ` on balanced cells therefore
gives a signal floor of order `exp(ε*t)` for every `ε > δ`. The previous
fixed factor 4096 in the transferred exponent is unnecessary.

The balanced-cell arithmetic floor is still a hypothesis. The new input
proved independently is the arbitrarily close relative recovery estimate,
not a bound on negative excursion depth.
-/

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

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

/-- A balanced-cell power floor transfers using any prescribed time
ratio greater than one. All localization and finite-cutoff conditions are
discharged by the actual signal's unconditional relative recovery. -/
theorem suzukiLegendre_eventually_exp_lower_of_balanced_power_floor_ratio
    {K δ C : ℝ} (hK : 1 < K) (hδ : 0 < δ)
    (hb : ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      -(C * ((count + 2 : ℕ) : ℝ) ^ δ) ≤ suzukiMassLegendrePotential count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in atTop,
      -(D * Real.exp ((K * δ) * t)) ≤ suzukiLegendreSignal t := by
  obtain ⟨start, hs⟩ := eventually_atTop.mp hb
  let A := -(K * suzukiArchimedeanSlopeConstant)
  let B := -suzukiArchimedeanIntercept
  let D := |C| + |A| / (K * δ) + |B|
  have hK0 : 0 < K := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hδ' : 0 < K * δ := by positivity
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_suzukiLegendre_deep_value_has_relative_localMin hK,
    eventually_gt_atTop (K * Real.log ((start + 3 : ℕ) : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hmin ht ht0
  by_cases hdeep : suzukiLegendreSignal t <
      suzukiArchimedeanSlopeConstant * (K * t) + suzukiArchimedeanIntercept
  · obtain ⟨r, htr, hrt, hlocal, hval⟩ := hmin hdeep
    have hrstart : Real.log ((start + 3 : ℕ) : ℝ) < r := by
      have hh := (div_lt_iff₀ hK0).mp htr
      nlinarith
    have hr2 : Real.log 2 < r := lt_of_le_of_lt
      (Real.log_le_log (by norm_num) (by norm_cast; omega)) hrstart
    obtain ⟨count, hbal, hl, hu, _, heq⟩ := suzukiLegendreSignal_localMin_balanced hr2 hlocal
    have hc : start ≤ count := by
      have hlog := hrstart.trans_le hu
      have hn : (start + 3 : ℕ) < count + 3 := by
        exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
      omega
    have hpow : ((count + 2 : ℕ) : ℝ) ^ δ ≤ Real.exp ((K * δ) * t) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (hl.trans hrt.le) hδ.le]
    have hfloor := hs count hc hbal
    have hCpow := mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((count + 2 : ℕ) : ℝ)) δ)
    have hp := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    have hDge : |C| ≤ D := by
      dsimp [D]
      have hp : 0 ≤ |A| / (K * δ) := by positivity
      linarith [abs_nonneg B]
    have hd := mul_le_mul_of_nonneg_right hDge (Real.exp_pos ((K * δ) * t)).le
    rw [heq] at hval
    linarith
  · have haf := affine_le_exp hδ' A B ht0
    have hDge : |A| / (K * δ) + |B| ≤ D := by
      dsimp [D]
      linarith [abs_nonneg C]
    have hd := mul_le_mul_of_nonneg_right hDge (Real.exp_pos ((K * δ) * t)).le
    dsimp [A, B] at haf
    linarith

/-- A balanced-cell floor of order `N^δ` gives a global eventual signal
floor of order `exp(ε*t)` for every `ε > δ`. No fixed multiplicative loss
in the exponent remains. The independent arithmetic floor stays explicit. -/
theorem suzukiLegendre_eventually_exp_lower_of_balanced_power_floor_arbitrarily_small_loss
    {δ ε C : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hb : ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      -(C * ((count + 2 : ℕ) : ℝ) ^ δ) ≤ suzukiMassLegendrePotential count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in atTop,
      -(D * Real.exp (ε * t)) ≤ suzukiLegendreSignal t := by
  have hratio : (1 : ℝ) < ε / δ := (lt_div_iff₀ hδ).mpr (by simpa using hδε)
  obtain ⟨K, hK, hKe⟩ := exists_between hratio
  have hKd : K * δ < ε := (lt_div_iff₀ hδ).mp hKe
  obtain ⟨D, hD, hd⟩ := suzukiLegendre_eventually_exp_lower_of_balanced_power_floor_ratio hK hδ hb
  refine ⟨D, hD, ?_⟩
  filter_upwards [hd, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have he := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKd.le ht0)) hD
  linarith

/-- The same arbitrarily small exponent loss holds for the literal Suzuki
Laplace signal. Its complete affine correction is absorbed explicitly;
the balanced-cell arithmetic floor remains the only unproved input. -/
theorem suzukiSignal_eventually_exp_lower_of_balanced_power_floor_arbitrarily_small_loss
    {δ ε C : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    (hb : ∀ᶠ count : ℕ in atTop, SuzukiMassBalancedCell count →
      -(C * ((count + 2 : ℕ) : ℝ) ^ δ) ≤ suzukiMassLegendrePotential count) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ t : ℝ in atTop,
      -(D * Real.exp (ε * t)) ≤ suzukiChebyshevLogAverageLaplaceSignal t := by
  obtain ⟨D, hD, hd⟩ :=
    suzukiLegendre_eventually_exp_lower_of_balanced_power_floor_arbitrarily_small_loss hδ hδε hb
  refine ⟨D + |suzukiArchimedeanIntercept|, by positivity, ?_⟩
  filter_upwards [hd, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  rw [suzukiLegendreSignal_eq_laplace_add_affine ht0] at ht
  have he : 1 ≤ Real.exp (ε * t) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (hδ.trans hδε).le ht0)
  have hc := mul_le_mul_of_nonneg_left he (abs_nonneg suzukiArchimedeanIntercept)
  have hs := mul_nonpos_of_nonpos_of_nonneg suzukiArchimedeanSlopeConstant_neg.le ht0
  nlinarith [le_abs_self suzukiArchimedeanIntercept]

end
end RiemannGaussian
