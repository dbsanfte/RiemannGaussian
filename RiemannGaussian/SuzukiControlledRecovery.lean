/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaMomentRecovery
import RiemannGaussian.SuzukiPositiveDelayMoments

/-!
# Unconditional recovery times for the actual Suzuki signal

Exact positive delay cancellation and the surviving central double pole
give linearly growing signed gamma moments. The independent weighted-L1
tail estimate localizes a positive delayed value. Positivity of the delay
weights then recovers an actual positive Suzuki value within its finite
backward span.

The conclusion holds at every sufficiently late scale and assumes neither
RH nor an arithmetic floor. It bounds recovery times, not the depths of
the intervening negative excursions.
-/

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

/-- The exact zero-window delay average has signed moments tending to
positive infinity. The positive linear coefficient is the actual negative
Archimedean slope, independent of the chosen height window. -/
theorem tendsto_suzukiZeroWindowDelayGammaMoment_atTop {T : ℝ}
    (hT : (5 : ℝ) / 4 ≤ T) :
    Tendsto (suzukiPositiveDelayGammaMoment (suzukiZeroWindowDelayNodes T)) atTop atTop := by
  obtain ⟨C, _, hC⟩ := exists_suzukiZeroWindowDelayGammaMoment_uniform_error hT
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hl := tendsto_atTop_add_const_right atTop (-C)
    (hn.const_mul_atTop (neg_pos.mpr suzukiArchimedeanSlopeConstant_neg))
  apply tendsto_atTop_mono _ hl
  intro n
  have h := (abs_le.mp (hC n)).1
  nlinarith

private theorem integrable_gamma (L : List ℂ) (n : ℕ) :
    Integrable (fun t : ℝ => suzukiPositiveDelaySignal L t * factorialGammaKernel n t) := by
  apply (integrable_suzukiPositiveDelayGammaMoment L n).congr
  filter_upwards with t
  unfold factorialGammaKernel
  ring

/-- At each sufficiently late moment scale, the exact delayed arithmetic
signal has a positive value in a fixed multiplicative time interval. -/
theorem eventually_exists_pos_suzukiPositiveDelaySignal {T : ℝ}
    (hT : (5 : ℝ) / 4 ≤ T) :
    ∀ᶠ n : ℕ in atTop, ∃ t ∈ Icc ((n : ℝ) / 16) (64 * (n : ℝ)),
      0 < suzukiPositiveDelaySignal (suzukiZeroWindowDelayNodes T) t := by
  apply eventually_exists_pos_in_gammaInterval
    (fun t ht => suzukiPositiveDelaySignal_eq_zero_of_nonpositive _ ht)
    (integrable_suzukiPositiveDelaySignal_real_laplace _ (by norm_num : (1 : ℝ) / 2 < 3 / 4))
    (integrable_gamma _)
  have he : (fun n : ℕ => ∫ t : ℝ,
      suzukiPositiveDelaySignal (suzukiZeroWindowDelayNodes T) t * factorialGammaKernel n t) =
      suzukiPositiveDelayGammaMoment (suzukiZeroWindowDelayNodes T) := by
    funext n
    apply integral_congr_ae
    filter_upwards with t
    unfold factorialGammaKernel
    ring
  rw [he]
  exact tendsto_suzukiZeroWindowDelayGammaMoment_atTop hT

/-- The literal, unaveraged Suzuki signal has positive recovery values in
every sufficiently late interval `[n/32, 64*n]`. This is unconditional. -/
theorem eventually_exists_pos_suzukiSignal_in_controlled_interval :
    ∀ᶠ n : ℕ in atTop, ∃ u ∈ Icc ((n : ℝ) / 32) (64 * (n : ℝ)),
      0 < suzukiChebyshevLogAverageLaplaceSignal u := by
  let L := suzukiZeroWindowDelayNodes 2
  have hpos := eventually_exists_pos_suzukiPositiveDelaySignal (T := 2) (by norm_num)
  have hspan := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_gt_atTop (32 * positiveDelaySpan L))
  filter_upwards [hpos, hspan] with n hn hs
  obtain ⟨t, ht, hh⟩ := hn
  have hst : positiveDelaySpan L < t := by linarith [ht.1, positiveDelaySpan_nonneg L]
  obtain ⟨u, hu, hsu⟩ := exists_suzukiSignal_ge_positiveDelay L hst
  refine ⟨u, ⟨?_, ?_⟩, hh.trans_le hsu⟩
  · linarith [hu.1, ht.1]
  · exact hu.2.trans ht.2

/-- The recovery estimate holds after every sufficiently large real start
time, with a universal multiplicative interval. The constant is deliberately
loose; no coefficient or frequency optimization is used. -/
theorem eventually_exists_pos_suzukiSignal_between_time_multiples :
    ∀ᶠ a : ℝ in atTop, ∃ u ∈ Icc a (4096 * a),
      0 < suzukiChebyshevLogAverageLaplaceSignal u := by
  have hc : Tendsto (fun a : ℝ => Nat.ceil (32 * a)) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 32))
  filter_upwards [hc.eventually eventually_exists_pos_suzukiSignal_in_controlled_interval,
    eventually_ge_atTop (1 : ℝ)] with a ha ha1
  obtain ⟨u, hu, hp⟩ := ha
  have hl := Nat.le_ceil (32 * a)
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 32 * a by positivity)
  refine ⟨u, ⟨?_, ?_⟩, hp⟩
  · linarith [hu.1]
  · linarith [hu.2]

/-- The exact Legendre signal recovers above an explicit linear threshold
within the same controlled interval. This keeps the affine correction
needed when localizing deep excursions to actual balanced minima. -/
theorem eventually_exists_suzukiLegendre_recovery_between_time_multiples :
    ∀ᶠ a : ℝ in atTop, ∃ u ∈ Icc a (4096 * a),
      suzukiArchimedeanSlopeConstant * (4096 * a) + suzukiArchimedeanIntercept <
        suzukiLegendreSignal u := by
  filter_upwards [eventually_exists_pos_suzukiSignal_between_time_multiples,
    eventually_ge_atTop (0 : ℝ)] with a ha ha0
  obtain ⟨u, hu, hp⟩ := ha
  refine ⟨u, hu, ?_⟩
  rw [suzukiLegendreSignal_eq_laplace_add_affine (ha0.trans hu.1)]
  have hm := mul_le_mul_of_nonpos_left hu.2 suzukiArchimedeanSlopeConstant_neg.le
  linarith

end
end RiemannGaussian
