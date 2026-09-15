/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompleteHeadHarmonic
import RiemannGaussian.ZetaRieszLengthAsymptotic
import RiemannGaussian.HarmonicIntervalLimit

/-!
# Exact limiting cost of the entire complete prime head

The physical length and actual order endpoints give an explicit harmonic head cost. The head component permits u<=3/5 under exposed-zero hypotheses; the full source keeps its narrower annulus.
-/

namespace RiemannGaussian.ZetaRieszHeadHarmonicAsymptotic
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCompletedCarrier ZetaRieszCompleteHeadHarmonic
open HarmonicIntervalLimit ZetaRieszLengthAsymptotic

/-- The complementary endpoint of the exact completed-head order interval. -/
def complementaryEndpoint (N : ℕ) : ℕ := N - (15 * N + 64) / 32

/-- The actual integer endpoint has an explicit reciprocal-order error;
no continuous endpoint is substituted into the finite head. -/
theorem complementaryEndpoint_ratio_error (N : ℕ) (hN : 256 ≤ N) :
    |(complementaryEndpoint N : ℝ) / (N + 1) - 17 / 32| ≤ 3 / (N + 1) := by
  have hlo : 17 * (N + 1) ≤ 32 * complementaryEndpoint N + 96 := by
    unfold complementaryEndpoint
    omega
  have hhi : 32 * complementaryEndpoint N ≤ 17 * (N + 1) + 96 := by
    unfold complementaryEndpoint
    omega
  have hlor : (17 : ℝ) * (N + 1) ≤ 32 * complementaryEndpoint N + 96 := by
    exact_mod_cast hlo
  have hhir : (32 : ℝ) * complementaryEndpoint N ≤ 17 * (N + 1) + 96 := by
    exact_mod_cast hhi
  have hm : (0 : ℝ) < N + 1 := by positivity
  have hb : |(complementaryEndpoint N : ℝ) - (17 / 32) * (N + 1)| ≤ 3 := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ = |(complementaryEndpoint N : ℝ) - (17 / 32) * (N + 1)| / (N + 1) := by
      rw [show (complementaryEndpoint N : ℝ) / (N + 1) - 17 / 32 =
        ((complementaryEndpoint N : ℝ) - (17 / 32) * (N + 1)) / (N + 1) by
          field_simp, abs_div, abs_of_pos hm]
    _ ≤ _ := div_le_div_of_nonneg_right hb hm.le

/-- The exact complementary endpoint keeps the fraction seventeen
thirty-seconds of the full order in the limit. -/
theorem tendsto_complementaryEndpoint_ratio :
    Tendsto (fun N : ℕ => (complementaryEndpoint N : ℝ) / (N + 1))
      atTop (nhds (17 / 32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun N : ℕ => (complementaryEndpoint N : ℝ) / (N + 1) - 17 / 32)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => (3 : ℝ) / (N + 1)) (by
      filter_upwards [eventually_ge_atTop 256] with N hN
      simpa only [Real.norm_eq_abs] using complementaryEndpoint_ratio_error N hN)
    exact hm.const_div_atTop 3
  convert! he.add_const (17 / 32 : ℝ) using 1
  · funext N
    ring
  · norm_num

/-- The lower harmonic endpoint diverges with the actual integer cutoff. -/
theorem tendsto_complementaryEndpoint_atTop :
    Tendsto complementaryEndpoint atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop (3 * b + 256)] with N hN
  unfold complementaryEndpoint
  omega

/-- The full finite reciprocal head is exactly the difference of its
actual harmonic endpoints, once the structural partition is valid. -/
theorem head_reciprocal_eq_harmonic (N : ℕ) (hN : 256 ≤ N) :
    (∑ k ∈ completeHeadOrders N, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ)) =
      (harmonic (N + 1) : ℝ) - (harmonic (complementaryEndpoint N) : ℝ) := by
  rw [completeHeadOrders_eq_range N hN]
  rw [reversed_harmonic_prefix (N + 1) ((15 * N + 64) / 32) (by omega)]
  have he : N + 1 - (15 * N + 64) / 32 - 1 = complementaryEndpoint N := by
    unfold complementaryEndpoint
    omega
  rw [he]

/-- The entire actual reciprocal head tends to the exact logarithm of
the endpoint ratio, independently of zeros and prime-distribution estimates. -/
theorem tendsto_head_reciprocal :
    Tendsto (fun N : ℕ => ∑ k ∈ completeHeadOrders N,
      (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ)) atTop (nhds (Real.log (32 / 17))) := by
  have hr : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / (complementaryEndpoint N : ℝ))
      atTop (nhds (32 / 17)) := by
    have h := tendsto_complementaryEndpoint_ratio.inv₀ (by norm_num)
    simpa only [inv_div, Nat.cast_add, Nat.cast_one] using h
  have h := tendsto_harmonic_difference (fun N => N + 1) complementaryEndpoint
    (tendsto_add_atTop_nat 1) tendsto_complementaryEndpoint_atTop (by norm_num) hr
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  exact (head_reciprocal_eq_harmonic N hN).symm

/-- The actual harmonic head weight has a fully evaluated analytic
limit, retaining its source radius and the exact order endpoint ratio. -/
theorem tendsto_headHarmonicWeight {u : ℝ} (hu : 0 < u) (huq : u ≤ 3 / 5) :
    Tendsto (headHarmonicWeight u) atTop
      (nhds (Real.log (32 / 17) / (-2 * u * Real.log u))) := by
  have h := (tendsto_head_length_factor hu huq).mul tendsto_head_reciprocal
  unfold headHarmonicWeight
  simpa only [Nat.cast_add, Nat.cast_one, one_div,
    inv_mul_eq_div] using h

/-- The exact length limit pays the centered complete-head error on
the larger component range, without imposing the whole carrier's annular
restriction. The exposed-zero hypotheses are still explicit. -/
theorem tendsto_completeHead_centered_exact_length (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huq : 3 / 2 - rho.1.re ≤ 3 / 5) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      completeHead (3 / 2 - rho.1.re) rho.1.im N +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (headHarmonicWeight (3 / 2 - rho.1.re) N : ℂ)) atTop (nhds 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hE := HarmonicProductContinuity.tendsto_harmonic_product_error
    (ZetaRieszMatchedMiddle.weightedComplete u rho.1.im)
    (-(analyticZetaZeroMultiplicity rho : ℂ))
    (ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed)
    completeHeadOrders (by
      filter_upwards [eventually_ge_atTop 256] with N hN
      exact completeHeadOrders_le_half N hN)
  simp only [neg_sq] at hE
  have hf := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_head_length_factor hu huq).neg
  have h := hf.mul hE
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  have he := normalized_completeHead_centered_eq u rho.1.im N
    (analyticZetaZeroMultiplicity rho : ℂ) hu hN
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using he.symm

/-- The entire negative complete prime head has an exact asymptotic
constant, with unrestricted multiplicity and the actual source radius. -/
theorem tendsto_completeHead_exact_cost (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huq : 3 / 2 - rho.1.re ≤ 3 / 5) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      completeHead (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        ((Real.log (32 / 17) /
          (-2 * (3 / 2 - rho.1.re) * Real.log (3 / 2 - rho.1.re)) : ℝ) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hw := ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_headHarmonicWeight hu huq)).const_mul
    ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
  have h := (tendsto_completeHead_centered_exact_length rho hrho hexposed huq).sub hw
  convert! h using 1
  · funext N
    dsimp only [Function.comp_def]
    ring
  · ring

/-- A two-sided eventual bound with a fully evaluated constant for
the real complete head. No finite-height phase threshold is asserted. -/
theorem eventually_completeHead_exact_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huq : 3 / 2 - rho.1.re ≤ 3 / 5) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
          (Real.log (32 / 17) / (-2 * (3 / 2 - rho.1.re) * Real.log (3 / 2 - rho.1.re))) - ε ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          completeHead (3 / 2 - rho.1.re) rho.1.im N).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completeHead (3 / 2 - rho.1.re) rho.1.im N).re ≤
          -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
            (Real.log (32 / 17) / (-2 * (3 / 2 - rho.1.re) * Real.log (3 / 2 - rho.1.re))) + ε := by
  have h := (Complex.continuous_re.tendsto _).comp
    (tendsto_completeHead_exact_cost rho hrho hexposed huq)
  have he : (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
      ((Real.log (32 / 17) / (-2 * (3 / 2 - rho.1.re) *
        Real.log (3 / 2 - rho.1.re)) : ℝ) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
        (Real.log (32 / 17) / (-2 * (3 / 2 - rho.1.re) *
          Real.log (3 / 2 - rho.1.re))) := by
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero, neg_zero]
  rw [he] at h
  have hn := (h.sub_const (-(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
    (Real.log (32 / 17) / (-2 * (3 / 2 - rho.1.re) *
      Real.log (3 / 2 - rho.1.re))))).norm
  simp only [sub_self, norm_zero] at hn
  filter_upwards [hn.eventually (eventually_lt_nhds hε)] with N hN
  have hb := abs_le.mp (by simpa only [Real.norm_eq_abs] using hN.le)
  dsimp only [Function.comp_def] at hb
  constructor <;> linarith

/-- The full source relation now has a constant head cost. The actual
three-prime, higher-prime and tapered sums still need a joint arithmetic
floor, and the bounded central block is retained rather than discarded. -/
theorem tendsto_three_higher_taper_exact_head (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszReflectedCarrier.centralBlock (3 / 2 - rho.1.re) rho.1.im N +
       taperedWing (3 / 2 - rho.1.re) rho.1.im N))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          ((Real.log (32 / 17) /
            (-2 * (3 / 2 - rho.1.re) * Real.log (3 / 2 - rho.1.re)) : ℝ) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hw := ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_headHarmonicWeight hu
      (ZetaRieszHeadAdaptive.annular_radius_le_three_fifths huh))).const_mul
        ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
  have h := (tendsto_three_higher_taper_budget rho hrho hexposed huh).add hw
  convert! h using 1
  funext N
  dsimp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszHeadHarmonicAsymptotic
