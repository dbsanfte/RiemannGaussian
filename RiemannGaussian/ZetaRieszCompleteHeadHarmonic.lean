/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompletedCarrier
import RiemannGaussian.HarmonicProductContinuity

/-!
# Explicit harmonic cost of the entire complete prime head

Under the original exposed-zero assumptions, the negative complete head equals minus the full multiplicity square times an explicit harmonic weight, with vanishing error. The whole source still retains all three unpaid prime components and the bounded central block.
-/

namespace RiemannGaussian.ZetaRieszCompleteHeadHarmonic
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedPrimeMoments ZetaRieszMatchedMiddle ZetaRieszPrimeCompletionPhase
open ZetaRieszCompletedCarrier ZetaRieszLowHeadCorrection
open HarmonicProductContinuity

/-- The remaining complete-head cost is an explicit finite harmonic
weight with the original physical length and exact order selection. -/
def headHarmonicWeight (u : ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N) *
    ∑ k ∈ completeHeadOrders N, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ)

/-- The reference head cost is nonnegative at every positive radius. -/
theorem headHarmonicWeight_nonneg {u : ℝ} (hu : 0 < u) (N : ℕ) :
    0 ≤ headHarmonicWeight u N := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  unfold headHarmonicWeight
  positivity

/-- The negative complete head retains both weighted prime phases,
with the whole source prefactor outside one reflected harmonic sum. -/
theorem normalized_completeHead_eq (u y : ℝ) (N : ℕ) (hu : 0 < u) (hN : 256 ≤ N) :
    (u : ℂ) ^ (N + 1) * completeHead u y N =
      ((-(((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N)) : ℝ) : ℂ) *
        ∑ k ∈ completeHeadOrders N,
          (weightedComplete u y (k + 1) * weightedComplete u y (N + 1 - k)) /
            ((N + 1 - k : ℕ) : ℂ) := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  unfold completeHead headArray
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkhalf := completeHeadOrders_le_half N hN k hk
  have hkM : k ≤ N + 1 := by omega
  have hl : 0 < N + 1 - k := by omega
  have he := normalized_head_atom u (SquarefreeVaughanLogSource.length u N)
    ((N + 1 : ℕ) : ℝ) k (N + 1 - k)
    (ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y))
    (ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)) hu.ne' hL.ne' (by omega)
  rw [show k + (N + 1 - k) = N + 1 by omega] at he
  convert! he using 1
  · push_cast
    ring
  · unfold weightedComplete
    push_cast
    ring

/-- Centering at any complex reference preserves its exact squared
phase. The remaining error is the full coupled harmonic product error. -/
theorem normalized_completeHead_centered_eq (u y : ℝ) (N : ℕ) (b : ℂ)
    (hu : 0 < u) (hN : 256 ≤ N) :
    (u : ℂ) ^ (N + 1) * completeHead u y N + b ^ 2 * (headHarmonicWeight u N : ℂ) =
      ((-(((N + 1 : ℕ) : ℝ) / (u * SquarefreeVaughanLogSource.length u N)) : ℝ) : ℂ) *
        ∑ k ∈ completeHeadOrders N,
          (weightedComplete u y (k + 1) * weightedComplete u y (N + 1 - k) - b ^ 2) /
            ((N + 1 - k : ℕ) : ℂ) := by
  rw [normalized_completeHead_eq u y N hu hN]
  simp only [sub_div, Finset.sum_sub_distrib]
  have hs : (∑ k ∈ completeHeadOrders N, b ^ 2 / ((N + 1 - k : ℕ) : ℂ)) =
      b ^ 2 * ((∑ k ∈ completeHeadOrders N, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ)) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  unfold headHarmonicWeight
  push_cast
  ring

/-- The arithmetic part of the entire retained complete head vanishes
after its explicit harmonic cost is subtracted. The full multiplicity
square and all exposed-zero hypotheses remain visible. -/
theorem tendsto_completeHead_centered (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      completeHead (3 / 2 - rho.1.re) rho.1.im N +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (headHarmonicWeight (3 / 2 - rho.1.re) N : ℂ)) atTop (nhds 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  let E : ℕ → ℂ := fun N => ∑ k ∈ completeHeadOrders N,
    (weightedComplete u rho.1.im (k + 1) * weightedComplete u rho.1.im (N + 1 - k) -
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2) / ((N + 1 - k : ℕ) : ℂ)
  have hE : Tendsto E atTop (nhds 0) := by
    have hh := tendsto_harmonic_product_error (weightedComplete u rho.1.im)
      (-(analyticZetaZeroMultiplicity rho : ℂ)) (tendsto_weighted_complete rho hrho hexposed)
      completeHeadOrders (by
        filter_upwards [eventually_ge_atTop 256] with N hN
        exact completeHeadOrders_le_half N hN)
    simpa only [neg_sq] using hh
  apply squeeze_zero_norm' (a := fun N : ℕ => (2 / u) * ‖E N‖) (by
    filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
      (by norm_num : (0 : ℝ) ≤ 2 / 3) huh, eventually_ge_atTop 256] with N hL hN
    rw [normalized_completeHead_centered_eq u rho.1.im N _ hu hN, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hLp := SquarefreeVaughanLogSource.length_pos u N
    rw [Complex.norm_real, norm_neg, Real.norm_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (mul_pos hu hLp) hu).mpr
    have hNc : (256 : ℝ) ≤ N := by exact_mod_cast hN
    have hm : ((N + 1 : ℕ) : ℝ) ≤ 2 * SquarefreeVaughanLogSource.length u N := by
      push_cast
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hm hu.le])
  simpa only [norm_zero, mul_zero] using hE.norm.const_mul (2 / u)

/-- A two-sided arithmetic bound for the whole negative complete head:
only its explicit finite harmonic weight and an arbitrarily small error
remain, rather than an unbounded prime sum. -/
theorem eventually_completeHead_re_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 * headHarmonicWeight (3 / 2 - rho.1.re) N - ε ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          completeHead (3 / 2 - rho.1.re) rho.1.im N).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        completeHead (3 / 2 - rho.1.re) rho.1.im N).re ≤
          -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 * headHarmonicWeight (3 / 2 - rho.1.re) N + ε := by
  have he := (tendsto_completeHead_centered rho hrho hexposed huh).norm
  simp only [norm_zero] at he
  filter_upwards [he.eventually (eventually_lt_nhds hε)] with N hN
  have hr := (Complex.abs_re_le_norm _).trans hN.le
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.mul_im, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero, sub_zero, Complex.ofReal_re] at hr
  simp only [Complex.mul_re]
  constructor <;> linarith [abs_le.mp hr]

/-- The original source now constrains exactly the three unpaid prime
components together with the bounded central block and explicit harmonic
head cost. Every completion error has already been discharged in this chain. -/
theorem tendsto_three_higher_taper_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse 1 (3 / 2 - rho.1.re) rho.1.im N +
       ZetaRieszReflectedCarrier.centralBlock (3 / 2 - rho.1.re) rho.1.im N +
       taperedWing (3 / 2 - rho.1.re) rho.1.im N) -
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (headHarmonicWeight (3 / 2 - rho.1.re) N : ℂ))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_completedCarrier_exposed rho hrho hexposed huh).sub
    (tendsto_completeHead_centered rho hrho hexposed huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_completedCarrier_eq_prime_layers rho.1.im hu huh] with N he
  rw [he]
  ring

end
end RiemannGaussian.ZetaRieszCompleteHeadHarmonic
