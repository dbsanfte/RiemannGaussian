import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevQuadratic

/-!
# Discrete drift of the fixed-endpoint Suzuki statistics

The quadratic frontier is expressed through a weighted Chebyshev mass error
and a log-moment error centered at the endpoint.  These statistics are not
independent as the endpoint advances.  A newly admitted von Mangoldt atom is
located exactly at the new logarithmic center, so its direct contribution to
the new centered moment cancels.

This file proves the resulting one-step identity.  The endpoint error changes
by a nonnegative smooth convexity drift minus the previous mass error times
the logarithmic step.  Telescoping this recurrence exposes the precise signed
cumulative work that must be controlled in the entropy or quadratic attack.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Natural-endpoint recurrences -/

/-- Advancing a natural endpoint adds exactly the next Suzuki prime weight to
the weighted Chebyshev mass. -/
theorem suzukiChebyshevWeightedMass_nat_succ (cutoff : ℕ) :
    suzukiChebyshevWeightedMass (((cutoff + 2 : ℕ) : ℝ)) =
      suzukiChebyshevWeightedMass (((cutoff + 1 : ℕ) : ℝ)) +
        suzukiPrimeWeight cutoff := by
  rw [← screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass
      (cutoff + 1),
    ← screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass cutoff,
    screwPrefixMass_succ]

/-- Advancing a natural endpoint adds the next weighted log-location to the
weighted Chebyshev log-moment. -/
theorem suzukiChebyshevWeightedLogMoment_nat_succ (cutoff : ℕ) :
    suzukiChebyshevWeightedLogMoment (((cutoff + 2 : ℕ) : ℝ)) =
      suzukiChebyshevWeightedLogMoment (((cutoff + 1 : ℕ) : ℝ)) +
        suzukiPrimeWeight cutoff * suzukiPrimeLocation cutoff := by
  rw [← screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment
      (cutoff + 1),
    ← screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment cutoff,
    screwPrefixMoment_succ]

/-- The weighted mass error receives the arithmetic atom and loses the exact
increment of its continuous square-root comparison. -/
theorem suzukiChebyshevWeightedMassError_nat_succ (cutoff : ℕ) :
    suzukiChebyshevWeightedMassError (((cutoff + 2 : ℕ) : ℝ)) -
        suzukiChebyshevWeightedMassError (((cutoff + 1 : ℕ) : ℝ)) =
      suzukiPrimeWeight cutoff -
        2 *
          ((((cutoff + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) -
            (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ))) := by
  unfold suzukiChebyshevWeightedMassError
    suzukiChebyshevContinuousMass
  rw [suzukiChebyshevWeightedMass_nat_succ]
  ring

/-! ## Endpoint-error work identity -/

/-- Smooth part of the fixed-endpoint one-step drift. -/
def suzukiChebyshevSmoothEndpointDrift (b c : ℝ) : ℝ :=
  4 * (c ^ (1 / 2 : ℝ) - b ^ (1 / 2 : ℝ)) -
    2 * b ^ (1 / 2 : ℝ) * Real.log (c / b)

/-- Before separating the continuous mass, the endpoint-error increment is
the square-root main increment minus the logarithmic step times arithmetic
mass plus one.  The new endpoint atom cancels exactly. -/
theorem suzukiChebyshevEndpointCenteredError_nat_succ_raw
    (cutoff : ℕ) :
    suzukiChebyshevEndpointCenteredError
          (((cutoff + 2 : ℕ) : ℝ)) -
        suzukiChebyshevEndpointCenteredError
          (((cutoff + 1 : ℕ) : ℝ)) =
      4 *
          ((((cutoff + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) -
            (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ))) -
        Real.log
            (((cutoff + 2 : ℕ) : ℝ) /
              ((cutoff + 1 : ℕ) : ℝ)) *
          (suzukiChebyshevWeightedMass
              (((cutoff + 1 : ℕ) : ℝ)) + 1) := by
  let b : ℝ := ((cutoff + 1 : ℕ) : ℝ)
  let c : ℝ := ((cutoff + 2 : ℕ) : ℝ)
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < cutoff + 1 by omega)
  have hc : 0 < c := by
    dsimp only [c]
    exact_mod_cast (show 0 < cutoff + 2 by omega)
  have hmass := suzukiChebyshevWeightedMass_nat_succ cutoff
  have hmoment := suzukiChebyshevWeightedLogMoment_nat_succ cutoff
  change suzukiChebyshevWeightedMass c =
    suzukiChebyshevWeightedMass b + suzukiPrimeWeight cutoff at hmass
  change suzukiChebyshevWeightedLogMoment c =
    suzukiChebyshevWeightedLogMoment b +
      suzukiPrimeWeight cutoff * suzukiPrimeLocation cutoff at hmoment
  have hlocation : suzukiPrimeLocation cutoff = Real.log c := by
    rfl
  have hlog : Real.log (c / b) = Real.log c - Real.log b :=
    Real.log_div hc.ne' hb.ne'
  change
    suzukiChebyshevEndpointCenteredError c -
        suzukiChebyshevEndpointCenteredError b =
      4 * (c ^ (1 / 2 : ℝ) - b ^ (1 / 2 : ℝ)) -
        Real.log (c / b) * (suzukiChebyshevWeightedMass b + 1)
  unfold suzukiChebyshevEndpointCenteredError
    suzukiChebyshevWeightedLogMomentError
    suzukiChebyshevWeightedMassError
    suzukiChebyshevContinuousLogMoment
    suzukiChebyshevContinuousMass
  rw [hmass, hmoment, hlocation, hlog]
  ring

/-- Exact coupled drift: the fixed-endpoint error gains a smooth convexity
increment and loses logarithmic work against the preceding mass error. -/
theorem suzukiChebyshevEndpointCenteredError_nat_succ
    (cutoff : ℕ) :
    suzukiChebyshevEndpointCenteredError
          (((cutoff + 2 : ℕ) : ℝ)) -
        suzukiChebyshevEndpointCenteredError
          (((cutoff + 1 : ℕ) : ℝ)) =
      suzukiChebyshevSmoothEndpointDrift
          (((cutoff + 1 : ℕ) : ℝ))
          (((cutoff + 2 : ℕ) : ℝ)) -
        Real.log
            (((cutoff + 2 : ℕ) : ℝ) /
              ((cutoff + 1 : ℕ) : ℝ)) *
          suzukiChebyshevWeightedMassError
            (((cutoff + 1 : ℕ) : ℝ)) := by
  rw [suzukiChebyshevEndpointCenteredError_nat_succ_raw]
  unfold suzukiChebyshevSmoothEndpointDrift
    suzukiChebyshevWeightedMassError
    suzukiChebyshevContinuousMass
  ring

/-! ## Positivity of the smooth drift -/

/-- The smooth endpoint drift is nonnegative whenever the positive endpoint
increases.  This is the scalar inequality `log q ≤ q - 1` in square-root
coordinates. -/
theorem suzukiChebyshevSmoothEndpointDrift_nonnegative
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    0 ≤ suzukiChebyshevSmoothEndpointDrift b c := by
  let ratio : ℝ := Real.sqrt (c / b)
  have hratioPos : 0 < ratio := by
    dsimp only [ratio]
    exact Real.sqrt_pos.2 (div_pos hc hb)
  have hlog := Real.log_le_sub_one_of_pos hratioPos
  have hfactor : 0 ≤ (4 : ℝ) * Real.sqrt b :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg b)
  have hscaled := mul_le_mul_of_nonneg_left hlog hfactor
  have hlogRatio : Real.log (c / b) = 2 * Real.log ratio := by
    have hsqrtLog := Real.log_sqrt (div_nonneg hc.le hb.le)
    linarith
  have hscale : Real.sqrt b * ratio = Real.sqrt c := by
    dsimp only [ratio]
    rw [Real.sqrt_div hc.le]
    field_simp [(Real.sqrt_pos.2 hb).ne']
  unfold suzukiChebyshevSmoothEndpointDrift
  simp only [← Real.sqrt_eq_rpow, hlogRatio]
  nlinarith [hscale]

/-- In particular every successive natural-endpoint smooth drift is
nonnegative. -/
theorem suzukiChebyshevSmoothEndpointDrift_nat_succ_nonnegative
    (cutoff : ℕ) :
    0 ≤ suzukiChebyshevSmoothEndpointDrift
      (((cutoff + 1 : ℕ) : ℝ)) (((cutoff + 2 : ℕ) : ℝ)) := by
  apply suzukiChebyshevSmoothEndpointDrift_nonnegative
  · exact_mod_cast (show 0 < cutoff + 1 by omega)
  · exact_mod_cast (show 0 < cutoff + 2 by omega)

/-! ## Telescoping the arithmetic work -/

/-- Net work in advancing the canonical endpoint from `count + 2` to
`count + 3`. -/
def suzukiChebyshevEndpointWork (count : ℕ) : ℝ :=
  suzukiChebyshevSmoothEndpointDrift
      (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ)) -
    Real.log
        ((((count + 3 : ℕ) : ℝ) / ((count + 2 : ℕ) : ℝ))) *
      suzukiChebyshevWeightedMassError (((count + 2 : ℕ) : ℝ))

/-- Cumulative nonnegative smooth drift through the first `count` endpoint
steps. -/
def suzukiChebyshevCumulativeSmoothEndpointDrift (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.range count,
    suzukiChebyshevSmoothEndpointDrift
      (((index + 2 : ℕ) : ℝ)) (((index + 3 : ℕ) : ℝ))

/-- Cumulative signed logarithmic work of the mass error through the first
`count` endpoint steps. -/
def suzukiChebyshevCumulativeMassErrorWork (count : ℕ) : ℝ :=
  ∑ index ∈ Finset.range count,
    Real.log
        ((((index + 3 : ℕ) : ℝ) / ((index + 2 : ℕ) : ℝ))) *
      suzukiChebyshevWeightedMassError (((index + 2 : ℕ) : ℝ))

/-- The endpoint work is exactly the one-step increment of the fixed-center
error along the canonical endpoint sequence. -/
theorem suzukiChebyshevEndpointCenteredError_firstTail_succ
    (count : ℕ) :
    suzukiChebyshevEndpointCenteredError (((count + 3 : ℕ) : ℝ)) -
        suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) =
      suzukiChebyshevEndpointWork count := by
  simpa only [suzukiChebyshevEndpointWork,
    show count + 1 + 1 = count + 2 by omega,
    show count + 1 + 2 = count + 3 by omega] using
      suzukiChebyshevEndpointCenteredError_nat_succ (count + 1)

/-- Exact telescoping formula for the endpoint error. -/
theorem suzukiChebyshevEndpointCenteredError_eq_initial_add_sum_work
    (count : ℕ) :
    suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) =
      suzukiChebyshevEndpointCenteredError 2 +
        ∑ index ∈ Finset.range count,
          suzukiChebyshevEndpointWork index := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Finset.sum_range_succ]
      have hstep :=
        suzukiChebyshevEndpointCenteredError_firstTail_succ count
      change
        suzukiChebyshevEndpointCenteredError (((count + 3 : ℕ) : ℝ)) =
          suzukiChebyshevEndpointCenteredError 2 +
            ((∑ index ∈ Finset.range count,
                suzukiChebyshevEndpointWork index) +
              suzukiChebyshevEndpointWork count)
      calc
        suzukiChebyshevEndpointCenteredError (((count + 3 : ℕ) : ℝ)) =
            suzukiChebyshevEndpointCenteredError
                (((count + 2 : ℕ) : ℝ)) +
              suzukiChebyshevEndpointWork count := by
          linarith
        _ = suzukiChebyshevEndpointCenteredError 2 +
            ((∑ index ∈ Finset.range count,
                suzukiChebyshevEndpointWork index) +
              suzukiChebyshevEndpointWork count) := by
          rw [ih]
          ring

/-- At the first endpoint the centered arithmetic sum vanishes, leaving an
explicit positive smooth margin. -/
theorem suzukiChebyshevEndpointCenteredError_two_eq :
    suzukiChebyshevEndpointCenteredError 2 =
      4 * (2 : ℝ) ^ (1 / 2 : ℝ) - Real.log 2 - 4 := by
  have h := suzukiChebyshevEndpointCenteredError_nat_eq_sum_add_offset 1
  norm_num [suzukiChebyshevCenteredKernel] at h
  exact h

/-- The initial fixed-endpoint margin is strictly positive. -/
theorem suzukiChebyshevEndpointCenteredError_two_pos :
    0 < suzukiChebyshevEndpointCenteredError 2 := by
  rw [suzukiChebyshevEndpointCenteredError_two_eq,
    ← Real.sqrt_eq_rpow]
  have hsqrtSquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtLower : (5 / 4 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hlog : Real.log 2 < (1 : ℝ) := by
    have := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at this ⊢
    exact this
  nlinarith

/-- Expanded cumulative-work formula.  The only signed terms are the prior
mass errors; every smooth drift in the other sum is nonnegative. -/
theorem suzukiChebyshevEndpointCenteredError_eq_initial_add_smooth_sum_sub_massWork
    (count : ℕ) :
    suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) =
      4 * (2 : ℝ) ^ (1 / 2 : ℝ) - Real.log 2 - 4 +
          ∑ index ∈ Finset.range count,
            suzukiChebyshevSmoothEndpointDrift
              (((index + 2 : ℕ) : ℝ)) (((index + 3 : ℕ) : ℝ)) -
        ∑ index ∈ Finset.range count,
          Real.log
              ((((index + 3 : ℕ) : ℝ) / ((index + 2 : ℕ) : ℝ))) *
            suzukiChebyshevWeightedMassError
              (((index + 2 : ℕ) : ℝ)) := by
  rw [suzukiChebyshevEndpointCenteredError_eq_initial_add_sum_work,
    suzukiChebyshevEndpointCenteredError_two_eq]
  simp_rw [suzukiChebyshevEndpointWork]
  rw [Finset.sum_sub_distrib]
  ring

/-- Compact cumulative-work form of the preceding exact identity. -/
theorem suzukiChebyshevEndpointCenteredError_eq_initial_add_cumulativeDrift_sub_work
    (count : ℕ) :
    suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) =
      4 * (2 : ℝ) ^ (1 / 2 : ℝ) - Real.log 2 - 4 +
        suzukiChebyshevCumulativeSmoothEndpointDrift count -
        suzukiChebyshevCumulativeMassErrorWork count := by
  exact
    suzukiChebyshevEndpointCenteredError_eq_initial_add_smooth_sum_sub_massWork
      count

/-- The cumulative smooth endpoint drift is nonnegative. -/
theorem suzukiChebyshevCumulativeSmoothEndpointDrift_nonnegative
    (count : ℕ) :
    0 ≤ suzukiChebyshevCumulativeSmoothEndpointDrift count := by
  unfold suzukiChebyshevCumulativeSmoothEndpointDrift
  exact Finset.sum_nonneg fun index _hindex =>
    suzukiChebyshevSmoothEndpointDrift_nat_succ_nonnegative (index + 1)

/-- If the prior mass error is nonpositive, the one-step endpoint work is
nonnegative. -/
theorem suzukiChebyshevEndpointWork_nonnegative_of_massError_nonpositive
    {count : ℕ}
    (hmass : suzukiChebyshevWeightedMassError
      (((count + 2 : ℕ) : ℝ)) ≤ 0) :
    0 ≤ suzukiChebyshevEndpointWork count := by
  have hdrift :=
    suzukiChebyshevSmoothEndpointDrift_nat_succ_nonnegative (count + 1)
  change 0 ≤ suzukiChebyshevSmoothEndpointDrift
    (((count + 2 : ℕ) : ℝ)) (((count + 3 : ℕ) : ℝ)) at hdrift
  have hratio : (1 : ℝ) ≤
      ((count + 3 : ℕ) : ℝ) / ((count + 2 : ℕ) : ℝ) := by
    have hden : 0 < (((count + 2 : ℕ) : ℝ)) := by positivity
    exact (le_div_iff₀ (a := (1 : ℝ))
      (b := (((count + 3 : ℕ) : ℝ)))
      (c := (((count + 2 : ℕ) : ℝ))) hden).2 (by
        norm_num only [one_mul]
        exact_mod_cast (show count + 2 ≤ count + 3 by omega))
  have hlog : 0 ≤ Real.log
      (((count + 3 : ℕ) : ℝ) / ((count + 2 : ℕ) : ℝ)) :=
    Real.log_nonneg hratio
  unfold suzukiChebyshevEndpointWork
  nlinarith

/-- A block inequality for cumulative mass-error work implies the quadratic
mass--moment premise and therefore literal Suzuki-tail positivity.  The block
inequality itself remains the arithmetic obligation. -/
theorem riemannXiSuzukiPsiNonnegative_on_logTwo_tail_of_cumulativeQuadraticWork
    (hwork : ∀ count : ℕ, 1 ≤ count →
      suzukiChebyshevQuadraticMassCost
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevCumulativeMassErrorWork count ≤
        4 * (2 : ℝ) ^ (1 / 2 : ℝ) - Real.log 2 - 4 +
          suzukiChebyshevCumulativeSmoothEndpointDrift count +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)))) :
    ∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t := by
  apply riemannXiSuzukiPsiNonnegative_on_logTwo_tail_of_quadraticMassMoment
  intro count hcount
  have hblock := hwork count hcount
  have hendpoint :=
    suzukiChebyshevEndpointCenteredError_eq_initial_add_cumulativeDrift_sub_work
      count
  linarith

end

end RiemannGaussian
