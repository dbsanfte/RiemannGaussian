/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeGaussianBand
import RiemannGaussian.ZetaSquarefreeEulerFamilyDecay

/-!
# Uniform arithmetic decay throughout the explicit Gaussian height band

The actual compact quotient tube supplies one arithmetic constant and one
starting order for every center in the proved height band. A full quadratic
prime sieve is allowed. Exact logarithmic transport and the complete lcm
matrix retain every complex coefficient before their total masses are paid.
Ordinary primes are included in this response; its decay does not provide
an independent bound for the separately isolated ordinary-prime tail.
-/

namespace RiemannGaussian.SquarefreeGaussianBand
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The complete quadratic-sieve response has one constant and one
starting order uniform throughout the actual explicit height band. Every
prime subset, natural mark and complex polynomial is covered. -/
theorem exists_uniform_sieve_bound (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y ∈ ordinateBand, ∀ S : Finset ℕ,
        (∀ a ∈ S, a.Prime ∧ a ≤ R N) → ∀ (P : ℕ) (p : Polynomial ℂ),
          ‖RoughSquarefreeBare.response p S P N (3 / 2 + I * y)‖ ≤
            C * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
              ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_quotient_bound
  exact exists_squarefreeEuler_uniform_quadratic_sieve_bound_of_analytic
    ordinateBand radius M radius_bounds.1 (by linarith [radius_bounds.2]) hM
    (fun _ hy ↦ analyticOnNhd_response hy) hb R hR hcut

/-- The physical logarithm costs only its proved linear moment factor,
uniformly in the center as well as every arithmetic mark and polynomial. -/
theorem exists_uniform_log_bound (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y ∈ ordinateBand, ∀ S : Finset ℕ,
        (∀ a ∈ S, a.Prime ∧ a ≤ R N) → ∀ (P : ℕ) (p : Polynomial ℂ),
          ‖SquarefreeEulerLog.response p S P N (3 / 2 + I * y)‖ ≤
            C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
              ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_sieve_bound R hR hcut
  refine ⟨C, hC, hb.mono ?_⟩
  intro N hN y hy S hS P p
  rw [SquarefreeEulerLog.response_eq_raised]
  exact (hN y hy S hS P (Polynomial.X * SquarefreeEulerLog.raisedPolynomial p N)).trans
    ((mul_le_mul_of_nonneg_left (SquarefreeEulerLog.raisedPolynomial_envelope_le p N)
      (by positivity)).trans_eq (by ring))

/-- The whole logarithmic divisor matrix has one independent bound
throughout the actual height band. Both complete coefficient masses are
paid after the exact convergent lcm expansion, with all cross terms present. -/
theorem exists_uniform_family_bound (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ y ∈ ordinateBand, ∀ S : Finset ℕ,
        (∀ a ∈ S, a.Prime ∧ a ≤ R N) →
        ∀ (T : Finset ℕ) (w v : ℕ → ℂ) (p : Polynomial ℂ),
          ‖SquarefreeEulerQuadratic.logResponse p S T w v N (3 / 2 + I * y)‖ ≤
            C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
              (∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖) *
                (∑ d ∈ T, ‖w d‖) * (∑ e ∈ T, ‖v e‖) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_log_bound R hR hcut
  refine ⟨C, hC, hb.mono ?_⟩
  intro N hN y hy S hS T w v p
  let A := C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
    ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖
  rw [SquarefreeEulerQuadratic.logResponse_eq_lcm_sum p S T
    (fun a ha ↦ (hS a ha).1) w v N (by norm_num)]
  calc
    _ ≤ ∑ d ∈ T, ∑ e ∈ T, ‖w d‖ * ‖v e‖ * A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hN y hy S hS (Nat.lcm d e) p) (by positivity)
    _ = ∑ d ∈ T, ‖w d‖ * ((∑ e ∈ T, ‖v e‖) * A) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ ↦ by ring)
    _ = (∑ d ∈ T, ‖w d‖) * ((∑ e ∈ T, ‖v e‖) * A) := (Finset.sum_mul ..).symm
    _ = _ := by dsimp [A]; ring

/-- Arbitrary moving ordinates, sieves, divisor families and polynomial
filters inherit decay when their complete normalized mass stays bounded.
No fixed center or coefficient choice is hidden in the conclusion. -/
theorem tendsto_family_of_mass_budget (R : ℕ → ℕ) (hR : Tendsto R atTop atTop)
    (hcut : ∀ᶠ N in atTop, Real.sqrt (R N) ≤ (N : ℝ) / 40)
    (y : ℕ → ℝ) (hy : ∀ᶠ N in atTop, y N ∈ ordinateBand)
    (S T : ℕ → Finset ℕ) (hS : ∀ N a, a ∈ S N → a.Prime ∧ a ≤ R N)
    (w v : ℕ → ℕ → ℂ) (p : ℕ → Polynomial ℂ) (scale : ℕ → ℂ) (B : ℝ)
    (hbudget : ∀ᶠ N in atTop,
      ‖scale N‖ * (∑ k ∈ (p N).support, (k + 1 : ℝ) * ‖(p N).coeff k‖) *
        (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖) ≤ B) :
    Tendsto (fun N ↦ scale N *
      SquarefreeEulerQuadratic.logResponse (p N) (S N) (T N) (w N) (v N) N
        (3 / 2 + I * y N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_family_bound R hR hcut
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖scale N * SquarefreeEulerQuadratic.logResponse (p N) (S N) (T N) (w N) (v N) N
        (3 / 2 + I * y N)‖ ≤
          (C * B) * ((N + 1 : ℝ) *
            Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ)))) := by
    filter_upwards [hb, hy, hbudget] with N hN hy hbudget
    let E := ∑ k ∈ (p N).support, (k + 1 : ℝ) * ‖(p N).coeff k‖
    rw [norm_mul]
    calc
      _ ≤ ‖scale N‖ * (C * (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))) *
          E * (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖)) :=
        mul_le_mul_of_nonneg_left (hN (y N) hy (S N) (hS N) (T N) (w N) (v N) (p N))
          (norm_nonneg _)
      _ = (C * ((N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))))) *
          (‖scale N‖ * E * (∑ d ∈ T N, ‖w N d‖) * (∑ e ∈ T N, ‖v N e‖)) := by ring
      _ ≤ (C * ((N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (R N + 2 : ℝ))))) * B :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by ring
  apply squeeze_zero_norm' hbound
  simpa using (SquarefreeEulerLog.tendsto_quadratic_sieve_log_allowance R hcut).const_mul (C * B)

/-- A single quadratic prime ceiling containing every original
right-half-zero sieve, independently of the selected zero. -/
def primeCeiling (N : ℕ) : ℕ := (N / 40) ^ 2

/-- The common prime ceiling grows without a zero-dependent slope. -/
theorem primeCeiling_atTop : Tendsto primeCeiling atTop atTop := by
  apply tendsto_atTop.2
  intro b
  refine eventually_atTop.mpr ⟨40 * b, ?_⟩
  intro N hN
  have hb : b ≤ N / 40 := by omega
  unfold primeCeiling
  by_cases h : N / 40 = 0
  · simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hb
  · have hp : 1 ≤ N / 40 := by omega
    nlinarith

/-- Integer rounding preserves the exact quadratic-sieve allowance. -/
theorem primeCeiling_sqrt_le (N : ℕ) : Real.sqrt (primeCeiling N) ≤ (N : ℝ) / 40 := by
  rw [primeCeiling, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  have h : ((N / 40 : ℕ) : ℝ) * 40 ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N 40
  linarith

/-- Every selected-zero sieve fits the common ceiling, even when the
selected zero changes and its own sieve cutoff need not tend to infinity. -/
theorem actual_primeCutoff_le (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) (N : ℕ) :
    zetaRightHalfPrimePatternCutoff ρ N ≤ primeCeiling N := by
  have h := sqrt_zetaRightHalfPrimePatternCutoff_le ρ hρ N
  rw [zetaRightHalfPrimePatternCutoff, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)] at h
  have hm : 40 * ⌊zetaRightHalfPrimePatternSlope ρ * N⌋₊ ≤ N := by
    exact_mod_cast (show (40 : ℝ) * ⌊zetaRightHalfPrimePatternSlope ρ * N⌋₊ ≤ N by linarith)
  have hb : ⌊zetaRightHalfPrimePatternSlope ρ * N⌋₊ ≤ N / 40 := by omega
  unfold zetaRightHalfPrimePatternCutoff primeCeiling
  gcongr

/-- The common vanishing allowance after paying the physical logarithm,
with the full quadratic prime ceiling and all integer rounding retained. -/
def matrixAllowance (N : ℕ) : ℝ :=
  (N + 1 : ℝ) * Real.exp (-(N : ℝ) / (20 * Real.log (primeCeiling N + 2 : ℝ)))

/-- The same arithmetic allowance tends to zero independently of every
selected zero, center, mark and divisor coefficient family. -/
theorem matrixAllowance_tendsto_zero : Tendsto matrixAllowance atTop (𝓝 0) :=
  SquarefreeEulerLog.tendsto_quadratic_sieve_log_allowance primeCeiling
    (Eventually.of_forall primeCeiling_sqrt_le)

/-- The actual source normalization pays every ordered divisor pair
through the squared cutoff. One constant and one starting order now
work for every right-half zero in the explicit ordinate band, all bounded
complex divisor weights, and all filters with their full envelope retained. -/
theorem exists_uniform_normalized_matrix_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ ρ : NontrivialZetaZero, 1 / 2 < ρ.1.re → ρ.1.im ∈ ordinateBand →
        ∀ (D : ℕ) (w v : ℕ → ℂ) (p : Polynomial ℂ),
          D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - ρ.1.re)) N) ^ 2 →
          (∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1) →
          (∀ e ∈ Finset.Icc 1 D, ‖v e‖ ≤ 1) →
          ‖SquarefreeEulerQuadratic.normalizedLogResponse ρ p N D w v‖ ≤
            C * matrixAllowance N *
                ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_family_bound primeCeiling primeCeiling_atTop
    (Eventually.of_forall primeCeiling_sqrt_le)
  refine ⟨C, hC, hb.mono ?_⟩
  intro N hN ρ hρ hy D w v p hD hw hv
  let u : ℝ := 3 / 2 - ρ.1.re
  have hu : 0 < u := by dsimp [u]; linarith [ρ.re_lt_one]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hS : ∀ a ∈ zetaRightHalfPrimePatternPrimes ρ N, a.Prime ∧ a ≤ primeCeiling N := by
    intro a ha
    have h := zetaRightHalfPrimePatternPrimes_eligible ρ N a ha
    exact ⟨h.1, h.2.trans (actual_primeCutoff_le ρ hρ N)⟩
  have hbudget : u ^ (N + 1) *
      (∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖) ≤ 1 := by
    rw [mul_assoc]
    exact ((mul_le_mul_of_nonneg_left
      (RoughDivisorCorrelation.mass_budget_of_norm_le_one D w v hw hv)
      (by positivity)).trans
        (SquarefreeEulerQuadratic.source_pair_count_bound hu N D hD)).trans hu1
  let A := C * ((N + 1 : ℝ) *
    Real.exp (-(N : ℝ) / (20 * Real.log (primeCeiling N + 2 : ℝ)))) *
      ∑ k ∈ p.support, (k + 1 : ℝ) * ‖p.coeff k‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [SquarefreeEulerQuadratic.normalizedLogResponse, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (A * (∑ d ∈ Finset.Icc 1 D, ‖w d‖) *
        (∑ e ∈ Finset.Icc 1 D, ‖v e‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [A, mul_assoc] using
        hN ρ.1.im hy (zetaRightHalfPrimePatternPrimes ρ N) hS (Finset.Icc 1 D) w v p
    _ = A * (u ^ (N + 1) * (∑ d ∈ Finset.Icc 1 D, ‖w d‖) *
        (∑ e ∈ Finset.Icc 1 D, ‖v e‖)) := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hbudget hA
    _ = _ := by rw [mul_one]; rfl

/-- Actual normalized divisor responses decay even when the selected
zero, complex weights, cutoff and polynomial change with the order.
Only the explicit coefficient envelope is bounded; no fixed-zero Cauchy
constant or lower growth assumption on its own prime sieve remains. -/
theorem tendsto_moving_normalized_matrix (ρ : ℕ → NontrivialZetaZero)
    (hρ : ∀ N, 1 / 2 < (ρ N).1.re) (hy : ∀ᶠ N in atTop, (ρ N).1.im ∈ ordinateBand)
    (D : ℕ → ℕ) (w v : ℕ → ℕ → ℂ)
    (hD : ∀ᶠ N in atTop,
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - (ρ N).1.re)) N) ^ 2 ∧
        (∀ d ∈ Finset.Icc 1 (D N), ‖w N d‖ ≤ 1) ∧
        (∀ e ∈ Finset.Icc 1 (D N), ‖v N e‖ ≤ 1))
    (p : ℕ → Polynomial ℂ) (B : ℝ)
    (hp : ∀ᶠ N in atTop, ∑ k ∈ (p N).support, (k + 1 : ℝ) * ‖(p N).coeff k‖ ≤ B) :
    Tendsto (fun N ↦ SquarefreeEulerQuadratic.normalizedLogResponse
      (ρ N) (p N) N (D N) (w N) (v N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_matrix_bound
  have hbound : ∀ᶠ N in atTop,
      ‖SquarefreeEulerQuadratic.normalizedLogResponse (ρ N) (p N) N (D N) (w N) (v N)‖ ≤
        (C * B) * matrixAllowance N := by
    filter_upwards [hb, hy, hD, hp] with N hN hy hD hp
    exact (hN (ρ N) (hρ N) hy (D N) (w N) (v N) (p N) hD.1 hD.2.1 hD.2.2).trans
      ((mul_le_mul_of_nonneg_left hp (by unfold matrixAllowance; positivity)).trans_eq (by ring))
  apply squeeze_zero_norm' hbound
  simpa using matrixAllowance_tendsto_zero.const_mul (C * B)

/-- The original full Möbius square inherits the moving-zero theorem
with its weight premises discharged by the actual arithmetic function.
Ordinary primes remain included; their isolated signed tail is separate. -/
theorem tendsto_moving_moebius_matrix (ρ : ℕ → NontrivialZetaZero)
    (hρ : ∀ N, 1 / 2 < (ρ N).1.re) (hy : ∀ᶠ N in atTop, (ρ N).1.im ∈ ordinateBand)
    (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop,
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - (ρ N).1.re)) N) ^ 2)
    (p : ℕ → Polynomial ℂ) (B : ℝ)
    (hp : ∀ᶠ N in atTop, ∑ k ∈ (p N).support, (k + 1 : ℝ) * ‖(p N).coeff k‖ ≤ B) :
    Tendsto (fun N ↦ SquarefreeEulerQuadratic.normalizedLogResponse
      (ρ N) (p N) N (D N)
      (fun d ↦ (ArithmeticFunction.moebius d : ℂ))
      (fun d ↦ (ArithmeticFunction.moebius d : ℂ))) atTop (𝓝 0) := by
  have hm (d : ℕ) : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  exact tendsto_moving_normalized_matrix ρ hρ hy D
    (fun _ d ↦ (ArithmeticFunction.moebius d : ℂ))
    (fun _ d ↦ (ArithmeticFunction.moebius d : ℂ))
    (hD.mono (fun _ h ↦ ⟨h, fun d _ ↦ hm d, fun d _ ↦ hm d⟩)) p B hp

end
end RiemannGaussian.SquarefreeGaussianBand
