/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianSmoothedIdentity
import RiemannGaussian.ZetaStripFiniteSource

/-!
# The original Gaussian prime sum in the complete signed strip bound

The exact Gaussian Euler identity and the full nearby cotangent strip
inequality now share the same actual divisor, center and physical scale.
The rational pole and its smoothing remainder recombine exactly. Every
selected compensated zero remains on the prime side, while the original
signed vertical boundary and the full completion difference remain visible.
Explicit completion and shifted-Poisson allowances are downstream estimates.
These theorems hold at genuine Euler centers with real part greater than one.
-/

namespace RiemannGaussian.ZetaGaussianStripBound
noncomputable section
open Complex
open ZetaGaussianNearCancellation ZetaStripBoundaryConstraint
open CotangentRegularization (frequency)
open scoped Classical

/-- The original Gaussian prime sum and any finite selected source obey the
actual signed strip bound, with the smoothed pole recombined exactly. -/
theorem prime_add_selected_le {σ B η M : ℝ} (hσ : 1 < σ) (hB : 0 < B) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ σ - η) (hhi : σ + η ≤ 3 / 2) (hM : 0 ≤ M)
    (t : ℝ) (S : Finset NontrivialZetaZero) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
        (∑ ρ ∈ S, compensated B η ((σ : ℂ) + I * t) ρ) ≤
      boundary ((σ : ℂ) + I * t) η M +
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1)).re -
        (1 / ((σ : ℂ) + I * t + 1) : ℂ).re +
        (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t) -
          zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re +
        (24 * B / η ^ 2) * (logDeriv riemannXi ((σ : ℂ) + I * t + (η : ℂ))).re := by
  have h := ZetaGaussianSmoothedIdentity.prime_add_selected_le hσ hB hη t S
  have hs := ZetaStripFiniteSource.near_zero_constraint
    (c := (σ : ℂ) + I * t) (by simpa using hσ) hη
      (by simpa using hlo) (by simpa using hhi) hM
  simp only [GaussianLaplacePoleRemainder.remainder, Complex.sub_re] at h hs ⊢
  linarith

/-- The full complex completion error has an explicit Gaussian first-moment
allowance; the signed two-line strip functional is unchanged. -/
theorem prime_add_selected_le_completion_allowance {σ B η M : ℝ}
    (hσ : 1 < σ) (hB : 0 < B) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ σ - η) (hhi : σ + η ≤ 3 / 2) (hM : 0 ≤ M)
    (t : ℝ) (S : Finset NontrivialZetaZero) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
        (∑ ρ ∈ S, compensated B η ((σ : ℂ) + I * t) ρ) ≤
      boundary ((σ : ℂ) + I * t) η M +
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1)).re -
        (1 / ((σ : ℂ) + I * t + 1) : ℂ).re +
        4 * B / GaussianPolynomialTransport.mass B +
        (24 * B / η ^ 2) * (logDeriv riemannXi ((σ : ℂ) + I * t + (η : ℂ))).re := by
  have h := prime_add_selected_le hσ hB hη hlo hhi hM t S
  have hc := ZetaGaussianCompletionAverage.norm_response_sub_center_le hB
    (s := (σ : ℂ) + I * t) (by simpa using (show 0 < σ by linarith))
  have hr := Complex.re_le_norm (ZetaGaussianCompletionAverage.response B ((σ : ℂ) + I * t) -
    zetaGlobalRegularCorrection ((σ : ℂ) + I * t))
  linarith

/-- The original shifted xi response has the same elementary Poisson
allowance at every eligible Euler center, with its true distance from one. -/
theorem re_logDeriv_shift_le {σ η : ℝ} (hσ : 1 < σ) (hη : 0 < η)
    (hsmall : σ + η - 1 ≤ 1 / 4) (t : ℝ) :
    (logDeriv riemannXi ((σ : ℂ) + I * t + (η : ℂ))).re ≤
      ZetaGaussianDistanceRemainder.poissonAllowance (σ + η - 1) t := by
  have h := ZetaGaussianDistanceRemainder.re_logDeriv_shift_le
    (by linarith : 0 < σ + η - 1) hsmall t
  have he : (((1 + (σ + η - 1) : ℝ) : ℂ) + I * t) =
      (σ : ℂ) + I * t + (η : ℂ) := by push_cast; ring
  rwa [he] at h

/-- The complete nearby and distant zero correction is paid by an explicit
allowance. Only the original prime sum and signed strip boundary remain. -/
theorem prime_add_selected_le_poisson_allowance {σ B η M : ℝ}
    (hσ : 1 < σ) (hB : 0 < B) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ σ - η) (hsmall : σ + η - 1 ≤ 1 / 4) (hM : 0 ≤ M)
    (t : ℝ) (S : Finset NontrivialZetaZero) :
    GaussianFermiPrimeComparison.ordinarySum σ B t +
        (∑ ρ ∈ S, compensated B η ((σ : ℂ) + I * t) ρ) ≤
      boundary ((σ : ℂ) + I * t) η M +
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * t - 1)).re -
        (1 / ((σ : ℂ) + I * t + 1) : ℂ).re +
        4 * B / GaussianPolynomialTransport.mass B +
        (24 * B / η ^ 2) * ZetaGaussianDistanceRemainder.poissonAllowance (σ + η - 1) t := by
  have h := prime_add_selected_le_completion_allowance hσ hB hη hlo (by linarith) hM t S
  have hp := mul_le_mul_of_nonneg_left (re_logDeriv_shift_le hσ hη hsmall t)
    (show 0 ≤ 24 * B / η ^ 2 by positivity)
  linarith

/-- At any safe aligned center the selected source keeps its exact Gaussian,
cotangent-minus-pole correction and its own shifted Poisson reserve. -/
theorem compensated_at_ordinate {σ η : ℝ} (hσ : 1 ≤ σ) (hη : 0 < η) (B : ℝ)
    (ρ : NontrivialZetaZero) (hρ : σ - ρ.1.re < η) :
    compensated B η ((σ : ℂ) + I * ρ.1.im) ρ =
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (GaussianFermiLaplaceOrder.halfGaussian B (σ - ρ.1.re) +
          frequency η * Real.cot (frequency η * (σ - ρ.1.re)) - 1 / (σ - ρ.1.re)) +
        (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (σ + η - ρ.1.re)) := by
  have hu : 0 < σ - ρ.1.re := by linarith [NontrivialZetaZero.re_lt_one ρ]
  have he : (σ : ℂ) + I * (ρ.1.im : ℂ) - ρ.1 = ((σ - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hd : ‖(σ : ℂ) + I * (ρ.1.im : ℂ) - ρ.1‖ < η := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact hρ
  have hs : (σ : ℂ) + I * (ρ.1.im : ℂ) + (η : ℂ) = ((σ + η : ℝ) : ℂ) + I * ρ.1.im := by
    push_cast
    ring
  simp only [compensated, nearSource, nearRestrict, hd, if_true,
    ZetaGaussianDistanceRemainder.nearPoisson, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  rw [he, SmoothedCotangentSource.gaussian_source_real hη B hu (by linarith), hs,
    zetaGlobalPoissonSummand_at_ordinate ρ (by linarith : 1 ≤ σ + η)]

/-- The selected half-Gaussian loses only a term linear in its actual
distance from the safe center; its full Poisson reserve remains positive. -/
theorem compensated_at_ordinate_lower {σ η : ℝ} (hσ : 1 ≤ σ) (hη : 0 < η) (B : ℝ)
    (ρ : NontrivialZetaZero) (hρ : σ - ρ.1.re < η) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
        (GaussianFermiLaplaceOrder.halfGaussian B (σ - ρ.1.re) -
          Real.pi ^ 2 * (σ - ρ.1.re) / (8 * η ^ 2)) +
      (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (σ + η - ρ.1.re)) ≤
        compensated B η ((σ : ℂ) + I * ρ.1.im) ρ := by
  rw [compensated_at_ordinate hσ hη B ρ hρ]
  have h := CotangentRegularization.scaled_cot_real_lower hη
    (by linarith [NontrivialZetaZero.re_lt_one ρ] : 0 < σ - ρ.1.re) hρ.le
  apply add_le_add (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) le_rfl
  linarith

/-- An actual nearby zero forces its full Gaussian source into the literal
prime/strip inequality, with every zero-side and completion cost explicit. -/
theorem prime_add_source_le {σ B η M : ℝ} (hσ : 1 < σ) (hB : 0 < B) (hη : 0 < η)
    (hlo : (1 / 2 : ℝ) ≤ σ - η) (hsmall : σ + η - 1 ≤ 1 / 4) (hM : 0 ≤ M)
    (ρ : NontrivialZetaZero) (hρ : σ - ρ.1.re < η) :
    GaussianFermiPrimeComparison.ordinarySum σ B ρ.1.im +
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        (GaussianFermiLaplaceOrder.halfGaussian B (σ - ρ.1.re) -
          Real.pi ^ 2 * (σ - ρ.1.re) / (8 * η ^ 2)) +
      (24 * B / η ^ 2) * ((analyticZetaZeroMultiplicity ρ : ℝ) / (σ + η - ρ.1.re)) ≤
      boundary ((σ : ℂ) + I * ρ.1.im) η M +
        (GaussianComplexHalfMoments.transform B ((σ : ℂ) + I * ρ.1.im - 1)).re -
        (1 / ((σ : ℂ) + I * ρ.1.im + 1) : ℂ).re +
        4 * B / GaussianPolynomialTransport.mass B +
        (24 * B / η ^ 2) *
          ZetaGaussianDistanceRemainder.poissonAllowance (σ + η - 1) ρ.1.im := by
  have h := prime_add_selected_le_poisson_allowance hσ hB hη hlo hsmall hM ρ.1.im {ρ}
  simp only [Finset.sum_singleton] at h
  have hs := compensated_at_ordinate_lower hσ.le hη B ρ hρ
  linarith

end
end RiemannGaussian.ZetaGaussianStripBound
