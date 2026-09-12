/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PositiveCosineLaplace
import RiemannGaussian.ZetaGaussianPoleRemainder
import RiemannGaussian.ZetaGlobalPoisson

/-!
# Positive Gaussian Laplace mass of the complete zeta divisor

The all-window cosine theorem supplies the sign of every actual Gaussian
zero contribution on the closed right half-plane. The entire real series
is genuinely summable: it is the complete positive Poisson series plus
the real part of the absolutely convergent complex pole remainder.
An aligned selected zero retains the original half-Gaussian source and
its analytic multiplicity. No smoothed prime identity is assumed here.
-/

namespace RiemannGaussian.ZetaGaussianLaplaceMass
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianComplexHalfMoments GaussianFermiZeroPair

/-- The original pure Gaussian transform is exactly the all-window Laplace carrier. -/
theorem transform_eq_laplace (B : ℝ) (z : ℂ) :
    transform B z = PositiveCosineLaplace.laplace (window B) z := by
  simp only [transform, moment, atom, pow_zero, one_mul, PositiveCosineLaplace.laplace]

/-- Every positive Gaussian scale has nonnegative real transform at every
point of the closed right half-plane, including all imaginary frequencies. -/
theorem transform_re_nonneg {B : ℝ} (hB : 0 < B) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (transform B z).re := by
  rw [transform_eq_laplace]
  apply PositiveCosineLaplace.laplace_re_nonneg (continuous_window B)
    (integrable_window_exp hB) ?_ hz
  intro w hw
  have he : w = (w.im : ℂ) * I := by apply Complex.ext <;> simp [hw]
  rw [he, PositiveCosineLaplace.laplace, integral_half_boundary_re hB]
  positivity

/-- The full real Gaussian contribution of an actual zero, with original multiplicity. -/
def mass (B : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity ρ : ℝ) * (transform B (s - ρ.1)).re

/-- Every actual contribution has a proved favorable sign throughout `Re s ≥ 1`. -/
theorem mass_nonneg {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (ρ : NontrivialZetaZero) : 0 ≤ mass B s ρ :=
  mul_nonneg (Nat.cast_nonneg _) (transform_re_nonneg hB
    (ZetaGaussianPoleRemainder.re_displacement_pos hs ρ).le)

/-- The original Gaussian mass splits into the actual Poisson term and
the real part of the exact complex remainder, before either series is summed. -/
theorem mass_eq_poisson_add_remainder (B : ℝ) (s : ℂ) (ρ : NontrivialZetaZero) :
    mass B s ρ = zetaGlobalPoissonSummand s ρ + (ZetaGaussianPoleRemainder.term B s ρ).re := by
  simp only [mass, zetaGlobalPoissonSummand, ZetaGaussianPoleRemainder.term,
    GaussianLaplacePoleRemainder.remainder, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, Complex.sub_re, one_div, Complex.inv_re]
  ring

/-- The complete Gaussian zero mass is genuinely absolutely summable;
the proof does not split the divergent unpaired complex pole series. -/
theorem summable_mass {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (mass B s) := by
  have hr := Complex.reCLM.summable (ZetaGaussianPoleRemainder.summable_term hB hs)
  exact ((summable_zetaGlobalPoissonSummand hs).add hr).congr
    fun ρ => (mass_eq_poisson_add_remainder B s ρ).symm

/-- The entire real Gaussian divisor mass is exactly the original xi
logarithmic derivative plus the full signed complex smoothing correction. -/
theorem tsum_mass_eq {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' ρ : NontrivialZetaZero, mass B s ρ) = (logDeriv riemannXi s).re +
      (∑' ρ : NontrivialZetaZero, ZetaGaussianPoleRemainder.term B s ρ).re := by
  have hr := ZetaGaussianPoleRemainder.summable_term hB hs
  have hre : Summable (fun ρ : NontrivialZetaZero => (ZetaGaussianPoleRemainder.term B s ρ).re) :=
    Complex.reCLM.summable hr
  simp_rw [mass_eq_poisson_add_remainder]
  rw [(summable_zetaGlobalPoissonSummand hs).tsum_add hre,
    tsum_zetaGlobalPoissonSummand hs, Complex.re_tsum hr]

/-- Any selected finite set consumes its genuine nonnegative portion of
the complete Gaussian mass, with all omitted zero signs discharged. -/
theorem sum_mass_le {B : ℝ} (hB : 0 < B) {s : ℂ} (hs : 1 ≤ s.re)
    (S : Finset NontrivialZetaZero) :
    (∑ ρ ∈ S, mass B s ρ) ≤ ∑' ρ : NontrivialZetaZero, mass B s ρ :=
  (summable_mass hB hs).sum_le_tsum S (fun ρ _ => mass_nonneg hB hs ρ)

/-- At a selected zero's ordinate, the source is exactly its original
real half-Gaussian Laplace value, with no small-angle or pole approximation. -/
theorem mass_at_ordinate (B σ : ℝ) (ρ : NontrivialZetaZero) :
    mass B ((σ : ℂ) + I * ρ.1.im) ρ =
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        GaussianFermiLaplaceOrder.halfGaussian B (σ - ρ.1.re) := by
  have he : (σ : ℂ) + I * ρ.1.im - ρ.1 = ((σ - ρ.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [mass, he, transform_real, Complex.ofReal_re]

/-- The exact selected half-Gaussian source is bounded by the full
nonnegative mass, including on the boundary line `σ = 1`. -/
theorem selected_source_le {B σ : ℝ} (hB : 0 < B) (hσ : 1 ≤ σ)
    (ρ : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity ρ : ℝ) *
      GaussianFermiLaplaceOrder.halfGaussian B (σ - ρ.1.re) ≤
      ∑' τ : NontrivialZetaZero, mass B ((σ : ℂ) + I * ρ.1.im) τ := by
  rw [← mass_at_ordinate]
  have hs : 1 ≤ ((σ : ℂ) + I * ρ.1.im).re := by simpa using hσ
  exact (summable_mass hB hs).le_tsum ρ (fun τ _ => mass_nonneg hB hs τ)

end
end RiemannGaussian.ZetaGaussianLaplaceMass
