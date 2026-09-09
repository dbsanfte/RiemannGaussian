/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiCarrierArithmeticDensity

/-!
# The signed boundary phase inside Suzuki's Gram

On the real axis, the carrier `C = i*(1+Theta)/2` lies on the circle
`normSq C = im C` away from zeros of its denominator. The exceptional
points form a null set. Thus the genuine quadratic carrier Gram has an
exact representation through the signed difference `C - conj C`.

The two boundary channels remain together inside the integrable quotient;
their separate integrability is not assumed. This retains information for
the global signed Suzuki problem, without asserting an arithmetic floor
or moving a contour through unknown poles.
-/

open Complex MeasureTheory Set Filter
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

/-- Away from a zero of the de Branges denominator, the carrier's
imaginary component is its full squared norm, rather than just a bound. -/
theorem suzukiXiRealAxisCarrierDensity_eq_im {x : ℝ}
    (hE : suzukiXiEValue (x : ℂ) ≠ 0) :
    suzukiXiRealAxisCarrierDensity x = (suzukiRealAxisXiZeroCarrier x).im := by
  rw [suzukiXiRealAxisCarrierDensity_eq_ratio_of_E_ne_zero x hE]
  change _ = (suzukiXiZeroCarrier (x : ℂ)).im
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE]
  simp only [Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    riemannXiSpectral_ofReal_im, sub_zero, mul_zero,
    suzukiXiEValue_ofReal_re]
  rw [← Complex.sq_norm, norm_sq_suzukiXiEValue_ofReal]
  ring

/-- Every exceptional real denominator zero is a spectral xi zero.
The entire exceptional set is countable, without a simplicity assumption. -/
theorem countable_suzukiXiEValue_real_zeros :
    {x : ℝ | suzukiXiEValue (x : ℂ) = 0}.Countable := by
  apply (Set.countable_range (fun rho : NontrivialZetaZero ↦
    (zetaSpectralCoordinate rho.1).re)).mono
  intro x hx
  have hre : (riemannXiSpectral (x : ℂ)).re = 0 := by
    rw [← suzukiXiEValue_ofReal_re, hx]
    rfl
  have hz : riemannXiSpectral (x : ℂ) = 0 :=
    Complex.ext hre (riemannXiSpectral_ofReal_im x)
  obtain ⟨rho, hrho⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero (x : ℂ)).mp hz
  exact ⟨rho, (congrArg Complex.re hrho).symm⟩

/-- The exceptional denominator zeros have zero Lebesgue measure. -/
theorem ae_suzukiXiEValue_ofReal_ne_zero :
    ∀ᵐ x : ℝ, suzukiXiEValue (x : ℂ) ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not] using
    countable_suzukiXiEValue_real_zeros.measure_zero (volume : Measure ℝ)

/-- The circle law holds almost everywhere for the literal carrier,
including its already defined totalized values at exceptional points. -/
theorem suzukiXiRealAxisCarrierDensity_ae_eq_im :
    suzukiXiRealAxisCarrierDensity =ᵐ[volume]
      fun x ↦ (suzukiRealAxisXiZeroCarrier x).im := by
  filter_upwards [ae_suzukiXiEValue_ofReal_ne_zero] with x hx
  exact suzukiXiRealAxisCarrierDensity_eq_im hx

/-- The full quadratic carrier numerator is the signed difference of
its two boundary phases. Neither phase is replaced by its absolute value. -/
theorem suzukiRealAxisXiZeroCarrier_ae_quadratic_eq_signed :
    (fun x : ℝ ↦ starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x) *
      suzukiRealAxisXiZeroCarrier x) =ᵐ[volume]
      fun x ↦ (suzukiRealAxisXiZeroCarrier x -
        starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) / (2 * I) := by
  filter_upwards [suzukiXiRealAxisCarrierDensity_ae_eq_im] with x hx
  change ‖suzukiRealAxisXiZeroCarrier x‖ ^ 2 = _ at hx
  rw [Complex.sq_norm, Complex.normSq_apply] at hx
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> nlinarith only [hx]

/-- The genuine common-carrier Gram is exactly the integral of a signed
two-channel quotient. This identity is unconditional and preserves all
mixed nodes, their orientations and their possible real positions. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_signed_integral
    (rho sigma : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      ∫ x : ℝ, (suzukiRealAxisXiZeroCarrier x -
        starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) /
          ((2 * I) * (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
            ((x : ℂ) - zetaSpectralCoordinate sigma.1))) := by
  apply integral_congr_ae
  filter_upwards [suzukiRealAxisXiZeroCarrier_ae_quadratic_eq_signed] with x hx
  unfold suzukiXiBoundaryCarrierGramIntegrand
  rw [hx, div_div]

/-- The complete signed quotient is genuinely integrable, even when
one cannot integrate its two channels separately at real divisor points. -/
theorem integrable_suzukiXiBoundaryCarrier_signed_integrand
    (rho sigma : NontrivialZetaZero) :
    Integrable (fun x : ℝ ↦ (suzukiRealAxisXiZeroCarrier x -
      starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) /
        ((2 * I) * (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          ((x : ℂ) - zetaSpectralCoordinate sigma.1)))) := by
  apply (integrable_suzukiXiBoundaryCarrierGramIntegrand rho sigma).congr
  filter_upwards [suzukiRealAxisXiZeroCarrier_ae_quadratic_eq_signed] with x hx
  unfold suzukiXiBoundaryCarrierGramIntegrand
  rw [hx, div_div]

/-- The signed phase integrand for the complete two-time arithmetic signal.
Both arithmetic factors contain the full prime, pole and gamma contributions. -/
def suzukiArithmeticPhaseGramIntegrand (t u x : ℝ) : ℂ :=
  (suzukiRealAxisXiZeroCarrier x -
      starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) / (2 * I) *
    starRingEnd ℂ (riemannXiSuzukiArithmeticPPositive t (x : ℂ)) *
      riemannXiSuzukiArithmeticPPositive u (x : ℂ)

/-- The signed phase formula agrees almost everywhere with the actual
arithmetic signal product, before any integration or time averaging. -/
theorem suzukiArithmeticPhaseGramIntegrand_ae_eq_signal_product (t u : ℝ) :
    suzukiArithmeticPhaseGramIntegrand t u =ᵐ[volume]
      fun x ↦ starRingEnd ℂ (suzukiRealAxisArithmeticSignalPositive t x) *
        suzukiRealAxisArithmeticSignalPositive u x := by
  filter_upwards [suzukiRealAxisXiZeroCarrier_ae_quadratic_eq_signed] with x hx
  unfold suzukiArithmeticPhaseGramIntegrand
  rw [← hx]
  change _ = starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x *
    riemannXiSuzukiArithmeticPPositive t (x : ℂ)) *
      (suzukiRealAxisXiZeroCarrier x *
        riemannXiSuzukiArithmeticPPositive u (x : ℂ))
  rw [map_mul]
  ring

/-- The complete signed arithmetic integrand is integrable at every pair
of positive times. No infinite spectral boundary identification is needed. -/
theorem integrable_suzukiArithmeticPhaseGramIntegrand
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Integrable (suzukiArithmeticPhaseGramIntegrand t u) := by
  apply (L2.integrable_inner
    (suzukiRealAxisArithmeticSignalPositiveLp t ht)
    (suzukiRealAxisArithmeticSignalPositiveLp u hu)).congr
  filter_upwards [suzukiRealAxisArithmeticSignalPositiveLp_ae t ht,
    suzukiRealAxisArithmeticSignalPositiveLp_ae u hu,
    suzukiArithmeticPhaseGramIntegrand_ae_eq_signal_product t u] with x ht' hu' hx
  rw [ht', hu', RCLike.inner_apply', hx]

/-- The literal arithmetic two-time Gram has an exact signed phase integral.
This is unconditional; it does not identify that Gram with a screw kernel. -/
theorem inner_suzukiArithmeticSignal_eq_phase_integral
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    inner ℂ (suzukiRealAxisArithmeticSignalPositiveLp t ht)
      (suzukiRealAxisArithmeticSignalPositiveLp u hu) =
        ∫ x : ℝ, suzukiArithmeticPhaseGramIntegrand t u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiRealAxisArithmeticSignalPositiveLp_ae t ht,
    suzukiRealAxisArithmeticSignalPositiveLp_ae u hu,
    suzukiArithmeticPhaseGramIntegrand_ae_eq_signal_product t u] with x ht' hu' hx
  rw [ht', hu', RCLike.inner_apply', hx]

private theorem phaseGram_sum_factorization
    {ι : Type*} [Fintype ι] (t : ι → ℝ) (a : ι → ℂ) (x : ℝ) :
    (∑ i, ∑ j, starRingEnd ℂ (a i) * a j *
      suzukiArithmeticPhaseGramIntegrand (t i) (t j) x) =
        (suzukiRealAxisXiZeroCarrier x -
            starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) / (2 * I) *
          starRingEnd ℂ (∑ i, a i *
            riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ)) *
          (∑ i, a i * riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ)) := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  unfold suzukiArithmeticPhaseGramIntegrand
  ring

/-- Every finite complex combination of positive-time arithmetic signals
has this genuinely integrable coupled phase representation. -/
theorem integrable_suzukiArithmetic_finite_phase_energy
    {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 < t i) (a : ι → ℂ) :
    Integrable (fun x : ℝ ↦
      (suzukiRealAxisXiZeroCarrier x -
          starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) / (2 * I) *
        starRingEnd ℂ (∑ i, a i *
          riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ)) *
        (∑ i, a i * riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ))) := by
  have hsum := integrable_finsetSum Finset.univ fun i _hi ↦
    integrable_finsetSum Finset.univ fun j _hj ↦
      (integrable_suzukiArithmeticPhaseGramIntegrand (ht i) (ht j)).const_mul
        (starRingEnd ℂ (a i) * a j)
  apply hsum.congr
  exact Eventually.of_forall (phaseGram_sum_factorization t a)

/-- The exact signed phase energy of an arbitrary finite time test is its
literal arithmetic `L²` norm square. All mixed times and complex coefficients
are retained, with no orthogonality or RH premise. -/
theorem suzukiArithmetic_finite_phase_energy_eq_norm_sq
    {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 < t i) (a : ι → ℂ) :
    (∫ x : ℝ, (suzukiRealAxisXiZeroCarrier x -
          starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x)) / (2 * I) *
        starRingEnd ℂ (∑ i, a i *
          riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ)) *
        (∑ i, a i * riemannXiSuzukiArithmeticPPositive (t i) (x : ℂ))) =
      (‖∑ i, a i • suzukiRealAxisArithmeticSignalPositiveLp (t i) (ht i)‖ : ℂ) ^ 2 := by
  have hnorm := inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    (∑ i, a i • suzukiRealAxisArithmeticSignalPositiveLp (t i) (ht i))
  apply Eq.trans ?_ hnorm
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_suzukiArithmeticSignal_eq_phase_integral]
  calc
    _ = ∫ x : ℝ, ∑ i, ∑ j, starRingEnd ℂ (a i) * a j *
        suzukiArithmeticPhaseGramIntegrand (t i) (t j) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ (phaseGram_sum_factorization t a x).symm
    _ = _ := by
      rw [integral_finsetSum _ (fun i _hi ↦
        integrable_finsetSum Finset.univ fun j _hj ↦
          (integrable_suzukiArithmeticPhaseGramIntegrand (ht i) (ht j)).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finsetSum _ (fun j _hj ↦
        (integrable_suzukiArithmeticPhaseGramIntegrand (ht i) (ht j)).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_const_mul]
      ring

end
end RiemannGaussian
