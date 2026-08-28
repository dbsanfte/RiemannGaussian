import RiemannGaussian.RiemannXiSuzukiZeroFunctionL2

/-!
# The finite Suzuki zero-function Gram identity

Every normalized genuine xi-zero function is now an actual vector in
`L²(ℝ, ℂ)`.  This file forms their finite Suzuki synthesis and proves that it
is exactly the previously defined real-axis finite spectral signal.  It then
expands the Hilbert norm into the genuine finite zero-function Gram quadratic
form.

All statements here are unconditional and finite.  In particular, they do
not assume a real-boundary identity for the infinite spectral series or any
boundedness of the infinite synthesis operator.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The published scalar multiplying one normalized zero function in
Suzuki's finite expansion. -/
def suzukiXiZeroSynthesisCoefficient
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
    suzukiSpectralScrewCoefficient t (zetaSpectralCoordinate rho.1)

/-- The published synthesis scalar is `sqrt(pi)` times the corresponding
coordinate of the complete `ℓ²` Suzuki coefficient vector. -/
theorem suzukiXiZeroSynthesisCoefficient_eq_sqrtPi_mul_feature
    (t : ℝ) (rho : NontrivialZetaZero) :
    suzukiXiZeroSynthesisCoefficient t rho =
      (Real.sqrt Real.pi : ℂ) *
        zetaSuzukiSpectralCoefficientFeature t rho := by
  exact suzukiXiPublishedCoefficient_eq_sqrtPi_mul_feature t rho

/-- The finite Suzuki synthesis formed inside the actual boundary Hilbert
space. -/
def suzukiRealAxisSignalWindowSynthesisLp
    (t T : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    suzukiXiZeroSynthesisCoefficient t rho •
      suzukiRealAxisZeroFunctionLp rho

/-- The Hilbert-space synthesis has the literal finite sum of normalized
zero-function formulas as an almost-everywhere representative. -/
theorem suzukiRealAxisSignalWindowSynthesisLp_ae
    (t T : ℝ) :
    suzukiRealAxisSignalWindowSynthesisLp t T =ᵐ[volume]
      fun x : ℝ ↦ ∑ rho ∈ spectralZetaZeroWindow T,
        suzukiXiZeroSynthesisCoefficient t rho *
          suzukiRealAxisZeroFunction rho x := by
  let W := spectralZetaZeroWindow T
  have hsum := Lp.coeFn_fun_finsetSum W (fun rho ↦
    suzukiXiZeroSynthesisCoefficient t rho •
      suzukiRealAxisZeroFunctionLp rho)
  have hterms : ∀ᵐ x : ℝ ∂volume,
      ∀ rho ∈ W,
        (suzukiXiZeroSynthesisCoefficient t rho •
            suzukiRealAxisZeroFunctionLp rho) x =
          suzukiXiZeroSynthesisCoefficient t rho *
            suzukiRealAxisZeroFunction rho x := by
    apply (eventually_all_finset W).2
    intro rho _hrho
    filter_upwards [
      Lp.coeFn_smul (suzukiXiZeroSynthesisCoefficient t rho)
        (suzukiRealAxisZeroFunctionLp rho),
      suzukiRealAxisZeroFunctionLp_ae rho] with x hsmul hzero
    rw [hsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hzero]
  filter_upwards [hsum, hterms] with x hsumx htermsx
  calc
    suzukiRealAxisSignalWindowSynthesisLp t T x =
        ∑ rho ∈ W,
          (suzukiXiZeroSynthesisCoefficient t rho •
            suzukiRealAxisZeroFunctionLp rho) x := by
      simpa [suzukiRealAxisSignalWindowSynthesisLp, W] using hsumx
    _ = ∑ rho ∈ W,
        suzukiXiZeroSynthesisCoefficient t rho *
          suzukiRealAxisZeroFunction rho x := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact htermsx rho hrho
    _ = ∑ rho ∈ spectralZetaZeroWindow T,
        suzukiXiZeroSynthesisCoefficient t rho *
          suzukiRealAxisZeroFunction rho x := by rfl

/-- The literal real-axis finite signal and its Hilbert-space synthesis are
the same `L²` vector. -/
theorem suzukiRealAxisSignalWindowLp_eq_synthesis
    (t T : ℝ) :
    suzukiRealAxisSignalWindowLp t T =
      suzukiRealAxisSignalWindowSynthesisLp t T := by
  apply Lp.ext
  filter_upwards [suzukiRealAxisSignalWindowLp_ae t T,
    suzukiRealAxisSignalWindowSynthesisLp_ae t T]
      with x hwindow hsynthesis
  rw [hwindow, hsynthesis,
    suzukiRealAxisSignalWindow_eq_sum_zeroFunctions]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rfl

/-- The genuine boundary Gram entry between two normalized xi-zero
functions. -/
def suzukiXiZeroFunctionGramEntry
    (rho sigma : NontrivialZetaZero) : ℂ :=
  inner ℂ (suzukiRealAxisZeroFunctionLp rho)
    (suzukiRealAxisZeroFunctionLp sigma)

/-- The zero-function Gram kernel is Hermitian. -/
theorem suzukiXiZeroFunctionGramEntry_swap
    (rho sigma : NontrivialZetaZero) :
    suzukiXiZeroFunctionGramEntry sigma rho =
      starRingEnd ℂ (suzukiXiZeroFunctionGramEntry rho sigma) := by
  unfold suzukiXiZeroFunctionGramEntry
  rw [← inner_conj_symm]

/-- A diagonal Gram entry is exactly the squared `L²` norm of its normalized
zero function. -/
theorem suzukiXiZeroFunctionGramEntry_self
    (rho : NontrivialZetaZero) :
    suzukiXiZeroFunctionGramEntry rho rho =
      (‖suzukiRealAxisZeroFunctionLp rho‖ : ℂ) ^ 2 := by
  exact inner_self_eq_norm_sq_to_K _

/-- The finite Gram quadratic form of Suzuki's published zero-function
coefficients. -/
def suzukiXiFiniteZeroFunctionGramQuadratic (t T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ spectralZetaZeroWindow T,
      starRingEnd ℂ (suzukiXiZeroSynthesisCoefficient t rho) *
        suzukiXiZeroSynthesisCoefficient t sigma *
          suzukiXiZeroFunctionGramEntry rho sigma

/-- The inner square of the literal finite real-axis signal is exactly its
genuine zero-function Gram quadratic form. -/
theorem inner_suzukiRealAxisSignalWindowLp_eq_gramQuadratic
    (t T : ℝ) :
    inner ℂ (suzukiRealAxisSignalWindowLp t T)
        (suzukiRealAxisSignalWindowLp t T) =
      suzukiXiFiniteZeroFunctionGramQuadratic t T := by
  rw [suzukiRealAxisSignalWindowLp_eq_synthesis]
  unfold suzukiRealAxisSignalWindowSynthesisLp
    suzukiXiFiniteZeroFunctionGramQuadratic
    suzukiXiZeroFunctionGramEntry
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  ring

/-- The finite Gram quadratic is exactly the squared boundary `L²` norm of
the literal finite Suzuki signal. -/
theorem suzukiXiFiniteZeroFunctionGramQuadratic_eq_norm_sq
    (t T : ℝ) :
    suzukiXiFiniteZeroFunctionGramQuadratic t T =
      (‖suzukiRealAxisSignalWindowLp t T‖ : ℂ) ^ 2 := by
  rw [← inner_suzukiRealAxisSignalWindowLp_eq_gramQuadratic]
  exact inner_self_eq_norm_sq_to_K _

/-- The finite Gram quadratic is real. -/
theorem suzukiXiFiniteZeroFunctionGramQuadratic_im
    (t T : ℝ) :
    (suzukiXiFiniteZeroFunctionGramQuadratic t T).im = 0 := by
  rw [suzukiXiFiniteZeroFunctionGramQuadratic_eq_norm_sq]
  rw [pow_two]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero]
  ring

/-- Its real part is the literal finite signal's squared `L²` norm. -/
theorem suzukiXiFiniteZeroFunctionGramQuadratic_re
    (t T : ℝ) :
    (suzukiXiFiniteZeroFunctionGramQuadratic t T).re =
      ‖suzukiRealAxisSignalWindowLp t T‖ ^ 2 := by
  rw [suzukiXiFiniteZeroFunctionGramQuadratic_eq_norm_sq]
  rw [pow_two]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Hence every genuine finite Suzuki zero-function Gram quadratic is
nonnegative, without any RH assumption. -/
theorem suzukiXiFiniteZeroFunctionGramQuadratic_re_nonneg
    (t T : ℝ) :
    0 ≤ (suzukiXiFiniteZeroFunctionGramQuadratic t T).re := by
  rw [suzukiXiFiniteZeroFunctionGramQuadratic_re]
  positivity

/-- The same finite Gram form with the universal `sqrt(pi)` removed from the
coefficients, so its scalar family is literally the restriction of the
complete `ℓ²` coefficient vector. -/
def suzukiXiFiniteCoefficientGramQuadratic (t T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ spectralZetaZeroWindow T,
      starRingEnd ℂ (zetaSuzukiSpectralCoefficientFeature t rho) *
        zetaSuzukiSpectralCoefficientFeature t sigma *
          suzukiXiZeroFunctionGramEntry rho sigma

/-- Removing the two universal square-root factors extracts exactly one
factor of `pi` from the finite Gram form. -/
theorem suzukiXiFiniteZeroFunctionGramQuadratic_eq_pi_mul_coefficientGram
    (t T : ℝ) :
    suzukiXiFiniteZeroFunctionGramQuadratic t T =
      (Real.pi : ℂ) * suzukiXiFiniteCoefficientGramQuadratic t T := by
  unfold suzukiXiFiniteZeroFunctionGramQuadratic
    suzukiXiFiniteCoefficientGramQuadratic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [suzukiXiZeroSynthesisCoefficient_eq_sqrtPi_mul_feature,
    suzukiXiZeroSynthesisCoefficient_eq_sqrtPi_mul_feature]
  simp only [map_mul, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_nonneg
  rw [← hsqrt]
  ring

/-- The exact finite coefficient-vector Gram identity.  Its left side is the
literal boundary norm; its right side uses coordinates of the complete
unconditional `ℓ²` Suzuki coefficient vector. -/
theorem norm_sq_suzukiRealAxisSignalWindowLp_eq_pi_mul_coefficientGram
    (t T : ℝ) :
    (‖suzukiRealAxisSignalWindowLp t T‖ : ℂ) ^ 2 =
      (Real.pi : ℂ) * suzukiXiFiniteCoefficientGramQuadratic t T := by
  rw [← suzukiXiFiniteZeroFunctionGramQuadratic_eq_pi_mul_coefficientGram,
    suzukiXiFiniteZeroFunctionGramQuadratic_eq_norm_sq]

end

end RiemannGaussian
