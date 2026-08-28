import RiemannGaussian.RiemannXiSuzukiBoundaryCompactTests

/-!
# The common-carrier resolvent form of Suzuki's boundary Gram kernel

Every normalized zero function in Suzuki's spectral expansion contains the
same xi carrier.  This file keeps that common factor intact instead of
discarding it through a pointwise norm estimate.  For genuine xi nodes
`alpha_rho` and `alpha_sigma`, the exact boundary Gram entry is

`N_rho N_sigma * integral |carrier(x)|^2 /
  ((x - conj alpha_rho) (x - alpha_sigma)) dx`.

The displayed quotient is Lean's totalized quotient.  Its apparent
singularities at real nodes are removable only after the xi carrier is kept
in the numerator.  Integrability is therefore proved from the already
constructed `L²` zero functions, and is valid without RH, zero simplicity,
or an off-axis hypothesis.

The resulting carrier kernel is Hermitian.  Its normalization-weighted
finite quadratic is exactly the genuine zero-function Gram quadratic, so the
coefficient-tail frontier and the compact-test boundary-identification
criterion are rewritten without loss as statements about this one common
carrier resolvent kernel.  No vanishing or boundary convergence is asserted.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- Every genuine xi-zero normalization is strictly positive. -/
theorem suzukiXiZeroNormalization_pos
    (rho : NontrivialZetaZero) :
    0 < suzukiXiZeroNormalization rho := by
  unfold suzukiXiZeroNormalization
  apply Real.sqrt_pos.2
  exact div_pos
    (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
    Real.pi_pos

/-- The common-carrier resolvent density underlying one genuine Suzuki Gram
entry.  The conjugated node occurs in the first denominator because Lean's
complex inner product is conjugate-linear in its first argument. -/
def suzukiXiBoundaryCarrierGramIntegrand
    (rho sigma : NontrivialZetaZero) (x : ℝ) : ℂ :=
  starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x) *
      suzukiRealAxisXiZeroCarrier x /
    (((x : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      ((x : ℂ) - zetaSpectralCoordinate sigma.1))

/-- Pointwise factorization of a pair of normalized zero functions through
their common xi carrier.  Because complex division is totalized, this
identity also holds at real divisor points. -/
theorem conj_suzukiRealAxisZeroFunction_mul_eq_carrierIntegrand
    (rho sigma : NontrivialZetaZero) (x : ℝ) :
    starRingEnd ℂ (suzukiRealAxisZeroFunction rho x) *
        suzukiRealAxisZeroFunction sigma x =
      (((suzukiXiZeroNormalization rho *
          suzukiXiZeroNormalization sigma : ℝ) : ℂ) *
        suzukiXiBoundaryCarrierGramIntegrand rho sigma x) := by
  unfold suzukiRealAxisZeroFunction suzukiXiZeroFunctionFormula
    suzukiXiBoundaryCarrierGramIntegrand suzukiRealAxisXiZeroCarrier
  simp only [map_mul, map_inv₀, map_sub, Complex.conj_ofReal,
    div_eq_mul_inv, mul_inv]
  push_cast
  ring

/-- The literal product of any two normalized xi-zero boundary formulas is
Lebesgue integrable. -/
theorem integrable_conj_suzukiRealAxisZeroFunction_mul
    (rho sigma : NontrivialZetaZero) :
    Integrable (fun x : ℝ ↦
      starRingEnd ℂ (suzukiRealAxisZeroFunction rho x) *
        suzukiRealAxisZeroFunction sigma x) := by
  apply (L2.integrable_inner (suzukiRealAxisZeroFunctionLp rho)
    (suzukiRealAxisZeroFunctionLp sigma)).congr
  filter_upwards [suzukiRealAxisZeroFunctionLp_ae rho,
    suzukiRealAxisZeroFunctionLp_ae sigma] with x hrho hsigma
  rw [hrho, hsigma, RCLike.inner_apply']

/-- The common-carrier resolvent density is genuinely integrable for every
pair of genuine nodes, including real and multiple nodes. -/
theorem integrable_suzukiXiBoundaryCarrierGramIntegrand
    (rho sigma : NontrivialZetaZero) :
    Integrable (suzukiXiBoundaryCarrierGramIntegrand rho sigma) := by
  let N : ℂ := ((suzukiXiZeroNormalization rho *
    suzukiXiZeroNormalization sigma : ℝ) : ℂ)
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (mul_pos (suzukiXiZeroNormalization_pos rho)
      (suzukiXiZeroNormalization_pos sigma)).ne'
  have hintegrable :=
    (integrable_conj_suzukiRealAxisZeroFunction_mul rho sigma).const_mul N⁻¹
  apply hintegrable.congr
  exact Eventually.of_forall fun x ↦ by
    change N⁻¹ *
      (starRingEnd ℂ (suzukiRealAxisZeroFunction rho x) *
        suzukiRealAxisZeroFunction sigma x) = _
    rw [conj_suzukiRealAxisZeroFunction_mul_eq_carrierIntegrand]
    change N⁻¹ * (N * suzukiXiBoundaryCarrierGramIntegrand rho sigma x) = _
    field_simp [hN]

/-- The common-carrier resolvent kernel on the genuine spectral-xi divisor. -/
def suzukiXiBoundaryCarrierGramKernel
    (rho sigma : NontrivialZetaZero) : ℂ :=
  ∫ x : ℝ, suzukiXiBoundaryCarrierGramIntegrand rho sigma x

/-- Every genuine zero-function Gram entry is exactly the normalization
product times the common-carrier resolvent kernel. -/
theorem suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel
    (rho sigma : NontrivialZetaZero) :
    suzukiXiZeroFunctionGramEntry rho sigma =
      (((suzukiXiZeroNormalization rho *
          suzukiXiZeroNormalization sigma : ℝ) : ℂ) *
        suzukiXiBoundaryCarrierGramKernel rho sigma) := by
  rw [suzukiXiZeroFunctionGramEntry_eq_integral]
  unfold suzukiXiBoundaryCarrierGramKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦
    conj_suzukiRealAxisZeroFunction_mul_eq_carrierIntegrand rho sigma x

/-- The common-carrier resolvent kernel is Hermitian on the complete genuine
xi divisor, with no RH or simplicity assumption. -/
theorem suzukiXiBoundaryCarrierGramKernel_swap
    (rho sigma : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel sigma rho =
      starRingEnd ℂ (suzukiXiBoundaryCarrierGramKernel rho sigma) := by
  have hswap := suzukiXiZeroFunctionGramEntry_swap rho sigma
  rw [suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel,
    suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel] at hswap
  simp only [map_mul, Complex.conj_ofReal] at hswap
  rw [mul_comm (suzukiXiZeroNormalization sigma)
    (suzukiXiZeroNormalization rho)] at hswap
  have hN : (((suzukiXiZeroNormalization rho *
      suzukiXiZeroNormalization sigma : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_pos (suzukiXiZeroNormalization_pos rho)
      (suzukiXiZeroNormalization_pos sigma)).ne'
  exact mul_left_cancel₀ hN hswap

/-- The ordinary finite quadratic form of the unweighted common-carrier
resolvent kernel. -/
def suzukiXiBoundaryCarrierKernelFinsetQuadratic
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) : ℂ :=
  ∑ rho ∈ S,
    ∑ sigma ∈ S,
      starRingEnd ℂ (a rho) * a sigma *
        suzukiXiBoundaryCarrierGramKernel rho sigma

/-- Finite synthesis for the unweighted carrier kernel.  Strict positivity
of every `N_rho` makes the normalization division legitimate. -/
def suzukiXiBoundaryCarrierKernelFiniteSynthesis
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ rho ∈ S,
    (a rho / (suzukiXiZeroNormalization rho : ℂ)) •
      suzukiRealAxisZeroFunctionLp rho

/-- The unweighted carrier-kernel quadratic is exactly the inner square of
its normalization-divided finite synthesis. -/
theorem inner_suzukiXiBoundaryCarrierKernelFiniteSynthesis_eq_quadratic
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) :
    inner ℂ (suzukiXiBoundaryCarrierKernelFiniteSynthesis S a)
        (suzukiXiBoundaryCarrierKernelFiniteSynthesis S a) =
      suzukiXiBoundaryCarrierKernelFinsetQuadratic S a := by
  unfold suzukiXiBoundaryCarrierKernelFiniteSynthesis
    suzukiXiBoundaryCarrierKernelFinsetQuadratic
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  change
    starRingEnd ℂ
        (a rho / (suzukiXiZeroNormalization rho : ℂ)) *
        ((a sigma / (suzukiXiZeroNormalization sigma : ℂ)) *
          suzukiXiZeroFunctionGramEntry rho sigma) = _
  rw [suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel]
  have hrho : (suzukiXiZeroNormalization rho : ℂ) ≠ 0 := by
    exact_mod_cast (suzukiXiZeroNormalization_pos rho).ne'
  have hsigma : (suzukiXiZeroNormalization sigma : ℂ) ≠ 0 := by
    exact_mod_cast (suzukiXiZeroNormalization_pos sigma).ne'
  simp only [map_div₀, Complex.conj_ofReal]
  push_cast
  field_simp [hrho, hsigma]

/-- Exact squared-norm realization of every finite unweighted carrier-kernel
quadratic. -/
theorem suzukiXiBoundaryCarrierKernelFinsetQuadratic_eq_norm_sq
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) :
    suzukiXiBoundaryCarrierKernelFinsetQuadratic S a =
      (‖suzukiXiBoundaryCarrierKernelFiniteSynthesis S a‖ : ℂ) ^ 2 := by
  rw [← inner_suzukiXiBoundaryCarrierKernelFiniteSynthesis_eq_quadratic]
  exact inner_self_eq_norm_sq_to_K _

/-- Every finite unweighted carrier-kernel quadratic is real. -/
theorem suzukiXiBoundaryCarrierKernelFinsetQuadratic_im
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) :
    (suzukiXiBoundaryCarrierKernelFinsetQuadratic S a).im = 0 := by
  rw [suzukiXiBoundaryCarrierKernelFinsetQuadratic_eq_norm_sq, pow_two]
  simp

/-- The unweighted common-carrier resolvent kernel is positive semidefinite
on every finite subset of the genuine spectral-xi divisor. -/
theorem suzukiXiBoundaryCarrierKernelFinsetQuadratic_re_nonneg
    (S : Finset NontrivialZetaZero)
    (a : NontrivialZetaZero → ℂ) :
    0 ≤ (suzukiXiBoundaryCarrierKernelFinsetQuadratic S a).re := by
  rw [suzukiXiBoundaryCarrierKernelFinsetQuadratic_eq_norm_sq, pow_two]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  positivity

/-- In particular, every diagonal value of the common-carrier kernel has
nonnegative real part. -/
theorem suzukiXiBoundaryCarrierGramKernel_self_re_nonneg
    (rho : NontrivialZetaZero) :
    0 ≤ (suzukiXiBoundaryCarrierGramKernel rho rho).re := by
  simpa [suzukiXiBoundaryCarrierKernelFinsetQuadratic] using
    suzukiXiBoundaryCarrierKernelFinsetQuadratic_re_nonneg
      {rho} (fun _ ↦ 1)

/-- Every diagonal carrier-kernel value is real. -/
theorem suzukiXiBoundaryCarrierGramKernel_self_im
    (rho : NontrivialZetaZero) :
    (suzukiXiBoundaryCarrierGramKernel rho rho).im = 0 := by
  simpa [suzukiXiBoundaryCarrierKernelFinsetQuadratic] using
    suzukiXiBoundaryCarrierKernelFinsetQuadratic_im
      {rho} (fun _ ↦ 1)

/-- On the diagonal, multiplication by the exact normalization square
recovers the squared `L²` norm of the normalized zero function. -/
theorem sq_normalization_mul_suzukiXiBoundaryCarrierGramKernel_self
    (rho : NontrivialZetaZero) :
    (suzukiXiZeroNormalization rho : ℂ) ^ 2 *
        suzukiXiBoundaryCarrierGramKernel rho rho =
      (‖suzukiRealAxisZeroFunctionLp rho‖ : ℂ) ^ 2 := by
  have h := suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel rho rho
  rw [suzukiXiZeroFunctionGramEntry_self] at h
  push_cast at h
  simpa [pow_two] using h.symm

/-- The carrier-kernel quadratic with the exact normalization weights from
Suzuki's zero functions. -/
def suzukiXiBoundaryCarrierFinsuppQuadratic
    (c : NontrivialZetaZero →₀ ℂ) : ℂ :=
  ∑ rho ∈ c.support,
    ∑ sigma ∈ c.support,
      starRingEnd ℂ (c rho) * c sigma *
        (((suzukiXiZeroNormalization rho *
            suzukiXiZeroNormalization sigma : ℝ) : ℂ) *
          suzukiXiBoundaryCarrierGramKernel rho sigma)

/-- The normalization-weighted common-carrier quadratic is exactly the
genuine zero-function Gram quadratic for every finite coefficient family. -/
theorem suzukiXiBoundaryCarrierFinsuppQuadratic_eq_gramQuadratic
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiBoundaryCarrierFinsuppQuadratic c =
      suzukiXiZeroFunctionFinsuppGramQuadratic c := by
  unfold suzukiXiBoundaryCarrierFinsuppQuadratic
    suzukiXiZeroFunctionFinsuppGramQuadratic
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [suzukiXiZeroFunctionGramEntry_eq_carrierGramKernel]

/-- Every finite normalization-weighted carrier-kernel quadratic has
nonnegative real part. -/
theorem suzukiXiBoundaryCarrierFinsuppQuadratic_re_nonneg
    (c : NontrivialZetaZero →₀ ℂ) :
    0 ≤ (suzukiXiBoundaryCarrierFinsuppQuadratic c).re := by
  rw [suzukiXiBoundaryCarrierFinsuppQuadratic_eq_gramQuadratic,
    suzukiXiZeroFunctionFinsuppGramQuadratic_re]
  positivity

/-- The common-carrier form of one genuine Suzuki coefficient-window tail. -/
def suzukiXiCoefficientTailCarrierQuadratic
    (t T U : ℝ) : ℂ :=
  suzukiXiBoundaryCarrierFinsuppQuadratic
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The coefficient-tail Gram frontier is exactly its common-carrier
resolvent quadratic. -/
theorem suzukiXiCoefficientTailGramQuadratic_eq_carrierQuadratic
    (t T U : ℝ) :
    suzukiXiCoefficientTailGramQuadratic t T U =
      suzukiXiCoefficientTailCarrierQuadratic t T U := by
  unfold suzukiXiCoefficientTailGramQuadratic
    suzukiXiCoefficientTailCarrierQuadratic
  exact
    (suzukiXiBoundaryCarrierFinsuppQuadratic_eq_gramQuadratic _).symm

/-- Tail vanishing stated directly for the common-carrier resolvent
quadratic.  This declaration names the remaining estimate; it does not
assert it. -/
def SuzukiXiCoefficientTailCarrierVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (suzukiXiCoefficientTailCarrierQuadratic t T U).re < epsilon

/-- The original tail-Gram target and the common-carrier target are exactly
equivalent. -/
theorem coefficientTailGramVanishing_iff_carrierVanishing
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      SuzukiXiCoefficientTailCarrierVanishing t := by
  unfold SuzukiXiCoefficientTailGramVanishing
    SuzukiXiCoefficientTailCarrierVanishing
  simp_rw [suzukiXiCoefficientTailGramQuadratic_eq_carrierQuadratic]

/-- The current strong boundary meeting problem, expressed entirely through
the common carrier and literal compactly supported test integrals. -/
theorem arithmeticBoundaryIdentification_iff_carrierTailVanishing_and_compactTests
    (t : ℝ) (ht : 0 < t) :
    SuzukiXiArithmeticBoundaryIdentification t ht ↔
      SuzukiXiCoefficientTailCarrierVanishing t ∧
        SuzukiXiArithmeticBoundaryCompactTestIdentification t := by
  rw [arithmeticBoundaryIdentification_iff_tailGramVanishing_and_compactTests,
    coefficientTailGramVanishing_iff_carrierVanishing]

end

end RiemannGaussian
