import RiemannGaussian.RiemannXiSuzukiCarrierNevanlinnaMeasure

/-!
# Finite-measure Gram geometry of Suzuki's xi carrier

For the finite carrier measure

`dμ(x) = density(x) dx / (1 + x^2)`,

the rational feature `F_z(x) = (x - i) / (x - z)` has the exact Gram
product

`conj(F_w(x)) * F_z(x) dμ(x)
  = density(x) dx / ((x - conj(w)) * (x - z))`.

This file proves that every genuine xi-node feature, including real and
multiple nodes, is an actual vector in `L²(μ)`.  It then identifies the
existing common-carrier kernel and its coefficient-tail quadratic with the
literal Gram kernel and squared norm in this finite measure space.

No tail vanishing, rigidity theorem, or RH conclusion is asserted here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The canonical rational feature associated with one spectral parameter.
It is totalized at a real collision, as are all divisions in Lean. -/
def suzukiXiCarrierNevanlinnaFeature (z : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - Complex.I) / ((x : ℂ) - z)

/-- The normalization parameter `i` gives the constant unit feature. -/
@[simp] theorem suzukiXiCarrierNevanlinnaFeature_I (x : ℝ) :
    suzukiXiCarrierNevanlinnaFeature Complex.I x = 1 := by
  unfold suzukiXiCarrierNevanlinnaFeature
  exact div_self (ofReal_sub_ne_zero_of_im_ne_zero (by simp) x)

/-- The canonical feature is Borel measurable for every parameter, including
a real parameter where its totalized value at the collision is zero. -/
theorem measurable_suzukiXiCarrierNevanlinnaFeature (z : ℂ) :
    Measurable (suzukiXiCarrierNevanlinnaFeature z) := by
  unfold suzukiXiCarrierNevanlinnaFeature
  exact (Complex.continuous_ofReal.measurable.sub measurable_const).div
    (Complex.continuous_ofReal.measurable.sub measurable_const)

/-- The generic density-resolvent kernel represented by two canonical
features. -/
def suzukiXiCarrierNevanlinnaKernelIntegrand
    (w z : ℂ) (x : ℝ) : ℂ :=
  (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) /
    (((x : ℂ) - starRingEnd ℂ w) * ((x : ℂ) - z))

/-- Exact pointwise cancellation of the finite Nevanlinna weight against the
two feature numerators.  No off-axis assumption is needed. -/
theorem suzukiXiCarrierNevanlinnaWeight_smul_featureProduct
    (w z : ℂ) (x : ℝ) :
    suzukiXiCarrierNevanlinnaWeight x •
        (starRingEnd ℂ (suzukiXiCarrierNevanlinnaFeature w x) *
          suzukiXiCarrierNevanlinnaFeature z x) =
      suzukiXiCarrierNevanlinnaKernelIntegrand w z x := by
  rw [Complex.real_smul]
  unfold suzukiXiCarrierNevanlinnaWeight
    suzukiXiCarrierNevanlinnaFeature
    suzukiXiCarrierNevanlinnaKernelIntegrand
  simp only [map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_I,
    sub_neg_eq_add]
  have hquad := one_add_sq_ofReal_ne_zero x
  push_cast
  rw [div_mul_div_comm]
  have hnumerator :
      ((x : ℂ) + Complex.I) * ((x : ℂ) - Complex.I) =
        1 + (x : ℂ) ^ 2 := by
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hnumerator]
  calc
    (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) /
          (1 + (x : ℂ) ^ 2) *
        ((1 + (x : ℂ) ^ 2) /
          (((x : ℂ) - starRingEnd ℂ w) * ((x : ℂ) - z))) =
        (((suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) /
          (1 + (x : ℂ) ^ 2)) * (1 + (x : ℂ) ^ 2)) /
          (((x : ℂ) - starRingEnd ℂ w) * ((x : ℂ) - z)) := by
      ring
    _ = (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) /
        (((x : ℂ) - starRingEnd ℂ w) * ((x : ℂ) - z)) := by
      rw [div_mul_cancel₀ _ hquad]

/-- At genuine xi nodes, the generic finite-measure kernel integrand is the
previously constructed explicit arithmetic carrier Gram integrand. -/
theorem suzukiXiCarrierNevanlinnaKernelIntegrand_node
    (rho sigma : NontrivialZetaZero) (x : ℝ) :
    suzukiXiCarrierNevanlinnaKernelIntegrand
        (zetaSpectralCoordinate rho.1)
        (zetaSpectralCoordinate sigma.1) x =
      suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x := by
  rfl

/-- Integrability against the finite carrier measure is equivalent to
integrability of the literal weight-scaled function against Lebesgue measure. -/
theorem integrable_carrierNevanlinnaMeasure_iff_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} :
    Integrable g suzukiXiCarrierNevanlinnaMeasure ↔
      Integrable (fun x ↦ suzukiXiCarrierNevanlinnaWeight x • g x) := by
  unfold suzukiXiCarrierNevanlinnaMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    measurable_suzukiXiCarrierNevanlinnaWeight.ennreal_ofReal
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr
  exact Eventually.of_forall fun x ↦ by
    change (ENNReal.ofReal
      (suzukiXiCarrierNevanlinnaWeight x)).toReal • g x =
        suzukiXiCarrierNevanlinnaWeight x • g x
    rw [ENNReal.toReal_ofReal
      (suzukiXiCarrierNevanlinnaWeight_nonneg x)]

/-- The canonical finite-measure feature at one genuine spectral-xi node. -/
def suzukiXiCarrierNevanlinnaNodeFeature
    (rho : NontrivialZetaZero) (x : ℝ) : ℂ :=
  suzukiXiCarrierNevanlinnaFeature
    (zetaSpectralCoordinate rho.1) x

/-- Every genuine-node feature is Borel measurable. -/
theorem measurable_suzukiXiCarrierNevanlinnaNodeFeature
    (rho : NontrivialZetaZero) :
    Measurable (suzukiXiCarrierNevanlinnaNodeFeature rho) :=
  measurable_suzukiXiCarrierNevanlinnaFeature _

/-- On the diagonal, the weighted feature norm square is exactly the
arithmetic common-carrier Gram density, embedded in the complex numbers. -/
theorem ofReal_weight_mul_normSq_nodeFeature
    (rho : NontrivialZetaZero) (x : ℝ) :
    ((suzukiXiCarrierNevanlinnaWeight x *
        ‖suzukiXiCarrierNevanlinnaNodeFeature rho x‖ ^ 2 : ℝ) : ℂ) =
      suzukiXiBoundaryArithmeticCarrierGramIntegrand rho rho x := by
  have h := suzukiXiCarrierNevanlinnaWeight_smul_featureProduct
    (zetaSpectralCoordinate rho.1)
    (zetaSpectralCoordinate rho.1) x
  rw [RCLike.conj_mul] at h
  rw [suzukiXiCarrierNevanlinnaKernelIntegrand_node] at h
  simpa [suzukiXiCarrierNevanlinnaNodeFeature,
    Complex.real_smul] using h

/-- The squared norm of every genuine-node feature is integrable against the
finite carrier measure, including at real and multiple nodes. -/
theorem integrable_normSq_suzukiXiCarrierNevanlinnaNodeFeature
    (rho : NontrivialZetaZero) :
    Integrable (fun x : ℝ ↦
      ‖suzukiXiCarrierNevanlinnaNodeFeature rho x‖ ^ 2)
      suzukiXiCarrierNevanlinnaMeasure := by
  rw [integrable_carrierNevanlinnaMeasure_iff_smul]
  have hcomplex : Integrable (fun x : ℝ ↦
      ((suzukiXiCarrierNevanlinnaWeight x *
        ‖suzukiXiCarrierNevanlinnaNodeFeature rho x‖ ^ 2 : ℝ) : ℂ)) := by
    apply (integrable_suzukiXiBoundaryArithmeticCarrierGramIntegrand
      rho rho).congr
    exact Eventually.of_forall fun x ↦
      (ofReal_weight_mul_normSq_nodeFeature rho x).symm
  apply hcomplex.re.congr
  exact Eventually.of_forall fun x ↦ by
    change ((suzukiXiCarrierNevanlinnaWeight x *
      ‖suzukiXiCarrierNevanlinnaNodeFeature rho x‖ ^ 2 : ℝ) : ℂ).re =
        suzukiXiCarrierNevanlinnaWeight x *
          ‖suzukiXiCarrierNevanlinnaNodeFeature rho x‖ ^ 2
    norm_cast

/-- Every genuine-node feature is an actual vector in the finite carrier
Hilbert space `L²(μ)`. -/
theorem memLp_two_suzukiXiCarrierNevanlinnaNodeFeature
    (rho : NontrivialZetaZero) :
    MemLp (suzukiXiCarrierNevanlinnaNodeFeature rho) 2
      suzukiXiCarrierNevanlinnaMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_suzukiXiCarrierNevanlinnaNodeFeature rho).aestronglyMeasurable).2
  exact integrable_normSq_suzukiXiCarrierNevanlinnaNodeFeature rho

/-- A genuine-node canonical feature packaged in the finite carrier Hilbert
space. -/
def suzukiXiCarrierNevanlinnaNodeFeatureLp
    (rho : NontrivialZetaZero) :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  (memLp_two_suzukiXiCarrierNevanlinnaNodeFeature rho).toLp
    (suzukiXiCarrierNevanlinnaNodeFeature rho)

/-- The packaged node feature has its literal rational formula almost
everywhere. -/
theorem suzukiXiCarrierNevanlinnaNodeFeatureLp_ae
    (rho : NontrivialZetaZero) :
    suzukiXiCarrierNevanlinnaNodeFeatureLp rho =ᵐ[
      suzukiXiCarrierNevanlinnaMeasure]
        suzukiXiCarrierNevanlinnaNodeFeature rho :=
  MemLp.coeFn_toLp (memLp_two_suzukiXiCarrierNevanlinnaNodeFeature rho)

/-- The finite-measure inner product of two genuine-node features is exactly
the existing common-carrier Gram kernel. -/
theorem inner_suzukiXiCarrierNevanlinnaNodeFeatureLp_eq_carrierKernel
    (rho sigma : NontrivialZetaZero) :
    inner ℂ (suzukiXiCarrierNevanlinnaNodeFeatureLp rho)
        (suzukiXiCarrierNevanlinnaNodeFeatureLp sigma) =
      suzukiXiBoundaryCarrierGramKernel rho sigma := by
  rw [L2.inner_def]
  calc
    (∫ x : ℝ,
        inner ℂ (suzukiXiCarrierNevanlinnaNodeFeatureLp rho x)
          (suzukiXiCarrierNevanlinnaNodeFeatureLp sigma x)
        ∂suzukiXiCarrierNevanlinnaMeasure) =
        ∫ x : ℝ,
          starRingEnd ℂ (suzukiXiCarrierNevanlinnaNodeFeature rho x) *
            suzukiXiCarrierNevanlinnaNodeFeature sigma x
          ∂suzukiXiCarrierNevanlinnaMeasure := by
      apply integral_congr_ae
      filter_upwards [suzukiXiCarrierNevanlinnaNodeFeatureLp_ae rho,
        suzukiXiCarrierNevanlinnaNodeFeatureLp_ae sigma]
          with x hrho hsigma
      rw [hrho, hsigma, RCLike.inner_apply']
    _ = ∫ x : ℝ, suzukiXiCarrierNevanlinnaWeight x •
          (starRingEnd ℂ (suzukiXiCarrierNevanlinnaNodeFeature rho x) *
            suzukiXiCarrierNevanlinnaNodeFeature sigma x) :=
      integral_suzukiXiCarrierNevanlinnaMeasure_eq_smul _
    _ = ∫ x : ℝ,
        suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        have h := suzukiXiCarrierNevanlinnaWeight_smul_featureProduct
          (zetaSpectralCoordinate rho.1)
          (zetaSpectralCoordinate sigma.1) x
        rw [suzukiXiCarrierNevanlinnaKernelIntegrand_node] at h
        simpa [suzukiXiCarrierNevanlinnaNodeFeature] using h
    _ = suzukiXiBoundaryCarrierGramKernel rho sigma :=
      (suzukiXiBoundaryCarrierGramKernel_eq_arithmetic_integral
        rho sigma).symm

/-- A diagonal carrier-kernel value is the squared norm of its canonical
feature in the finite carrier Hilbert space. -/
theorem suzukiXiBoundaryCarrierGramKernel_self_eq_nevanlinnaFeature_norm_sq
    (rho : NontrivialZetaZero) :
    suzukiXiBoundaryCarrierGramKernel rho rho =
      (‖suzukiXiCarrierNevanlinnaNodeFeatureLp rho‖ : ℂ) ^ 2 := by
  rw [← inner_suzukiXiCarrierNevanlinnaNodeFeatureLp_eq_carrierKernel]
  exact inner_self_eq_norm_sq_to_K _

/-- Finite synthesis of canonical node features with the exact Suzuki
normalization weights. -/
def suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis
    (c : NontrivialZetaZero →₀ ℂ) :
    Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  ∑ rho ∈ c.support,
    ((suzukiXiZeroNormalization rho : ℂ) * c rho) •
      suzukiXiCarrierNevanlinnaNodeFeatureLp rho

/-- The normalization-weighted common-carrier quadratic is exactly the inner
square of its canonical finite-measure feature synthesis. -/
theorem inner_suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis_eq_quadratic
    (c : NontrivialZetaZero →₀ ℂ) :
    inner ℂ (suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c)
        (suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c) =
      suzukiXiBoundaryCarrierFinsuppQuadratic c := by
  unfold suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis
    suzukiXiBoundaryCarrierFinsuppQuadratic
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  change
    starRingEnd ℂ ((suzukiXiZeroNormalization rho : ℂ) * c rho) *
        (((suzukiXiZeroNormalization sigma : ℂ) * c sigma) *
          inner ℂ (suzukiXiCarrierNevanlinnaNodeFeatureLp rho)
            (suzukiXiCarrierNevanlinnaNodeFeatureLp sigma)) = _
  rw [inner_suzukiXiCarrierNevanlinnaNodeFeatureLp_eq_carrierKernel]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- Exact squared-norm realization of every normalization-weighted carrier
quadratic in the finite Nevanlinna measure space. -/
theorem suzukiXiBoundaryCarrierFinsuppQuadratic_eq_nevanlinna_norm_sq
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiBoundaryCarrierFinsuppQuadratic c =
      (‖suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis c‖ : ℂ) ^ 2 := by
  rw [← inner_suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis_eq_quadratic]
  exact inner_self_eq_norm_sq_to_K _

/-- The canonical finite-measure feature synthesis of one genuine Suzuki
coefficient-window tail. -/
def suzukiXiCoefficientTailNevanlinnaFeatureSynthesis
    (t T U : ℝ) : Lp ℂ 2 suzukiXiCarrierNevanlinnaMeasure :=
  suzukiXiCarrierNevanlinnaFeatureFiniteSynthesis
    (riemannXiSuzukiSpectralCoefficientTailFinsupp t T U)

/-- The common-carrier tail quadratic is exactly the squared norm of the
corresponding feature synthesis in the finite carrier measure space. -/
theorem suzukiXiCoefficientTailCarrierQuadratic_eq_nevanlinna_norm_sq
    (t T U : ℝ) :
    suzukiXiCoefficientTailCarrierQuadratic t T U =
      (‖suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U‖ : ℂ) ^ 2 := by
  unfold suzukiXiCoefficientTailCarrierQuadratic
    suzukiXiCoefficientTailNevanlinnaFeatureSynthesis
  exact suzukiXiBoundaryCarrierFinsuppQuadratic_eq_nevanlinna_norm_sq _

/-- The original genuine zero-function tail Gram quadratic has the same
finite-measure squared-norm realization. -/
theorem suzukiXiCoefficientTailGramQuadratic_eq_nevanlinna_norm_sq
    (t T U : ℝ) :
    suzukiXiCoefficientTailGramQuadratic t T U =
      (‖suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U‖ : ℂ) ^ 2 := by
  rw [suzukiXiCoefficientTailGramQuadratic_eq_carrierQuadratic,
    suzukiXiCoefficientTailCarrierQuadratic_eq_nevanlinna_norm_sq]

/-- Real part of the carrier tail quadratic as a literal nonnegative real
squared norm in the finite measure space. -/
theorem suzukiXiCoefficientTailCarrierQuadratic_re_eq_nevanlinna_norm_sq
    (t T U : ℝ) :
    (suzukiXiCoefficientTailCarrierQuadratic t T U).re =
      ‖suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U‖ ^ 2 := by
  rw [suzukiXiCoefficientTailCarrierQuadratic_eq_nevanlinna_norm_sq,
    pow_two]
  simp
  ring

/-- Tail vanishing expressed as norm convergence of the canonical rational
feature syntheses in the finite carrier Hilbert space.  This names the exact
remaining estimate and does not assert it. -/
def SuzukiXiCoefficientTailNevanlinnaNormVanishing (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      ‖suzukiXiCoefficientTailNevanlinnaFeatureSynthesis t T U‖ ^ 2 < epsilon

/-- Common-carrier tail vanishing is exactly finite-measure feature-norm
vanishing. -/
theorem coefficientTailCarrierVanishing_iff_nevanlinnaNormVanishing
    (t : ℝ) :
    SuzukiXiCoefficientTailCarrierVanishing t ↔
      SuzukiXiCoefficientTailNevanlinnaNormVanishing t := by
  unfold SuzukiXiCoefficientTailCarrierVanishing
    SuzukiXiCoefficientTailNevanlinnaNormVanishing
  simp_rw [suzukiXiCoefficientTailCarrierQuadratic_re_eq_nevanlinna_norm_sq]

/-- The original zero-function Gram frontier is therefore exactly norm
vanishing for canonical rational features in one finite positive measure. -/
theorem coefficientTailGramVanishing_iff_nevanlinnaNormVanishing
    (t : ℝ) :
    SuzukiXiCoefficientTailGramVanishing t ↔
      SuzukiXiCoefficientTailNevanlinnaNormVanishing t := by
  rw [coefficientTailGramVanishing_iff_carrierVanishing,
    coefficientTailCarrierVanishing_iff_nevanlinnaNormVanishing]

end

end RiemannGaussian
