import RiemannGaussian.RiemannXiSuzukiCarrierArithmeticDensity

/-!
# A normalized Herglotz transform for Suzuki's spectral-xi carrier

The arithmetic carrier density is bounded but need not have finite total
mass.  Its unregularized Cauchy transform therefore has only `1 / |x|`
decay.  This file installs the standard real normalization

`1 / (x - z) - x / (1 + x^2)`

whose decay is quadratic.  We prove its absolute integrability directly in
Lean for every nonreal `z`, multiply it by the exact spectral-xi carrier
density, and define the resulting normalized Cauchy--Herglotz transform.

For off-axis genuine xi nodes, subtraction of two transform values cancels
the normalization term and recovers the common-carrier Gram kernel through
the resolvent identity.  Thus the new positive Gram kernel is a genuine Pick
divided-difference kernel of one scalar arithmetic entire-function transform,
not merely an abstract positive matrix.

No boundary limit, tail vanishing, or RH conclusion is asserted here.
-/

open Asymptotics Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- A polynomial quotient with a two-degree denominator advantage decays
quadratically along any real end. -/
theorem polynomialBoundaryQuotient_isBigO_inv_sq
    {q P : ℂ[X]} (hgap : q.natDegree + 2 ≤ P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0)
    {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ ↦ (x : ℂ)) l
      (Bornology.cobounded ℂ)) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[l]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹) ^ 2) := by
  have hP : P ≠ 0 := by
    intro hzero
    simpa [hzero] using hreal 0
  by_cases hq : q = 0
  · apply IsBigO.of_bound 0
    simp [hq]
  have hdegree : (X ^ 2 * q).degree ≤ P.degree := by
    rw [degree_eq_natDegree (mul_ne_zero (pow_ne_zero 2 X_ne_zero) hq),
      degree_eq_natDegree hP]
    exact_mod_cast (show (X ^ 2 * q).natDegree ≤ P.natDegree by
      rw [natDegree_X_pow_mul 2 hq]
      exact hgap)
  have hpoly :
      (X ^ 2 * q).eval =O[Bornology.cobounded ℂ] P.eval :=
    Polynomial.isBigO_cobounded_of_degree_le hdegree
  obtain ⟨c, hc⟩ := (hpoly.comp_tendsto hl).bound
  have hnonzero : ∀ᶠ x : ℝ in l, (x : ℂ) ≠ 0 := by
    have haway : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 := by
      filter_upwards [
        (Bornology.isBounded_singleton (x := (0 : ℂ))).compl]
        with z hz
      simpa using hz
    exact hl.eventually haway
  apply IsBigO.of_bound c
  filter_upwards [hc, hnonzero] with x hx hxComplex
  have hxnorm : 0 < ‖(x : ℂ)‖ := norm_pos_iff.mpr hxComplex
  have hxnormSq : 0 < ‖(x : ℂ)‖ ^ 2 := sq_pos_of_pos hxnorm
  have hPnorm : 0 < ‖P.eval (x : ℂ)‖ :=
    norm_pos_iff.mpr (hreal x)
  change ‖(X ^ 2 * q).eval (x : ℂ)‖ ≤
    c * ‖P.eval (x : ℂ)‖ at hx
  rw [eval_mul, eval_pow, eval_X, norm_mul, norm_pow] at hx
  rw [norm_div, norm_pow, norm_inv]
  calc
    ‖q.eval (x : ℂ)‖ / ‖P.eval (x : ℂ)‖ ≤
        (c * ‖P.eval (x : ℂ)‖ / ‖(x : ℂ)‖ ^ 2) /
          ‖P.eval (x : ℂ)‖ := by
      apply (div_le_div_iff_of_pos_right hPnorm).2
      exact (le_div_iff₀ hxnormSq).2 (by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hx)
    _ = c * ‖(x : ℂ)‖⁻¹ ^ 2 := by
      field_simp [hxnorm.ne', hPnorm.ne']

/-- At `+infinity`, the same two-degree polynomial quotient has quadratic
inverse decay. -/
theorem polynomialBoundaryQuotient_isBigO_inv_sq_atTop
    {q P : ℂ[X]} (hgap : q.natDegree + 2 ≤ P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[atTop]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹) ^ 2) :=
  polynomialBoundaryQuotient_isBigO_inv_sq hgap hreal
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ)

/-- At `-infinity`, the same two-degree polynomial quotient has quadratic
inverse decay. -/
theorem polynomialBoundaryQuotient_isBigO_inv_sq_atBot
    {q P : ℂ[X]} (hgap : q.natDegree + 2 ≤ P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    (fun x : ℝ ↦ q.eval (x : ℂ) / P.eval (x : ℂ)) =O[atBot]
      (fun x : ℝ ↦ ((x : ℂ)⁻¹) ^ 2) :=
  polynomialBoundaryQuotient_isBigO_inv_sq hgap hreal
    (RCLike.tendsto_ofReal_atBot_cobounded ℂ)

/-- A continuous real-boundary polynomial quotient with two degrees of
denominator advantage is absolutely integrable. -/
theorem polynomialBoundaryQuotient_integrable_of_natDegree_add_two_le
    {q P : ℂ[X]} (hgap : q.natDegree + 2 ≤ P.natDegree)
    (hreal : ∀ x : ℝ, P.eval (x : ℂ) ≠ 0) :
    Integrable (fun x : ℝ ↦
      q.eval (x : ℂ) / P.eval (x : ℂ)) := by
  let f : ℝ → ℂ := fun x ↦ q.eval (x : ℂ) / P.eval (x : ℂ)
  let g : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹
  have hfarTop : ∀ᶠ x : ℝ in atTop, 1 ≤ |x| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact hx.trans (le_abs_self x)
  have hfarBot : ∀ᶠ x : ℝ in atBot, 1 ≤ |x| := by
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with x hx
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hinvTop :
      (fun x : ℝ ↦ ‖((x : ℂ)⁻¹) ^ 2‖) =O[atTop] g := by
    simpa only [norm_pow] using
      norm_complex_inv_ofReal_sq_isBigO_cauchy hfarTop
  have hinvBot :
      (fun x : ℝ ↦ ‖((x : ℂ)⁻¹) ^ 2‖) =O[atBot] g := by
    simpa only [norm_pow] using
      norm_complex_inv_ofReal_sq_isBigO_cauchy hfarBot
  have htop : (fun x ↦ ‖f x‖) =O[atTop] g :=
    (polynomialBoundaryQuotient_isBigO_inv_sq_atTop
      hgap hreal).norm_norm.trans hinvTop
  have hbot : (fun x ↦ ‖f x‖) =O[atBot] g :=
    (polynomialBoundaryQuotient_isBigO_inv_sq_atBot
      hgap hreal).norm_norm.trans hinvBot
  have hcontinuous : Continuous f :=
    polynomialBoundaryQuotient_continuous hreal
  have hnormIntegrable : Integrable (fun x ↦ ‖f x‖) :=
    hcontinuous.norm.locallyIntegrable.integrable_of_isBigO_atBot_atTop
      hbot (integrable_inv_one_add_sq.integrableAtFilter atBot)
      htop (integrable_inv_one_add_sq.integrableAtFilter atTop)
  exact (integrable_norm_iff hcontinuous.aestronglyMeasurable).1
    hnormIntegrable

/-- The numerator polynomial of the normalized Cauchy kernel. -/
def suzukiXiNormalizedCauchyNumerator (z : ℂ) : ℂ[X] :=
  C z * X + C 1

/-- The denominator polynomial of the normalized Cauchy kernel. -/
def suzukiXiNormalizedCauchyDenominator (z : ℂ) : ℂ[X] :=
  (X - C z) * (C 1 + X ^ 2)

/-- The real-axis normalized Cauchy kernel used in the Herglotz transform. -/
def suzukiXiNormalizedCauchyKernel (z : ℂ) (x : ℝ) : ℂ :=
  1 / ((x : ℂ) - z) -
    (x : ℂ) / (1 + (x : ℂ) ^ 2)

/-- A real point cannot equal a nonreal spectral parameter. -/
theorem ofReal_sub_ne_zero_of_im_ne_zero
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    (x : ℂ) - z ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub,
    Complex.zero_im, neg_eq_zero] at him
  exact hz him

/-- The quadratic real normalization denominator never vanishes. -/
theorem one_add_sq_ofReal_ne_zero (x : ℝ) :
    (1 : ℂ) + (x : ℂ) ^ 2 ≠ 0 := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  exact_mod_cast hpos.ne'

/-- Evaluation of the normalized Cauchy numerator. -/
theorem suzukiXiNormalizedCauchyNumerator_eval
    (z : ℂ) (x : ℝ) :
    (suzukiXiNormalizedCauchyNumerator z).eval (x : ℂ) =
      z * (x : ℂ) + 1 := by
  simp [suzukiXiNormalizedCauchyNumerator]

/-- Evaluation of the normalized Cauchy denominator. -/
theorem suzukiXiNormalizedCauchyDenominator_eval
    (z : ℂ) (x : ℝ) :
    (suzukiXiNormalizedCauchyDenominator z).eval (x : ℂ) =
      ((x : ℂ) - z) * (1 + (x : ℂ) ^ 2) := by
  simp [suzukiXiNormalizedCauchyDenominator]

/-- The normalized numerator has degree at most one. -/
theorem suzukiXiNormalizedCauchyNumerator_natDegree_le_one
    (z : ℂ) :
    (suzukiXiNormalizedCauchyNumerator z).natDegree ≤ 1 := by
  unfold suzukiXiNormalizedCauchyNumerator
  exact natDegree_linear_le

/-- The normalized denominator has degree exactly three. -/
theorem suzukiXiNormalizedCauchyDenominator_natDegree
    (z : ℂ) :
    (suzukiXiNormalizedCauchyDenominator z).natDegree = 3 := by
  unfold suzukiXiNormalizedCauchyDenominator
  compute_degree <;> norm_num

/-- The denominator polynomial has no real zero for a nonreal parameter. -/
theorem suzukiXiNormalizedCauchyDenominator_eval_ne_zero
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    (suzukiXiNormalizedCauchyDenominator z).eval (x : ℂ) ≠ 0 := by
  rw [suzukiXiNormalizedCauchyDenominator_eval]
  exact mul_ne_zero (ofReal_sub_ne_zero_of_im_ne_zero hz x)
    (one_add_sq_ofReal_ne_zero x)

/-- Algebraic reduction of the normalized Cauchy kernel to the preceding
degree-one-over-degree-three polynomial quotient. -/
theorem suzukiXiNormalizedCauchyKernel_eq_polynomialQuotient
    {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    suzukiXiNormalizedCauchyKernel z x =
      (suzukiXiNormalizedCauchyNumerator z).eval (x : ℂ) /
        (suzukiXiNormalizedCauchyDenominator z).eval (x : ℂ) := by
  rw [suzukiXiNormalizedCauchyNumerator_eval,
    suzukiXiNormalizedCauchyDenominator_eval]
  unfold suzukiXiNormalizedCauchyKernel
  have hxz := ofReal_sub_ne_zero_of_im_ne_zero hz x
  have hquad := one_add_sq_ofReal_ne_zero x
  field_simp [hxz, hquad]
  ring

/-- The normalized Cauchy kernel is absolutely integrable for every nonreal
parameter. -/
theorem integrable_suzukiXiNormalizedCauchyKernel
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (suzukiXiNormalizedCauchyKernel z) := by
  have hgap :
      (suzukiXiNormalizedCauchyNumerator z).natDegree + 2 ≤
        (suzukiXiNormalizedCauchyDenominator z).natDegree := by
    have hnum := suzukiXiNormalizedCauchyNumerator_natDegree_le_one z
    rw [suzukiXiNormalizedCauchyDenominator_natDegree]
    omega
  have h := polynomialBoundaryQuotient_integrable_of_natDegree_add_two_le
    hgap (suzukiXiNormalizedCauchyDenominator_eval_ne_zero hz)
  apply h.congr
  exact Eventually.of_forall fun x ↦
    (suzukiXiNormalizedCauchyKernel_eq_polynomialQuotient hz x).symm

/-- The spectral-xi carrier density times the normalized Cauchy kernel. -/
def suzukiXiCarrierHerglotzIntegrand (z : ℂ) (x : ℝ) : ℂ :=
  (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ) *
    suzukiXiNormalizedCauchyKernel z x

/-- The density-weighted normalized Cauchy kernel is absolutely integrable
for every nonreal parameter. -/
theorem integrable_suzukiXiCarrierHerglotzIntegrand
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (suzukiXiCarrierHerglotzIntegrand z) := by
  have hdensity : AEStronglyMeasurable (fun x : ℝ ↦
      (suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp
      measurable_suzukiXiRealAxisArithmeticCarrierDensity).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖(suzukiXiRealAxisArithmeticCarrierDensity x : ℂ)‖ ≤ 1 := by
    exact Eventually.of_forall fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiXiRealAxisArithmeticCarrierDensity_nonneg x)]
      exact suzukiXiRealAxisArithmeticCarrierDensity_le_one x
  exact (integrable_suzukiXiNormalizedCauchyKernel hz).bdd_mul
    hdensity hbound

/-- The normalized scalar Cauchy--Herglotz transform of the exact
spectral-xi carrier density. -/
def suzukiXiCarrierHerglotzTransform (z : ℂ) : ℂ :=
  ∫ x : ℝ, suzukiXiCarrierHerglotzIntegrand z x

/-- The normalized Cauchy kernel respects conjugation of its nonreal
parameter. -/
theorem suzukiXiNormalizedCauchyKernel_conj
    (z : ℂ) (x : ℝ) :
    suzukiXiNormalizedCauchyKernel (starRingEnd ℂ z) x =
      starRingEnd ℂ (suzukiXiNormalizedCauchyKernel z x) := by
  unfold suzukiXiNormalizedCauchyKernel
  simp only [map_sub, map_div₀, map_one, map_add, map_pow,
    Complex.conj_ofReal]

/-- The density-weighted Herglotz integrand respects conjugation. -/
theorem suzukiXiCarrierHerglotzIntegrand_conj
    (z : ℂ) (x : ℝ) :
    suzukiXiCarrierHerglotzIntegrand (starRingEnd ℂ z) x =
      starRingEnd ℂ (suzukiXiCarrierHerglotzIntegrand z x) := by
  unfold suzukiXiCarrierHerglotzIntegrand
  rw [suzukiXiNormalizedCauchyKernel_conj]
  simp

/-- The normalized carrier transform has the Schwarz reflection symmetry. -/
theorem suzukiXiCarrierHerglotzTransform_conj (z : ℂ) :
    suzukiXiCarrierHerglotzTransform (starRingEnd ℂ z) =
      starRingEnd ℂ (suzukiXiCarrierHerglotzTransform z) := by
  unfold suzukiXiCarrierHerglotzTransform
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦
    suzukiXiCarrierHerglotzIntegrand_conj z x

/-- The difference of two normalized Cauchy kernels is their exact
two-resolvent divided difference. -/
theorem suzukiXiNormalizedCauchyKernel_sub
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : ℝ) :
    suzukiXiNormalizedCauchyKernel z x -
        suzukiXiNormalizedCauchyKernel w x =
      (z - w) /
        (((x : ℂ) - w) * ((x : ℂ) - z)) := by
  unfold suzukiXiNormalizedCauchyKernel
  have hxz := ofReal_sub_ne_zero_of_im_ne_zero hz x
  have hxw := ofReal_sub_ne_zero_of_im_ne_zero hw x
  have hquad := one_add_sq_ofReal_ne_zero x
  field_simp [hxz, hxw, hquad]
  ring

/-- At two off-axis genuine nodes, the difference of the density-weighted
transform integrands is the node separation times the arithmetic carrier
Gram density. -/
theorem suzukiXiCarrierHerglotzIntegrand_node_sub
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0)
    (x : ℝ) :
    suzukiXiCarrierHerglotzIntegrand
          (zetaSpectralCoordinate sigma.1) x -
        suzukiXiCarrierHerglotzIntegrand
          (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) x =
      (zetaSpectralCoordinate sigma.1 -
          starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        suzukiXiBoundaryArithmeticCarrierGramIntegrand rho sigma x := by
  have hconj :
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im ≠ 0 := by
    simp only [Complex.conj_im, neg_ne_zero]
    exact hrho
  unfold suzukiXiCarrierHerglotzIntegrand
    suzukiXiBoundaryArithmeticCarrierGramIntegrand
  rw [← mul_sub]
  rw [suzukiXiNormalizedCauchyKernel_sub hsigma hconj]
  ring

/-- The difference of transform values at two off-axis node parameters is
exactly their separation times the common-carrier Gram kernel. -/
theorem suzukiXiCarrierHerglotzTransform_node_sub
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate sigma.1) -
        suzukiXiCarrierHerglotzTransform
          (starRingEnd ℂ (zetaSpectralCoordinate rho.1)) =
      (zetaSpectralCoordinate sigma.1 -
          starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        suzukiXiBoundaryCarrierGramKernel rho sigma := by
  have hconj :
      (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im ≠ 0 := by
    simp only [Complex.conj_im, neg_ne_zero]
    exact hrho
  unfold suzukiXiCarrierHerglotzTransform
  rw [← integral_sub
    (integrable_suzukiXiCarrierHerglotzIntegrand hsigma)
    (integrable_suzukiXiCarrierHerglotzIntegrand hconj),
    suzukiXiBoundaryCarrierGramKernel_eq_arithmetic_integral,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦
    suzukiXiCarrierHerglotzIntegrand_node_sub
      rho sigma hrho hsigma x

/-- Schwarz reflection turns the preceding identity into the standard Pick
numerator `H(z) - conj(H(w))`. -/
theorem suzukiXiCarrierHerglotzTransform_node_sub_conj
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate sigma.1) -
        starRingEnd ℂ (suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate rho.1)) =
      (zetaSpectralCoordinate sigma.1 -
          starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        suzukiXiBoundaryCarrierGramKernel rho sigma := by
  rw [← suzukiXiCarrierHerglotzTransform_conj]
  exact suzukiXiCarrierHerglotzTransform_node_sub
    rho sigma hrho hsigma

/-- Two nodes in the open upper half-plane have nonzero Pick denominator. -/
theorem upper_nodes_sub_conj_ne_zero
    (rho sigma : NontrivialZetaZero)
    (hrho : 0 < (zetaSpectralCoordinate rho.1).im)
    (hsigma : 0 < (zetaSpectralCoordinate sigma.1).im) :
    zetaSpectralCoordinate sigma.1 -
        starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  linarith

/-- On the genuine upper spectral-xi divisor, the common-carrier Gram kernel
is exactly the Pick divided-difference kernel of the scalar arithmetic
Herglotz transform. -/
theorem suzukiXiBoundaryCarrierGramKernel_eq_herglotzPick
    (rho sigma : NontrivialZetaZero)
    (hrho : 0 < (zetaSpectralCoordinate rho.1).im)
    (hsigma : 0 < (zetaSpectralCoordinate sigma.1).im) :
    suzukiXiBoundaryCarrierGramKernel rho sigma =
      (suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate sigma.1) -
        starRingEnd ℂ (suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate rho.1))) /
      (zetaSpectralCoordinate sigma.1 -
        starRingEnd ℂ (zetaSpectralCoordinate rho.1)) := by
  have hden := upper_nodes_sub_conj_ne_zero rho sigma hrho hsigma
  have hidentity := suzukiXiCarrierHerglotzTransform_node_sub_conj
    rho sigma hrho.ne' hsigma.ne'
  rw [hidentity]
  field_simp [hden]

/-- The imaginary part of the normalized Cauchy kernel is the positive
Poisson resolvent density when the parameter lies in the upper half-plane. -/
theorem suzukiXiNormalizedCauchyKernel_im
    (z : ℂ) (x : ℝ) :
    (suzukiXiNormalizedCauchyKernel z x).im =
      z.im / Complex.normSq ((x : ℂ) - z) := by
  unfold suzukiXiNormalizedCauchyKernel
  simp only [Complex.sub_im, one_div, Complex.inv_im,
    Complex.ofReal_im, zero_sub, neg_neg, Complex.div_im,
    Complex.ofReal_re, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, pow_two, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Exact imaginary part of the density-weighted Herglotz integrand. -/
theorem suzukiXiCarrierHerglotzIntegrand_im
    (z : ℂ) (x : ℝ) :
    (suzukiXiCarrierHerglotzIntegrand z x).im =
      suzukiXiRealAxisArithmeticCarrierDensity x *
        (z.im / Complex.normSq ((x : ℂ) - z)) := by
  unfold suzukiXiCarrierHerglotzIntegrand
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  rw [suzukiXiNormalizedCauchyKernel_im]
  ring

/-- The imaginary part of the normalized transform is the integral of an
explicit positive Poisson density. -/
theorem suzukiXiCarrierHerglotzTransform_im_eq
    {z : ℂ} (hz : z.im ≠ 0) :
    (suzukiXiCarrierHerglotzTransform z).im =
      ∫ x : ℝ,
        suzukiXiRealAxisArithmeticCarrierDensity x *
          (z.im / Complex.normSq ((x : ℂ) - z)) := by
  unfold suzukiXiCarrierHerglotzTransform
  calc
    (∫ x : ℝ, suzukiXiCarrierHerglotzIntegrand z x).im =
        ∫ x : ℝ, (suzukiXiCarrierHerglotzIntegrand z x).im := by
      simpa using
        (integral_im (integrable_suzukiXiCarrierHerglotzIntegrand hz)).symm
    _ = ∫ x : ℝ,
        suzukiXiRealAxisArithmeticCarrierDensity x *
          (z.im / Complex.normSq ((x : ℂ) - z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦
        suzukiXiCarrierHerglotzIntegrand_im z x

/-- The normalized spectral-xi carrier transform maps the open upper
half-plane into the closed upper half-plane: it is a Herglotz function at the
level of its checked integral representation. -/
theorem suzukiXiCarrierHerglotzTransform_im_nonneg
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (suzukiXiCarrierHerglotzTransform z).im := by
  rw [suzukiXiCarrierHerglotzTransform_im_eq hz.ne']
  apply integral_nonneg
  intro x
  exact mul_nonneg
    (suzukiXiRealAxisArithmeticCarrierDensity_nonneg x)
    (div_nonneg hz.le (Complex.normSq_nonneg _))

/-- On one genuine upper xi node, the diagonal carrier Gram value is the
imaginary part of the scalar Herglotz transform divided by the node height. -/
theorem suzukiXiBoundaryCarrierGramKernel_self_eq_herglotz_im_div_im
    (rho : NontrivialZetaZero)
    (hrho : 0 < (zetaSpectralCoordinate rho.1).im) :
    suzukiXiBoundaryCarrierGramKernel rho rho =
      (((suzukiXiCarrierHerglotzTransform
          (zetaSpectralCoordinate rho.1)).im /
        (zetaSpectralCoordinate rho.1).im : ℝ) : ℂ) := by
  rw [suzukiXiBoundaryCarrierGramKernel_eq_herglotzPick
    rho rho hrho hrho]
  rw [Complex.sub_conj, Complex.sub_conj]
  push_cast
  field_simp [hrho.ne', Complex.I_ne_zero]

/-- Consequently, the normalized zero-function norm square is an exact
Herglotz-height ratio times its analytic multiplicity normalization. -/
theorem norm_sq_suzukiRealAxisZeroFunctionLp_eq_herglotz
    (rho : NontrivialZetaZero)
    (hrho : 0 < (zetaSpectralCoordinate rho.1).im) :
    (‖suzukiRealAxisZeroFunctionLp rho‖ : ℂ) ^ 2 =
      (suzukiXiZeroNormalization rho : ℂ) ^ 2 *
        (((suzukiXiCarrierHerglotzTransform
            (zetaSpectralCoordinate rho.1)).im /
          (zetaSpectralCoordinate rho.1).im : ℝ) : ℂ) := by
  rw [← sq_normalization_mul_suzukiXiBoundaryCarrierGramKernel_self,
    suzukiXiBoundaryCarrierGramKernel_self_eq_herglotz_im_div_im rho hrho]

end

end RiemannGaussian
