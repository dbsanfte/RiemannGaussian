import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceHeat
import RiemannGaussian.RiemannXiBoundaryHeatResidues
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cauchy--Green coordinates for the arithmetic boundary heat

The fixed-time hyperbolic heat weight is not holomorphic in the zero
coordinate, so it cannot legitimately be inserted into a one-variable
residue theorem.  This file instead moves the boundary heat detector into
the shifted Laplace coordinate `p = rho - 1/2` and computes its full real
derivative.

The resulting kernel is

`-2 * re p * exp (-tau * ((x - im p)^2 + (re p)^2))`.

It vanishes on the critical boundary `re p = 0`, is positive in the selected
half-strip `re p < 0`, and its local pole-cleared arithmetic residues sum to
the complete fixed-time boundary heat.  Its explicit Cauchy--Green source
is nonzero on the critical boundary, formally certifying the obstruction to
a holomorphic weighting shortcut.

Finally, Lean proves an exact Cauchy--Green area--boundary identity for the
kernel times the pole-cleared arithmetic continuation on every zero-free
rectangle.  Passing this identity across punctures and then to an expanding
half-strip remains the next global divisor step; no zero-location conclusion
is asserted here.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The smooth boundary heat kernel in the shifted arithmetic Laplace
coordinate `p = rho - 1/2`. -/
def suzukiChebyshevLaplaceBoundaryHeatKernel
    (x tau : ℝ) : ℂ → ℂ :=
  Complex.ofRealCLM ∘
    ((fun p : ℂ => -2 * p.re) *
      fun p : ℂ => Real.exp
        (-tau * ((x - p.im) ^ 2 + p.re ^ 2)))

/-- Pointwise formula for the shifted-coordinate boundary heat kernel. -/
@[simp] theorem suzukiChebyshevLaplaceBoundaryHeatKernel_apply
    (x tau : ℝ) (p : ℂ) :
    suzukiChebyshevLaplaceBoundaryHeatKernel x tau p =
      ((-2 * p.re * Real.exp
        (-tau * ((x - p.im) ^ 2 + p.re ^ 2))) : ℝ) := rfl

/-- Boundary-to-spectral distance written in the shifted arithmetic zero
coordinate. -/
theorem normSq_boundary_sub_zetaSpectralCoordinate_eq_laplaceZeroCoordinate
    (x : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq
        ((x : ℂ) - zetaSpectralCoordinate rho.1) =
      (x - (suzukiChebyshevLaplaceZeroCoordinate rho).im) ^ 2 +
        (suzukiChebyshevLaplaceZeroCoordinate rho).re ^ 2 := by
  unfold suzukiChebyshevLaplaceZeroCoordinate zetaSpectralCoordinate
    Complex.normSq
  simp
  ring

/-- At a zeta-zero coordinate, the shifted kernel is exactly the existing
fixed-time boundary heat weight. -/
theorem suzukiChebyshevLaplaceBoundaryHeatKernel_zeroCoordinate
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho) =
      ((2 * (zetaSpectralCoordinate rho.1).im *
        Real.exp (-(Complex.normSq
          ((x : ℂ) - zetaSpectralCoordinate rho.1) * tau))) : ℝ) := by
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply,
    normSq_boundary_sub_zetaSpectralCoordinate_eq_laplaceZeroCoordinate]
  unfold suzukiChebyshevLaplaceZeroCoordinate zetaSpectralCoordinate
  simp
  ring_nf

/-- The selected upper spectral half-plane is the negative-real half of the
shifted arithmetic Laplace strip. -/
theorem suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper
    (rho : NontrivialZetaZero) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0 ↔
      0 < (zetaSpectralCoordinate rho.1).im := by
  unfold suzukiChebyshevLaplaceZeroCoordinate zetaSpectralCoordinate
  simp

/-- The selected boundary heat residue, expressed entirely in the shifted
arithmetic Laplace coordinate. -/
def suzukiChebyshevLaplaceBoundaryHeatResidue
    (x tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0 then
    suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho) *
      (analyticZetaZeroMultiplicity rho : ℂ)
  else 0

/-- Each shifted arithmetic boundary residue is the existing genuine
spectral-xi boundary heat residue. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho =
      riemannXiUpperHyperbolicBoundaryHeatResidue x tau rho := by
  by_cases hp : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0
  · have hupper :=
      (suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mp hp
    rw [suzukiChebyshevLaplaceBoundaryHeatResidue, if_pos hp,
      riemannXiUpperHyperbolicBoundaryHeatResidue,
      zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper,
      suzukiChebyshevLaplaceBoundaryHeatKernel_zeroCoordinate]
    push_cast
    ring
  · have hupper : ¬0 < (zetaSpectralCoordinate rho.1).im :=
      fun h => hp
        ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mpr h)
    rw [suzukiChebyshevLaplaceBoundaryHeatResidue, if_neg hp,
      riemannXiUpperHyperbolicBoundaryHeatResidue,
      zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
    norm_num

/-- The complete shifted arithmetic boundary residue series sums to the
existing positive fixed-time boundary heat detector. -/
theorem hasSum_suzukiChebyshevLaplaceBoundaryHeatResidue
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasSum (suzukiChebyshevLaplaceBoundaryHeatResidue x tau)
      (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) := by
  exact (hasSum_riemannXiUpperHyperbolicBoundaryHeatResidue x htau).congr_fun
    (suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi x tau)

/-- A selected boundary heat coefficient is the local weighted residue of
the pole-cleared arithmetic continuation. -/
theorem tendsto_suzukiChebyshevLaplaceBoundaryHeatKernel_mul_poleCleared
    (x tau : ℝ) (rho : NontrivialZetaZero)
    (hp : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (fun w : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          ((w - suzukiChebyshevLaplaceZeroCoordinate rho) *
            suzukiChebyshevLogAverageLaplacePoleClearedContinuation w))
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  have hconst : Tendsto
      (fun _ : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (suzukiChebyshevLaplaceZeroCoordinate rho))
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho))) :=
    tendsto_const_nhds
  have hlimit := hconst.mul
    (tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_poleClearedContinuation
      rho)
  simpa only [suzukiChebyshevLaplaceBoundaryHeatResidue, if_pos hp] using
    hlimit

/-- The shifted boundary heat kernel is everywhere real differentiable. -/
theorem differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
    (x tau : ℝ) (p : ℂ) :
    DifferentiableAt ℝ
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM p :=
    Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM p :=
    Complex.imCLM.hasFDerivAt
  have hxsub : HasFDerivAt (fun w : ℂ => x - w.im)
      (-Complex.imCLM) p := him.const_sub x
  have hD := (hxsub.pow 2).add (hre.pow 2)
  have hneg := hD.const_mul (-tau)
  have hexp := hneg.exp
  have hcoef := hre.const_mul (-2)
  have hreal := hcoef.mul hexp
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp p hreal
  change HasFDerivAt (𝕜 := ℝ)
    (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) _ p at hcomplex
  exact hcomplex.differentiableAt

/-- Explicit full real Fréchet derivative of the shifted boundary heat
kernel. -/
theorem fderiv_real_suzukiChebyshevLaplaceBoundaryHeatKernel
    (x tau : ℝ) (p : ℂ) :
    fderiv ℝ (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p =
      Complex.reCLM.smulRight
          (((4 * tau * p.re ^ 2 - 2) * Real.exp
            (-(tau * ((x - p.im) ^ 2 + p.re ^ 2))) : ℝ) : ℂ) +
        Complex.imCLM.smulRight
          (((-4 * tau * p.re * (x - p.im)) * Real.exp
            (-(tau * ((x - p.im) ^ 2 + p.re ^ 2))) : ℝ) : ℂ) := by
  have hre : HasFDerivAt (fun w : ℂ => w.re) Complex.reCLM p :=
    Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun w : ℂ => w.im) Complex.imCLM p :=
    Complex.imCLM.hasFDerivAt
  have hxsub : HasFDerivAt (fun w : ℂ => x - w.im)
      (-Complex.imCLM) p := him.const_sub x
  have hD := (hxsub.pow 2).add (hre.pow 2)
  have hneg := hD.const_mul (-tau)
  have hexp := hneg.exp
  have hcoef := hre.const_mul (-2)
  have hreal := hcoef.mul hexp
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp p hreal
  change HasFDerivAt (𝕜 := ℝ)
    (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) _ p at hcomplex
  rw [hcomplex.fderiv]
  ext q
  simp [pow_two]
  ring

/-- The explicit `2 i partial-bar` source of the non-holomorphic boundary
heat kernel. -/
def suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
    (x tau : ℝ) (p : ℂ) : ℂ :=
  (2 * Real.exp (-tau * ((x - p.im) ^ 2 + p.re ^ 2)) : ℂ) *
    (2 * tau * p.re * (x - p.im) +
      Complex.I * (2 * tau * p.re ^ 2 - 1))

/-- The Cauchy--Green source is exactly
`i * partial_re kernel - partial_im kernel`. -/
theorem cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel
    (x tau : ℝ) (p : ℂ) :
    Complex.I • fderiv ℝ
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p 1 -
        fderiv ℝ (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p
          Complex.I =
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p := by
  rw [fderiv_real_suzukiChebyshevLaplaceBoundaryHeatKernel]
  simp [suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource]
  ring

/-- The shifted boundary heat kernel vanishes on the critical boundary. -/
theorem suzukiChebyshevLaplaceBoundaryHeatKernel_eq_zero_of_re_eq_zero
    (x tau : ℝ) {p : ℂ} (hp : p.re = 0) :
    suzukiChebyshevLaplaceBoundaryHeatKernel x tau p = 0 := by
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply, hp]
  norm_num

/-- The real value of the shifted boundary kernel is strictly positive in
the selected half-strip. -/
theorem suzukiChebyshevLaplaceBoundaryHeatKernel_re_pos_of_re_neg
    (x tau : ℝ) {p : ℂ} (hp : p.re < 0) :
    0 < (suzukiChebyshevLaplaceBoundaryHeatKernel x tau p).re := by
  rw [suzukiChebyshevLaplaceBoundaryHeatKernel_apply, Complex.ofReal_re]
  exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) hp)
    (Real.exp_pos _)

/-- On the critical boundary the Cauchy--Green source is an explicit
nonzero imaginary Gaussian. -/
theorem suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource_of_re_eq_zero
    (x tau : ℝ) {p : ℂ} (hp : p.re = 0) :
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p =
      -(2 * Real.exp (-tau * (x - p.im) ^ 2) : ℂ) * Complex.I := by
  unfold suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
  rw [hp]
  norm_num

/-- The boundary value of the Cauchy--Green source never vanishes. -/
theorem suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource_ne_zero_of_re_eq_zero
    (x tau : ℝ) {p : ℂ} (hp : p.re = 0) :
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p ≠ 0 := by
  rw [suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource_of_re_eq_zero
    x tau hp]
  exact mul_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))))
    Complex.I_ne_zero

/-- In particular, the boundary heat weight is not complex differentiable
on the critical boundary; a holomorphic residue theorem cannot absorb it. -/
theorem suzukiChebyshevLaplaceBoundaryHeatKernel_not_differentiableAt_complex
    (x tau : ℝ) {p : ℂ} (hp : p.re = 0) :
    ¬DifferentiableAt ℂ
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p := by
  intro hcomplex
  have hcr :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hcomplex).2
  have hsource :=
    cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel x tau p
  rw [hcr, sub_self] at hsource
  exact
    suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource_ne_zero_of_re_eq_zero
      x tau hp hsource.symm

/-- Global real differentiability of the shifted boundary heat kernel. -/
theorem differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
    (x tau : ℝ) :
    Differentiable ℝ
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) :=
  fun p =>
    differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel x tau p

/-- The explicit Cauchy--Green source is continuous. -/
theorem continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
    (x tau : ℝ) :
    Continuous
      (suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau) := by
  unfold suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
  fun_prop

/-- Exact Cauchy--Green area--boundary identity for the unweighted shifted
boundary heat kernel on every rectangle. -/
theorem suzukiChebyshevLaplaceBoundaryHeatKernel_cauchyGreenRectangle
    (x tau : ℝ) (z w : ℂ) :
    (∫ a : ℝ in z.re..w.re,
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (a + z.im * Complex.I)) -
        (∫ a : ℝ in z.re..w.re,
          suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (a + w.im * Complex.I)) +
      Complex.I • (∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (w.re + b * Complex.I)) -
      Complex.I • (∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (z.re + b * Complex.I)) =
      ∫ a : ℝ in z.re..w.re, ∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau
          (a + b * Complex.I) := by
  let R : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  have hd : DifferentiableOn ℝ
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) R :=
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau).differentiableOn
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hsource : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau) R :=
    (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
      x tau).continuousOn.integrableOn_compact hcompact
  have hi : IntegrableOn
      (fun p : ℂ =>
        Complex.I • fderiv ℝ
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p 1 -
          fderiv ℝ
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) p
              Complex.I) R := by
    simpa only [
      cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel] using
      hsource
  simpa only [
    cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel] using
    (Complex.integral_boundary_rect_of_differentiableOn_real
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) z w hd hi)

/-- The `2 i partial-bar` source operator used by the rectangular
Cauchy--Green theorem. -/
def complexCauchyGreenSource (f : ℂ → ℂ) (p : ℂ) : ℂ :=
  Complex.I • fderiv ℝ f p 1 - fderiv ℝ f p Complex.I

/-- Multiplication by a complex-differentiable factor only multiplies the
Cauchy--Green source; its own `partial-bar` contribution cancels. -/
theorem complexCauchyGreenSource_mul_of_differentiableAt_complex
    {f g : ℂ → ℂ} {p : ℂ}
    (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℂ g p) :
    complexCauchyGreenSource (fun z => f z * g z) p =
      complexCauchyGreenSource f p * g p := by
  have hgReal : DifferentiableAt ℝ g p := hg.restrictScalars ℝ
  have hproduct := hf.hasFDerivAt.mul hgReal.hasFDerivAt
  have hcr :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hg).2
  change complexCauchyGreenSource (f * g) p =
    complexCauchyGreenSource f p * g p
  unfold complexCauchyGreenSource
  rw [hproduct.fderiv]
  simp only [add_apply, smul_apply]
  rw [hcr]
  ring

/-- The boundary heat kernel multiplied by the pole-cleared arithmetic
Laplace continuation. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (p : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau p *
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation p

/-- On the zero-free continuation domain, the weighted response has exactly
the heat source times the arithmetic response as its Cauchy--Green source. -/
theorem complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) {p : ℂ}
    (hp : p ∈ suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    complexCauchyGreenSource
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) p =
      suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p *
        suzukiChebyshevLogAverageLaplacePoleClearedContinuation p := by
  have hP : DifferentiableAt ℂ
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation p :=
    (analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation
      p hp).differentiableAt
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  rw [complexCauchyGreenSource_mul_of_differentiableAt_complex
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau p) hP]
  exact congrArg
    (fun q : ℂ => q *
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation p)
    (cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel x tau p)

/-- On every rectangle contained in the zero-free continuation domain, the
boundary integral of the heat-weighted arithmetic response equals the area
integral of the explicit heat source times that response. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_cauchyGreenRectangle
    (x tau : ℝ) (z w : ℂ)
    (hdomain :
      [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain) :
    (∫ a : ℝ in z.re..w.re,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          (a + z.im * Complex.I)) -
        (∫ a : ℝ in z.re..w.re,
          suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
            (a + w.im * Complex.I)) +
      Complex.I • (∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          (w.re + b * Complex.I)) -
      Complex.I • (∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau
          (z.re + b * Complex.I)) =
      ∫ a : ℝ in z.re..w.re, ∫ b : ℝ in z.im..w.im,
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau
            (a + b * Complex.I) *
          suzukiChebyshevLogAverageLaplacePoleClearedContinuation
            (a + b * Complex.I) := by
  let R : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  let P := suzukiChebyshevLogAverageLaplacePoleClearedContinuation
  have hPanalytic : AnalyticOnNhd ℂ P R :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation.mono
      hdomain
  have hd : DifferentiableOn ℝ
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) R := by
    intro p hp
    unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    exact
      ((differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
          x tau p).mul
        ((hPanalytic p hp).differentiableAt.restrictScalars ℝ)
      ).differentiableWithinAt
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hexplicit : IntegrableOn
      (fun p : ℂ =>
        suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau p * P p)
      R :=
    ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
      x tau).continuousOn.mul
      hPanalytic.continuousOn).integrableOn_compact hcompact
  have hi : IntegrableOn
      (fun p : ℂ => complexCauchyGreenSource
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) p) R :=
    hexplicit.congr_fun (fun p hp =>
      (complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
        x tau (hdomain hp)).symm) hcompact.measurableSet
  have hboundary :=
    Complex.integral_boundary_rect_of_differentiableOn_real
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) z w hd (by
        simpa only [complexCauchyGreenSource] using hi)
  calc
    _ = ∫ a : ℝ in z.re..w.re, ∫ b : ℝ in z.im..w.im,
          complexCauchyGreenSource
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)
              (a + b * Complex.I) := by
      simpa only [complexCauchyGreenSource] using hboundary
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      exact
        complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
          x tau (hdomain ⟨by simpa using ha, by simpa using hb⟩)

end

end RiemannGaussian
