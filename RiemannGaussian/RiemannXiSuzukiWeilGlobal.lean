import RiemannGaussian.RiemannXiSuzukiWeilArchimedean
import RiemannGaussian.GaussianXiDivisorContour
import RiemannGaussian.GaussianXiQuantitativeContour

/-!
# The global Suzuki--Weil divisor bridge

This file begins the one remaining global step in Suzuki's positive-time
formula: passing from the genuine spectral-xi zero divisor to the completely
evaluated local Weil right-hand side.

The first stage is finite and unconditional.  We realize Suzuki's transformed
test as a holomorphic spectral weight, remove every logarithmic-derivative
pole in a finite xi contour rectangle, and identify the resulting residues
with the literal finite windows of `riemannXiSuzukiSpectralP`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-! ## The holomorphic Suzuki spectral weight -/

/-- Suzuki's continuously extended screw coefficient is the divided
difference of its entire spectral exponential. -/
theorem suzukiSpectralScrewCoefficient_eq_dslope
    (t : ℝ) (alpha : ℂ) :
    suzukiSpectralScrewCoefficient t alpha =
      dslope (fun w : ℂ ↦
        Complex.exp (-Complex.I * w * (t : ℂ))) 0 alpha := by
  by_cases halpha : alpha = 0
  · subst alpha
    rw [suzukiSpectralScrewCoefficient_zero, dslope_same]
    have hinner : HasDerivAt
        (fun w : ℂ ↦ -Complex.I * w * (t : ℂ))
        (-Complex.I * (t : ℂ)) 0 := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id (0 : ℂ)).const_mul
          (-Complex.I)).mul_const (t : ℂ))
    have hexp :=
      (Complex.hasDerivAt_exp
        (-Complex.I * (0 : ℂ) * (t : ℂ))).comp 0 hinner
    rw [show (fun w : ℂ ↦
        Complex.exp (-Complex.I * w * (t : ℂ))) =
      Complex.exp ∘ (fun w : ℂ ↦ -Complex.I * w * (t : ℂ)) by rfl,
      hexp.deriv]
    simp
  · rw [suzukiSpectralScrewCoefficient_of_ne_zero t halpha,
      dslope_of_ne _ halpha, slope_def_field]
    unfold spectralScrewExponential
    simp

/-- As a function of spectral frequency, Suzuki's continuously extended
screw coefficient is entire. -/
theorem differentiable_suzukiSpectralScrewCoefficient (t : ℝ) :
    Differentiable ℂ (suzukiSpectralScrewCoefficient t) := by
  have hbase : DifferentiableOn ℂ
      (fun w : ℂ ↦ Complex.exp (-Complex.I * w * (t : ℂ))) univ := by
    fun_prop
  have hslope : DifferentiableOn ℂ
      (dslope (fun w : ℂ ↦
        Complex.exp (-Complex.I * w * (t : ℂ))) 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).2 hbase
  rw [show suzukiSpectralScrewCoefficient t =
      dslope (fun w : ℂ ↦
        Complex.exp (-Complex.I * w * (t : ℂ))) 0 by
    funext alpha
    exact suzukiSpectralScrewCoefficient_eq_dslope t alpha]
  exact differentiableOn_univ.mp hslope

/-- The Fourier--Laplace transform of Suzuki's Weil test, regarded as a
function of the spectral variable.  Its only possible pole is the evaluation
point `z`, which lies above the contour strip used below. -/
def suzukiWeilSpectralTransform
    (t : ℝ) (z gamma : ℂ) : ℂ :=
  suzukiSpectralScrewCoefficient t gamma / (z - gamma)

/-- The Suzuki spectral transform is analytic away from its evaluation
pole. -/
theorem analyticAt_suzukiWeilSpectralTransform_of_ne
    (t : ℝ) (z : ℂ) {gamma : ℂ} (hgamma : gamma ≠ z) :
    AnalyticAt ℂ (suzukiWeilSpectralTransform t z) gamma := by
  unfold suzukiWeilSpectralTransform
  exact (differentiable_suzukiSpectralScrewCoefficient t).analyticAt gamma |>.div
    (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr hgamma.symm)

/-- Above the height-one contour, the Suzuki spectral transform is analytic
at every point of the closed spectral rectangle. -/
theorem analyticAt_suzukiWeilSpectralTransform_of_mem_rectangle
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} {gamma : ℂ}
    (hgamma : gamma ∈ spectralContourRectangle T) :
    AnalyticAt ℂ (suzukiWeilSpectralTransform t z) gamma := by
  apply analyticAt_suzukiWeilSpectralTransform_of_ne
  intro heq
  have him : |gamma.im| ≤ 1 := hgamma.2
  rw [heq, abs_le] at him
  linarith

/-- On every genuine zero, the Suzuki transform is exactly the zero summand
before multiplication by analytic multiplicity. -/
theorem suzukiWeilSpectralTransform_zetaSpectralCoordinate
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    suzukiWeilSpectralTransform t z
        (zetaSpectralCoordinate rho.1) =
      suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1) /
        suzukiXiUpperEvaluationDenominator z
          (zetaSpectralCoordinate rho.1) := by
  rfl

/-! ## Local spectral-xi residues -/

/-- A spectral xi zero cannot equal a point above the height-one contour. -/
theorem zetaSpectralCoordinate_ne_of_one_lt_im
    {z : ℂ} (hz : 1 < z.im) (rho : NontrivialZetaZero) :
    zetaSpectralCoordinate rho.1 ≠ z := by
  intro heq
  have him := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  rw [heq] at him
  have hzAbs : z.im ≤ |z.im| := le_abs_self z.im
  linarith

/-- The Suzuki transform multiplied by the genuine spectral-xi negative
logarithmic derivative. -/
def suzukiXiWeilSpectralIntegrand
    (t : ℝ) (z w : ℂ) : ℂ :=
  suzukiWeilSpectralTransform t z w *
    xiSpectralNegativeLogDerivative w

/-- The true local residue of the Suzuki-weighted spectral-xi integrand. -/
def suzukiXiWeilSpectralResidue
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  suzukiWeilSpectralTransform t z
      (zetaSpectralCoordinate rho.1) *
    (Complex.I * (analyticZetaZeroMultiplicity rho : ℂ))

/-- The constant-numerator principal part attached to one genuine xi zero. -/
def suzukiXiWeilSpectralPrincipalPart
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) (w : ℂ) : ℂ :=
  suzukiXiWeilSpectralResidue t z rho /
    (w - zetaSpectralCoordinate rho.1)

/-- Away from both the xi divisor and the evaluation pole, the weighted
spectral integrand is analytic. -/
theorem analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    (t : ℝ) (z : ℂ) {w : ℂ}
    (hwz : w ≠ z) (hxi : riemannXiSpectral w ≠ 0) :
    AnalyticAt ℂ (suzukiXiWeilSpectralIntegrand t z) w := by
  unfold suzukiXiWeilSpectralIntegrand
  exact (analyticAt_suzukiWeilSpectralTransform_of_ne t z hwz).mul
    (analyticAt_xiSpectralNegativeLogDerivative_of_ne hxi)

/-- The Suzuki-weighted logarithmic derivative differs locally from its
true multiplicity-weighted principal part by a function analytic through the
selected zero. -/
theorem exists_suzukiXiWeilSpectralIntegrand_eq_principalPart_add_analytic
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    (rho : NontrivialZetaZero) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate rho.1) ∧
      suzukiXiWeilSpectralIntegrand t z =ᶠ[
        𝓝[≠] zetaSpectralCoordinate rho.1]
        fun w ↦ suzukiXiWeilSpectralPrincipalPart t z rho w + h w := by
  obtain ⟨k, hkAnalytic, hk⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic rho
  let a : ℂ := zetaSpectralCoordinate rho.1
  let m : ℂ := (analyticZetaZeroMultiplicity rho : ℂ)
  let H : ℂ → ℂ := suzukiWeilSpectralTransform t z
  let h : ℂ → ℂ := fun w ↦
    H w * (Complex.I * k w) +
      (Complex.I * m) * dslope H a w
  have haz : a ≠ z := zetaSpectralCoordinate_ne_of_one_lt_im hz rho
  have hHAnalytic : AnalyticAt ℂ H a := by
    exact analyticAt_suzukiWeilSpectralTransform_of_ne t z haz
  have hHdiff : DifferentiableOn ℂ H ({z}ᶜ : Set ℂ) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    exact (analyticAt_suzukiWeilSpectralTransform_of_ne t z
      (by simpa using hw)).differentiableAt
  have hcompl : ({z}ᶜ : Set ℂ) ∈ 𝓝 a :=
    isOpen_compl_singleton.mem_nhds (by simpa using haz)
  have hSlopeDiff : DifferentiableOn ℂ (dslope H a) ({z}ᶜ : Set ℂ) :=
    (Complex.differentiableOn_dslope hcompl).2 hHdiff
  have hSlopeAnalytic : AnalyticAt ℂ (dslope H a) a := by
    exact (hSlopeDiff.analyticOnNhd isOpen_compl_singleton) a
      (by simpa using haz)
  have hhAnalytic : AnalyticAt ℂ h a := by
    unfold h
    exact (hHAnalytic.mul (analyticAt_const.mul hkAnalytic)).add
      (analyticAt_const.mul hSlopeAnalytic)
  refine ⟨h, hhAnalytic, ?_⟩
  filter_upwards [hk, self_mem_nhdsWithin] with w hlog (hwa : w ≠ a)
  unfold suzukiXiWeilSpectralIntegrand
  rw [xiSpectralNegativeLogDerivative_eq_I_mul_logDeriv, hlog]
  change
    H w * (Complex.I * (m / (w - a) + k w)) =
      suzukiXiWeilSpectralPrincipalPart t z rho w +
        (H w * (Complex.I * k w) +
          (Complex.I * m) * dslope H a w)
  rw [dslope_of_ne H hwa, slope_def_field]
  unfold suzukiXiWeilSpectralPrincipalPart
    suzukiXiWeilSpectralResidue
  change
    H w * (Complex.I * (m / (w - a) + k w)) =
      H a * (Complex.I * m) / (w - a) +
        (H w * (Complex.I * k w) +
          (Complex.I * m) * ((H w - H a) / (w - a)))
  field_simp [sub_ne_zero.mpr hwa]
  ring

/-! ## Removing a finite xi divisor -/

/-- A Suzuki principal part is analytic away from its selected zero. -/
theorem analyticAt_suzukiXiWeilSpectralPrincipalPart_of_ne
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) {w : ℂ}
    (hw : w ≠ zetaSpectralCoordinate rho.1) :
    AnalyticAt ℂ (suzukiXiWeilSpectralPrincipalPart t z rho) w := by
  unfold suzukiXiWeilSpectralPrincipalPart
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hw)

/-- Sum of all Suzuki principal parts in one symmetric genuine-zero
window. -/
def suzukiXiWeilWindowPrincipalSum
    (t : ℝ) (z : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    suzukiXiWeilSpectralPrincipalPart t z rho w

/-- The raw finite-window remainder after subtracting every selected true
principal part from the Suzuki-weighted logarithmic derivative. -/
def suzukiXiWeilWindowRawRemainder
    (t : ℝ) (z : ℂ) (T : ℝ) (w : ℂ) : ℂ :=
  suzukiXiWeilSpectralIntegrand t z w -
    suzukiXiWeilWindowPrincipalSum t z T w

/-- The finite principal sum is analytic away from the selected zero set. -/
theorem analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem
    (t : ℝ) (z : ℂ) (T : ℝ) {w : ℂ}
    (hw : w ∉ spectralXiZeroWindow T) :
    AnalyticAt ℂ (suzukiXiWeilWindowPrincipalSum t z T) w := by
  unfold suzukiXiWeilWindowPrincipalSum
  apply analyticAt_finset_sum_apply
  intro rho hrho
  apply analyticAt_suzukiXiWeilSpectralPrincipalPart_of_ne
  intro heq
  apply hw
  apply Finset.mem_image.mpr
  exact ⟨rho, hrho, heq.symm⟩

/-- Inside the height-one rectangle, the raw remainder is analytic away
from its finite selected divisor. -/
theorem analyticAt_suzukiXiWeilWindowRawRemainder_of_not_mem
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    {w : ℂ} (hwRect : w ∈ spectralContourRectangle T)
    (hw : w ∉ spectralXiZeroWindow T) :
    AnalyticAt ℂ (suzukiXiWeilWindowRawRemainder t z T) w := by
  have hxi : riemannXiSpectral w ≠ 0 := by
    intro hzero
    exact hw ((mem_spectralXiZeroWindow_iff hT w).mpr
      ⟨hzero, hwRect.1⟩)
  have hwz : w ≠ z := by
    intro heq
    have him : |w.im| ≤ 1 := hwRect.2
    rw [heq, abs_le] at him
    linarith
  unfold suzukiXiWeilWindowRawRemainder
  exact (analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    t z hwz hxi).sub
      (analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem
        t z T hw)

/-- At a selected zero, the raw finite-window remainder agrees in a
punctured neighborhood with a function analytic through that zero. -/
theorem exists_suzukiXiWeilWindowRawRemainder_eq_analyticAt
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ}
    (_hT : 0 ≤ T) (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate rho.1) ∧
      suzukiXiWeilWindowRawRemainder t z T =ᶠ[
        𝓝[≠] zetaSpectralCoordinate rho.1] h := by
  obtain ⟨k, hkAnalytic, hk⟩ :=
    exists_suzukiXiWeilSpectralIntegrand_eq_principalPart_add_analytic
      t hz rho
  let W := spectralZetaZeroWindow T
  let h : ℂ → ℂ := fun w ↦
    k w - ∑ sigma ∈ W.erase rho,
      suzukiXiWeilSpectralPrincipalPart t z sigma w
  have hother : AnalyticAt ℂ
      (fun w ↦ ∑ sigma ∈ W.erase rho,
        suzukiXiWeilSpectralPrincipalPart t z sigma w)
      (zetaSpectralCoordinate rho.1) := by
    have hterm (sigma : NontrivialZetaZero)
        (hsigma : sigma ∈ W.erase rho) :
        AnalyticAt ℂ (suzukiXiWeilSpectralPrincipalPart t z sigma)
          (zetaSpectralCoordinate rho.1) := by
      apply analyticAt_suzukiXiWeilSpectralPrincipalPart_of_ne
      intro heq
      have hval : rho.1 = sigma.1 :=
        zetaSpectralCoordinate_injective heq
      have hrs : rho = sigma := Subtype.ext hval
      exact (Finset.mem_erase.mp hsigma).1 hrs.symm
    exact analyticAt_finset_sum_apply (W.erase rho)
      (fun sigma ↦ suzukiXiWeilSpectralPrincipalPart t z sigma) hterm
  have hhAnalytic : AnalyticAt ℂ h
      (zetaSpectralCoordinate rho.1) := by
    unfold h
    exact hkAnalytic.sub hother
  refine ⟨h, hhAnalytic, ?_⟩
  filter_upwards [hk] with w hw
  unfold suzukiXiWeilWindowRawRemainder
    suzukiXiWeilWindowPrincipalSum h
  rw [hw]
  have hsum := W.add_sum_erase
    (fun sigma ↦ suzukiXiWeilSpectralPrincipalPart t z sigma w) hrho
  rw [← hsum]
  ring

/-- The finite Suzuki-weighted xi remainder admits one holomorphic
representative on the complete height-one contour rectangle. -/
theorem exists_suzukiXiWeilWindowRegularization
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ spectralContourRectangle T, AnalyticAt ℂ F w) ∧
      (∀ w ∉ spectralXiZeroWindow T,
        F w = suzukiXiWeilWindowRawRemainder t z T w) := by
  apply exists_analyticAtOn_of_finite_removable
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨rho, hrho, rfl⟩
    constructor
    · exact (mem_spectralZetaZeroWindow hT rho).mp hrho
    · exact (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le.trans
        (by norm_num)
  · intro w hwRect hw
    exact analyticAt_suzukiXiWeilWindowRawRemainder_of_not_mem
      t hz hT hwRect hw
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨rho, hrho, rfl⟩
    exact exists_suzukiXiWeilWindowRawRemainder_eq_analyticAt
      t hz hT rho hrho

/-! ## The exact finite rectangle identity -/

/-- Each selected Suzuki principal part contributes `2πi` times its true
residue to the height-one spectral rectangle. -/
theorem spectralRectangleBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilSpectralPrincipalPart t z rho) =
      (2 * Real.pi : ℝ) * Complex.I *
        suzukiXiWeilSpectralResidue t z rho := by
  let a : ℂ := zetaSpectralCoordinate rho.1
  have hreLe : |a.re| ≤ T :=
    (mem_spectralZetaZeroWindow hT rho).mp hrho
  have hreLt : |a.re| < T :=
    lt_of_le_of_ne hreLe (hboundary rho)
  have hre : -T < a.re ∧ a.re < T := abs_lt.mp hreLt
  have himHalf : |a.im| < (1 / 2 : ℝ) :=
    NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have him : (-1 : ℝ) < a.im ∧ a.im < 1 := by
    rcases abs_lt.mp himHalf with ⟨hlower, hupper⟩
    constructor <;> linarith
  rw [spectralRectangleBoundaryIntegral_eq_rectangularBoundaryIntegral]
  change rectangularBoundaryIntegral (-T) T (-1) 1
      (simplePoleKernel (suzukiXiWeilSpectralResidue t z rho) a) = _
  exact rectangularBoundaryIntegral_simplePoleKernel_of_mem
    (suzukiXiWeilSpectralResidue t z rho) a
      hre.1 hre.2 him.1 him.2

/-- Multiplying a Suzuki residue by `2πi` gives minus `2π` times the
corresponding genuine multiplicity-weighted `P_t` summand. -/
theorem two_pi_I_mul_suzukiXiWeilSpectralResidue
    (t : ℝ) (z : ℂ) (rho : NontrivialZetaZero) :
    (2 * Real.pi : ℝ) * Complex.I *
        suzukiXiWeilSpectralResidue t z rho =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        ((analyticZetaZeroMultiplicity rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1) /
          (z - zetaSpectralCoordinate rho.1)) := by
  unfold suzukiXiWeilSpectralResidue suzukiWeilSpectralTransform
  calc
    (2 * Real.pi : ℝ) * Complex.I *
          (suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1) /
            (z - zetaSpectralCoordinate rho.1) *
              (Complex.I *
                (analyticZetaZeroMultiplicity rho : ℂ))) =
        (((2 * Real.pi : ℝ) : ℂ)) *
          (Complex.I * Complex.I) *
            ((analyticZetaZeroMultiplicity rho : ℂ) *
              suzukiSpectralScrewCoefficient t
                (zetaSpectralCoordinate rho.1) /
              (z - zetaSpectralCoordinate rho.1)) := by ring
    _ = -(((2 * Real.pi : ℝ) : ℂ)) *
        ((analyticZetaZeroMultiplicity rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1) /
          (z - zetaSpectralCoordinate rho.1)) := by
      rw [Complex.I_mul_I]
      ring

/-- A selected Suzuki principal part is interval-integrable on all four
zero-free sides of the spectral rectangle. -/
theorem spectralRectangleBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T)
    (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    spectralRectangleBoundaryIntegrable T
      (suzukiXiWeilSpectralPrincipalPart t z rho) := by
  have hanalytic {w : ℂ} (hw : w ∉ spectralXiZeroWindow T) :
      AnalyticAt ℂ (suzukiXiWeilSpectralPrincipalPart t z rho) w := by
    apply analyticAt_suzukiXiWeilSpectralPrincipalPart_of_ne
    intro heq
    apply hw
    exact Finset.mem_image.mpr ⟨rho, hrho, heq.symm⟩
  unfold spectralRectangleBoundaryIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun x : ℝ ↦ (x : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact hanalytic (lower_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun x : ℝ ↦ (x : ℂ) + Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact hanalytic (upper_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact hanalytic
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralPrincipalPart t z rho)
      (fun y : ℝ ↦ (-T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact hanalytic
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)

/-- The finite Suzuki principal sum integrates to the sum of its exact
`2πi` residues. -/
theorem spectralRectangleBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_residues
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilWindowPrincipalSum t z T) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        (2 * Real.pi : ℝ) * Complex.I *
          suzukiXiWeilSpectralResidue t z rho := by
  unfold suzukiXiWeilWindowPrincipalSum
  rw [spectralRectangleBoundaryIntegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro rho hrho
    exact
      spectralRectangleBoundaryIntegral_suzukiXiWeilSpectralPrincipalPart
        t z hT hboundary rho hrho
  · intro rho hrho
    exact
      spectralRectangleBoundaryIntegrable_suzukiXiWeilSpectralPrincipalPart
        t z hT hboundary rho hrho

/-- The complete finite principal-part contour is exactly minus `2π` times
the genuine finite Suzuki spectral window. -/
theorem spectralRectangleBoundaryIntegral_suzukiXiWeilWindowPrincipalSum
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilWindowPrincipalSum t z T) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiSpectralPWindow t T z := by
  rw [spectralRectangleBoundaryIntegral_suzukiXiWeilWindowPrincipalSum_residues
    t z hT hboundary]
  unfold suzukiXiSpectralPWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact two_pi_I_mul_suzukiXiWeilSpectralResidue t z rho

/-- When the evaluation point lies above the height-one contour, the actual
Suzuki-weighted xi logarithmic derivative is integrable on every zero-free
rectangle boundary. -/
theorem spectralRectangleBoundaryIntegrable_suzukiXiWeilSpectralIntegrand
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegrable T
      (suzukiXiWeilSpectralIntegrand t z) := by
  unfold spectralRectangleBoundaryIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralIntegrand t z)
      (fun x : ℝ ↦ (x : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilSpectralIntegrand t z)
      (fun x : ℝ ↦ (x : ℂ) + Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
    · intro heq
      have him := congrArg Complex.im heq
      simp at him
      linarith
    · apply riemannXiSpectral_ne_zero_of_half_le_abs_im
      norm_num
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ (suzukiXiWeilSpectralIntegrand t z)
        ((T : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        rw [uIcc_of_le (by norm_num)] at hy
        linarith [hy.2]
      · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
        simp [abs_of_nonneg hT]
    have hpath : ContinuousAt
        (fun u : ℝ ↦ (T : ℂ) + (u : ℂ) * Complex.I) y := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦ (T : ℂ) + (u : ℂ) * Complex.I) y :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)
  · apply ContinuousOn.intervalIntegrable
    intro y hy
    apply ContinuousAt.continuousWithinAt
    have hanalytic : AnalyticAt ℂ (suzukiXiWeilSpectralIntegrand t z)
        ((-T : ℂ) + (y : ℂ) * Complex.I) := by
      apply analyticAt_suzukiXiWeilSpectralIntegrand_of_ne
      · intro heq
        have him := congrArg Complex.im heq
        simp at him
        rw [uIcc_of_le (by norm_num)] at hy
        linarith [hy.2]
      · apply riemannXiSpectral_ne_zero_of_abs_re_ne hboundary
        simp [abs_of_nonneg hT]
    have hpath : ContinuousAt
        (fun u : ℝ ↦ (-T : ℂ) + (u : ℂ) * Complex.I) y := by
      fun_prop
    have hcomp : ContinuousAt
        (suzukiXiWeilSpectralIntegrand t z ∘
          fun u : ℝ ↦ (-T : ℂ) + (u : ℂ) * Complex.I) y :=
      ContinuousAt.comp_of_eq hanalytic.continuousAt hpath rfl
    exact hcomp.congr (Eventually.of_forall fun _ ↦ rfl)

/-- The complete finite Suzuki principal sum is interval-integrable on all
four zero-free sides. -/
theorem spectralRectangleBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum
    (t : ℝ) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegrable T
      (suzukiXiWeilWindowPrincipalSum t z T) := by
  unfold spectralRectangleBoundaryIntegrable
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilWindowPrincipalSum t z T)
      (fun x : ℝ ↦ (x : ℂ) - Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem t z T
      (lower_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilWindowPrincipalSum t z T)
      (fun x : ℝ ↦ (x : ℂ) + Complex.I) (by fun_prop) ?_).intervalIntegrable
    intro x
    exact analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem t z T
      (upper_safeLine_not_mem_spectralXiZeroWindow T x)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilWindowPrincipalSum t z T)
      (fun y : ℝ ↦ (T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem t z T
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  · apply (continuous_comp_of_forall_analyticAt
      (suzukiXiWeilWindowPrincipalSum t z T)
      (fun y : ℝ ↦ (-T : ℂ) + (y : ℂ) * Complex.I)
      (by fun_prop) ?_).intervalIntegrable
    intro y
    exact analyticAt_suzukiXiWeilWindowPrincipalSum_of_not_mem t z T
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)

/-- Cauchy's theorem for the holomorphic regularization of the finite Suzuki
remainder. -/
theorem suzukiXiWeilWindowRawRemainder_rectangle_identity
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
      (suzukiXiWeilWindowRawRemainder t z T) = 0 := by
  obtain ⟨F, hFanalytic, hFoff⟩ :=
    exists_suzukiXiWeilWindowRegularization t hz hT
  have hdiff : DifferentiableOn ℂ F
      (Complex.Rectangle ((-T : ℂ) - Complex.I)
        ((T : ℂ) + Complex.I)) := by
    intro w hw
    apply (hFanalytic w ?_).differentiableAt.differentiableWithinAt
    constructor
    · have hre : w.re ∈ uIcc (-T) T := by
        simpa using hw.1
      rw [uIcc_of_le (by linarith)] at hre
      exact (abs_le).2 hre
    · have him : w.im ∈ uIcc (-1) 1 := by
        simpa using hw.2
      rw [uIcc_of_le (by norm_num)] at him
      exact (abs_le).2 him
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F ((-T : ℂ) - Complex.I) ((T : ℂ) + Complex.I) hdiff
  have hrectF : spectralRectangleBoundaryIntegral T F = 0 := by
    simpa [spectralRectangleBoundaryIntegral, sub_eq_add_neg] using hrect
  have hlower (x : ℝ) :
      F ((x : ℂ) - Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) - Complex.I) :=
    hFoff _ (lower_safeLine_not_mem_spectralXiZeroWindow T x)
  have hupper (x : ℝ) :
      F ((x : ℂ) + Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((x : ℂ) + Complex.I) :=
    hFoff _ (upper_safeLine_not_mem_spectralXiZeroWindow T x)
  have hright (y : ℝ) :
      F ((T : ℂ) + (y : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((T : ℂ) + (y : ℂ) * Complex.I) :=
    hFoff _
      (right_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  have hleft (y : ℝ) :
      F ((-T : ℂ) + (y : ℂ) * Complex.I) =
        suzukiXiWeilWindowRawRemainder t z T
          ((-T : ℂ) + (y : ℂ) * Complex.I) :=
    hFoff _
      (left_vertical_not_mem_spectralXiZeroWindow hT hboundary y)
  unfold spectralRectangleBoundaryIntegral at hrectF ⊢
  simp_rw [hlower, hupper, hright, hleft] at hrectF
  exact hrectF

/-- On every zero-free finite rectangle, the actual Suzuki-weighted xi
logarithmic derivative has the same boundary integral as the complete sum of
its genuine principal parts. -/
theorem suzukiXiWeilSpectralIntegrand_rectangle_eq_windowPrincipalSum
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilSpectralIntegrand t z) =
      spectralRectangleBoundaryIntegral T
        (suzukiXiWeilWindowPrincipalSum t z T) := by
  have hraw := suzukiXiWeilWindowRawRemainder_rectangle_identity
    t hz hT hboundary
  have hintegrand :=
    spectralRectangleBoundaryIntegrable_suzukiXiWeilSpectralIntegrand
      t hz hT hboundary
  have hprincipal :=
    spectralRectangleBoundaryIntegrable_suzukiXiWeilWindowPrincipalSum
      t z hT hboundary
  have hsub := spectralRectangleBoundaryIntegral_sub T
    hintegrand hprincipal
  change spectralRectangleBoundaryIntegral T
      (fun w ↦ suzukiXiWeilSpectralIntegrand t z w -
        suzukiXiWeilWindowPrincipalSum t z T w) = 0 at hraw
  rw [hsub] at hraw
  exact sub_eq_zero.mp hraw

/-- Exact finite Suzuki--xi divisor formula.  The contour integral of the
actual transformed logarithmic derivative is minus `2π` times precisely the
enclosed genuine spectral `P_t` window, with analytic multiplicities. -/
theorem suzukiXiWeilSpectralIntegrand_rectangle_eq_spectralPWindow
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilSpectralIntegrand t z) =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiSpectralPWindow t T z := by
  rw [suzukiXiWeilSpectralIntegrand_rectangle_eq_windowPrincipalSum
      t hz hT hboundary,
    spectralRectangleBoundaryIntegral_suzukiXiWeilWindowPrincipalSum
      t z hT hboundary]

/-! ## Passing from finite rectangles to the complete spectral sum -/

/-- The difference of the lower and upper horizontal sides of the Suzuki--xi
rectangle.  Keeping this separate from the vertical contribution isolates the
safe-line evaluation needed in the infinite-contour argument. -/
def suzukiXiWeilHorizontalBoundaryIntegral
    (t : ℝ) (z : ℂ) (T : ℝ) : ℂ :=
  (∫ x : ℝ in -T..T,
      suzukiXiWeilSpectralIntegrand t z ((x : ℂ) - Complex.I)) -
    (∫ x : ℝ in -T..T,
      suzukiXiWeilSpectralIntegrand t z ((x : ℂ) + Complex.I))

/-- The two oriented vertical sides of the Suzuki--xi rectangle. -/
def suzukiXiWeilVerticalBoundaryIntegral
    (t : ℝ) (z : ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ y : ℝ in (-1 : ℝ)..1,
      suzukiXiWeilSpectralIntegrand t z
        ((T : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in (-1 : ℝ)..1,
      suzukiXiWeilSpectralIntegrand t z
        ((-T : ℂ) + (y : ℂ) * Complex.I))

/-- The full rectangle boundary is exactly its horizontal part plus its
vertical part. -/
theorem spectralRectangleBoundaryIntegral_suzukiXiWeilSpectralIntegrand_eq_parts
    (t : ℝ) (z : ℂ) (T : ℝ) :
    spectralRectangleBoundaryIntegral T
        (suzukiXiWeilSpectralIntegrand t z) =
      suzukiXiWeilHorizontalBoundaryIntegral t z T +
        suzukiXiWeilVerticalBoundaryIntegral t z T := by
  unfold spectralRectangleBoundaryIntegral
    suzukiXiWeilHorizontalBoundaryIntegral
    suzukiXiWeilVerticalBoundaryIntegral
  ring

/-- Finite zero-free rectangles already give the exact decomposed identity
whose limit will be taken below. -/
theorem suzukiXiWeilHorizontal_add_vertical_eq_spectralPWindow
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {T : ℝ} (hT : 0 ≤ T)
    (hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T) :
    suzukiXiWeilHorizontalBoundaryIntegral t z T +
        suzukiXiWeilVerticalBoundaryIntegral t z T =
      -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiSpectralPWindow t T z := by
  rw [←
    spectralRectangleBoundaryIntegral_suzukiXiWeilSpectralIntegrand_eq_parts]
  exact suzukiXiWeilSpectralIntegrand_rectangle_eq_spectralPWindow
    t hz hT hboundary

/-- Along any nonnegative zero-free truncation sequence tending to infinity,
convergence of the horizontal contribution to `H` and vanishing of the
vertical contribution force `H` to be exactly minus `2π` times the complete
Suzuki spectral function.  Thus no infinite residue theorem is assumed: this
is a direct limit of the finite identity above. -/
theorem suzukiXiWeilHorizontalLimit_eq_spectralP_of_admissible_limits
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) (T : ℕ → ℝ)
    (hTnonneg : ∀ n, 0 ≤ T n)
    (hTtop : Tendsto T atTop atTop)
    (hTboundary : ∀ (n : ℕ) (rho : NontrivialZetaZero),
      |(zetaSpectralCoordinate rho.1).re| ≠ T n)
    {H : ℂ}
    (hhorizontal : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilHorizontalBoundaryIntegral t z (T n))
      atTop (𝓝 H))
    (hvertical : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilVerticalBoundaryIntegral t z (T n))
      atTop (𝓝 0)) :
    H = -(((2 * Real.pi : ℝ) : ℂ)) *
      riemannXiSuzukiSpectralP t z := by
  have hleft : Tendsto
      (fun n : ℕ ↦
        suzukiXiWeilHorizontalBoundaryIntegral t z (T n) +
          suzukiXiWeilVerticalBoundaryIntegral t z (T n))
      atTop (𝓝 H) := by
    simpa using hhorizontal.add hvertical
  have hzHalf : (1 / 2 : ℝ) < z.im := by linarith
  have hwindow :=
    (tendsto_suzukiXiSpectralPWindow t hzHalf).comp hTtop
  have hright : Tendsto
      (fun n : ℕ ↦ -(((2 * Real.pi : ℝ) : ℂ)) *
        suzukiXiSpectralPWindow t (T n) z)
      atTop
      (𝓝 (-(((2 * Real.pi : ℝ) : ℂ)) *
        riemannXiSuzukiSpectralP t z)) :=
    tendsto_const_nhds.mul hwindow
  have hrightAsLeft := hright.congr'
    (Filter.Eventually.of_forall fun n ↦ by
      symm
      exact suzukiXiWeilHorizontal_add_vertical_eq_spectralPWindow
        t hz (hTnonneg n) (hTboundary n))
  exact tendsto_nhds_unique hleft hrightAsLeft

/-- The generic limit theorem specialized to the quantitatively separated
zero-free contour chosen in every unit interval. -/
theorem suzukiXiWeilHorizontalLimit_eq_spectralP_of_quantitative_limits
    (t : ℝ) {z : ℂ} (hz : 1 < z.im) {H : ℂ}
    (hhorizontal : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilHorizontalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop (𝓝 H))
    (hvertical : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop (𝓝 0)) :
    H = -(((2 * Real.pi : ℝ) : ℂ)) *
      riemannXiSuzukiSpectralP t z := by
  apply suzukiXiWeilHorizontalLimit_eq_spectralP_of_admissible_limits
    t hz quantitativeSpectralBoundaryTruncation
  · intro n
    exact (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  · exact tendsto_quantitativeSpectralBoundaryTruncation_atTop
  · exact quantitativeSpectralBoundaryTruncation_zeroFree
  · exact hhorizontal
  · exact hvertical

/-- Once the safe-line calculation identifies the horizontal limit with the
already evaluated arithmetic expression and the selected vertical sides
vanish, the arithmetic and spectral Suzuki functions are equal at the given
height-above-one point. -/
theorem riemannXiSuzukiArithmeticPPositive_eq_spectral_of_quantitative_limits
    (t : ℝ) {z : ℂ} (hz : 1 < z.im)
    (hhorizontal : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilHorizontalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop
      (𝓝 (-(((2 * Real.pi : ℝ) : ℂ)) *
        riemannXiSuzukiArithmeticPPositive t z)))
    (hvertical : Tendsto
      (fun n : ℕ ↦ suzukiXiWeilVerticalBoundaryIntegral t z
        (quantitativeSpectralBoundaryTruncation n))
      atTop (𝓝 0)) :
    riemannXiSuzukiArithmeticPPositive t z =
      riemannXiSuzukiSpectralP t z := by
  have hscaled :=
    suzukiXiWeilHorizontalLimit_eq_spectralP_of_quantitative_limits
      t hz hhorizontal hvertical
  have hscale : -(((2 * Real.pi : ℝ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  exact mul_left_cancel₀ hscale hscaled

end

end RiemannGaussian
