import RiemannGaussian.RiemannXiSuzukiRealAxisSignalL2
import Mathlib.MeasureTheory.Group.Integral

/-!
# Suzuki's normalized xi-zero functions on the real axis

This file constructs the local removable model needed to put every normalized
zero function in Suzuki's expansion into `L²(ℝ)`, without assuming RH or
simplicity of the xi zeros.

At a spectral xi zero `alpha` of analytic multiplicity `m`, write

`xi'/xi = m / (z - alpha) + h(z)`.

Away from the divisor, Suzuki's carrier is `i xi / (xi + i xi')`.  Dividing
once more by `z - alpha` therefore cancels to the analytic local model

`i / (i m + (z - alpha) (1 + i h(z)))`.

The denominator is nonzero at the center because `m > 0`.  This handles real
multiple zeros just as well as simple zeros.  Off the center, the already
proved unit bound for the carrier gives the global Cauchy tail.  These two
facts are combined below into a square-integrable real-axis representative.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The analytic local model for Suzuki's normalized zero function at one
spectral xi divisor point. -/
def suzukiXiZeroFunctionRegularization
    (rho : NontrivialZetaZero) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (suzukiXiZeroNormalization rho : ℂ) * Complex.I /
    ((analyticZetaZeroMultiplicity rho : ℂ) * Complex.I +
      (z - zetaSpectralCoordinate rho.1) * (1 + Complex.I * h z))

/-- The local zero-function model is analytic at its divisor point. -/
theorem analyticAt_suzukiXiZeroFunctionRegularization
    (rho : NontrivialZetaZero) {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h (zetaSpectralCoordinate rho.1)) :
    AnalyticAt ℂ (suzukiXiZeroFunctionRegularization rho h)
      (zetaSpectralCoordinate rho.1) := by
  let alpha := zetaSpectralCoordinate rho.1
  have hlinear : AnalyticAt ℂ (fun z : ℂ ↦ z - alpha) alpha := by
    fun_prop
  have hden : AnalyticAt ℂ (fun z : ℂ ↦
      (analyticZetaZeroMultiplicity rho : ℂ) * Complex.I +
        (z - alpha) * (1 + Complex.I * h z)) alpha := by
    exact analyticAt_const.add
      (hlinear.mul (analyticAt_const.add (analyticAt_const.mul hh)))
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by
      exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne')
      Complex.I_ne_zero
  unfold suzukiXiZeroFunctionRegularization
  apply analyticAt_const.div hden
  simpa [alpha] using hm

/-- The totalized quotient formula agrees punctured-locally with its analytic
regularization at every genuine xi divisor point. -/
theorem eventuallyEq_suzukiXiZeroFunctionFormula_regularization
    (rho : NontrivialZetaZero) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (zetaSpectralCoordinate rho.1) ∧
      suzukiXiZeroFunctionFormula rho =ᶠ[
        𝓝[≠] zetaSpectralCoordinate rho.1]
        suzukiXiZeroFunctionRegularization rho h := by
  let alpha := zetaSpectralCoordinate rho.1
  obtain ⟨h, hh, hlog⟩ :=
    exists_logDeriv_riemannXiSpectral_eq_zetaPrincipalPart_add_analytic rho
  have hfinite : analyticOrderAt riemannXiSpectral alpha ≠ ⊤ := by
    dsimp [alpha]
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hxiNe : ∀ᶠ z in 𝓝[≠] alpha, riemannXiSpectral z ≠ 0 :=
    (analyticAt_riemannXiSpectral alpha).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun hzero ↦ hfinite (analyticOrderAt_eq_top.mpr hzero)
  let D : ℂ → ℂ := fun z ↦
    (analyticZetaZeroMultiplicity rho : ℂ) * Complex.I +
      (z - alpha) * (1 + Complex.I * h z)
  have hDanalytic : AnalyticAt ℂ D alpha := by
    dsimp [D]
    exact analyticAt_const.add
      ((by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z - alpha) alpha).mul
        (analyticAt_const.add (analyticAt_const.mul hh)))
  have hDcenter : D alpha ≠ 0 := by
    dsimp [D]
    simp only [sub_self, zero_mul, add_zero]
    exact mul_ne_zero (by
      exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne')
      Complex.I_ne_zero
  have hDNe : ∀ᶠ z in 𝓝[≠] alpha, D z ≠ 0 :=
    (hDanalytic.continuousAt.eventually_ne hDcenter).filter_mono
      nhdsWithin_le_nhds
  refine ⟨h, hh, ?_⟩
  filter_upwards [hlog, hxiNe, hDNe, self_mem_nhdsWithin]
      with z hzlog hxi hDz hza
  have hsub : z - alpha ≠ 0 := sub_ne_zero.mpr hza
  have hDidentity :
      D z = (z - alpha) *
        (1 + Complex.I * logDeriv riemannXiSpectral z) := by
    dsimp [D, alpha]
    rw [hzlog]
    field_simp [show z - zetaSpectralCoordinate rho.1 ≠ 0 by
      simpa [alpha] using hsub]
    ring
  have hlogFactor :
      1 + Complex.I * logDeriv riemannXiSpectral z ≠ 0 := by
    intro hzero
    apply hDz
    rw [hDidentity, hzero, mul_zero]
  have hEfactor :
      suzukiXiEValue z = riemannXiSpectral z *
        (1 + Complex.I * logDeriv riemannXiSpectral z) := by
    rw [suzukiXiEValue_eq, logDeriv_apply]
    field_simp [hxi]
  have hE : suzukiXiEValue z ≠ 0 := by
    rw [hEfactor]
    exact mul_ne_zero hxi hlogFactor
  rw [suzukiXiZeroFunctionFormula,
    suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE,
    suzukiXiZeroFunctionRegularization, hEfactor]
  change
    (suzukiXiZeroNormalization rho : ℂ) *
          (Complex.I * riemannXiSpectral z /
            (riemannXiSpectral z *
              (1 + Complex.I * logDeriv riemannXiSpectral z))) /
        (z - alpha) =
      (suzukiXiZeroNormalization rho : ℂ) * Complex.I / D z
  rw [hDidentity]
  field_simp [hxi, hsub, hDz, hlogFactor]

/-- One normalized Suzuki zero function restricted to the real spectral
axis. -/
def suzukiRealAxisZeroFunction
    (rho : NontrivialZetaZero) (x : ℝ) : ℂ :=
  suzukiXiZeroFunctionFormula rho (x : ℂ)

/-- Every real-axis zero-function formula is Borel measurable. -/
theorem measurable_suzukiRealAxisZeroFunction
    (rho : NontrivialZetaZero) :
    Measurable (suzukiRealAxisZeroFunction rho) := by
  change Measurable (fun x : ℝ ↦
    (suzukiXiZeroNormalization rho : ℂ) *
      suzukiRealAxisXiZeroCarrier x /
        ((x : ℂ) - zetaSpectralCoordinate rho.1))
  exact (measurable_const.mul measurable_suzukiRealAxisXiZeroCarrier).div
    (Complex.continuous_ofReal.sub continuous_const).measurable

/-- The square-root normalization of a zero function is nonnegative. -/
theorem suzukiXiZeroNormalization_nonneg
    (rho : NontrivialZetaZero) :
    0 ≤ suzukiXiZeroNormalization rho := by
  unfold suzukiXiZeroNormalization
  positivity

/-- A nonreal spectral node gives an ordinary square-integrable Cauchy
kernel on the real boundary. -/
theorem memLp_two_suzukiRealAxisCauchyKernel_of_im_ne_zero
    {alpha : ℂ} (halpha : alpha.im ≠ 0) :
    MemLp (fun x : ℝ ↦ (1 : ℂ) / ((x : ℂ) - alpha)) 2 := by
  have h := polynomialBoundaryQuotient_memLp_two
      (q := (1 : ℂ[X])) (P := X - C alpha)
      (by simp)
      (by
        intro x hzero
        have him := congrArg Complex.im hzero
        simp only [eval_sub, eval_X, eval_C, Complex.sub_im,
          Complex.ofReal_im, zero_sub] at him
        exact halpha (neg_eq_zero.mp him))
  convert h using 1
  funext x
  simp

/-- Every off-axis normalized xi-zero function belongs to boundary `L²`.
This uses only the carrier's proved `L∞` bound and the nonreal Cauchy
denominator. -/
theorem memLp_two_suzukiRealAxisZeroFunction_of_im_ne_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    MemLp (suzukiRealAxisZeroFunction rho) 2 := by
  have hcauchy :=
    memLp_two_suzukiRealAxisCauchyKernel_of_im_ne_zero hrho
  have hproduct : MemLp (fun x : ℝ ↦
      suzukiRealAxisXiZeroCarrier x *
        ((1 : ℂ) / ((x : ℂ) - zetaSpectralCoordinate rho.1))) 2 :=
    hcauchy.mul' memLp_top_suzukiRealAxisXiZeroCarrier
  have hscaled := hproduct.const_mul
    (suzukiXiZeroNormalization rho : ℂ)
  convert hscaled using 1
  funext x
  unfold suzukiRealAxisZeroFunction suzukiXiZeroFunctionFormula
    suzukiRealAxisXiZeroCarrier
  ring

/-- At a real spectral zero, analytic multiplicity supplies a genuine local
bound for the totalized zero-function formula.  No simplicity assumption is
used. -/
theorem exists_local_bound_suzukiRealAxisZeroFunction_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ,
        |x - (zetaSpectralCoordinate rho.1).re| < r →
          ‖suzukiRealAxisZeroFunction rho x‖ ≤ C := by
  let alpha := zetaSpectralCoordinate rho.1
  have halpha : ((alpha.re : ℝ) : ℂ) = alpha := by
    apply Complex.ext
    · simp
    · simpa [alpha] using hrho.symm
  obtain ⟨h, hh, heq⟩ :=
    eventuallyEq_suzukiXiZeroFunctionFormula_regularization rho
  let F : ℂ → ℂ := suzukiXiZeroFunctionRegularization rho h
  have hFcontinuous : ContinuousAt F alpha := by
    exact (analyticAt_suzukiXiZeroFunctionRegularization rho hh).continuousAt
  have hnear : ∀ᶠ z in 𝓝 alpha, ‖F z - F alpha‖ < 1 :=
    hFcontinuous.tendsto.eventually
      (eventually_norm_sub_lt (F alpha) (by norm_num))
  have hboundF : ∀ᶠ z in 𝓝 alpha, ‖F z‖ ≤ ‖F alpha‖ + 1 := by
    filter_upwards [hnear] with z hz
    calc
      ‖F z‖ ≤ ‖F z - F alpha‖ + ‖F alpha‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F z - F alpha) (F alpha)
      _ ≤ ‖F alpha‖ + 1 := by linarith
  have heq' : ∀ᶠ z in 𝓝 alpha, z ≠ alpha →
      suzukiXiZeroFunctionFormula rho z = F z := by
    change ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
      suzukiXiZeroFunctionFormula rho z =
        suzukiXiZeroFunctionRegularization rho h z at heq
    have heqWithin : ∀ᶠ z in 𝓝[≠] alpha,
        suzukiXiZeroFunctionFormula rho z = F z := by
      simpa [alpha, F] using heq
    rw [eventually_nhdsWithin_iff] at heqWithin
    exact heqWithin
  have hlocal : ∀ᶠ z in 𝓝 alpha, z ≠ alpha →
      ‖suzukiXiZeroFunctionFormula rho z‖ ≤ ‖F alpha‖ + 1 := by
    filter_upwards [heq', hboundF] with z hzEq hzBound hza
    rw [hzEq hza]
    exact hzBound
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  refine ⟨r, hr, ‖F alpha‖ + 1, by positivity, ?_⟩
  intro x hx
  by_cases hxa : x = alpha.re
  · subst x
    have hden : ((alpha.re : ℝ) : ℂ) -
        zetaSpectralCoordinate rho.1 = 0 := by
      rw [halpha]
      simp [alpha]
    simp [suzukiRealAxisZeroFunction, suzukiXiZeroFunctionFormula, hden]
    positivity
  · apply hball
    · have hdist : dist ((x : ℝ) : ℂ) alpha = |x - alpha.re| := by
        calc
          dist ((x : ℝ) : ℂ) alpha =
              dist ((x : ℝ) : ℂ) ((alpha.re : ℝ) : ℂ) :=
            congrArg (fun w : ℂ ↦ dist ((x : ℝ) : ℂ) w) halpha.symm
          _ = |x - alpha.re| := by
            rw [dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
              Real.norm_eq_abs]
      rw [hdist]
      simpa [alpha] using hx
    · intro hcomplex
      apply hxa
      have hre := congrArg Complex.re hcomplex
      simpa using hre

/-- At a real divisor, the unit carrier bound gives the exact totalized
Cauchy estimate needed away from the locally cancelled center. -/
theorem norm_suzukiRealAxisZeroFunction_le_div_abs_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0)
    (x : ℝ) :
    ‖suzukiRealAxisZeroFunction rho x‖ ≤
      suzukiXiZeroNormalization rho /
        |x - (zetaSpectralCoordinate rho.1).re| := by
  let alpha := zetaSpectralCoordinate rho.1
  have halpha : ((alpha.re : ℝ) : ℂ) = alpha := by
    apply Complex.ext
    · simp
    · simpa [alpha] using hrho.symm
  have hden : ‖(x : ℂ) - alpha‖ = |x - alpha.re| := by
    calc
      ‖(x : ℂ) - alpha‖ =
          ‖(x : ℂ) - ((alpha.re : ℝ) : ℂ)‖ := by rw [halpha]
      _ = |x - alpha.re| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hnormalization := suzukiXiZeroNormalization_nonneg rho
  change ‖(suzukiXiZeroNormalization rho : ℂ) *
      suzukiXiZeroCarrier (x : ℂ) /
        ((x : ℂ) - alpha)‖ ≤
    suzukiXiZeroNormalization rho / |x - alpha.re|
  rw [norm_div, norm_mul, hden, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnormalization]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact mul_le_of_le_one_right hnormalization
    (norm_suzukiXiZeroCarrier_ofReal_le_one x)

/-- Translation preserves integrability of the standard Cauchy density. -/
theorem integrable_suzukiShiftedCauchyDensity (a : ℝ) :
    Integrable (fun x : ℝ ↦ (1 + (x - a) ^ 2)⁻¹) := by
  have h := integrable_inv_one_add_sq.comp_add_right (-a)
  convert h using 1
  funext x
  congr 2

/-- A compact bound plus a shifted Cauchy tail for the squared norm of one
real-axis zero function. -/
def suzukiRealAxisZeroFunctionNormSqMajorant
    (rho : NontrivialZetaZero) (delta C x : ℝ) : ℝ :=
  (Icc ((zetaSpectralCoordinate rho.1).re - delta)
      ((zetaSpectralCoordinate rho.1).re + delta)).indicator
        (fun _ ↦ C ^ 2) x +
    (suzukiXiZeroNormalization rho ^ 2 *
      (1 + (delta ^ 2)⁻¹)) *
        (1 + (x - (zetaSpectralCoordinate rho.1).re) ^ 2)⁻¹

/-- The compact-plus-Cauchy zero-function majorant is integrable. -/
theorem integrable_suzukiRealAxisZeroFunctionNormSqMajorant
    (rho : NontrivialZetaZero) (delta C : ℝ) :
    Integrable (suzukiRealAxisZeroFunctionNormSqMajorant rho delta C) := by
  have hcompact : Integrable
      ((Icc ((zetaSpectralCoordinate rho.1).re - delta)
          ((zetaSpectralCoordinate rho.1).re + delta)).indicator
            (fun _ : ℝ ↦ C ^ 2)) :=
    (integrableOn_const (s :=
      Icc ((zetaSpectralCoordinate rho.1).re - delta)
        ((zetaSpectralCoordinate rho.1).re + delta))
      (by simp)).integrable_indicator measurableSet_Icc
  have htail : Integrable (fun x : ℝ ↦
      (suzukiXiZeroNormalization rho ^ 2 *
        (1 + (delta ^ 2)⁻¹)) *
          (1 + (x - (zetaSpectralCoordinate rho.1).re) ^ 2)⁻¹) :=
    (integrable_suzukiShiftedCauchyDensity
      (zetaSpectralCoordinate rho.1).re).const_mul
        (suzukiXiZeroNormalization rho ^ 2 *
          (1 + (delta ^ 2)⁻¹))
  exact hcompact.add htail

/-- The local analytic cancellation and the global carrier estimate together
dominate the squared norm of a real-node zero function by an integrable
majorant. -/
theorem normSq_suzukiRealAxisZeroFunction_le_majorant_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0)
    {r C delta : ℝ} (hdelta : 0 < delta) (hdeltaR : delta < r)
    (hlocal : ∀ x : ℝ,
      |x - (zetaSpectralCoordinate rho.1).re| < r →
        ‖suzukiRealAxisZeroFunction rho x‖ ≤ C)
    (x : ℝ) :
    ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
      suzukiRealAxisZeroFunctionNormSqMajorant rho delta C x := by
  let a := (zetaSpectralCoordinate rho.1).re
  let N := suzukiXiZeroNormalization rho
  by_cases hx : |x - a| ≤ delta
  · have hxmem : x ∈ Icc (a - delta) (a + delta) := by
      rcases abs_le.mp hx with ⟨hlower, hupper⟩
      constructor <;> linarith
    have hnorm : ‖suzukiRealAxisZeroFunction rho x‖ ≤ C := by
      apply hlocal
      exact hx.trans_lt hdeltaR
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    unfold suzukiRealAxisZeroFunctionNormSqMajorant
    rw [Set.indicator_of_mem (by simpa [a] using hxmem)]
    exact hsquare.trans (le_add_of_nonneg_right (by positivity))
  · have hxgt : delta < |x - a| := lt_of_not_ge hx
    have hxnotmem : x ∉ Icc (a - delta) (a + delta) := by
      intro hxmem
      apply hx
      apply abs_le.mpr
      constructor <;> linarith [hxmem.1, hxmem.2]
    have hnorm : ‖suzukiRealAxisZeroFunction rho x‖ ≤
        N / |x - a| := by
      simpa [a, N] using
        norm_suzukiRealAxisZeroFunction_le_div_abs_of_im_eq_zero
          rho hrho x
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    let u : ℝ := (x - a) ^ 2
    let d : ℝ := delta ^ 2
    have hd : 0 < d := sq_pos_of_pos hdelta
    have habs : 0 < |x - a| := hdelta.trans hxgt
    have hu : 0 < u := by
      dsimp [u]
      exact sq_pos_of_ne_zero (abs_pos.mp habs)
    have hdu : d ≤ u := by
      dsimp [d, u]
      rw [← sq_abs (x - a)]
      exact (sq_le_sq₀ hdelta.le (abs_nonneg _)).2 hxgt.le
    have hrecip : u⁻¹ ≤ (1 + d⁻¹) * (1 + u)⁻¹ := by
      calc
        u⁻¹ = 1 / u := by simp [one_div]
        _ ≤ (1 + 1 / d) / (1 + u) := by
          rw [div_le_div_iff₀ hu (by positivity : 0 < 1 + u)]
          field_simp [hd.ne']
          nlinarith
        _ = (1 + d⁻¹) * (1 + u)⁻¹ := by ring
    have hnormalizationSq : 0 ≤ N ^ 2 := sq_nonneg N
    unfold suzukiRealAxisZeroFunctionNormSqMajorant
    rw [Set.indicator_of_notMem (by simpa [a] using hxnotmem), zero_add]
    change ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
      (N ^ 2 * (1 + d⁻¹)) * (1 + u)⁻¹
    calc
      ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
          (N / |x - a|) ^ 2 := hsquare
      _ = N ^ 2 * u⁻¹ := by
        dsimp [u]
        rw [div_pow, sq_abs]
        ring
      _ ≤ N ^ 2 * ((1 + d⁻¹) * (1 + u)⁻¹) :=
        mul_le_mul_of_nonneg_left hrecip hnormalizationSq
      _ = (N ^ 2 * (1 + d⁻¹)) * (1 + u)⁻¹ := by ring

/-- Every normalized Suzuki zero function attached to a real spectral node
has square-integrable boundary values, with arbitrary analytic
multiplicity. -/
theorem integrable_normSq_suzukiRealAxisZeroFunction_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Integrable (fun x : ℝ ↦ ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) := by
  obtain ⟨r, hr, C, _hC, hlocal⟩ :=
    exists_local_bound_suzukiRealAxisZeroFunction_of_im_eq_zero rho hrho
  let delta : ℝ := min (r / 2) 1
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (half_pos hr) zero_lt_one
  have hdeltaR : delta < r := by
    exact (min_le_left (r / 2) 1).trans_lt (half_lt_self hr)
  exact
    (integrable_suzukiRealAxisZeroFunctionNormSqMajorant rho delta C).mono'
      ((measurable_suzukiRealAxisZeroFunction rho).aestronglyMeasurable.norm.pow 2)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact
          normSq_suzukiRealAxisZeroFunction_le_majorant_of_im_eq_zero
            rho hrho hdelta hdeltaR hlocal x)

/-- Every real-node normalized Suzuki zero function belongs to boundary
`L²`, including every possible multiple critical-line zero. -/
theorem memLp_two_suzukiRealAxisZeroFunction_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    MemLp (suzukiRealAxisZeroFunction rho) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_suzukiRealAxisZeroFunction rho).aestronglyMeasurable).2
  exact integrable_normSq_suzukiRealAxisZeroFunction_of_im_eq_zero rho hrho

/-- Unconditionally, every normalized zero function in Suzuki's genuine xi
divisor expansion is an element of `L²(ℝ)`. -/
theorem memLp_two_suzukiRealAxisZeroFunction
    (rho : NontrivialZetaZero) :
    MemLp (suzukiRealAxisZeroFunction rho) 2 := by
  by_cases hrho : (zetaSpectralCoordinate rho.1).im = 0
  · exact memLp_two_suzukiRealAxisZeroFunction_of_im_eq_zero rho hrho
  · exact memLp_two_suzukiRealAxisZeroFunction_of_im_ne_zero rho hrho

/-- One genuine normalized Suzuki zero function as an actual vector in
`L²(ℝ, ℂ)`. -/
def suzukiRealAxisZeroFunctionLp
    (rho : NontrivialZetaZero) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_suzukiRealAxisZeroFunction rho).toLp
    (suzukiRealAxisZeroFunction rho)

/-- The packaged zero function has the literal quotient formula as an
almost-everywhere representative. -/
theorem suzukiRealAxisZeroFunctionLp_ae
    (rho : NontrivialZetaZero) :
    suzukiRealAxisZeroFunctionLp rho =ᵐ[volume]
      suzukiRealAxisZeroFunction rho :=
  MemLp.coeFn_toLp (memLp_two_suzukiRealAxisZeroFunction rho)

/-- A finite genuine-zero Suzuki signal restricted to the real axis. -/
def suzukiRealAxisSignalWindow (t T x : ℝ) : ℂ :=
  suzukiXiSignalWindow t T (x : ℂ)

/-- The real-axis finite signal is exactly the finite synthesis of its
normalized zero functions. -/
theorem suzukiRealAxisSignalWindow_eq_sum_zeroFunctions
    (t T x : ℝ) :
    suzukiRealAxisSignalWindow t T x =
      ∑ rho ∈ spectralZetaZeroWindow T,
        ((suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1)) *
              suzukiRealAxisZeroFunction rho x := by
  rw [suzukiRealAxisSignalWindow,
    suzukiXiSignalWindow_eq_sum_zeroFunctionFormulas]
  apply Finset.sum_congr rfl
  intro rho _hrho
  unfold suzukiRealAxisZeroFunction
  ring

/-- Every finite genuine-zero Suzuki signal belongs unconditionally to
boundary `L²`. -/
theorem memLp_two_suzukiRealAxisSignalWindow (t T : ℝ) :
    MemLp (suzukiRealAxisSignalWindow t T) 2 := by
  have hsum : MemLp (fun x : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        ((suzukiXiZeroCoefficientAmplitude rho : ℂ) *
          suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1)) *
              suzukiRealAxisZeroFunction rho x) 2 := by
    apply memLp_finsetSum
    intro rho _hrho
    exact (memLp_two_suzukiRealAxisZeroFunction rho).const_mul
      ((suzukiXiZeroCoefficientAmplitude rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1))
  exact (memLp_congr_ae (Filter.Eventually.of_forall fun x ↦
    suzukiRealAxisSignalWindow_eq_sum_zeroFunctions t T x)).2 hsum

/-- A finite genuine-zero Suzuki signal as an actual boundary Hilbert-space
vector. -/
def suzukiRealAxisSignalWindowLp
    (t T : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_two_suzukiRealAxisSignalWindow t T).toLp
    (suzukiRealAxisSignalWindow t T)

/-- The packaged finite-window vector has the literal finite spectral signal
as an almost-everywhere representative. -/
theorem suzukiRealAxisSignalWindowLp_ae
    (t T : ℝ) :
    suzukiRealAxisSignalWindowLp t T =ᵐ[volume]
      suzukiRealAxisSignalWindow t T :=
  MemLp.coeFn_toLp (memLp_two_suzukiRealAxisSignalWindow t T)

end

end RiemannGaussian
