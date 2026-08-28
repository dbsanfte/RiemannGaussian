import RiemannGaussian.RiemannXiSuzukiZeroFunctionNormBound

/-!
# Quantitative norms of real-node Suzuki zero functions

At a critical-line spectral zero, the apparent Cauchy pole is locally
cancelled by analytic multiplicity.  The qualitative `L²` proof already
constructed a compact-plus-Cauchy majorant from any local bound.  This file
computes that majorant's integral exactly and turns the local cancellation
data into the explicit global estimate

`‖f_rho‖₂² <= 2*delta*C² + m_rho*(1 + delta⁻²)`.

The estimate is unconditional once its local bound is supplied, and the
existing analytic regularization supplies such data for every real spectral
zero.  Uniform control of those data across the divisor is not asserted.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Exact integral of the shifted normalized Cauchy density. -/
theorem integral_suzukiShiftedCauchyDensity (a : ℝ) :
    ∫ x : ℝ, (1 + (x - a) ^ 2)⁻¹ = Real.pi := by
  simpa [suzukiShiftedScaledCauchyDensity, add_comm] using
    (integral_suzukiShiftedScaledCauchyDensity a
      (b := (1 : ℝ)) one_ne_zero)

/-- Exact integral of a constant on a centered compact interval. -/
theorem integral_centeredIcc_indicator_const
    (a delta C : ℝ) (hdelta : 0 ≤ delta) :
    ∫ x : ℝ, (Icc (a - delta) (a + delta)).indicator
      (fun _ ↦ C ^ 2) x = 2 * delta * C ^ 2 := by
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal]
  · ring
  · linarith

/-- Exact integral of the compact-plus-Cauchy majorant used for a real-node
zero function. -/
theorem integral_suzukiRealAxisZeroFunctionNormSqMajorant
    (rho : NontrivialZetaZero) (delta C : ℝ)
    (hdelta : 0 ≤ delta) :
    ∫ x : ℝ,
        suzukiRealAxisZeroFunctionNormSqMajorant rho delta C x =
      2 * delta * C ^ 2 +
        (suzukiXiZeroNormalization rho ^ 2 *
          (1 + (delta ^ 2)⁻¹)) * Real.pi := by
  let a := (zetaSpectralCoordinate rho.1).re
  let N := suzukiXiZeroNormalization rho
  have hcompact : Integrable
      ((Icc (a - delta) (a + delta)).indicator
        (fun _ : ℝ ↦ C ^ 2)) :=
    (integrableOn_const (s := Icc (a - delta) (a + delta))
      (by simp)).integrable_indicator measurableSet_Icc
  have htail : Integrable (fun x : ℝ ↦
      (N ^ 2 * (1 + (delta ^ 2)⁻¹)) *
        (1 + (x - a) ^ 2)⁻¹) :=
    (integrable_suzukiShiftedCauchyDensity a).const_mul
      (N ^ 2 * (1 + (delta ^ 2)⁻¹))
  unfold suzukiRealAxisZeroFunctionNormSqMajorant
  change (∫ x : ℝ,
      (Icc (a - delta) (a + delta)).indicator
          (fun _ ↦ C ^ 2) x +
        (N ^ 2 * (1 + (delta ^ 2)⁻¹)) *
          (1 + (x - a) ^ 2)⁻¹) = _
  rw [integral_add hcompact htail,
    integral_centeredIcc_indicator_const a delta C hdelta,
    integral_const_mul, integral_suzukiShiftedCauchyDensity]

/-- The analytic regularization gives a local real-axis bound with an
explicit constant: twice its exact central value `sqrt(m/pi) / m`.  Only the
radius remains zero-dependent. -/
theorem exists_explicit_local_bound_suzukiRealAxisZeroFunction_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ,
      |x - (zetaSpectralCoordinate rho.1).re| < r →
        ‖suzukiRealAxisZeroFunction rho x‖ ≤
          2 * suzukiXiZeroNormalization rho /
            (analyticZetaZeroMultiplicity rho : ℝ) := by
  let alpha := zetaSpectralCoordinate rho.1
  let N := suzukiXiZeroNormalization rho
  let m : ℝ := analyticZetaZeroMultiplicity rho
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hN : 0 < N := by
    dsimp [N, suzukiXiZeroNormalization]
    exact Real.sqrt_pos.2
      (div_pos (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        Real.pi_pos)
  have halpha : ((alpha.re : ℝ) : ℂ) = alpha := by
    apply Complex.ext
    · simp
    · simpa [alpha] using hrho.symm
  obtain ⟨h, hh, heq⟩ :=
    eventuallyEq_suzukiXiZeroFunctionFormula_regularization rho
  let F : ℂ → ℂ := suzukiXiZeroFunctionRegularization rho h
  have hFcontinuous : ContinuousAt F alpha := by
    exact (analyticAt_suzukiXiZeroFunctionRegularization rho hh).continuousAt
  have hFcenter : ‖F alpha‖ = N / m := by
    dsimp [F, suzukiXiZeroFunctionRegularization, alpha, N, m]
    simp only [sub_self, zero_mul, add_zero, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, norm_I,
      Complex.norm_natCast, mul_one]
    rw [abs_of_pos hN]
  have hcenterLt : ‖F alpha‖ < 2 * N / m := by
    rw [hFcenter]
    have hNm : 0 < N / m := div_pos hN hm
    calc
      N / m < 2 * (N / m) := by linarith
      _ = 2 * N / m := by ring
  have hnear : ∀ᶠ z in 𝓝 alpha, ‖F z‖ < 2 * N / m :=
    hFcontinuous.norm.tendsto.eventually (Iio_mem_nhds hcenterLt)
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
      ‖suzukiXiZeroFunctionFormula rho z‖ ≤ 2 * N / m := by
    filter_upwards [heq', hnear] with z hzEq hzBound hza
    rw [hzEq hza]
    exact hzBound.le
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  refine ⟨r, hr, ?_⟩
  intro x hx
  by_cases hxa : x = alpha.re
  · subst x
    have hden : ((alpha.re : ℝ) : ℂ) -
        zetaSpectralCoordinate rho.1 = 0 := by
      rw [halpha]
      simp [alpha]
    simp [suzukiRealAxisZeroFunction, suzukiXiZeroFunctionFormula, hden]
    exact (div_pos (mul_pos two_pos hN) hm).le
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

/-- A local cancellation bound on a real spectral zero gives an explicit
global boundary norm bound. -/
theorem norm_sq_suzukiRealAxisZeroFunctionLp_le_of_real_local_bound
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0)
    {r C delta : ℝ} (hdelta : 0 < delta) (hdeltaR : delta < r)
    (hlocal : ∀ x : ℝ,
      |x - (zetaSpectralCoordinate rho.1).re| < r →
        ‖suzukiRealAxisZeroFunction rho x‖ ≤ C) :
    ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 ≤
      2 * delta * C ^ 2 +
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (1 + (delta ^ 2)⁻¹) := by
  have hleft : Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) :=
    integrable_normSq_suzukiRealAxisZeroFunction_of_im_eq_zero rho hrho
  have hright :=
    integrable_suzukiRealAxisZeroFunctionNormSqMajorant rho delta C
  rw [norm_sq_suzukiRealAxisZeroFunctionLp]
  calc
    (∫ x : ℝ, ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) ≤
        ∫ x : ℝ,
          suzukiRealAxisZeroFunctionNormSqMajorant rho delta C x := by
      apply integral_mono hleft hright
      intro x
      exact
        normSq_suzukiRealAxisZeroFunction_le_majorant_of_im_eq_zero
          rho hrho hdelta hdeltaR hlocal x
    _ = 2 * delta * C ^ 2 +
        (suzukiXiZeroNormalization rho ^ 2 *
          (1 + (delta ^ 2)⁻¹)) * Real.pi :=
      integral_suzukiRealAxisZeroFunctionNormSqMajorant
        rho delta C hdelta.le
    _ = 2 * delta * C ^ 2 +
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (1 + (delta ^ 2)⁻¹) := by
      rw [sq_suzukiXiZeroNormalization]
      field_simp [Real.pi_ne_zero]

/-- Every real-node zero function admits concrete local parameters for the
preceding quantitative global norm bound. -/
theorem exists_norm_sq_suzukiRealAxisZeroFunctionLp_bound_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 ≤
        2 * delta * C ^ 2 +
          (analyticZetaZeroMultiplicity rho : ℝ) *
            (1 + (delta ^ 2)⁻¹) := by
  obtain ⟨r, hr, C, hC, hlocal⟩ :=
    exists_local_bound_suzukiRealAxisZeroFunction_of_im_eq_zero rho hrho
  let delta : ℝ := min (r / 2) 1
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (half_pos hr) zero_lt_one
  have hdeltaR : delta < r :=
    (min_le_left (r / 2) 1).trans_lt (half_lt_self hr)
  refine ⟨delta, hdelta, C, hC, ?_⟩
  exact norm_sq_suzukiRealAxisZeroFunctionLp_le_of_real_local_bound
    rho hrho hdelta hdeltaR hlocal

/-- Eliminating the opaque local constant leaves an unconditional
one-parameter norm bound for every real spectral zero. -/
theorem exists_explicit_norm_sq_suzukiRealAxisZeroFunctionLp_bound_of_im_eq_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 ≤
        8 * delta /
            (Real.pi * (analyticZetaZeroMultiplicity rho : ℝ)) +
          (analyticZetaZeroMultiplicity rho : ℝ) *
            (1 + (delta ^ 2)⁻¹) := by
  obtain ⟨r, hr, hlocal⟩ :=
    exists_explicit_local_bound_suzukiRealAxisZeroFunction_of_im_eq_zero
      rho hrho
  let delta : ℝ := min (r / 2) 1
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (half_pos hr) zero_lt_one
  have hdeltaR : delta < r :=
    (min_le_left (r / 2) 1).trans_lt (half_lt_self hr)
  refine ⟨delta, hdelta, ?_⟩
  have hbound :=
    norm_sq_suzukiRealAxisZeroFunctionLp_le_of_real_local_bound
      rho hrho hdelta hdeltaR hlocal
  calc
    ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 ≤
        2 * delta *
            (2 * suzukiXiZeroNormalization rho /
              (analyticZetaZeroMultiplicity rho : ℝ)) ^ 2 +
          (analyticZetaZeroMultiplicity rho : ℝ) *
            (1 + (delta ^ 2)⁻¹) := hbound
    _ = 8 * delta /
          (Real.pi * (analyticZetaZeroMultiplicity rho : ℝ)) +
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (1 + (delta ^ 2)⁻¹) := by
      rw [div_pow, show (2 * suzukiXiZeroNormalization rho) ^ 2 =
        4 * suzukiXiZeroNormalization rho ^ 2 by ring,
        sq_suzukiXiZeroNormalization]
      have hm : (analyticZetaZeroMultiplicity rho : ℝ) ≠ 0 := by
        exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'
      field_simp [Real.pi_ne_zero, hm]
      ring

end

end RiemannGaussian
