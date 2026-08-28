import RiemannGaussian.RiemannXiSuzukiRealAxisCancellation
import RiemannGaussian.GaussianCompletedLogDerivative

/-!
# The completed logarithmic derivative on Suzuki's real axis

The arithmetic formula contains `ζ'/ζ(1/2 - i z)`.  Estimating that term
separately would lose the cancellation supplied by Suzuki's xi carrier.  This
file extends the completed-zeta logarithmic-derivative identity from the
Euler-product half-plane to every point with positive real part at which zeta
is nonzero.  It then specializes the identity to the real spectral axis.

The result groups the potentially singular zeta logarithmic derivative into
the spectral-xi logarithmic derivative, which the carrier cancels, plus only
the two elementary pole terms and the digamma term.  No asymptotic estimate
or `L²` conclusion is asserted in this file.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- In the positive-real-part half-plane, the entire xi normalization is the
polynomial factor times `Gammaℝ` and zeta. -/
theorem riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s =
      s * (1 - s) * Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hGammaℝ : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hs
  have hzetaCompleted := riemannZeta_def_of_ne_zero hs0
  have hzetaMul : riemannZeta s * Complex.Gammaℝ s =
      completedRiemannZeta s :=
    (eq_div_iff hGammaℝ).mp hzetaCompleted
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, ← hzetaMul]
  ring

/-- Exact completed logarithmic derivative wherever `Re s > 0`, `s ≠ 1`,
and zeta is nonzero.  This includes every nonzero point of zeta on the
critical line. -/
theorem logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaℝ : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hs
  have hGammaℝDiff : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hs
  have hzetaDiff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hlocal : riemannXi =ᶠ[nhds s]
      (fun z : ℂ ↦
        z * (1 - z) * Complex.Gammaℝ z * riemannZeta z) := by
    filter_upwards
      [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs,
        eventually_ne_nhds hs1] with z hz hzone
    exact riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hz hzone
  rw [(logDeriv_congr_nhds hlocal).self_of_nhds]
  have hlinear :
      logDeriv (fun z : ℂ ↦ z * (1 - z)) s =
        1 / s + 1 / (s - 1) := by
    have hderivSub : deriv (fun z : ℂ ↦ 1 - z) s = -1 :=
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv.trans (by ring)
    rw [logDeriv_mul (f := fun z : ℂ ↦ z)
      (g := fun z : ℂ ↦ 1 - z) s hs0 h1s
      (by fun_prop) (by fun_prop)]
    simp only [logDeriv_apply, deriv_id'', hderivSub]
    field_simp [hs0, hs1]
    ring
  have hcompleted :
      logDeriv
          (fun z : ℂ ↦ z * (1 - z) * Complex.Gammaℝ z) s =
        1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
          Complex.digamma (s / 2) / 2 := by
    rw [logDeriv_mul (f := fun z : ℂ ↦ z * (1 - z))
      (g := Complex.Gammaℝ) s (mul_ne_zero hs0 h1s) hGammaℝ
      ((by fun_prop) :
        DifferentiableAt ℂ (fun z : ℂ ↦ z * (1 - z)) s)
      hGammaℝDiff]
    rw [hlinear, logDeriv_Gammaℝ hs]
    ring
  rw [logDeriv_mul
    (f := fun z : ℂ ↦ z * (1 - z) * Complex.Gammaℝ z)
    (g := riemannZeta) s
    (mul_ne_zero (mul_ne_zero hs0 h1s) hGammaℝ)
    hzeta
    (((by fun_prop) :
      DifferentiableAt ℂ (fun z : ℂ ↦ z * (1 - z)) s).mul
        hGammaℝDiff)
    hzetaDiff]
  rw [hcompleted]

/-- Suzuki's zeta argument is the functional-equation reflection of the
completed spectral coordinate. -/
theorem suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate
    (z : ℂ) :
    suzukiArithmeticZetaArgument z =
      1 - completedSpectralCoordinate z := by
  unfold suzukiArithmeticZetaArgument completedSpectralCoordinate
  ring

/-- The completed xi logarithmic derivative at Suzuki's reflected argument
is exactly the spectral negative logarithmic derivative.  This identity also
holds at a totalized zero. -/
theorem logDeriv_riemannXi_suzukiArithmeticZetaArgument (z : ℂ) :
    logDeriv riemannXi (suzukiArithmeticZetaArgument z) =
      xiSpectralNegativeLogDerivative z := by
  rw [suzukiArithmeticZetaArgument_eq_one_sub_completedSpectralCoordinate,
    logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub]
  rfl

/-- The nonspectral terms left after completing the zeta logarithmic
derivative. -/
def suzukiArithmeticCompletedLogRemainder (z : ℂ) : ℂ :=
  1 / suzukiArithmeticZetaArgument z +
    1 / (suzukiArithmeticZetaArgument z - 1) -
      Complex.log Real.pi / 2 +
        Complex.digamma (suzukiArithmeticZetaArgument z / 2) / 2

/-- The reciprocal of Suzuki's critical-line zeta argument is uniformly
bounded by two. -/
theorem norm_one_div_suzukiArithmeticZetaArgument_ofReal_le_two
    (x : ℝ) :
    ‖1 / suzukiArithmeticZetaArgument (x : ℂ)‖ ≤ 2 := by
  have hs0 : suzukiArithmeticZetaArgument (x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [suzukiArithmeticZetaArgument] at hre
  have hsNorm : (1 / 2 : ℝ) ≤
      ‖suzukiArithmeticZetaArgument (x : ℂ)‖ := by
    have h := Complex.abs_re_le_norm
      (suzukiArithmeticZetaArgument (x : ℂ))
    norm_num [suzukiArithmeticZetaArgument] at h ⊢
    exact h
  rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  linarith

/-- The reciprocal of the reflected elementary pole factor is likewise
uniformly bounded by two. -/
theorem norm_one_div_suzukiArithmeticZetaArgument_sub_one_ofReal_le_two
    (x : ℝ) :
    ‖1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1)‖ ≤ 2 := by
  have hs0 : suzukiArithmeticZetaArgument (x : ℂ) - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [suzukiArithmeticZetaArgument] at hre
  have hsNorm : (1 / 2 : ℝ) ≤
      ‖suzukiArithmeticZetaArgument (x : ℂ) - 1‖ := by
    have h := Complex.abs_re_le_norm
      (suzukiArithmeticZetaArgument (x : ℂ) - 1)
    norm_num [suzukiArithmeticZetaArgument] at h ⊢
    exact h
  rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.mpr hs0)]
  linarith

/-- The completed remainder consists of a fixed elementary budget plus the
single quarter-line digamma norm. -/
theorem norm_suzukiArithmeticCompletedLogRemainder_ofReal_le
    (x : ℝ) :
    ‖suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ ≤
      4 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
  unfold suzukiArithmeticCompletedLogRemainder
  calc
    ‖1 / suzukiArithmeticZetaArgument (x : ℂ) +
          1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1) -
          Complex.log Real.pi / 2 +
          Complex.digamma
            (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ ≤
        ‖1 / suzukiArithmeticZetaArgument (x : ℂ) +
          1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1) -
          Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ :=
      norm_add_le _ _
    _ ≤
        (‖1 / suzukiArithmeticZetaArgument (x : ℂ) +
            1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1)‖ +
          ‖Complex.log Real.pi / 2‖) +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
        ((‖1 / suzukiArithmeticZetaArgument (x : ℂ)‖ +
            ‖1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1)‖) +
          ‖Complex.log Real.pi / 2‖) +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 4 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
      have ha :=
        norm_one_div_suzukiArithmeticZetaArgument_ofReal_le_two x
      have hb :=
        norm_one_div_suzukiArithmeticZetaArgument_sub_one_ofReal_le_two x
      linarith

/-- Away from a critical-line zeta zero, its logarithmic derivative is the
carrier-cancellable spectral-xi term minus explicit elementary and digamma
terms. -/
theorem logDeriv_riemannZeta_suzukiArithmeticZetaArgument_ofReal
    (x : ℝ)
    (hzeta :
      riemannZeta (suzukiArithmeticZetaArgument (x : ℂ)) ≠ 0) :
    logDeriv riemannZeta
        (suzukiArithmeticZetaArgument (x : ℂ)) =
      xiSpectralNegativeLogDerivative (x : ℂ) -
        1 / suzukiArithmeticZetaArgument (x : ℂ) -
        1 / (suzukiArithmeticZetaArgument (x : ℂ) - 1) +
        Complex.log Real.pi / 2 -
        Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2 := by
  have hs :
      0 < (suzukiArithmeticZetaArgument (x : ℂ)).re := by
    simp [suzukiArithmeticZetaArgument]
  have hs1 : suzukiArithmeticZetaArgument (x : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [suzukiArithmeticZetaArgument] at hre
  have hcompleted :=
    logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero hs hs1 hzeta
  rw [logDeriv_riemannXi_suzukiArithmeticZetaArgument] at hcompleted
  rw [hcompleted]
  ring

/-- Compact form of the critical-line completed-logarithmic-derivative
decomposition. -/
theorem logDeriv_riemannZeta_suzukiArithmeticZetaArgument_eq_sub_remainder
    (x : ℝ)
    (hzeta :
      riemannZeta (suzukiArithmeticZetaArgument (x : ℂ)) ≠ 0) :
    logDeriv riemannZeta
        (suzukiArithmeticZetaArgument (x : ℂ)) =
      xiSpectralNegativeLogDerivative (x : ℂ) -
        suzukiArithmeticCompletedLogRemainder (x : ℂ) := by
  rw [logDeriv_riemannZeta_suzukiArithmeticZetaArgument_ofReal x hzeta]
  unfold suzukiArithmeticCompletedLogRemainder
  ring

/-- The exact grouping used in the real-axis decay estimate: after
multiplication by Suzuki's carrier, the only singular logarithmic derivative
is already packaged as the bounded carrier-xi product. -/
theorem suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal
    (x : ℝ)
    (hzeta :
      riemannZeta (suzukiArithmeticZetaArgument (x : ℂ)) ≠ 0) :
    suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ)) =
      suzukiXiZeroCarrier (x : ℂ) *
        xiSpectralNegativeLogDerivative (x : ℂ) -
      suzukiXiZeroCarrier (x : ℂ) *
        suzukiArithmeticCompletedLogRemainder (x : ℂ) := by
  rw [
    logDeriv_riemannZeta_suzukiArithmeticZetaArgument_eq_sub_remainder
      x hzeta]
  ring

/-- The grouped critical-line zeta logarithmic derivative is controlled
unconditionally by one plus the explicit completed remainder.  At a zeta
zero the totalized logarithmic derivative is zero; away from the zero set,
the unit bound is exactly the carrier-xi cancellation theorem. -/
theorem norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le
    (x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      1 + ‖suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ := by
  by_cases hzeta :
      riemannZeta (suzukiArithmeticZetaArgument (x : ℂ)) = 0
  · rw [logDeriv_apply, hzeta, div_zero, mul_zero, norm_zero]
    positivity
  · rw [suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal x hzeta]
    calc
      ‖suzukiXiZeroCarrier (x : ℂ) *
            xiSpectralNegativeLogDerivative (x : ℂ) -
          suzukiXiZeroCarrier (x : ℂ) *
            suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ ≤
          ‖suzukiXiZeroCarrier (x : ℂ) *
            xiSpectralNegativeLogDerivative (x : ℂ)‖ +
          ‖suzukiXiZeroCarrier (x : ℂ) *
            suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + ‖suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ := by
        apply add_le_add
        · exact
            norm_suzukiXiZeroCarrier_mul_xiSpectralNegativeLogDerivative_ofReal_le_one
              x
        · rw [norm_mul]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right
              (norm_suzukiXiZeroCarrier_ofReal_le_one x)
              (norm_nonneg
                (suzukiArithmeticCompletedLogRemainder (x : ℂ)))

/-- Fully explicit reduction of the grouped zeta term to the quarter-line
digamma growth problem. -/
theorem norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le_digamma
    (x : ℝ) :
    ‖suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      5 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
  calc
    ‖suzukiXiZeroCarrier (x : ℂ) *
        logDeriv riemannZeta
          (suzukiArithmeticZetaArgument (x : ℂ))‖ ≤
      1 + ‖suzukiArithmeticCompletedLogRemainder (x : ℂ)‖ :=
        norm_suzukiXiZeroCarrier_mul_logDeriv_riemannZeta_ofReal_le x
    _ ≤ 1 + (4 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖) := by
      gcongr
      exact norm_suzukiArithmeticCompletedLogRemainder_ofReal_le x
    _ = 5 + ‖Complex.log Real.pi / 2‖ +
        ‖Complex.digamma
          (suzukiArithmeticZetaArgument (x : ℂ) / 2) / 2‖ := by
      ring

end

end RiemannGaussian
