import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourArchimedean

/-!
# Arithmetic reduction of the static-contour endpoint term

This module factors the completed-xi endpoint logarithms into their
elementary polynomial, Archimedean `Gammaℝ`, and Riemann-zeta parts.  The
polynomial term is uniformly bounded, while the preceding Archimedean module
proves the gamma term is sublinear.  Consequently the static vertical contour
is reduced exactly to the zeta endpoint log ratio on the quantitative
zero-free heights.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology
  RealInnerProductSpace

namespace RiemannGaussian

noncomputable section

/-- The critical completed-zeta endpoint at height `T`. -/
def staticContourCriticalEndpoint (T : ℝ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- The safe completed-zeta endpoint at height `T`. -/
def staticContourSafeEndpoint (T : ℝ) : ℂ :=
  ((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I

/-- Completed-xi log-modulus difference from the critical endpoint to the
safe endpoint. -/
def staticContourCompletedXiEndpointLogDifference (T : ℝ) : ℝ :=
  Real.log ‖riemannXi (staticContourSafeEndpoint T)‖ -
    Real.log ‖riemannXi (staticContourCriticalEndpoint T)‖

/-- Log-modulus difference of the elementary `s * (1 - s)` factors. -/
def staticContourPolynomialEndpointLogDifference (T : ℝ) : ℝ :=
  Real.log ‖staticContourSafeEndpoint T *
      (1 - staticContourSafeEndpoint T)‖ -
    Real.log ‖staticContourCriticalEndpoint T *
      (1 - staticContourCriticalEndpoint T)‖

/-- Log-modulus difference of the two Riemann-zeta endpoint values. -/
def staticContourZetaEndpointLogDifference (T : ℝ) : ℝ :=
  Real.log ‖riemannZeta (staticContourSafeEndpoint T)‖ -
    Real.log ‖riemannZeta (staticContourCriticalEndpoint T)‖

/-- At a nonzero completed-xi point in the positive half-plane, its
log-modulus splits exactly into polynomial, `Gammaℝ`, and zeta terms. -/
theorem log_norm_riemannXi_eq_polynomial_add_GammaR_add_zeta
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hxi : riemannXi s ≠ 0) :
    Real.log ‖riemannXi s‖ =
      Real.log ‖s * (1 - s)‖ + Real.log ‖Complex.Gammaℝ s‖ +
        Real.log ‖riemannZeta s‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGamma : Complex.Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzeta
    apply hxi
    rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs hs1,
      hzeta, mul_zero]
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs hs1]
  rw [show s * (1 - s) * Complex.Gammaℝ s * riemannZeta s =
      (s * (1 - s)) * Complex.Gammaℝ s * riemannZeta s by ring]
  rw [norm_mul, norm_mul]
  rw [Real.log_mul
      (mul_ne_zero (norm_ne_zero_iff.mpr (mul_ne_zero hs0 h1s))
        (norm_ne_zero_iff.mpr hGamma))
      (norm_ne_zero_iff.mpr hzeta),
    Real.log_mul
      (norm_ne_zero_iff.mpr (mul_ne_zero hs0 h1s))
      (norm_ne_zero_iff.mpr hGamma)]

/-- The critical quantitative endpoint is nonzero. -/
theorem riemannXi_staticContourCriticalEndpoint_quantitative_ne_zero
    (n : ℕ) :
    riemannXi (staticContourCriticalEndpoint
      (quantitativeSpectralBoundaryTruncation n)) ≠ 0 := by
  simpa [staticContourCriticalEndpoint, completedSpectralCoordinate,
    mul_comm] using riemannXi_quantitativeCompletedCoordinate_ne_zero n 0

/-- The safe endpoint is nonzero at every real height by absolute
nonvanishing of zeta in `Re s > 1`. -/
theorem riemannXi_staticContourSafeEndpoint_ne_zero (T : ℝ) :
    riemannXi (staticContourSafeEndpoint T) ≠ 0 := by
  let s : ℂ := staticContourSafeEndpoint T
  have hs : 0 < s.re := by simp [s, staticContourSafeEndpoint]
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, staticContourSafeEndpoint] at hre
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, staticContourSafeEndpoint] at hre
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGamma : Complex.Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re
      (by norm_num [s, staticContourSafeEndpoint])
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hs hs1]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 h1s) hGamma) hzeta

/-- On every quantitative height the completed-xi endpoint difference splits
exactly into its polynomial, gamma, and zeta contributions. -/
theorem staticContourCompletedXiEndpointLogDifference_eq_polynomial_add_gamma_add_zeta
    (n : ℕ) :
    staticContourCompletedXiEndpointLogDifference
        (quantitativeSpectralBoundaryTruncation n) =
      staticContourPolynomialEndpointLogDifference
          (quantitativeSpectralBoundaryTruncation n) +
        (staticContourGammaRHorizontalLogNorm
            (quantitativeSpectralBoundaryTruncation n) (3 / 2) -
          staticContourGammaRHorizontalLogNorm
            (quantitativeSpectralBoundaryTruncation n) (1 / 2)) +
        staticContourZetaEndpointLogDifference
          (quantitativeSpectralBoundaryTruncation n) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let s0 : ℂ := staticContourCriticalEndpoint T
  let s1 : ℂ := staticContourSafeEndpoint T
  have hsafe := log_norm_riemannXi_eq_polynomial_add_GammaR_add_zeta
    (s := s1) (by simp [s1, staticContourSafeEndpoint])
    (by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s1, staticContourSafeEndpoint] at hre)
    (by simpa [s1] using riemannXi_staticContourSafeEndpoint_ne_zero T)
  have hcritical := log_norm_riemannXi_eq_polynomial_add_GammaR_add_zeta
    (s := s0) (by simp [s0, staticContourCriticalEndpoint])
    (by
      intro h
      have hre := congrArg Complex.re h
      norm_num [s0, staticContourCriticalEndpoint] at hre)
    (by simpa [s0, T] using
      riemannXi_staticContourCriticalEndpoint_quantitative_ne_zero n)
  unfold staticContourCompletedXiEndpointLogDifference
    staticContourPolynomialEndpointLogDifference
    staticContourZetaEndpointLogDifference
    staticContourGammaRHorizontalLogNorm
  change Real.log ‖riemannXi s1‖ - Real.log ‖riemannXi s0‖ =
    (Real.log ‖s1 * (1 - s1)‖ - Real.log ‖s0 * (1 - s0)‖) +
      (Real.log ‖Complex.Gammaℝ s1‖ - Real.log ‖Complex.Gammaℝ s0‖) +
      (Real.log ‖riemannZeta s1‖ - Real.log ‖riemannZeta s0‖)
  rw [hsafe, hcritical]
  ring

/-- The critical endpoint is conjugate to its reflected elementary factor. -/
theorem one_sub_staticContourCriticalEndpoint (T : ℝ) :
    1 - staticContourCriticalEndpoint T =
      starRingEnd ℂ (staticContourCriticalEndpoint T) := by
  unfold staticContourCriticalEndpoint
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The safe endpoint's reflected elementary factor is the negative critical
endpoint. -/
theorem one_sub_staticContourSafeEndpoint (T : ℝ) :
    1 - staticContourSafeEndpoint T =
      -staticContourCriticalEndpoint T := by
  unfold staticContourSafeEndpoint staticContourCriticalEndpoint
  push_cast
  ring

/-- Moving from the critical endpoint to the safe endpoint increases its
norm by at most a factor of three. -/
theorem norm_staticContourCriticalEndpoint_le_safe_le_three_mul (T : ℝ) :
    ‖staticContourCriticalEndpoint T‖ ≤ ‖staticContourSafeEndpoint T‖ ∧
      ‖staticContourSafeEndpoint T‖ ≤
        3 * ‖staticContourCriticalEndpoint T‖ := by
  have hlower : ‖staticContourCriticalEndpoint T‖ ≤
      ‖staticContourSafeEndpoint T‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [staticContourCriticalEndpoint, staticContourSafeEndpoint,
      Complex.normSq_apply]
    nlinarith
  have hshift : staticContourSafeEndpoint T =
      staticContourCriticalEndpoint T + 1 := by
    unfold staticContourSafeEndpoint staticContourCriticalEndpoint
    push_cast
    ring
  have hhalf : (1 / 2 : ℝ) ≤ ‖staticContourCriticalEndpoint T‖ := by
    calc
      (1 / 2 : ℝ) = (staticContourCriticalEndpoint T).re := by
        simp [staticContourCriticalEndpoint]
      _ ≤ ‖staticContourCriticalEndpoint T‖ := Complex.re_le_norm _
  have hupper : ‖staticContourSafeEndpoint T‖ ≤
      3 * ‖staticContourCriticalEndpoint T‖ := by
    calc
      ‖staticContourSafeEndpoint T‖ =
          ‖staticContourCriticalEndpoint T + 1‖ := by rw [hshift]
      _ ≤ ‖staticContourCriticalEndpoint T‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖staticContourCriticalEndpoint T‖ + 1 := by norm_num
      _ ≤ 3 * ‖staticContourCriticalEndpoint T‖ := by linarith
  exact ⟨hlower, hupper⟩

/-- The elementary polynomial endpoint difference is the logarithm of the
ratio of the safe and critical endpoint norms. -/
theorem staticContourPolynomialEndpointLogDifference_eq_log_norm_div (T : ℝ) :
    staticContourPolynomialEndpointLogDifference T =
      Real.log
        (‖staticContourSafeEndpoint T‖ /
          ‖staticContourCriticalEndpoint T‖) := by
  have hcrit : staticContourCriticalEndpoint T ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [staticContourCriticalEndpoint] at hre
  have hsafe : staticContourSafeEndpoint T ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [staticContourSafeEndpoint] at hre
  have hcritNorm : ‖staticContourCriticalEndpoint T‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hcrit
  have hsafeNorm : ‖staticContourSafeEndpoint T‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hsafe
  unfold staticContourPolynomialEndpointLogDifference
  rw [one_sub_staticContourSafeEndpoint,
    one_sub_staticContourCriticalEndpoint,
    norm_mul, norm_mul, norm_neg, Complex.norm_conj]
  rw [Real.log_mul hsafeNorm hcritNorm,
    Real.log_mul hcritNorm hcritNorm,
    Real.log_div hsafeNorm hcritNorm]
  ring

/-- The elementary polynomial endpoint log difference is uniformly bounded
between zero and `log 3`. -/
theorem staticContourPolynomialEndpointLogDifference_nonneg_le_log_three
    (T : ℝ) :
    0 ≤ staticContourPolynomialEndpointLogDifference T ∧
      staticContourPolynomialEndpointLogDifference T ≤ Real.log 3 := by
  have hcritPos : 0 < ‖staticContourCriticalEndpoint T‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    norm_num [staticContourCriticalEndpoint] at hre
  have hnorm := norm_staticContourCriticalEndpoint_le_safe_le_three_mul T
  have hratioLower : 1 ≤
      ‖staticContourSafeEndpoint T‖ /
        ‖staticContourCriticalEndpoint T‖ :=
    (le_div_iff₀ hcritPos).2 (by simpa using hnorm.1)
  have hratioUpper :
      ‖staticContourSafeEndpoint T‖ /
          ‖staticContourCriticalEndpoint T‖ ≤ 3 :=
    (div_le_iff₀ hcritPos).2 hnorm.2
  rw [staticContourPolynomialEndpointLogDifference_eq_log_norm_div]
  exact ⟨Real.log_nonneg hratioLower,
    Real.log_le_log (by positivity) hratioUpper⟩

/-- The elementary endpoint factor contributes `o(T)` on the quantitative
height sequence. -/
theorem tendsto_staticContourPolynomialEndpointLogDifference_div_quantitative_zero :
    Tendsto
      (fun n : ℕ ↦
        staticContourPolynomialEndpointLogDifference
            (quantitativeSpectralBoundaryTruncation n) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  refine squeeze_zero_norm'
    (a := fun n : ℕ ↦ Real.log 3 / T n) ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      have hT : 0 < T n :=
        (Nat.cast_nonneg n).trans_lt
          (by simpa [T] using
            (quantitativeSpectralBoundaryTruncation_spec n).1)
      have hpoly :=
        staticContourPolynomialEndpointLogDifference_nonneg_le_log_three
          (T n)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hT,
        abs_of_nonneg hpoly.1]
      exact div_le_div_of_nonneg_right hpoly.2 hT.le
  · have hlim : Tendsto (fun n : ℕ ↦ Real.log 3 / T n)
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        tendsto_quantitativeSpectralBoundaryTruncation_atTop
    exact hlim

/-- After removing the zeta endpoint term, the remaining completed-xi
endpoint difference is `o(T)` on the quantitative heights. -/
theorem tendsto_staticContourCompletedXiEndpointLogDifference_sub_zeta_div_quantitative_zero :
    Tendsto
      (fun n : ℕ ↦
        (staticContourCompletedXiEndpointLogDifference
            (quantitativeSpectralBoundaryTruncation n) -
          staticContourZetaEndpointLogDifference
            (quantitativeSpectralBoundaryTruncation n)) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  have hpoly :=
    tendsto_staticContourPolynomialEndpointLogDifference_div_quantitative_zero
  have hgamma :=
    tendsto_staticContourGammaRHorizontalLogNorm_sub_div_quantitative_zero
  have hsum : Tendsto
      (fun n : ℕ ↦
        staticContourPolynomialEndpointLogDifference
            (quantitativeSpectralBoundaryTruncation n) /
          quantitativeSpectralBoundaryTruncation n +
        (staticContourGammaRHorizontalLogNorm
              (quantitativeSpectralBoundaryTruncation n) (3 / 2) -
            staticContourGammaRHorizontalLogNorm
              (quantitativeSpectralBoundaryTruncation n) (1 / 2)) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
    simpa using hpoly.add hgamma
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [staticContourCompletedXiEndpointLogDifference_eq_polynomial_add_gamma_add_zeta]
    ring

/-- The static vertical boundary is asymptotic solely to the zeta endpoint
log ratio.  Every elementary and Archimedean contribution has now been
removed by unconditional Lean theorems. -/
theorem tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_zeta_logNorm_main_quantitative_zero
    {v : ℝ} (hv : 1 < v) :
    Tendsto
      (fun n : ℕ ↦
        -Complex.I *
            xiSpectralBlaschkeSignedVerticalRemainderWindow
              (quantitativeSpectralBoundaryTruncation n) 0
              ((v : ℂ) * Complex.I) +
          (((4 / quantitativeSpectralBoundaryTruncation n) *
            staticContourZetaEndpointLogDifference
              (quantitativeSpectralBoundaryTruncation n) : ℝ) : ℂ))
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let C : ℕ → ℝ := fun n ↦
    staticContourCompletedXiEndpointLogDifference (T n)
  let Z : ℕ → ℝ := fun n ↦
    staticContourZetaEndpointLogDifference (T n)
  let V : ℕ → ℂ := fun n ↦
    -Complex.I * xiSpectralBlaschkeSignedVerticalRemainderWindow
      (T n) 0 ((v : ℂ) * Complex.I)
  have hmain : Tendsto
      (fun n : ℕ ↦ V n + (((4 / T n) * C n : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa [T, C, V, staticContourCompletedXiEndpointLogDifference,
      staticContourSafeEndpoint, staticContourCriticalEndpoint] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_completedXi_logNorm_main_quantitative_zero
        hv
  have hremainder : Tendsto
      (fun n : ℕ ↦ (C n - Z n) / T n) atTop (nhds 0) := by
    simpa [T, C, Z] using
      tendsto_staticContourCompletedXiEndpointLogDifference_sub_zeta_div_quantitative_zero
  have hremainderComplex : Tendsto
      (fun n : ℕ ↦ (((4 * ((C n - Z n) / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    have hreal : Tendsto
        (fun n : ℕ ↦ 4 * ((C n - Z n) / T n)) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hremainder
    simpa using hreal.ofReal
  have hdifference : Tendsto
      (fun n : ℕ ↦
        V n + (((4 / T n) * C n : ℝ) : ℂ) -
          (((4 * ((C n - Z n) / T n) : ℝ)) : ℂ))
      atTop (nhds 0) := by
    simpa using hmain.sub hremainderComplex
  apply hdifference.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp [V, T, C, Z]
    push_cast
    ring

end

end RiemannGaussian
