import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaLog

/-!
# The local eta canonical-factor product at the critical endpoint

This module combines the moving Jensen count, quantitative zero separation,
and the zero-free residual logarithm at the translated critical point `-1`.
The selected canonical disk lies strictly inside the Jensen disk, so every
canonical divisor point is covered by both the checked multiplicity count and
the local eta separation theorem.

Each canonical factor is bounded explicitly in terms of the separation
radius.  Summing with divisor multiplicity gives a finite-product estimate,
which is combined with the exact extended canonical decomposition.  The
result is an explicit lower logarithmic bound for paired eta at the selected
critical endpoints.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A canonical factor at any point of its closed disk is bounded in terms of
the distance to its divisor point. -/
lemma norm_canonicalFactor_le_of_closedBall_of_separated
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta)
    {i z : ℂ} (hi : i ∈ ball 0 R) (hz : ‖z‖ ≤ R)
    (hsep : delta ≤ ‖z - i‖) :
    ‖Complex.canonicalFactor R i z‖ ≤ 2 * R / delta := by
  have hiNorm : ‖i‖ < R := by
    simpa [mem_ball, dist_zero_right] using hi
  have hnum : ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ ≤ 2 * R ^ 2 := by
    calc
      ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ ≤
          ‖(R : ℂ) ^ 2‖ + ‖starRingEnd ℂ i * z‖ := norm_sub_le _ _
      _ = R ^ 2 + ‖i‖ * ‖z‖ := by simp [abs_of_pos hR]
      _ ≤ 2 * R ^ 2 := by
        nlinarith [norm_nonneg i, norm_nonneg z]
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp only [norm_real]
  calc
    ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ /
          (|R| * ‖z - i‖) ≤
        (2 * R ^ 2) / (R * delta) := by
      rw [abs_of_pos hR]
      exact div_le_div₀ (by positivity) hnum (mul_pos hR hdelta)
        (mul_le_mul_of_nonneg_left hsep hR.le)
    _ = 2 * R / delta := by field_simp

/-- The canonical-radius divisor count is controlled by the larger fixed
Jensen disk. -/
theorem sum_divisor_staticContourLocalEta_canonicalBall_le_log (n : ℕ) :
    ((∑ᶠ i, divisor
        (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n))
        (ball 0 (staticContourLocalEtaCanonicalRadius n)) i : ℤ) : ℝ) ≤
      Real.log
          (staticContourLocalEtaJensenConstant *
            (quantitativeSpectralBoundaryTruncation n + 4)) /
        Real.log (10 / 9 : ℝ) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  let f : ℂ → ℂ := staticContourLocalEta T
  let d : ℂ → ℤ := fun i => divisor f (ball 0 R) i
  let e : ℂ → ℤ := fun i =>
    divisor f (closedBall 0 staticContourLocalEtaInnerRadius) i
  have hRlt : R < staticContourLocalEtaInnerRadius := by
    simpa [R, staticContourLocalEtaInnerRadius] using
      (staticContourLocalEtaCanonicalRadius_spec n).2.1
  have hanalyticInner : AnalyticOnNhd ℂ f
      (closedBall 0 staticContourLocalEtaInnerRadius) := by
    exact (analyticOnNhd_staticContourLocalEta_closedBall T).mono
      (closedBall_subset_closedBall
        staticContourLocalEtaInnerRadius_lt_outer.le)
  have hmeromorphicBall : MeromorphicOn f (ball 0 R) :=
    (staticContourLocalEtaCanonicalResidual_decomp n).meromorphicOn.mono_set
      ball_subset_closedBall
  have hdFinite : (Function.support d).Finite := by
    simpa [d, f, R, T] using
      (staticContourLocalEtaCanonicalResidual_decomp n).meromorphicOn
        |>.divisor_ball_support_finite
  have heFinite : (Function.support e).Finite := by
    simpa [e] using
      (divisor f (closedBall 0 staticContourLocalEtaInnerRadius)).finiteSupport
        (isCompact_closedBall 0 staticContourLocalEtaInnerRadius)
  have hpoint : ∀ i, d i ≤ e i := by
    intro i
    by_cases hi : i ∈ ball (0 : ℂ) R
    · have hiInner : i ∈ closedBall (0 : ℂ)
          staticContourLocalEtaInnerRadius := by
        rw [mem_closedBall, dist_zero_right]
        have hiNorm : ‖i‖ < R := by
          simpa [mem_ball, dist_zero_right] using hi
        exact (hiNorm.trans hRlt).le
      dsimp [d, e]
      rw [hmeromorphicBall.divisor_apply hi,
        hanalyticInner.meromorphicOn.divisor_apply hiInner]
    · have hdZero : d i = 0 := by
        dsimp [d]
        change (if MeromorphicOn f (ball 0 R) ∧
            i ∈ ball 0 R then
              (meromorphicOrderAt f i).untop₀ else 0) = 0
        rw [if_neg (fun h => hi h.2)]
      rw [hdZero]
      exact hanalyticInner.divisor_nonneg i
  have hsumInt : (∑ᶠ i, d i) ≤ ∑ᶠ i, e i :=
    finsum_le_finsum' hdFinite heFinite hpoint
  have hsumReal : ((∑ᶠ i, d i : ℤ) : ℝ) ≤
      ((∑ᶠ i, e i : ℤ) : ℝ) := by
    exact_mod_cast hsumInt
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  exact hsumReal.trans (by
    simpa [e, f, T] using
      sum_divisor_staticContourLocalEta_closedBall_le_log hT)

/-- The multiplicity majorant for the selected canonical divisor. -/
def staticContourLocalEtaCanonicalCountMajorant (n : ℕ) : ℝ :=
  staticContourLocalEtaCanonicalLogMajorant n / Real.log (10 / 9 : ℝ)

lemma staticContourLocalEtaCanonicalCountMajorant_nonneg (n : ℕ) :
    0 ≤ staticContourLocalEtaCanonicalCountMajorant n := by
  unfold staticContourLocalEtaCanonicalCountMajorant
  exact div_nonneg (staticContourLocalEtaCanonicalLogMajorant_pos n).le
    (Real.log_pos (by norm_num : (1 : ℝ) < 10 / 9)).le

/-- A common logarithmic upper bound for every canonical factor at the
translated critical endpoint. -/
def staticContourLocalEtaCanonicalFactorLogMajorant (n : ℕ) : ℝ :=
  Real.log (1 + (9 / 4 : ℝ) / spectralBoundarySeparation n)

lemma staticContourLocalEtaCanonicalFactorLogMajorant_pos (n : ℕ) :
    0 < staticContourLocalEtaCanonicalFactorLogMajorant n := by
  apply Real.log_pos
  have hquot : 0 < (9 / 4 : ℝ) / spectralBoundarySeparation n := by
    exact div_pos (by norm_num) (spectralBoundarySeparation_pos n)
  linarith

/-- Translating the safe center by `-1` gives the critical endpoint. -/
@[simp] lemma staticContourLocalEta_neg_one_eq_pairedEtaCore_critical (T : ℝ) :
    staticContourLocalEta T (-1) =
      pairedEtaCore (staticContourCriticalEndpoint T) := by
  unfold staticContourLocalEta staticContourSafeEndpoint
    staticContourCriticalEndpoint
  congr 1
  push_cast
  ring

/-- Paired eta does not vanish at a selected quantitative critical endpoint. -/
lemma pairedEtaCore_critical_quantitative_ne_zero (n : ℕ) :
    pairedEtaCore
        (staticContourCriticalEndpoint
          (quantitativeSpectralBoundaryTruncation n)) ≠ 0 := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let s : ℂ := staticContourCriticalEndpoint T
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have heta := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := s) (by simp [s, staticContourCriticalEndpoint])
    (by simpa [s, staticContourCriticalEndpoint] using hT)
  have hfactorNorm : (1 / 3 : ℝ) ≤
      ‖1 - (2 : ℂ) * (2 : ℂ) ^ (-s)‖ := by
    simpa [s, staticContourCriticalEndpoint] using
      one_third_le_norm_pairedEtaFactor_critical T
  have hfactor : 1 - (2 : ℂ) * (2 : ℂ) ^ (-s) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 3).trans_le hfactorNorm)
  rw [heta]
  exact mul_ne_zero hfactor
    (by simpa [T, s] using
      riemannZeta_staticContourCriticalEndpoint_quantitative_ne_zero n)

/-- The exact canonical decomposition bounds the negative logarithm of paired
eta at a selected critical endpoint by the residual logarithm, center-floor
penalty, local multiplicity count, and zero-separation factor. -/
theorem neg_log_norm_pairedEtaCore_critical_quantitative_le
    (n : ℕ) (hn : 2 ≤ n) :
    -Real.log
        ‖pairedEtaCore
          (staticContourCriticalEndpoint
            (quantitativeSpectralBoundaryTruncation n))‖ ≤
      -Real.log
          (staticContourSafeEtaFactorFloor /
            staticContourSafeZetaDirichletMass) +
        32 * staticContourLocalEtaCanonicalLogMajorant n +
        staticContourLocalEtaCanonicalCountMajorant n *
          staticContourLocalEtaCanonicalFactorLogMajorant n := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  let f : ℂ → ℂ := staticContourLocalEta T
  let g : ℂ → ℂ := staticContourLocalEtaCanonicalResidual n
  let L : ℂ → ℂ := staticContourLocalEtaCanonicalLog n
  let d : ℂ → ℤ := fun i => divisor f (ball 0 R) i
  let M : ℝ := staticContourLocalEtaCanonicalLogMajorant n
  let B : ℝ := staticContourLocalEtaCanonicalCountMajorant n
  let C : ℝ := staticContourLocalEtaCanonicalFactorLogMajorant n
  let c : ℝ := staticContourSafeEtaFactorFloor /
    staticContourSafeZetaDirichletMass
  let z : ℂ := -1
  have hR : 0 < R := by
    simpa [R] using staticContourLocalEtaCanonicalRadius_pos n
  have hRltInner : R < staticContourLocalEtaInnerRadius := by
    simpa [R, staticContourLocalEtaInnerRadius] using
      (staticContourLocalEtaCanonicalRadius_spec n).2.1
  have hzNorm : ‖z‖ = 1 := by simp [z]
  have hzBall : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right, hzNorm]
    simpa [R] using one_lt_staticContourLocalEtaCanonicalRadius n
  have hzClosed : z ∈ closedBall 0 R := ball_subset_closedBall hzBall
  have hcpos : 0 < c := by
    dsimp [c]
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hfzero : f z ≠ 0 := by
    simpa [f, z, T] using pairedEtaCore_critical_quantitative_ne_zero n
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    hRltInner.trans staticContourLocalEtaInnerRadius_lt_outer
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_staticContourLocalEta_closedBall T).mono
      (closedBall_subset_closedBall hRltOuter.le)
  have horder : meromorphicOrderAt f z = 0 :=
    (hanalytic z hzClosed).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfzero
  have hLbound : ‖L z‖ ≤ 32 * M := by
    simpa [L, z, M] using
      norm_staticContourLocalEtaCanonicalLog_neg_one_le n
  have hLre : -(32 * M) ≤ (L z).re := by
    calc
      -(32 * M) ≤ -‖L z‖ := neg_le_neg hLbound
      _ ≤ (L z).re :=
        (abs_le.mp (Complex.abs_re_le_norm (L z))).1
  have hg0 : c ≤ ‖g 0‖ := by
    simpa [c, g] using
      staticContourSafeEtaFactorFloor_div_mass_le_norm_canonicalResidual_zero n
  have hg0pos : 0 < ‖g 0‖ :=
    hcpos.trans_le hg0
  have hlogg0 : Real.log c ≤ Real.log ‖g 0‖ :=
    Real.log_le_log hcpos hg0
  have hnormResidual := congrArg norm
    (exp_staticContourLocalEtaCanonicalLog_mul_zero_eq n hzBall)
  have hnormResidual' :
      Real.exp (L z).re * ‖g 0‖ = ‖g z‖ := by
    simpa [L, g, norm_mul, Complex.norm_exp] using hnormResidual
  have hlogResidualEq :
      Real.log ‖g z‖ = (L z).re + Real.log ‖g 0‖ := by
    rw [← hnormResidual', Real.log_mul (Real.exp_ne_zero _) hg0pos.ne',
      Real.log_exp]
  have hlogResidual : Real.log c - 32 * M ≤ Real.log ‖g z‖ := by
    rw [hlogResidualEq]
    linarith
  have hdFinite : (Function.support d).Finite := by
    simpa [d, f, R, T] using
      (staticContourLocalEtaCanonicalResidual_decomp n).meromorphicOn
        |>.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    dsimp [d]
    exact (hanalytic.mono ball_subset_closedBall).divisor_nonneg i
  have hC : 0 ≤ C := by
    simpa [C] using
      (staticContourLocalEtaCanonicalFactorLogMajorant_pos n).le
  have hfactorLog : ∀ i, d i ≠ 0 →
      Real.log ‖Complex.canonicalFactor R i z‖ ≤ C := by
    intro i hi
    have hiBall : i ∈ ball 0 R :=
      (divisor f (ball 0 R)).supportWithinDomain (by simpa [d] using hi)
    have hiInner : i ∈ ball (0 : ℂ) staticContourLocalEtaInnerRadius := by
      rw [mem_ball, dist_zero_right]
      have hiNorm : ‖i‖ < R := by
        simpa [mem_ball, dist_zero_right] using hiBall
      exact hiNorm.trans hRltInner
    have hmeromorphicBall : MeromorphicOn f (ball 0 R) :=
      hanalytic.meromorphicOn.mono_set ball_subset_closedBall
    have hanalyticInner : AnalyticOnNhd ℂ f
        (ball 0 staticContourLocalEtaInnerRadius) :=
      (analyticOnNhd_staticContourLocalEta_closedBall T).mono
        (fun w hw => ball_subset_closedBall
          ((ball_subset_ball staticContourLocalEtaInnerRadius_lt_outer.le) hw))
    have hiInnerDivisor :
        divisor f (ball 0 staticContourLocalEtaInnerRadius) i ≠ 0 := by
      have heq : divisor f (ball 0 R) i =
          divisor f (ball 0 staticContourLocalEtaInnerRadius) i := by
        rw [hmeromorphicBall.divisor_apply hiBall,
          hanalyticInner.meromorphicOn.divisor_apply hiInner]
      intro hzero
      apply hi
      dsimp [d]
      rw [heq, hzero]
    have hsep : spectralBoundarySeparation n ≤ ‖z - i‖ := by
      simpa [f, T, z] using
        spectralBoundarySeparation_le_norm_criticalLocal_sub_of_etaDivisor
          hn hiInnerDivisor
    have hzNormLe : ‖z‖ ≤ R := by
      rw [hzNorm]
      exact (one_lt_staticContourLocalEtaCanonicalRadius n).le
    have hfactor := norm_canonicalFactor_le_of_closedBall_of_separated
      (i := i) (z := z) hR (spectralBoundarySeparation_pos n)
        hiBall hzNormLe hsep
    have hRupper : 2 * R ≤ 9 / 4 := by
      have := (staticContourLocalEtaCanonicalRadius_spec n).2.1
      dsimp [R]
      linarith
    have hquotNonneg :
        0 ≤ (9 / 4 : ℝ) / spectralBoundarySeparation n := by
      exact div_nonneg (by norm_num) (spectralBoundarySeparation_pos n).le
    have hfactorBound :
        ‖Complex.canonicalFactor R i z‖ ≤
          1 + (9 / 4 : ℝ) / spectralBoundarySeparation n := by
      calc
        ‖Complex.canonicalFactor R i z‖ ≤
            2 * R / spectralBoundarySeparation n := hfactor
        _ ≤ (9 / 4 : ℝ) / spectralBoundarySeparation n :=
          div_le_div_of_nonneg_right hRupper
            (spectralBoundarySeparation_pos n).le
        _ ≤ 1 + (9 / 4 : ℝ) / spectralBoundarySeparation n := by linarith
    have hzi : z ≠ i := by
      intro hzi
      subst i
      simpa using
        (spectralBoundarySeparation_pos n |>.trans_le hsep).ne'
    have hfactorPos : 0 < ‖Complex.canonicalFactor R i z‖ :=
      norm_pos_iff.mpr
        (Complex.canonicalFactor_ne_zero hiBall hzClosed hzi)
    apply Real.log_le_log hfactorPos
    simpa [C, staticContourLocalEtaCanonicalFactorLogMajorant] using
      hfactorBound
  have hcanonicalRaw := finsum_intCast_mul_le_of_nonneg
    hdFinite hdnonneg hfactorLog
  have hcount : ((∑ᶠ i, d i : ℤ) : ℝ) ≤ B := by
    simpa [d, f, R, T, B, staticContourLocalEtaCanonicalCountMajorant,
      staticContourLocalEtaCanonicalLogMajorant] using
        sum_divisor_staticContourLocalEta_canonicalBall_le_log n
  have hcanonical :
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) ≤ B * C := by
    calc
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) ≤
        ((∑ᶠ i, d i : ℤ) : ℝ) * C := hcanonicalRaw
      _ ≤ B * C := mul_le_mul_of_nonneg_right hcount hC
  have hdecomp := (staticContourLocalEtaCanonicalResidual_decomp n).log_norm_eq
    hzClosed horder hR
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor f (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor f (sphere 0 R) = 0 by
      simpa [f, T, R] using
        divisor_staticContourLocalEta_sphere_canonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt f z = f z :=
    (hanalytic z hzClosed).meromorphicTrailingCoeffAt_of_ne_zero hfzero
  change Real.log ‖g z‖ = _ at hdecomp
  rw [hsphereSum, htrailing] at hdecomp
  simp only [sub_zero] at hdecomp
  have hlogEta : Real.log ‖f z‖ =
      Real.log ‖g z‖ -
        (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) := by
    change Real.log ‖g z‖ =
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) +
          Real.log ‖f z‖ at hdecomp
    linarith
  rw [show pairedEtaCore (staticContourCriticalEndpoint T) = f z by
    simp [f, z],
    hlogEta]
  linarith

end

end RiemannGaussian
