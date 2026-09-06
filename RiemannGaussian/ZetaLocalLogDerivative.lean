import RiemannGaussian.ZetaLocalJensen

/-!
# Exact local logarithmic derivative with the complete zero divisor

The zero-free residual and every enclosed canonical factor reconstruct the
actual logarithmic derivative. The subsequent signed estimates can retain
each pole contribution and bound only the analytic remainder.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A nonzero local analytic divisor coefficient is an actual zero of
the pole-removed zeta function. -/
theorem localZetaPoleRemoved_eq_zero_of_divisor_ne_zero (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i ≠ 0) :
    localZetaPoleRemoved y i = 0 := by
  by_contra hne
  have han := (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall
  have himem := (divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y))).supportWithinDomain hi
  have ho : meromorphicOrderAt (localZetaPoleRemoved y) i = 0 :=
    (han i himem).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hne
  apply hi
  rw [han.meromorphicOn.divisor_apply himem, ho]
  rfl

/-- Exact logarithmic differentiation retains every local zero with
its full divisor multiplicity and the actual analytic residual. -/
theorem logDeriv_localZetaPoleRemoved_eq_residual_sub_canonical_sum
    (y : ℝ) {z : ℂ} (hz : z ∈ ball 0 (localZetaCanonicalRadius y))
    (hf : localZetaPoleRemoved y z ≠ 0) :
    logDeriv (localZetaPoleRemoved y) z =
      logDeriv (localZetaCanonicalResidual y) z -
        ∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i •
          logDeriv (Complex.canonicalFactor (localZetaCanonicalRadius y) i) z := by
  let f := localZetaPoleRemoved y
  let R := localZetaCanonicalRadius y
  let d : ℂ → ℤ := fun i ↦ divisor f (ball 0 R) i
  let P : ℂ → ℂ := ∏ᶠ i, Complex.canonicalFactor R i ^ d i
  let g := localZetaCanonicalResidual y
  have hR : 0 < R := localZetaCanonicalRadius_pos y
  have hdFinite : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have hmulSupport : (fun i ↦ Complex.canonicalFactor R i ^ d i).HasFiniteMulSupport := by
    apply Set.Finite.subset hdFinite
    intro i hi
    by_contra hdi
    have hdi0 : d i = 0 := by simpa [Function.mem_support] using hdi
    simp [hdi0] at hi
  have himem {i : ℂ} (hi : d i ≠ 0) : i ∈ ball (0 : ℂ) R :=
    (divisor f (ball 0 R)).supportWithinDomain hi
  have hzi {i : ℂ} (hi : d i ≠ 0) : z ≠ i := by
    intro h
    subst i
    exact hf (localZetaPoleRemoved_eq_zero_of_divisor_ne_zero y hi)
  have hfactorNe {i : ℂ} (hi : d i ≠ 0) : Complex.canonicalFactor R i z ≠ 0 :=
    Complex.canonicalFactor_ne_zero (himem hi) (ball_subset_closedBall hz) (hzi hi)
  have hfactorDiff {i : ℂ} (hi : d i ≠ 0) : DifferentiableAt ℂ (Complex.canonicalFactor R i) z :=
    (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).differentiableAt
  have hPAnalytic : AnalyticAt ℂ P z := by
    dsimp [P]
    apply analyticAt_finprod
    intro i
    by_cases hi : d i = 0
    · rw [hi]
      change AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z
      exact analyticAt_const
    · exact (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).zpow (hfactorNe hi)
  have hPne : P z ≠ 0 := by
    dsimp [P]
    apply finprod_apply_ne_zero
    intro i
    by_cases hi : d i = 0
    · simp [hi]
    · exact zpow_ne_zero _ (hfactorNe hi)
  have hfactorEq : g =ᶠ[nhds z] P * f := by
    have hball : ball (0 : ℂ) R ∈ nhds z := isOpen_ball.mem_nhds hz
    have hfNe : ∀ᶠ w in nhds z, f w ≠ 0 :=
      ((differentiable_localZetaPoleRemoved y).analyticAt z).continuousAt.eventually_ne hf
    filter_upwards [hball, hfNe] with w hw hwf
    have han : AnalyticAt ℂ f w := (differentiable_localZetaPoleRemoved y).analyticAt w
    have horder : meromorphicOrderAt f w = 0 :=
      han.meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hwf
    have heq := (localZetaCanonicalResidual_decomp y)
      |>.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        (ball_subset_closedBall hw) horder hR
    have htrailing : meromorphicTrailingCoeffAt (localZetaPoleRemoved y) w = f w :=
      han.meromorphicTrailingCoeffAt_of_ne_zero hwf
    change g w = (P * f) w
    simpa [P, d, g, R, divisor_localZetaPoleRemoved_sphere_eq_zero y,
      htrailing, finprod_apply hmulSupport] using heq
  have hproductLog : logDeriv P z = ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z := by
    dsimp [P]
    exact logDeriv_finprod_zpow_apply_of_finite hdFinite
      (fun i hi ↦ hfactorNe hi) (fun i hi ↦ hfactorDiff hi)
  have hmul := logDeriv_mul (f := P) (g := f) z hPne hf
    hPAnalytic.differentiableAt (differentiable_localZetaPoleRemoved y z)
  have hlog : logDeriv g z = logDeriv P z + logDeriv f z := by
    rw [(logDeriv_congr_nhds hfactorEq).self_of_nhds]
    exact hmul
  rw [hproductLog] at hlog
  change logDeriv f z = logDeriv g z - ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z
  rw [hlog]
  ring

/-- The complete signed pole sum, retaining every local analytic
multiplicity before taking real parts. -/
def localZetaPoleSum (y : ℝ) (z : ℂ) : ℂ :=
  ∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i • (1 / (z - i))

/-- The regular part of the complete canonical factor sum. -/
def localZetaRegularSum (y : ℝ) (z : ℂ) : ℂ :=
  ∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y)) i •
    (starRingEnd ℂ i / ((localZetaCanonicalRadius y : ℂ) ^ 2 - starRingEnd ℂ i * z))

/-- The actual analytic remainder after separating the full signed
local pole sum. -/
def localZetaLogRemainder (y : ℝ) (z : ℂ) : ℂ :=
  logDeriv (localZetaCanonicalResidual y) z + localZetaRegularSum y z

/-- The complete local logarithmic derivative is its signed pole sum
plus the actual residual and canonical regular terms. -/
theorem logDeriv_localZetaPoleRemoved_eq_remainder_add_poleSum (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (localZetaCanonicalRadius y)) (hf : localZetaPoleRemoved y z ≠ 0) :
    logDeriv (localZetaPoleRemoved y) z = localZetaLogRemainder y z + localZetaPoleSum y z := by
  let R := localZetaCanonicalRadius y
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 R) i
  let B : ℂ → ℂ := fun i ↦ starRingEnd ℂ i / ((R : ℂ) ^ 2 - starRingEnd ℂ i * z)
  let P : ℂ → ℂ := fun i ↦ 1 / (z - i)
  have hd : (Function.support d).Finite :=
    (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have hB : (fun i ↦ d i • B i).HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [hdi]))
  have hP : (fun i ↦ d i • P i).HasFiniteSupport := hd.subset (by
    intro i hi hdi
    exact hi (by simp [hdi]))
  have he : ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z =
      -(localZetaRegularSum y z + localZetaPoleSum y z) := by
    calc
      _ = ∑ᶠ i, -(d i • B i + d i • P i) := by
        apply finsum_congr
        intro i
        by_cases hi : d i = 0
        · simp [hi]
        · have himem := (divisor (localZetaPoleRemoved y) (ball 0 R)).supportWithinDomain hi
          have hzi : z ≠ i := by
            intro h
            subst i
            exact hf (localZetaPoleRemoved_eq_zero_of_divisor_ne_zero y hi)
          rw [logDeriv_canonicalFactor_eq (localZetaCanonicalRadius_pos y) himem
            (ball_subset_closedBall hz) hzi]
          simp only [B, P, zsmul_eq_mul, neg_div]
          ring
      _ = _ := by rw [finsum_neg_distrib, finsum_add_distrib hB hP]; rfl
  rw [logDeriv_localZetaPoleRemoved_eq_residual_sub_canonical_sum y hz hf]
  change logDeriv (localZetaCanonicalResidual y) z -
      (∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z) = _
  rw [he]
  unfold localZetaLogRemainder
  ring

/-- Each canonical regular term is uniformly bounded on the inner
half-disc; no pole-distance estimate is used. -/
theorem norm_localZetaCanonicalRegularTerm_le (y : ℝ) {i z : ℂ}
    (hi : i ∈ ball 0 (localZetaCanonicalRadius y)) (hz : ‖z‖ ≤ 1 / 2) :
    ‖starRingEnd ℂ i / ((localZetaCanonicalRadius y : ℂ) ^ 2 - starRingEnd ℂ i * z)‖ ≤ 4 := by
  let R := localZetaCanonicalRadius y
  have hR : 3 / 4 < R := (localZetaCanonicalRadius_spec y).1
  have hRp : 0 < R := localZetaCanonicalRadius_pos y
  have hiNorm : ‖i‖ ≤ R := (show ‖i‖ < R by simpa only [mem_ball, dist_zero_right] using hi).le
  have hstar : ‖starRingEnd ℂ i‖ = ‖i‖ := norm_star i
  have hprod : ‖starRingEnd ℂ i * z‖ ≤ R * ‖z‖ := by
    rw [norm_mul, hstar]
    exact mul_le_mul_of_nonneg_right hiNorm (norm_nonneg _)
  have hden : R * (R - ‖z‖) ≤ ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ := by
    calc
      _ ≤ R ^ 2 - ‖starRingEnd ℂ i * z‖ := by nlinarith
      _ = ‖(R : ℂ) ^ 2‖ - ‖starRingEnd ℂ i * z‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp]
      _ ≤ _ := norm_sub_norm_le _ _
  have hdenpos : 0 < ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ :=
    (mul_pos hRp (by linarith)).trans_le hden
  rw [norm_div, hstar, div_le_iff₀ hdenpos]
  nlinarith

/-- Jensen's complete multiplicity count bounds the actual regular
canonical sum by logarithmic height. -/
theorem norm_localZetaRegularSum_le (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖localZetaRegularSum y z‖ ≤ 128 * localZetaLogHeight y := by
  have hd := (localZetaCanonicalResidual_decomp y).meromorphicOn.divisor_ball_support_finite
  have han := (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).mono ball_subset_closedBall
  have h := norm_finsum_zsmul_le_of_nonneg hd han.divisor_nonneg (C := 4) (by
    intro i hi
    exact norm_localZetaCanonicalRegularTerm_le y
      ((divisor (localZetaPoleRemoved y) (ball 0 (localZetaCanonicalRadius y))).supportWithinDomain hi) hz)
  apply h.trans
  nlinarith [sum_divisor_localZetaPoleRemoved_canonicalBall_le y]

/-- The complete local remainder has an explicit logarithmic bound
after every singular zero contribution has been kept in the pole sum. -/
theorem norm_localZetaLogRemainder_le (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖localZetaLogRemainder y z‖ ≤ 448 * localZetaLogHeight y := by
  exact (norm_add_le _ _).trans ((add_le_add (norm_logDeriv_localZetaCanonicalResidual_le y hz)
    (norm_localZetaRegularSum_le y hz)).trans_eq (by ring))

end

end RiemannGaussian
