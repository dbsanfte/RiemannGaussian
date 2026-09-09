/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaAdaptiveCanonical
import RiemannGaussian.ZetaCanonicalSign
import RiemannGaussian.ZetaSignedExactPole

/-!
# Signed canonical zero constraints throughout the right half of the strip

An adaptive local disc retains the complete canonical response. Each
negative response is paid by its own Jensen weight, whose full sum has
uniform logarithmic control. The source of a selected actual zero is
therefore retained without an unweighted count near the disc boundary.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

variable (r : Set.Ico (3 / 4 : ℝ) 1)

/-- A nonzero local analytic divisor coefficient is an actual zero of
the pole-removed zeta function. -/
theorem adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i ≠ 0) :
    localZetaPoleRemoved y i = 0 := by
  by_contra hne
  have han := (analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).mono ball_subset_closedBall
  have himem := (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain hi
  have ho : meromorphicOrderAt (localZetaPoleRemoved y) i = 0 :=
    (han i himem).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hne
  apply hi
  rw [han.meromorphicOn.divisor_apply himem, ho]
  rfl

/-- Exact logarithmic differentiation retains every local zero with
its full divisor multiplicity and the actual analytic residual. -/
theorem logDeriv_adaptiveZetaPoleRemoved_eq_residual_sub_canonical_sum
    (y : ℝ) {z : ℂ} (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y))
    (hf : localZetaPoleRemoved y z ≠ 0) :
    logDeriv (localZetaPoleRemoved y) z =
      logDeriv (adaptiveZetaCanonicalResidual r y) z -
        ∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i •
          logDeriv (Complex.canonicalFactor (adaptiveZetaCanonicalRadius r y) i) z := by
  let f := localZetaPoleRemoved y
  let R := adaptiveZetaCanonicalRadius r y
  let d : ℂ → ℤ := fun i ↦ divisor f (ball 0 R) i
  let P : ℂ → ℂ := ∏ᶠ i, Complex.canonicalFactor R i ^ d i
  let g := adaptiveZetaCanonicalResidual r y
  have hR : 0 < R := adaptiveZetaCanonicalRadius_pos r y
  have hdFinite : (Function.support d).Finite :=
    (adaptiveZetaCanonicalResidual_decomp r y).meromorphicOn.divisor_ball_support_finite
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
    exact hf (adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r y hi)
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
    have heq := (adaptiveZetaCanonicalResidual_decomp r y)
      |>.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        (ball_subset_closedBall hw) horder hR
    have htrailing : meromorphicTrailingCoeffAt (localZetaPoleRemoved y) w = f w :=
      han.meromorphicTrailingCoeffAt_of_ne_zero hwf
    change g w = (P * f) w
    simpa [P, d, g, R, divisor_adaptiveZetaPoleRemoved_sphere_eq_zero r y,
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


/-- Every actual divisor point remains to the left of the safe evaluation
half-plane, independently of the adaptive radius. -/
theorem adaptiveZetaDivisor_re_lt_neg_half (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i ≠ 0) :
    i.re < -(1 / 2 : ℝ) := by
  have hf := adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r y hi
  by_contra h
  have hs : 1 ≤ (3 / 2 + I * (y : ℂ) + i).re := by simp; linarith
  exact riemannZeta₁_ne_zero_of_one_le_re hs hf

/-- No local zero divisor point coincides with the nonvanishing safe center. -/
theorem adaptiveZetaDivisor_point_ne_zero (y : ℝ) {i : ℂ}
    (hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i ≠ 0) :
    i ≠ 0 := by
  intro he
  subst i
  exact localZetaPoleRemoved_zero_ne_zero y
    (adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r y hi)

/-- The full complex canonical response of the actual local divisor. -/
def adaptiveZetaCanonicalResponse (y : ℝ) (z : ℂ) : ℂ :=
  ∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i •
    zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z

/-- The exact local logarithmic derivative retains each pole together
with its own regular correction before any estimate is applied. -/
theorem logDeriv_adaptiveZetaPoleRemoved_eq_residual_add_response (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y)) (hf : localZetaPoleRemoved y z ≠ 0) :
    logDeriv (localZetaPoleRemoved y) z =
      logDeriv (adaptiveZetaCanonicalResidual r y) z + adaptiveZetaCanonicalResponse r y z := by
  have hsum : (∑ᶠ i, divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i •
      logDeriv (Complex.canonicalFactor (adaptiveZetaCanonicalRadius r y) i) z) =
      -adaptiveZetaCanonicalResponse r y z := by
    rw [adaptiveZetaCanonicalResponse, ← finsum_neg_distrib]
    apply finsum_congr
    intro i
    by_cases hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i = 0
    · simp [hi]
    · have himem := (divisor (localZetaPoleRemoved y)
        (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain hi
      have hzi : z ≠ i := by
        intro he
        subst i
        exact hf (adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r y hi)
      rw [logDeriv_canonicalFactor_eq (adaptiveZetaCanonicalRadius_pos r y) himem
        (ball_subset_closedBall hz) hzi]
      simp only [zetaCanonicalZeroResponse, zsmul_eq_mul]
      ring
  rw [logDeriv_adaptiveZetaPoleRemoved_eq_residual_sub_canonical_sum r y hz hf, hsum, sub_neg_eq_add]

/-- Taking real parts preserves the full multiplicity-weighted response. -/
theorem adaptiveZetaCanonicalResponse_re_eq (y : ℝ) (z : ℂ) :
    (adaptiveZetaCanonicalResponse r y z).re =
      ∑ᶠ i, (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
        (zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z).re := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i
  have hd : (Function.support d).Finite :=
    (adaptiveZetaCanonicalResidual_decomp r y).meromorphicOn.divisor_ball_support_finite
  have ht : (fun i ↦ d i • zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z).HasFiniteSupport :=
    hd.subset (by intro i hi hdi; exact hi (by simp [hdi]))
  change Complex.reAddGroupHom (∑ᶠ i, d i • _) = _
  rw [map_finsum Complex.reAddGroupHom ht]
  apply finsum_congr
  intro i
  simp [d, zsmul_eq_mul]

/-- Each actual canonical term is nonnegative after paying only its own
Jensen boundary weight. All ordinates and multiplicities remain explicit. -/
theorem adaptiveZetaCanonical_compensated_term_nonneg (y : ℝ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (i : ℂ) :
    0 ≤ (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
      ((zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i ((x - 1 / 2 : ℝ) : ℂ)).re +
        32 * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)) := by
  by_cases hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i = 0
  · simp [hi]
  · apply mul_nonneg
    · exact_mod_cast ((analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).mono
        ball_subset_closedBall).divisor_nonneg i
    · apply zetaCanonicalZeroResponse_re_add_log_nonneg
      · linarith [(adaptiveZetaCanonicalRadius_spec r y).1, r.property.1]
      · exact (adaptiveZetaCanonicalRadius_spec r y).2.1.le
      · simpa only [mem_ball, dist_zero_right] using
          (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain hi
      · exact adaptiveZetaDivisor_point_ne_zero r y hi
      · exact abs_le.mpr ⟨by linarith, by linarith⟩
      · linarith [adaptiveZetaDivisor_re_lt_neg_half r y hi]

/-- The complete compensated real response is an exact sum of
nonnegative terms; no absolute-value bound is applied to its selected source. -/
theorem adaptiveZetaCanonical_compensated_sum_eq (y : ℝ) (z : ℂ) :
    (adaptiveZetaCanonicalResponse r y z).re + 32 * adaptiveZetaJensenWeight r y =
      ∑ᶠ i, (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
        ((zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z).re +
          32 * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)) := by
  let d : ℂ → ℤ := fun i ↦ divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i
  have hd : (Function.support d).Finite :=
    (adaptiveZetaCanonicalResidual_decomp r y).meromorphicOn.divisor_ball_support_finite
  have hc : (fun i ↦ (d i : ℝ) * (zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i z).re).HasFiniteSupport :=
    hd.subset (by intro i hi hdi; exact hi (by simp [hdi]))
  have hm : (32 : ℝ) * (∑ᶠ i, (d i : ℝ) * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)) =
      ∑ᶠ i, 32 * ((d i : ℝ) * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)) := by
    simpa only [smul_eq_mul] using
      (smul_finsum (32 : ℝ) (fun i ↦ (d i : ℝ) * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)))
  have hl32 : (fun i ↦ (32 : ℝ) * ((d i : ℝ) * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖))).HasFiniteSupport :=
    hd.subset (by intro i hi hdi; exact hi (by simp [hdi]))
  rw [adaptiveZetaCanonicalResponse_re_eq, adaptiveZetaJensenWeight, hm]
  rw [← finsum_add_distrib hc hl32]
  apply finsum_congr
  intro i
  dsimp only [d]
  ring

/-- Each retained zero term is bounded by the complete response plus the
uniform Jensen compensation. This allows a selected source to survive even
when other canonical terms have a negative sign. -/
theorem adaptiveZetaCanonical_term_le_compensated_sum (y : ℝ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (i : ℂ) :
    (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
      ((zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i ((x - 1 / 2 : ℝ) : ℂ)).re +
        32 * Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)) ≤
      (adaptiveZetaCanonicalResponse r y ((x - 1 / 2 : ℝ) : ℂ)).re + 32 * adaptiveZetaJensenWeight r y := by
  rw [adaptiveZetaCanonical_compensated_sum_eq]
  apply single_le_finsum i _ (adaptiveZetaCanonical_compensated_term_nonneg r y hx hx1)
  apply (adaptiveZetaCanonicalResidual_decomp r y).meromorphicOn.divisor_ball_support_finite.subset
  intro j hj hdj
  exact hj (by simp [hdj])

/-- The literal zeta logarithmic derivative is reconstructed from the
entire adaptive response and residual. The shift now ranges up to one. -/
theorem neg_logDeriv_riemannZeta_eq_adaptive (y : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y) =
      1 / ((x : ℂ) + I * y) - logDeriv (adaptiveZetaCanonicalResidual r y) ((x - 1 / 2 : ℝ) : ℂ) -
        adaptiveZetaCanonicalResponse r y ((x - 1 / 2 : ℝ) : ℂ) := by
  let s : ℂ := ((1 + x : ℝ) : ℂ) + I * y
  let z : ℂ := ((x - 1 / 2 : ℝ) : ℂ)
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have he : 3 / 2 + I * (y : ℂ) + z = s := by dsimp [z, s]; push_cast; ring
  have hnorm : ‖z‖ ≤ 1 / 2 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmem : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y) := by
    rw [mem_ball, dist_zero_right]
    linarith [(adaptiveZetaCanonicalRadius_spec r y).1, r.property.1]
  have hf : localZetaPoleRemoved y z ≠ 0 := by
    rw [localZetaPoleRemoved, he]
    exact riemannZeta₁_ne_zero_of_one_le_re hs.le
  have hlog : logDeriv riemannZeta₁ s =
      logDeriv (adaptiveZetaCanonicalResidual r y) z + adaptiveZetaCanonicalResponse r y z := by
    rw [← he, ← logDeriv_localZetaPoleRemoved_eq]
    exact logDeriv_adaptiveZetaPoleRemoved_eq_residual_add_response r y hmem hf
  have hp : s - 1 = (x : ℂ) + I * y := by dsimp [s]; push_cast; ring
  change -logDeriv riemannZeta s = _
  rw [neg_logDeriv_riemannZeta_eq_pole_sub hs1 (riemannZeta_ne_zero_of_one_le_re hs.le), hlog, hp]
  ring

/-- Only the analytic residual is bounded in the full signed response
inequality. Its uniform constant does not depend on the adaptive radius. -/
theorem neg_logDeriv_add_adaptiveResponse_le (y : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re +
      (adaptiveZetaCanonicalResponse r y ((x - 1 / 2 : ℝ) : ℂ)).re ≤
        x / (x ^ 2 + y ^ 2) + 320 * localZetaLogHeight y := by
  have hn : ‖((x - 1 / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hrem := norm_logDeriv_adaptiveZetaCanonicalResidual_le r y hn
  rw [neg_logDeriv_riemannZeta_eq_adaptive r y hx hx1, Complex.sub_re, Complex.sub_re, zetaPole_real_part]
  linarith [(abs_le.mp (Complex.abs_re_le_norm
    (logDeriv (adaptiveZetaCanonicalResidual r y) ((x - 1 / 2 : ℝ) : ℂ)))).1]

/-- The complete negative canonical contribution has a uniform height
allowance, even for discs reaching arbitrarily close to the critical line. -/
theorem adaptiveZetaCanonicalResponse_re_lower (y : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -(128 : ℝ) * localZetaLogHeight y ≤
      (adaptiveZetaCanonicalResponse r y ((x - 1 / 2 : ℝ) : ℂ)).re := by
  have h : 0 ≤ (adaptiveZetaCanonicalResponse r y ((x - 1 / 2 : ℝ) : ℂ)).re +
      32 * adaptiveZetaJensenWeight r y := by
    rw [adaptiveZetaCanonical_compensated_sum_eq]
    exact finsum_nonneg (adaptiveZetaCanonical_compensated_term_nonneg r y hx hx1)
  linarith [adaptiveZetaJensenWeight_le r y]

/-- The unconditional exact-pole upper bound extends through the full
shift interval `0 < x <= 1`. -/
theorem neg_logDeriv_re_le_adaptive_exactPole (y : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re ≤
      x / (x ^ 2 + y ^ 2) + 448 * localZetaLogHeight y := by
  let r : Set.Ico (3 / 4 : ℝ) 1 := ⟨3 / 4, by constructor <;> norm_num⟩
  linarith [neg_logDeriv_add_adaptiveResponse_le r y hx hx1,
    adaptiveZetaCanonicalResponse_re_lower r y hx hx1]

/-- A selected zero's complete canonical source survives the signed
bound; only the remaining boundary-weighted error is paid. -/
theorem neg_logDeriv_add_adaptive_divisor_source_le (y : ℝ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (i : ℂ) :
    (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * y)).re +
      (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
        (zetaCanonicalZeroResponse (adaptiveZetaCanonicalRadius r y) i ((x - 1 / 2 : ℝ) : ℂ)).re ≤
      x / (x ^ 2 + y ^ 2) + 448 * localZetaLogHeight y := by
  have h := adaptiveZetaCanonical_term_le_compensated_sum r y hx hx1 i
  have hl : 0 ≤ (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
      Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖) := by
    by_cases hi : divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i = 0
    · simp [hi]
    · apply mul_nonneg
      · exact_mod_cast ((analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).mono
          ball_subset_closedBall).divisor_nonneg i
      · apply Real.log_nonneg
        apply (one_le_div (norm_pos_iff.mpr (adaptiveZetaDivisor_point_ne_zero r y hi))).mpr
        exact (show ‖i‖ < adaptiveZetaCanonicalRadius r y by
          simpa only [mem_ball, dist_zero_right] using
            (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain hi).le
  linarith [neg_logDeriv_add_adaptiveResponse_le r y hx hx1, adaptiveZetaJensenWeight_le r y]

end

end RiemannGaussian
