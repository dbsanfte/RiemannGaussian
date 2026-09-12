/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDiscCanonicalBounds

/-!
# Signed canonical zero contributions at the disc center

Each reciprocal-distance pole stays coupled to its canonical regular
correction. Their real part is a Cauchy kernel times the nonnegative
factor `1 - normSq(a) / R^2`. Zeros to the left of the center therefore
keep one common sign, without a separate bound on the zero count.
The full complex divisor identity is retained before taking real parts.
-/

namespace RiemannGaussian.AnalyticDiscSignedDerivative
noncomputable section
open Complex Filter MeromorphicOn Metric Set Topology AnalyticDiscCanonicalBounds
open scoped Classical ComplexConjugate

/-- The full pole and canonical correction at the disc center. -/
def kernel (R : ℝ) (a : ℂ) : ℂ := -1 / a + conj a / (R : ℂ) ^ 2

/-- The exact canonical factor derivative retains both complex terms. -/
theorem factor_center (hR : 0 < R) {a : ℂ} (ha : a ∈ ball 0 R) (ha0 : a ≠ 0) :
    logDeriv (Complex.canonicalFactor R a) 0 = -kernel R a := by
  rw [logDeriv_canonicalFactor_eq hR ha (mem_closedBall_self hR.le) ha0.symm]
  simp only [mul_zero, sub_zero, zero_sub, div_neg, neg_div, kernel]
  ring

/-- A nonzero analytic divisor coefficient is an actual zero. -/
theorem zero_of_divisor_ne_zero {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {a : ℂ}
    (ha : divisor f (ball 0 R) a ≠ 0) : f a = 0 := by
  by_contra hne
  have han := hf.mono ball_subset_closedBall
  have hm := (divisor f (ball 0 R)).supportWithinDomain ha
  have ho : meromorphicOrderAt f a = 0 :=
    (han a hm).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hne
  apply ha
  rw [han.meromorphicOn.divisor_apply hm, ho]
  rfl

/-- The exact complex center derivative is the analytic residual plus
the complete multiplicity-weighted coupled divisor sum. -/
theorem logDeriv_center_eq {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hs : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0) (D : ECanonicalDecomp f g R) :
    logDeriv f 0 = logDeriv g 0 + ∑ᶠ a, divisor f (ball 0 R) a • kernel R a := by
  let d : ℂ → ℤ := fun a ↦ divisor f (ball 0 R) a
  let P : ℂ → ℂ := ∏ᶠ a, Complex.canonicalFactor R a ^ d a
  have hd : (Function.support d).Finite := D.meromorphicOn.divisor_ball_support_finite
  have hmul : (fun a ↦ Complex.canonicalFactor R a ^ d a).HasFiniteMulSupport :=
    hd.subset (by
      intro a ha
      contrapose! ha
      simp only [Function.mem_support, ne_eq, not_not] at ha
      simp [ha])
  have ha_mem {a : ℂ} (ha : d a ≠ 0) : a ∈ ball (0 : ℂ) R :=
    (divisor f (ball 0 R)).supportWithinDomain ha
  have ha0 {a : ℂ} (ha : d a ≠ 0) : a ≠ 0 := by
    intro he
    subst a
    exact hf0 (zero_of_divisor_ne_zero hf ha)
  have hfactor_ne {a : ℂ} (ha : d a ≠ 0) : Complex.canonicalFactor R a 0 ≠ 0 :=
    Complex.canonicalFactor_ne_zero (ha_mem ha) (mem_closedBall_self hR.le) (ha0 ha).symm
  have hfactor_diff {a : ℂ} (ha : d a ≠ 0) :
      DifferentiableAt ℂ (Complex.canonicalFactor R a) 0 :=
    (Complex.analyticOnNhd_canonicalFactor R a 0 (ha0 ha).symm).differentiableAt
  have hP : AnalyticAt ℂ P 0 := by
    dsimp [P]
    apply analyticAt_finprod
    intro a
    by_cases ha : d a = 0
    · rw [ha]
      change AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) 0
      exact analyticAt_const
    · exact (Complex.analyticOnNhd_canonicalFactor R a 0 (ha0 ha).symm).zpow (hfactor_ne ha)
  have hP0 : P 0 ≠ 0 := by
    dsimp [P]
    apply finprod_apply_ne_zero
    intro a
    by_cases ha : d a = 0
    · simp [ha]
    · exact zpow_ne_zero _ (hfactor_ne ha)
  have hfactorEq : g =ᶠ[nhds 0] P * f := by
    have hball : ball (0 : ℂ) R ∈ nhds 0 := isOpen_ball.mem_nhds (mem_ball_self hR)
    have hfNe : ∀ᶠ w in nhds 0, f w ≠ 0 :=
      (hf 0 (mem_closedBall_self hR.le)).continuousAt.eventually_ne hf0
    filter_upwards [hball, hfNe] with w hw hwf
    have han := hf w (ball_subset_closedBall hw)
    have ho : meromorphicOrderAt f w = 0 :=
      han.meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hwf
    have he := D.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
      (ball_subset_closedBall hw) ho hR
    change g w = (P * f) w
    simpa [P, d, divisor_sphere_eq_zero hf hs,
      han.meromorphicTrailingCoeffAt_of_ne_zero hwf, finprod_apply hmul] using he
  have hproduct : logDeriv P 0 = ∑ᶠ a, d a • logDeriv (Complex.canonicalFactor R a) 0 := by
    dsimp [P]
    exact logDeriv_finprod_zpow_apply_of_finite hd
      (fun a ha ↦ hfactor_ne ha) (fun a ha ↦ hfactor_diff ha)
  have hlog : logDeriv g 0 = logDeriv P 0 + logDeriv f 0 := by
    rw [(logDeriv_congr_nhds hfactorEq).self_of_nhds]
    exact logDeriv_mul (f := P) (g := f) 0 hP0 hf0 hP.differentiableAt
      (hf 0 (mem_closedBall_self hR.le)).differentiableAt
  have he : (∑ᶠ a, d a • logDeriv (Complex.canonicalFactor R a) 0) =
      -(∑ᶠ a, d a • kernel R a) := by
    rw [← finsum_neg_distrib]
    apply finsum_congr
    intro a
    by_cases ha : d a = 0
    · simp [ha]
    · rw [factor_center hR (ha_mem ha) (ha0 ha), smul_neg]
  rw [hproduct, he] at hlog
  change logDeriv f 0 = logDeriv g 0 + ∑ᶠ a, d a • kernel R a
  rw [hlog]
  ring

/-- The real coupled kernel keeps the exact radial factor before any
sign estimate. -/
theorem kernel_re {R : ℝ} {a : ℂ} (ha : a ≠ 0) :
    (kernel R a).re = (-a.re / Complex.normSq a) * (1 - Complex.normSq a / R ^ 2) := by
  have hn : Complex.normSq a ≠ 0 := mt Complex.normSq_eq_zero.mp ha
  simp only [kernel, Complex.add_re, neg_div, one_div, Complex.neg_re,
    Complex.inv_re, ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.conj_re]
  field_simp
  ring

/-- Zeros left of the center give nonnegative complete contributions;
the regular correction is not separated by a triangle estimate. -/
theorem kernel_re_nonneg {R : ℝ} (hR : 0 < R) {a : ℂ}
    (ha : a ∈ ball 0 R) (ha0 : a ≠ 0) (hre : a.re ≤ 0) : 0 ≤ (kernel R a).re := by
  rw [kernel_re ha0]
  have hn : Complex.normSq a ≤ R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hlt : ‖a‖ < R := by simpa only [mem_ball, dist_zero_right] using ha
    nlinarith [norm_nonneg a]
  exact mul_nonneg (div_nonneg (neg_nonneg.mpr hre) (Complex.normSq_nonneg a))
    (sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hR)).mpr hn))

/-- A zero on the center's horizontal line keeps its reciprocal
distance and its exact quadratic radial correction. -/
theorem kernel_neg_real (R d : ℝ) :
    (kernel R (-((d : ℝ) : ℂ))).re = 1 / d - d / R ^ 2 := by
  simp [kernel, ← Complex.ofReal_pow]
  ring

end
end RiemannGaussian.AnalyticDiscSignedDerivative
