/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaCanonicalUnit
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Logarithmic variation of the full denominator's analytic unit

The actual canonical unit has a normalized analytic logarithm.
Its complete complex variation is controlled by logarithmic height,
using the proved polynomial envelope and fixed safe-center floor.
-/

open Complex Filter MeromorphicOn Metric Set Topology
namespace RiemannGaussian
noncomputable section

/-- A positive logarithmic majorant for the actual unit's variation. -/
def suzukiEtaCanonicalLogMajorant (t : {T : ℝ // 2 ≤ T}) : ℝ :=
  Real.log (1 + suzukiEtaLocalPoleJensenConstant * (t.1 + 4) ^ 2)

/-- The logarithmic majorant is strictly positive at every eligible height. -/
theorem suzukiEtaCanonicalLogMajorant_pos (t : {T : ℝ // 2 ≤ T}) :
    0 < suzukiEtaCanonicalLogMajorant t := by
  apply Real.log_pos
  have hp : 0 < suzukiEtaLocalPoleJensenConstant * (t.1 + 4) ^ 2 := by
    have ht := t.property
    positivity [suzukiEtaLocalPoleJensenConstant_pos]
  linarith

/-- Exponentiating the logarithmic allowance gives its exact
polynomial cost; no decay is concealed in this separate unit bound. -/
theorem exp_nat_mul_suzukiEtaCanonicalLogMajorant (t : {T : ℝ // 2 ≤ T}) (m : ℕ) :
    Real.exp ((m : ℝ) * suzukiEtaCanonicalLogMajorant t) =
      (1 + suzukiEtaLocalPoleJensenConstant * (t.1 + 4) ^ 2) ^ m := by
  rw [Real.exp_nat_mul, suzukiEtaCanonicalLogMajorant, Real.exp_log]
  positivity [suzukiEtaLocalPoleJensenConstant_pos]

private lemma suzukiEtaCleared_upper_div_centerFloor_eq (T : ℝ) :
    suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 /
      (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass) =
        suzukiEtaLocalPoleJensenConstant * (T + 4) ^ 2 := by
  unfold suzukiEtaLocalPoleJensenConstant
  ring

/-! ## The normalized analytic logarithm -/

/-- The zero-free full-denominator residual has a logarithmic derivative primitive
on its selected disk, normalized to vanish at the origin. -/
theorem exists_suzukiEtaCanonicalLog (t : {T : ℝ // 2 ≤ T}) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      ∀ z ∈ ball 0 (suzukiEtaCanonicalRadius t),
        HasDerivAt L
          (logDeriv (suzukiEtaCanonicalUnit t) z) z := by
  let R := suzukiEtaCanonicalRadius t
  let g := suzukiEtaCanonicalUnit t
  have hdiff : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have hg := (suzukiEtaCanonicalUnit_decomp t).analyticOnNhd z
      (ball_subset_closedBall (by simpa [R] using hz))
    have hlog : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((suzukiEtaCanonicalUnit_decomp t).ne_zero z
          (ball_subset_closedBall (by simpa [R, g] using hz)))
    exact hlog.differentiableAt.differentiableWithinAt
  simpa [R, g] using hdiff.isExactOn_ball.with_val_at 0 0

/-- A fixed normalized analytic logarithm of the full-denominator residual. -/
noncomputable def suzukiEtaCanonicalLog (t : {T : ℝ // 2 ≤ T}) : ℂ → ℂ :=
  Classical.choose (exists_suzukiEtaCanonicalLog t)

@[simp] theorem suzukiEtaCanonicalLog_zero (t : {T : ℝ // 2 ≤ T}) :
    suzukiEtaCanonicalLog t 0 = 0 :=
  (Classical.choose_spec (exists_suzukiEtaCanonicalLog t)).1

theorem suzukiEtaCanonicalLog_hasDerivAt
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ ball 0 (suzukiEtaCanonicalRadius t)) :
    HasDerivAt (suzukiEtaCanonicalLog t)
      (logDeriv (suzukiEtaCanonicalUnit t) z) z :=
  (Classical.choose_spec (exists_suzukiEtaCanonicalLog t)).2 z hz

/-- Exponentiating the normalized primitive recovers the full-denominator residual,
with its value at the origin as the normalizing constant. -/
theorem exp_suzukiEtaCanonicalLog_mul_zero_eq
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ ball 0 (suzukiEtaCanonicalRadius t)) :
    Complex.exp (suzukiEtaCanonicalLog t z) *
        suzukiEtaCanonicalUnit t 0 =
      suzukiEtaCanonicalUnit t z := by
  let R := suzukiEtaCanonicalRadius t
  let g := suzukiEtaCanonicalUnit t
  let L := suzukiEtaCanonicalLog t
  let q : ℂ → ℂ := (fun w => Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := by
    exact mem_ball_self (by
      simpa [R] using suzukiEtaCanonicalRadius_pos t)
  have hqdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := suzukiEtaCanonicalLog_hasDerivAt t
      (by simpa [R] using hw)
    have hg := (suzukiEtaCanonicalUnit_decomp t).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    exact (by
      simpa [q, L, g] using
        (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt
          |>.differentiableWithinAt)
  have hqderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := suzukiEtaCanonicalLog_hasDerivAt t
      (by simpa [R] using hw)
    have hg := (suzukiEtaCanonicalUnit_decomp t).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    have hqHas : HasDerivAt q
        (Complex.exp (-L w) *
            (-logDeriv g w) * g w +
          Complex.exp (-L w) * deriv g w) w := by
      simpa [q, L, g] using hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hqHas.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply]
    have hgne : g w ≠ 0 :=
      (suzukiEtaCanonicalUnit_decomp t).ne_zero w
        (ball_subset_closedBall (by simpa [R, g] using hw))
    rw [mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ hgne]
    ring
  have hqeq : q 0 = q z :=
    isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
      hqdiff hqderiv hzero (by simpa [R] using hz)
  have hg0eq : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, suzukiEtaCanonicalLog_zero] using hqeq
  change Complex.exp (L z) * g 0 = g z
  rw [hg0eq, ← mul_assoc, ← Complex.exp_add]
  simp

/-! ## Real-part and Borel--Carathéodory bounds -/

/-- The disk upper bound divided by the safe-center lower floor controls the
real part of the normalized residual logarithm. -/
theorem suzukiEtaCanonicalLog_re_le
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ ball 0 (suzukiEtaCanonicalRadius t)) :
    (suzukiEtaCanonicalLog t z).re ≤
      suzukiEtaCanonicalLogMajorant t := by
  let T : ℝ := t.1
  let g := suzukiEtaCanonicalUnit t
  let L := suzukiEtaCanonicalLog t
  let c : ℝ := staticContourSafeEtaFactorFloor ^ 2 /
    staticContourSafeZetaDirichletMass
  have hcpos : 0 < c := by
    dsimp [c]
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hid := congrArg norm
    (exp_suzukiEtaCanonicalLog_mul_zero_eq t hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : c ≤ ‖g 0‖ := by
    simpa [c, g] using
      suzukiEtaClearedFloor_le_norm_canonicalUnit_zero t
  have hgBound :
      ‖g z‖ ≤ suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 := by
    apply norm_suzukiEtaCanonicalUnit_le t
    exact ball_subset_closedBall (by simpa [T, g] using hz)
  have hexpTimesFloor :
      Real.exp (L z).re * c ≤
        suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 := by
    calc
      Real.exp (L z).re * c ≤ Real.exp (L z).re * ‖g 0‖ :=
        mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
      _ = ‖g z‖ := hid
      _ ≤ suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 := hgBound
  have hargpos :
      0 < suzukiEtaLocalPoleJensenConstant *
        (t.1 + 4) ^ 2 := by
    have ht := t.property
    positivity [suzukiEtaLocalPoleJensenConstant_pos]
  apply Real.exp_le_exp.mp
  rw [suzukiEtaCanonicalLogMajorant, Real.exp_log (by linarith : 0 < 1 + suzukiEtaLocalPoleJensenConstant * (t.1 + 4) ^ 2)]
  calc
    Real.exp (L z).re ≤
        suzukiEtaLocalClearedGrowthConstant * (T + 4) ^ 2 / c :=
      (le_div_iff₀ hcpos).2 hexpTimesFloor
    _ = suzukiEtaLocalPoleJensenConstant * (T + 4) ^ 2 := by
      simpa [c] using suzukiEtaCleared_upper_div_centerFloor_eq T
    _ ≤ 1 + suzukiEtaLocalPoleJensenConstant * (t.1 + 4) ^ 2 := by dsimp [T]; linarith

/-- Borel--Carathéodory turns the one-sided real-part estimate into a norm
bound throughout the selected full-denominator disk. -/
theorem norm_suzukiEtaCanonicalLog_le
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ ball 0 (suzukiEtaCanonicalRadius t)) :
    ‖suzukiEtaCanonicalLog t z‖ ≤
      2 * suzukiEtaCanonicalLogMajorant t * ‖z‖ /
        (suzukiEtaCanonicalRadius t - ‖z‖) := by
  let R := suzukiEtaCanonicalRadius t
  let L := suzukiEtaCanonicalLog t
  have hR : 0 < R := suzukiEtaCanonicalRadius_pos t
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (suzukiEtaCanonicalLog_hasDerivAt t
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero
    (M := suzukiEtaCanonicalLogMajorant t)
    (suzukiEtaCanonicalLogMajorant_pos t) hdiff
  · intro w hw
    exact suzukiEtaCanonicalLog_re_le t
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact suzukiEtaCanonicalLog_zero t

/-- The whole unit logarithm has a logarithmic-height bound throughout
the unit disk, including the complete translated strip segment. -/
theorem norm_suzukiEtaCanonicalLog_le_unit (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    ‖suzukiEtaCanonicalLog t z‖ ≤ 64 * suzukiEtaCanonicalLogMajorant t := by
  have hR := (suzukiEtaCanonicalRadius_spec t).1
  have hM := suzukiEtaCanonicalLogMajorant_pos t
  have hb : z ∈ ball 0 (suzukiEtaCanonicalRadius t) := by
    rw [mem_ball, dist_zero_right]
    linarith
  apply (norm_suzukiEtaCanonicalLog_le t hb).trans
  rw [div_le_iff₀ (by linarith : 0 < suzukiEtaCanonicalRadius t - ‖z‖)]
  nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hz),
    mul_nonneg hM.le (sub_nonneg.mpr hR.le)]

/-- The analytic factor remaining after all local poles are removed
has an explicit nonzero lower bound on the whole unit disk. -/
theorem suzukiEtaCanonicalUnit_lower_bound (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    (staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass) *
      Real.exp (-64 * suzukiEtaCanonicalLogMajorant t) ≤ ‖suzukiEtaCanonicalUnit t z‖ := by
  have hR := (suzukiEtaCanonicalRadius_spec t).1
  have hb : z ∈ ball 0 (suzukiEtaCanonicalRadius t) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have he := congrArg norm (exp_suzukiEtaCanonicalLog_mul_zero_eq t hb)
  rw [norm_mul, Complex.norm_exp] at he
  have hr : -64 * suzukiEtaCanonicalLogMajorant t ≤ (suzukiEtaCanonicalLog t z).re := by
    have hn := norm_suzukiEtaCanonicalLog_le_unit t hz
    have hl := (abs_le.mp (Complex.abs_re_le_norm (suzukiEtaCanonicalLog t z))).1
    linarith
  calc
    _ ≤ ‖suzukiEtaCanonicalUnit t 0‖ * Real.exp (suzukiEtaCanonicalLog t z).re :=
      mul_le_mul (suzukiEtaClearedFloor_le_norm_canonicalUnit_zero t)
        (Real.exp_le_exp.mpr hr) (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := by rw [mul_comm]; exact he

/-- Cauchy's estimate controls the logarithmic derivative of the
actual zero-free unit, uniformly throughout the unit disk. -/
theorem norm_logDeriv_suzukiEtaCanonicalUnit_le (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    ‖logDeriv (suzukiEtaCanonicalUnit t) z‖ ≤ 8320 * suzukiEtaCanonicalLogMajorant t := by
  have hR := (suzukiEtaCanonicalRadius_spec t).1
  have hM := suzukiEtaCanonicalLogMajorant_pos t
  have hnorm {w : ℂ} (hw : w ∈ closedBall z (1 / 64 : ℝ)) : ‖w‖ ≤ 65 / 64 := by
    have hd : ‖w - z‖ ≤ 1 / 64 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hn := norm_add_le (w - z) z
    rw [sub_add_cancel] at hn
    linarith
  have hsub : closedBall z (1 / 64 : ℝ) ⊆ ball 0 (suzukiEtaCanonicalRadius t) := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    linarith [hnorm hw]
  have hd : DiffContOnCl ℂ (suzukiEtaCanonicalLog t) (ball z (1 / 64 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 64 : ℝ) ≠ 0)]
    intro w hw
    exact (suzukiEtaCanonicalLog_hasDerivAt t (hsub hw)).differentiableAt.differentiableWithinAt
  have hsphere : ∀ w ∈ sphere z (1 / 64 : ℝ),
      ‖suzukiEtaCanonicalLog t w‖ ≤ 130 * suzukiEtaCanonicalLogMajorant t := by
    intro w hw
    have hn := hnorm (sphere_subset_closedBall hw)
    apply (norm_suzukiEtaCanonicalLog_le t (hsub (sphere_subset_closedBall hw))).trans
    rw [div_le_iff₀ (by linarith : 0 < suzukiEtaCanonicalRadius t - ‖w‖)]
    nlinarith [mul_nonneg hM.le (sub_nonneg.mpr hn),
      mul_nonneg hM.le (sub_nonneg.mpr hR.le)]
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 64) hd hsphere
  have hb : z ∈ ball 0 (suzukiEtaCanonicalRadius t) := by
    rw [mem_ball, dist_zero_right]
    linarith
  rw [(suzukiEtaCanonicalLog_hasDerivAt t hb).deriv] at he
  convert he using 1
  ring


end
end RiemannGaussian
