/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiEtaLocalPoleCount
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax

/-!
# Canonical analytic unit of the full eta carrier denominator

A selected circle retains all zeros and dyadic factors inside it.
Removing its complete canonical divisor produces an analytic unit whose
upper bound is quadratic in height and whose safe-center floor is fixed.
The exact canonical decomposition remains available with every phase
and multiplicity, before taking norms.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The fixed outer disk where the full cleared denominator has its
proved polynomial bound. -/
def suzukiEtaCanonicalOuterRadius : ℝ := 9 / 8

private lemma analyticOnNhd_suzukiEtaCleared_outer (t : {T : ℝ // 2 ≤ T}) :
    AnalyticOnNhd ℂ (suzukiEtaLocalClearedDenominator t.1)
      (closedBall 0 suzukiEtaCanonicalOuterRadius) :=
  analyticOnNhd_suzukiEtaLocalClearedDenominator t.property

private lemma suzukiEtaCleared_floor_le_norm_zero (t : {T : ℝ // 2 ≤ T}) :
    staticContourSafeEtaFactorFloor ^ 2 / staticContourSafeZetaDirichletMass ≤
      ‖suzukiEtaLocalClearedDenominator t.1 0‖ := by
  simpa only [suzukiEtaLocalClearedDenominator, add_zero] using
    safe_floor_le_norm_suzukiEtaClearedCarrierDenominator (by linarith [t.property] : 0 < t.1)


/-- The translated cleared denominator has finite meromorphic order throughout the
fixed outer disk at every height at least two. -/
lemma meromorphicOrderAt_suzukiEtaCleared_ne_top_outer
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ closedBall 0 suzukiEtaCanonicalOuterRadius) :
    meromorphicOrderAt
      (suzukiEtaLocalClearedDenominator t.1) z ≠
        ⊤ := by
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let CB : Set ℂ := closedBall 0 suzukiEtaCanonicalOuterRadius
  have hanalytic : AnalyticOnNhd ℂ f CB := by
    simpa [f, CB] using analyticOnNhd_suzukiEtaCleared_outer t
  have hcenterLower :=
    suzukiEtaCleared_floor_le_norm_zero t
  have hfloorPos : 0 < staticContourSafeEtaFactorFloor ^ 2 /
      staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hfzero : f 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (hfloorPos.trans_le (by simpa [f] using hcenterLower))
  have hzeroMem : (0 : ℂ) ∈ CB := by
    norm_num [CB, suzukiEtaCanonicalOuterRadius]
  have horderZero : meromorphicOrderAt f 0 = 0 :=
    (hanalytic 0 hzeroMem).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfzero
  have hfiniteAtZero : meromorphicOrderAt f 0 ≠ ⊤ := by
    simp [horderZero]
  have hconnected : IsConnected CB := by
    exact ⟨nonempty_closedBall.mpr (by
      norm_num [suzukiEtaCanonicalOuterRadius]),
      (convex_closedBall (0 : ℂ) suzukiEtaCanonicalOuterRadius).isPreconnected⟩
  have hall :=
    (hanalytic.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      hconnected).mp ⟨⟨0, hzeroMem⟩, hfiniteAtZero⟩
  exact hall ⟨z, by simpa [CB, T, f] using hz⟩

/-- Between the fixed target-containing radius and the Jensen radius there is
a sphere containing no cleared denominator zero. -/
theorem exists_suzukiEtaClearedSphere_zeroFree (t : {T : ℝ // 2 ≤ T}) :
    ∃ R : ℝ, 33 / 32 < R ∧ R < 17 / 16 ∧
      ∀ z : ℂ, ‖z‖ = R →
        suzukiEtaLocalClearedDenominator
          t.1 z ≠ 0 := by
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let CB : Set ℂ := closedBall 0 suzukiEtaCanonicalOuterRadius
  have hanalytic : AnalyticOnNhd ℂ f CB := by
    simpa [f, CB] using analyticOnNhd_suzukiEtaCleared_outer t
  have horders : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    apply meromorphicOrderAt_suzukiEtaCleared_ne_top_outer t
    exact u.property
  have hzeros : (CB ∩ f ⁻¹' {0}).Finite := by
    rw [hanalytic.meromorphicNFOn.zero_set_eq_divisor_support horders]
    exact (divisor f CB).finiteSupport
      (isCompact_closedBall 0 suzukiEtaCanonicalOuterRadius)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hinterval : (Ioo (33 / 32 : ℝ) (17 / 16 : ℝ)).Infinite :=
    Set.Ioo_infinite (by norm_num)
  have hnotSubset :
      ¬Ioo (33 / 32 : ℝ) (17 / 16 : ℝ) ⊆ (bad : Set ℝ) := by
    intro hsubset
    exact hinterval (bad.finite_toSet.subset hsubset)
  rcases Set.not_subset.mp hnotSubset with ⟨R, hR, hRbad⟩
  refine ⟨R, hR.1, hR.2, fun z hz hzero => ?_⟩
  apply hRbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right, hz]
    exact hR.2.le.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  · simpa [f] using hzero

/-- A selected zero-free boundary radius at each height at least two. -/
noncomputable def suzukiEtaCanonicalRadius (t : {T : ℝ // 2 ≤ T}) : ℝ :=
  Classical.choose (exists_suzukiEtaClearedSphere_zeroFree t)

theorem suzukiEtaCanonicalRadius_spec (t : {T : ℝ // 2 ≤ T}) :
    33 / 32 < suzukiEtaCanonicalRadius t ∧
      suzukiEtaCanonicalRadius t < 17 / 16 ∧
      ∀ z : ℂ, ‖z‖ = suzukiEtaCanonicalRadius t →
        suzukiEtaLocalClearedDenominator
          t.1 z ≠ 0 :=
  Classical.choose_spec (exists_suzukiEtaClearedSphere_zeroFree t)

lemma suzukiEtaCanonicalRadius_pos (t : {T : ℝ // 2 ≤ T}) :
    0 < suzukiEtaCanonicalRadius t :=
  (by norm_num : (0 : ℝ) < 33 / 32).trans
    (suzukiEtaCanonicalRadius_spec t).1

lemma one_lt_suzukiEtaCanonicalRadius (t : {T : ℝ // 2 ≤ T}) :
    1 < suzukiEtaCanonicalRadius t :=
  (by norm_num : (1 : ℝ) < 33 / 32).trans
    (suzukiEtaCanonicalRadius_spec t).1

/-- The the translated cleared denominator divisor vanishes on the selected boundary sphere. -/
theorem divisor_suzukiEtaCleared_sphere_canonicalRadius_eq_zero
    (t : {T : ℝ // 2 ≤ T}) :
    divisor
      (suzukiEtaLocalClearedDenominator t.1)
      (sphere 0 (suzukiEtaCanonicalRadius t)) = 0 := by
  classical
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let R : ℝ := suzukiEtaCanonicalRadius t
  have hanalyticOuter := analyticOnNhd_suzukiEtaCleared_outer t
  have hRltOuter : R < suzukiEtaCanonicalOuterRadius :=
    (suzukiEtaCanonicalRadius_spec t).2.1.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (sphere 0 R) :=
    hanalyticOuter.mono (fun z hz => by
      apply ball_subset_closedBall
      rw [mem_ball, dist_zero_right]
      have hznorm : ‖z‖ = R := by
        simpa [mem_sphere, dist_zero_right] using hz
      rwa [hznorm])
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) R
  · have hfz : f z ≠ 0 := by
      apply (suzukiEtaCanonicalRadius_spec t).2.2 z
      simpa [R, mem_sphere, dist_zero_right] using hz
    have horder : meromorphicOrderAt f z = 0 :=
      (hanalytic z hz).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
    rw [hanalytic.meromorphicOn.divisor_apply hz]
    simp [horder]
  · change (if MeromorphicOn f (sphere 0 R) ∧
        z ∈ sphere 0 R then
          (meromorphicOrderAt f z).untop₀ else 0) = 0
    rw [if_neg (fun h => hz h.2)]

/-- Extended canonical decomposition of the translated cleared denominator on its selected local
circle. -/
theorem exists_suzukiEtaClearedECanonicalDecomp (t : {T : ℝ // 2 ≤ T}) :
    ∃ g : ℂ → ℂ,
      Complex.ECanonicalDecomp
        (suzukiEtaLocalClearedDenominator t.1) g
        (suzukiEtaCanonicalRadius t) := by
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let R : ℝ := suzukiEtaCanonicalRadius t
  have hRltOuter : R < suzukiEtaCanonicalOuterRadius :=
    (suzukiEtaCanonicalRadius_spec t).2.1.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_suzukiEtaCleared_outer t).mono
      (closedBall_subset_closedBall hRltOuter.le)
  apply MeromorphicOn.exists_ecanonicalDecomp hanalytic.meromorphicOn
  intro z
  apply meromorphicOrderAt_suzukiEtaCleared_ne_top_outer t
  exact (closedBall_subset_closedBall hRltOuter.le) z.property

/-- The zero-free analytic residual in the moving local carrier decomposition. -/
noncomputable def suzukiEtaCanonicalUnit
    (t : {T : ℝ // 2 ≤ T}) : ℂ → ℂ :=
  Classical.choose (exists_suzukiEtaClearedECanonicalDecomp t)

theorem suzukiEtaCanonicalUnit_decomp (t : {T : ℝ // 2 ≤ T}) :
    Complex.ECanonicalDecomp
      (suzukiEtaLocalClearedDenominator t.1)
      (suzukiEtaCanonicalUnit t)
      (suzukiEtaCanonicalRadius t) :=
  Classical.choose_spec (exists_suzukiEtaClearedECanonicalDecomp t)

/-- On the selected sphere, the residual and the translated cleared denominator have exactly the
same norm. -/
theorem norm_suzukiEtaCanonicalUnit_eq_on_sphere
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ sphere 0 (suzukiEtaCanonicalRadius t)) :
    ‖suzukiEtaCanonicalUnit t z‖ =
      ‖suzukiEtaLocalClearedDenominator
        t.1 z‖ := by
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let R : ℝ := suzukiEtaCanonicalRadius t
  let g : ℂ → ℂ := suzukiEtaCanonicalUnit t
  have hR : 0 < R := suzukiEtaCanonicalRadius_pos t
  have hfz : f z ≠ 0 := by
    apply (suzukiEtaCanonicalRadius_spec t).2.2 z
    simpa [R, mem_sphere, dist_zero_right] using hz
  have hRltOuter : R < suzukiEtaCanonicalOuterRadius :=
    (suzukiEtaCanonicalRadius_spec t).2.1.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_suzukiEtaCleared_outer t).mono
      (closedBall_subset_closedBall hRltOuter.le)
  have horder : meromorphicOrderAt f z = 0 :=
    (hanalytic z (sphere_subset_closedBall hz)).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hlog := (suzukiEtaCanonicalUnit_decomp t).log_norm_eq
    (sphere_subset_closedBall hz) horder hR
  have hcanonical (i : ℂ) :
      ((divisor f (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖ = 0 := by
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor f (ball 0 R)).supportWithinDomain hi
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one himem hz,
        Real.log_one, mul_zero]
  have hcanonicalSum :
      (∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) = 0 :=
    finsum_eq_zero_of_forall_eq_zero hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) *
        Real.log ‖z - i‖) = 0 := by
    rw [show divisor f (sphere 0 R) = 0 by
      simpa [f, T, R] using
        divisor_suzukiEtaCleared_sphere_canonicalRadius_eq_zero t]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt f z = f z :=
    (hanalytic z (sphere_subset_closedBall hz))
      |>.meromorphicTrailingCoeffAt_of_ne_zero hfz
  change Real.log ‖g z‖ = _ at hlog
  rw [hcanonicalSum, hsphereSum, htrailing] at hlog
  simp only [sub_zero, zero_add] at hlog
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((suzukiEtaCanonicalUnit_decomp t).ne_zero z
      (sphere_subset_closedBall hz))
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  have hexp := congrArg Real.exp hlog
  simpa [Real.exp_log hgpos, Real.exp_log hfpos, f, g, T] using hexp

/-- The residual inherits the cleared denominator's quadratic bound throughout the selected closed
disk. -/
theorem norm_suzukiEtaCanonicalUnit_le
    (t : {T : ℝ // 2 ≤ T}) {z : ℂ}
    (hz : z ∈ closedBall 0 (suzukiEtaCanonicalRadius t)) :
    ‖suzukiEtaCanonicalUnit t z‖ ≤
      suzukiEtaLocalClearedGrowthConstant *
        (t.1 + 4) ^ 2 := by
  let T : ℝ := t.1
  let R : ℝ := suzukiEtaCanonicalRadius t
  let g : ℂ → ℂ := suzukiEtaCanonicalUnit t
  have hR : 0 < R := suzukiEtaCanonicalRadius_pos t
  have hT : 2 ≤ T := t.property
  have hRltOuter : R < suzukiEtaCanonicalOuterRadius :=
    (suzukiEtaCanonicalRadius_spec t).2.1.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  have hdiff : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (suzukiEtaCanonicalUnit_decomp t).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_suzukiEtaCanonicalUnit_eq_on_sphere t hw]
    apply norm_suzukiEtaLocalClearedDenominator_le hT
    apply ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    have hwnorm : ‖w‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hw
    rwa [hwnorm]
  · rwa [closure_ball 0 hR.ne']

/-- The safe-center cleared denominator lower floor transfers to the canonical residual at
the origin. -/
theorem suzukiEtaClearedFloor_le_norm_canonicalUnit_zero
    (t : {T : ℝ // 2 ≤ T}) :
    staticContourSafeEtaFactorFloor ^ 2 /
        staticContourSafeZetaDirichletMass ≤
      ‖suzukiEtaCanonicalUnit t 0‖ := by
  let T : ℝ := t.1
  let f : ℂ → ℂ := suzukiEtaLocalClearedDenominator T
  let R : ℝ := suzukiEtaCanonicalRadius t
  let g : ℂ → ℂ := suzukiEtaCanonicalUnit t
  have hR : 0 < R := suzukiEtaCanonicalRadius_pos t
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
  have hcenterLower :=
    suzukiEtaCleared_floor_le_norm_zero t
  have hfloorPos : 0 < staticContourSafeEtaFactorFloor ^ 2 /
      staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hfzero : f 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (hfloorPos.trans_le (by simpa [f] using hcenterLower))
  have hRltOuter : R < suzukiEtaCanonicalOuterRadius :=
    (suzukiEtaCanonicalRadius_spec t).2.1.trans (by
      norm_num [suzukiEtaCanonicalOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_suzukiEtaCleared_outer t).mono
      (closedBall_subset_closedBall hRltOuter.le)
  have horder : meromorphicOrderAt f 0 = 0 :=
    (hanalytic 0 hzero).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfzero
  have hlog := (suzukiEtaCanonicalUnit_decomp t).log_norm_eq
    hzero horder hR
  have hcanonical (i : ℂ) :
      0 ≤ ((divisor f (ball 0 R) i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i 0‖ := by
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor f (ball 0 R)).supportWithinDomain hi
      have hine : i ≠ 0 := by
        intro hi0
        subst i
        apply hi
        rw [(hanalytic.mono ball_subset_closedBall).meromorphicOn.divisor_apply]
        · simp [horder]
        · simpa [mem_ball, dist_zero_right] using hR
      have hinorm : ‖i‖ < R := by
        simpa [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hine)).mpr hinorm.le
      exact mul_nonneg (by
        exact_mod_cast (hanalytic.mono ball_subset_closedBall).divisor_nonneg i)
        (Real.log_nonneg hfactor)
  have hcanonicalSum :
      0 ≤ ∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i 0‖ :=
    finsum_nonneg hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) *
        Real.log ‖0 - i‖) = 0 := by
    rw [show divisor f (sphere 0 R) = 0 by
      simpa [f, T, R] using
        divisor_suzukiEtaCleared_sphere_canonicalRadius_eq_zero t]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (hanalytic 0 hzero).meromorphicTrailingCoeffAt_of_ne_zero hfzero
  change Real.log ‖g 0‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  have hlogle : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlog]
    linarith
  have hgpos : 0 < ‖g 0‖ := norm_pos_iff.mpr
    ((suzukiEtaCanonicalUnit_decomp t).ne_zero 0 hzero)
  have hfpos : 0 < ‖f 0‖ := norm_pos_iff.mpr hfzero
  have hnorm : ‖f 0‖ ≤ ‖g 0‖ := by
    have hexp := Real.exp_le_exp.mpr hlogle
    simpa [Real.exp_log hfpos, Real.exp_log hgpos] using hexp
  have hbase : staticContourSafeEtaFactorFloor ^ 2 /
      staticContourSafeZetaDirichletMass ≤ ‖f 0‖ := by
    simpa [f] using hcenterLower
  exact hbase.trans hnorm

end

end RiemannGaussian
