import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaSeparation
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax

/-!
# The zero-free residual on a moving local eta disk

For each quantitative endpoint, this module selects a radius strictly between
`17 / 16` and `9 / 8` whose sphere contains no zero of the translated paired
eta function.  The selection uses only finiteness of the analytic divisor on
the fixed compact outer disk.

The extended finite canonical decomposition then produces a zero-free
analytic residual.  Canonical factors have norm one on the selected sphere,
so the residual inherits eta's linear boundary bound.  At the origin, every
interior canonical factor has norm at least one; the already-proved safe eta
lower floor therefore transfers to the residual.  These are the two inputs
needed for a local Borel--Carathéodory estimate.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The translated eta function has finite meromorphic order throughout the
fixed outer disk at every quantitative height. -/
lemma meromorphicOrderAt_staticContourLocalEta_ne_top_outer
    (n : ℕ) {z : ℂ}
    (hz : z ∈ closedBall 0 staticContourLocalEtaOuterRadius) :
    meromorphicOrderAt
      (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n)) z ≠
        ⊤ := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let CB : Set ℂ := closedBall 0 staticContourLocalEtaOuterRadius
  have hTpos : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hanalytic : AnalyticOnNhd ℂ f CB := by
    simpa [f, CB] using analyticOnNhd_staticContourLocalEta_closedBall T
  have hcenterLower :=
    staticContourSafeEtaFactorFloor_div_mass_le_norm_localEta_zero hTpos
  have hfloorPos : 0 < staticContourSafeEtaFactorFloor /
      staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hfzero : f 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (hfloorPos.trans_le (by simpa [f] using hcenterLower))
  have hzeroMem : (0 : ℂ) ∈ CB := by
    norm_num [CB, staticContourLocalEtaOuterRadius]
  have horderZero : meromorphicOrderAt f 0 = 0 :=
    (hanalytic 0 hzeroMem).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfzero
  have hfiniteAtZero : meromorphicOrderAt f 0 ≠ ⊤ := by
    simp [horderZero]
  have hconnected : IsConnected CB := by
    exact ⟨nonempty_closedBall.mpr (by
      norm_num [staticContourLocalEtaOuterRadius]),
      (convex_closedBall (0 : ℂ) staticContourLocalEtaOuterRadius).isPreconnected⟩
  have hall :=
    (hanalytic.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
      hconnected).mp ⟨⟨0, hzeroMem⟩, hfiniteAtZero⟩
  exact hall ⟨z, by simpa [CB, T, f] using hz⟩

/-- Between the fixed target-containing radius and the Jensen radius there is
a sphere containing no translated eta zero. -/
theorem exists_staticContourLocalEtaSphere_zeroFree (n : ℕ) :
    ∃ R : ℝ, 17 / 16 < R ∧ R < 9 / 8 ∧
      ∀ z : ℂ, ‖z‖ = R →
        staticContourLocalEta
          (quantitativeSpectralBoundaryTruncation n) z ≠ 0 := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let CB : Set ℂ := closedBall 0 staticContourLocalEtaOuterRadius
  have hanalytic : AnalyticOnNhd ℂ f CB := by
    simpa [f, CB] using analyticOnNhd_staticContourLocalEta_closedBall T
  have horders : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    apply meromorphicOrderAt_staticContourLocalEta_ne_top_outer n
    exact u.property
  have hzeros : (CB ∩ f ⁻¹' {0}).Finite := by
    rw [hanalytic.meromorphicNFOn.zero_set_eq_divisor_support horders]
    exact (divisor f CB).finiteSupport
      (isCompact_closedBall 0 staticContourLocalEtaOuterRadius)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hinterval : (Ioo (17 / 16 : ℝ) (9 / 8 : ℝ)).Infinite :=
    Set.Ioo_infinite (by norm_num)
  have hnotSubset :
      ¬Ioo (17 / 16 : ℝ) (9 / 8 : ℝ) ⊆ (bad : Set ℝ) := by
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
      norm_num [staticContourLocalEtaOuterRadius])
  · simpa [f] using hzero

/-- A fixed zero-free local canonical radius at the `n`th quantitative
height. -/
noncomputable def staticContourLocalEtaCanonicalRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_staticContourLocalEtaSphere_zeroFree n)

theorem staticContourLocalEtaCanonicalRadius_spec (n : ℕ) :
    17 / 16 < staticContourLocalEtaCanonicalRadius n ∧
      staticContourLocalEtaCanonicalRadius n < 9 / 8 ∧
      ∀ z : ℂ, ‖z‖ = staticContourLocalEtaCanonicalRadius n →
        staticContourLocalEta
          (quantitativeSpectralBoundaryTruncation n) z ≠ 0 :=
  Classical.choose_spec (exists_staticContourLocalEtaSphere_zeroFree n)

lemma staticContourLocalEtaCanonicalRadius_pos (n : ℕ) :
    0 < staticContourLocalEtaCanonicalRadius n :=
  (by norm_num : (0 : ℝ) < 17 / 16).trans
    (staticContourLocalEtaCanonicalRadius_spec n).1

lemma one_lt_staticContourLocalEtaCanonicalRadius (n : ℕ) :
    1 < staticContourLocalEtaCanonicalRadius n :=
  (by norm_num : (1 : ℝ) < 17 / 16).trans
    (staticContourLocalEtaCanonicalRadius_spec n).1

/-- The translated eta divisor vanishes on the selected boundary sphere. -/
theorem divisor_staticContourLocalEta_sphere_canonicalRadius_eq_zero
    (n : ℕ) :
    divisor
      (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n))
      (sphere 0 (staticContourLocalEtaCanonicalRadius n)) = 0 := by
  classical
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  have hanalyticOuter := analyticOnNhd_staticContourLocalEta_closedBall T
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    (staticContourLocalEtaCanonicalRadius_spec n).2.1.trans (by
      norm_num [staticContourLocalEtaOuterRadius])
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
      apply (staticContourLocalEtaCanonicalRadius_spec n).2.2 z
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

/-- Extended canonical decomposition of translated eta on its selected local
circle. -/
theorem exists_staticContourLocalEtaECanonicalDecomp (n : ℕ) :
    ∃ g : ℂ → ℂ,
      Complex.ECanonicalDecomp
        (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n)) g
        (staticContourLocalEtaCanonicalRadius n) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    (staticContourLocalEtaCanonicalRadius_spec n).2.1.trans (by
      norm_num [staticContourLocalEtaOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_staticContourLocalEta_closedBall T).mono
      (closedBall_subset_closedBall hRltOuter.le)
  apply MeromorphicOn.exists_ecanonicalDecomp hanalytic.meromorphicOn
  intro z
  apply meromorphicOrderAt_staticContourLocalEta_ne_top_outer n
  exact (closedBall_subset_closedBall hRltOuter.le) z.property

/-- The zero-free analytic residual in the moving local eta decomposition. -/
noncomputable def staticContourLocalEtaCanonicalResidual
    (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_staticContourLocalEtaECanonicalDecomp n)

theorem staticContourLocalEtaCanonicalResidual_decomp (n : ℕ) :
    Complex.ECanonicalDecomp
      (staticContourLocalEta (quantitativeSpectralBoundaryTruncation n))
      (staticContourLocalEtaCanonicalResidual n)
      (staticContourLocalEtaCanonicalRadius n) :=
  Classical.choose_spec (exists_staticContourLocalEtaECanonicalDecomp n)

/-- On the selected sphere, the residual and translated eta have exactly the
same norm. -/
theorem norm_staticContourLocalEtaCanonicalResidual_eq_on_sphere
    (n : ℕ) {z : ℂ}
    (hz : z ∈ sphere 0 (staticContourLocalEtaCanonicalRadius n)) :
    ‖staticContourLocalEtaCanonicalResidual n z‖ =
      ‖staticContourLocalEta
        (quantitativeSpectralBoundaryTruncation n) z‖ := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  let g : ℂ → ℂ := staticContourLocalEtaCanonicalResidual n
  have hR : 0 < R := staticContourLocalEtaCanonicalRadius_pos n
  have hfz : f z ≠ 0 := by
    apply (staticContourLocalEtaCanonicalRadius_spec n).2.2 z
    simpa [R, mem_sphere, dist_zero_right] using hz
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    (staticContourLocalEtaCanonicalRadius_spec n).2.1.trans (by
      norm_num [staticContourLocalEtaOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_staticContourLocalEta_closedBall T).mono
      (closedBall_subset_closedBall hRltOuter.le)
  have horder : meromorphicOrderAt f z = 0 :=
    (hanalytic z (sphere_subset_closedBall hz)).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hlog := (staticContourLocalEtaCanonicalResidual_decomp n).log_norm_eq
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
        divisor_staticContourLocalEta_sphere_canonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt f z = f z :=
    (hanalytic z (sphere_subset_closedBall hz))
      |>.meromorphicTrailingCoeffAt_of_ne_zero hfz
  change Real.log ‖g z‖ = _ at hlog
  rw [hcanonicalSum, hsphereSum, htrailing] at hlog
  simp only [sub_zero, zero_add] at hlog
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((staticContourLocalEtaCanonicalResidual_decomp n).ne_zero z
      (sphere_subset_closedBall hz))
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  have hexp := congrArg Real.exp hlog
  simpa [Real.exp_log hgpos, Real.exp_log hfpos, f, g, T] using hexp

/-- The residual inherits eta's linear bound throughout the selected closed
disk. -/
theorem norm_staticContourLocalEtaCanonicalResidual_le
    (n : ℕ) {z : ℂ}
    (hz : z ∈ closedBall 0 (staticContourLocalEtaCanonicalRadius n)) :
    ‖staticContourLocalEtaCanonicalResidual n z‖ ≤
      staticContourLocalEtaMass *
        (quantitativeSpectralBoundaryTruncation n + 4) := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  let g : ℂ → ℂ := staticContourLocalEtaCanonicalResidual n
  have hR : 0 < R := staticContourLocalEtaCanonicalRadius_pos n
  have hT : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1.le)
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    (staticContourLocalEtaCanonicalRadius_spec n).2.1.trans (by
      norm_num [staticContourLocalEtaOuterRadius])
  have hdiff : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (staticContourLocalEtaCanonicalResidual_decomp n).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_staticContourLocalEtaCanonicalResidual_eq_on_sphere n hw]
    apply norm_staticContourLocalEta_le hT
    apply ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    have hwnorm : ‖w‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hw
    rwa [hwnorm]
  · rwa [closure_ball 0 hR.ne']

/-- The safe-center eta lower floor transfers to the canonical residual at
the origin. -/
theorem staticContourSafeEtaFactorFloor_div_mass_le_norm_canonicalResidual_zero
    (n : ℕ) :
    staticContourSafeEtaFactorFloor /
        staticContourSafeZetaDirichletMass ≤
      ‖staticContourLocalEtaCanonicalResidual n 0‖ := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let f : ℂ → ℂ := staticContourLocalEta T
  let R : ℝ := staticContourLocalEtaCanonicalRadius n
  let g : ℂ → ℂ := staticContourLocalEtaCanonicalResidual n
  have hR : 0 < R := staticContourLocalEtaCanonicalRadius_pos n
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
  have hTpos : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hcenterLower :=
    staticContourSafeEtaFactorFloor_div_mass_le_norm_localEta_zero hTpos
  have hfloorPos : 0 < staticContourSafeEtaFactorFloor /
      staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hfzero : f 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt (hfloorPos.trans_le (by simpa [f] using hcenterLower))
  have hRltOuter : R < staticContourLocalEtaOuterRadius :=
    (staticContourLocalEtaCanonicalRadius_spec n).2.1.trans (by
      norm_num [staticContourLocalEtaOuterRadius])
  have hanalytic : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    (analyticOnNhd_staticContourLocalEta_closedBall T).mono
      (closedBall_subset_closedBall hRltOuter.le)
  have horder : meromorphicOrderAt f 0 = 0 :=
    (hanalytic 0 hzero).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfzero
  have hlog := (staticContourLocalEtaCanonicalResidual_decomp n).log_norm_eq
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
        divisor_staticContourLocalEta_sphere_canonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (hanalytic 0 hzero).meromorphicTrailingCoeffAt_of_ne_zero hfzero
  change Real.log ‖g 0‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  have hlogle : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
    rw [hlog]
    linarith
  have hgpos : 0 < ‖g 0‖ := norm_pos_iff.mpr
    ((staticContourLocalEtaCanonicalResidual_decomp n).ne_zero 0 hzero)
  have hfpos : 0 < ‖f 0‖ := norm_pos_iff.mpr hfzero
  have hnorm : ‖f 0‖ ≤ ‖g 0‖ := by
    have hexp := Real.exp_le_exp.mpr hlogle
    simpa [Real.exp_log hfpos, Real.exp_log hgpos] using hexp
  have hbase : staticContourSafeEtaFactorFloor /
      staticContourSafeZetaDirichletMass ≤ ‖f 0‖ := by
    simpa [f] using hcenterLower
  exact hbase.trans hnorm

end

end RiemannGaussian
