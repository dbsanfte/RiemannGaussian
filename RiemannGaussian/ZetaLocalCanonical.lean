import RiemannGaussian.ZetaLocalDiscBounds
import RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# Complete local zero removal for pole-removed zeta

Every real ordinate has a zero-free sphere of radius between `3/4` and
`7/8` about the safe center. The finite canonical decomposition removes
the entire enclosed divisor and leaves one nonvanishing analytic residual.
No zero-location or zero-separation hypothesis is assumed.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The local pole-removed function is analytic near the whole unit disc. -/
theorem analyticOnNhd_localZetaPoleRemoved_unitDisc (y : ℝ) :
    AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 (1 : ℝ)) :=
  fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z

/-- The safe-center floor excludes an identically zero local function. -/
theorem localZetaPoleRemoved_zero_ne_zero (y : ℝ) : localZetaPoleRemoved y 0 ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (sixteenth_le_norm_localZetaPoleRemoved_zero y)))

/-- Every local meromorphic order on the unit disc is finite. -/
theorem meromorphicOrderAt_localZetaPoleRemoved_ne_top (y : ℝ) {z : ℂ}
    (hz : z ∈ closedBall 0 (1 : ℝ)) : meromorphicOrderAt (localZetaPoleRemoved y) z ≠ ⊤ := by
  let f := localZetaPoleRemoved y
  let CB : Set ℂ := closedBall 0 (1 : ℝ)
  have han := analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have hzero : (0 : ℂ) ∈ CB := by simp [CB]
  have horder : meromorphicOrderAt f 0 = 0 :=
    (han 0 hzero).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr (localZetaPoleRemoved_zero_ne_zero y)
  have hconnected : IsConnected CB :=
    ⟨nonempty_closedBall.mpr (by norm_num), (convex_closedBall (0 : ℂ) 1).isPreconnected⟩
  have hall := (han.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hconnected).mp
    ⟨⟨0, hzero⟩, by simp [f, horder]⟩
  exact hall ⟨z, hz⟩

/-- A complete local divisor admits a zero-free sphere in a fixed
interval of radii around every real ordinate. -/
theorem exists_localZetaSphere_zeroFree (y : ℝ) : ∃ R : ℝ,
    3 / 4 < R ∧ R < 7 / 8 ∧ ∀ z : ℂ, ‖z‖ = R → localZetaPoleRemoved y z ≠ 0 := by
  let f := localZetaPoleRemoved y
  let CB : Set ℂ := closedBall 0 (1 : ℝ)
  have han := analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have horders : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤ :=
    fun u ↦ meromorphicOrderAt_localZetaPoleRemoved_ne_top y u.property
  have hzeros : (CB ∩ f ⁻¹' {0}).Finite := by
    rw [han.meromorphicNFOn.zero_set_eq_divisor_support horders]
    exact (divisor f CB).finiteSupport (isCompact_closedBall 0 1)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬Ioo (3 / 4 : ℝ) (7 / 8 : ℝ) ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite (by norm_num : (3 / 4 : ℝ) < 7 / 8)) (bad.finite_toSet.subset h)
  obtain ⟨R, hR, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR.1, hR.2, fun z hz hzero ↦ ?_⟩
  apply hbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall, dist_zero_right, hz]
  linarith [hR.2]

/-- A selected local radius with no zeros on its boundary. -/
def localZetaCanonicalRadius (y : ℝ) : ℝ := Classical.choose (exists_localZetaSphere_zeroFree y)

/-- The selected radius lies in the fixed interval and its sphere is zero-free. -/
theorem localZetaCanonicalRadius_spec (y : ℝ) :
    3 / 4 < localZetaCanonicalRadius y ∧ localZetaCanonicalRadius y < 7 / 8 ∧
      ∀ z : ℂ, ‖z‖ = localZetaCanonicalRadius y → localZetaPoleRemoved y z ≠ 0 :=
  Classical.choose_spec (exists_localZetaSphere_zeroFree y)

/-- The selected canonical radius is positive. -/
theorem localZetaCanonicalRadius_pos (y : ℝ) : 0 < localZetaCanonicalRadius y :=
  (by norm_num : (0 : ℝ) < 3 / 4).trans (localZetaCanonicalRadius_spec y).1

/-- The local function is analytic on the selected closed disc. -/
theorem analyticOnNhd_localZetaPoleRemoved_canonicalDisc (y : ℝ) :
    AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 (localZetaCanonicalRadius y)) :=
  fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z

/-- The complete divisor vanishes on the chosen boundary sphere. -/
theorem divisor_localZetaPoleRemoved_sphere_eq_zero (y : ℝ) :
    divisor (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) = 0 := by
  have han : AnalyticOnNhd ℂ (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) :=
    fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) (localZetaCanonicalRadius y)
  · have hfz := (localZetaCanonicalRadius_spec y).2.2 z
      (by simpa only [mem_sphere, dist_zero_right] using hz)
    have ho : meromorphicOrderAt (localZetaPoleRemoved y) z = 0 :=
      (han z hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
    rw [han.meromorphicOn.divisor_apply hz]
    simp [ho]
  · change (if MeromorphicOn (localZetaPoleRemoved y) (sphere 0 (localZetaCanonicalRadius y)) ∧
        z ∈ sphere 0 (localZetaCanonicalRadius y) then _ else 0) = 0
    rw [if_neg (fun h ↦ hz h.2)]

/-- The actual local function admits a finite canonical decomposition
with a residual nonvanishing throughout the complete closed disc. -/
theorem exists_localZetaECanonicalDecomp (y : ℝ) : ∃ g : ℂ → ℂ,
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) g (localZetaCanonicalRadius y) := by
  apply MeromorphicOn.exists_ecanonicalDecomp
    (analyticOnNhd_localZetaPoleRemoved_canonicalDisc y).meromorphicOn
  intro z
  apply meromorphicOrderAt_localZetaPoleRemoved_ne_top y
  exact (closedBall_subset_closedBall (by linarith [(localZetaCanonicalRadius_spec y).2.1])) z.property

/-- The complete zero-free local residual of pole-removed zeta. -/
def localZetaCanonicalResidual (y : ℝ) : ℂ → ℂ := Classical.choose (exists_localZetaECanonicalDecomp y)

/-- The residual satisfies the actual complete canonical decomposition. -/
theorem localZetaCanonicalResidual_decomp (y : ℝ) :
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) (localZetaCanonicalResidual y) (localZetaCanonicalRadius y) :=
  Classical.choose_spec (exists_localZetaECanonicalDecomp y)

end

end RiemannGaussian
