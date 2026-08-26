import RiemannGaussian.GaussianXiQuantitativeContour
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville

/-!
# Growth of the xi logarithmic derivative on separated contours

This file develops the last analytic estimate needed by the Gaussian xi
contour.  The strategy is finite canonical decomposition on a larger circle:
factor out all enclosed xi zeros, control the remaining zero-free analytic
factor by maximum modulus and Borel--Carathéodory, and use the quantitative
zero separation proved in `GaussianXiQuantitativeContour` for the finite
factor.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeromorphicOn Metric Set Topology
open scoped Topology

/-! ## Larger zero-free canonical-decomposition circles -/

/-- Between any two real radii there is a sphere containing no xi zero. -/
theorem exists_riemannXiSphere_zeroFree
    {a b : ℝ} (hab : a < b) :
    ∃ R : ℝ, a < R ∧ R < b ∧
      ∀ z : ℂ, ‖z‖ = R → riemannXi z ≠ 0 := by
  let zeros : Set ℂ :=
    closedBall (0 : ℂ) b ∩ nontrivialZetaZeroSet
  have hzeros : zeros.Finite :=
    IsCompact.inter_nontrivialZetaZeroSet_finite
      (isCompact_closedBall (0 : ℂ) b)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hinterval : (Ioo a b).Infinite := Set.Ioo_infinite hab
  have hnotSubset : ¬Ioo a b ⊆ (bad : Set ℝ) := by
    intro hsubset
    exact hinterval (bad.finite_toSet.subset hsubset)
  rcases Set.not_subset.mp hnotSubset with ⟨R, hR, hRbad⟩
  refine ⟨R, hR.1, hR.2, fun z hz hxi => ?_⟩
  apply hRbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, (riemannXi_eq_zero_iff_isNontrivialZetaZero z).mp hxi⟩
  rw [mem_closedBall, dist_zero_right, hz]
  exact hR.2.le

/-- A zero-free radius more than four times the scale of the `n`th selected
vertical contour. -/
noncomputable def xiCanonicalRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_riemannXiSphere_zeroFree
    (show 4 * ((n : ℝ) + 3) < 4 * ((n : ℝ) + 3) + 1 by linarith))

theorem xiCanonicalRadius_spec (n : ℕ) :
    4 * ((n : ℝ) + 3) < xiCanonicalRadius n ∧
      xiCanonicalRadius n < 4 * ((n : ℝ) + 3) + 1 ∧
      ∀ z : ℂ, ‖z‖ = xiCanonicalRadius n → riemannXi z ≠ 0 :=
  Classical.choose_spec (exists_riemannXiSphere_zeroFree
    (show 4 * ((n : ℝ) + 3) < 4 * ((n : ℝ) + 3) + 1 by linarith))

theorem xiCanonicalRadius_pos (n : ℕ) : 0 < xiCanonicalRadius n :=
  (by positivity : 0 < 4 * ((n : ℝ) + 3)).trans
    (xiCanonicalRadius_spec n).1

/-- Xi has zero divisor on the selected boundary sphere. -/
theorem divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero (n : ℕ) :
    divisor riemannXi (sphere 0 (xiCanonicalRadius n)) = 0 := by
  classical
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) (xiCanonicalRadius n)
  · have hxi : riemannXi z ≠ 0 :=
      (xiCanonicalRadius_spec n).2.2 z
        (by simpa [mem_sphere, dist_zero_right] using hz)
    have horder : meromorphicOrderAt riemannXi z = 0 :=
      (analyticAt_riemannXi z).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
    rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hz]
    simp [horder]
  · change (if MeromorphicOn riemannXi
        (sphere 0 (xiCanonicalRadius n)) ∧
        z ∈ sphere 0 (xiCanonicalRadius n) then
          (meromorphicOrderAt riemannXi z).untop₀ else 0) = 0
    rw [if_neg (fun h => hz h.2)]

theorem meromorphicOrderAt_riemannXi_ne_top (z : ℂ) :
    meromorphicOrderAt riemannXi z ≠ ⊤ := by
  have hmeromorphic : Meromorphic riemannXi :=
    meromorphicOn_univ.mp analyticOnNhd_riemannXi.meromorphicOn
  apply hmeromorphic.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  refine ⟨0, ?_⟩
  have horder : meromorphicOrderAt riemannXi 0 = 0 :=
    (analyticAt_riemannXi 0).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr (by simp)
  simp [horder]

/-- Extended canonical decomposition of xi on the selected large circle. -/
theorem exists_riemannXiECanonicalDecomp (n : ℕ) :
    ∃ g : ℂ → ℂ,
      Complex.ECanonicalDecomp riemannXi g (xiCanonicalRadius n) := by
  apply MeromorphicOn.exists_ecanonicalDecomp
    (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn
  intro z
  exact meromorphicOrderAt_riemannXi_ne_top z

/-- The zero-free analytic residual in the canonical decomposition. -/
noncomputable def riemannXiCanonicalResidual (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_riemannXiECanonicalDecomp n)

theorem riemannXiCanonicalResidual_decomp (n : ℕ) :
    Complex.ECanonicalDecomp riemannXi
      (riemannXiCanonicalResidual n) (xiCanonicalRadius n) :=
  Classical.choose_spec (exists_riemannXiECanonicalDecomp n)

/-! ## Norm control of the zero-free residual -/

/-- On the selected boundary sphere, the canonical residual has exactly the
same norm as xi: all interior canonical factors have norm one there and the
boundary divisor is zero. -/
theorem norm_riemannXiCanonicalResidual_eq_on_sphere
    (n : ℕ) {z : ℂ} (hz : z ∈ sphere 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ = ‖riemannXi z‖ := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hxi : riemannXi z ≠ 0 :=
    (xiCanonicalRadius_spec n).2.2 z
      (by simpa [R, mem_sphere, dist_zero_right] using hz)
  have horder : meromorphicOrderAt riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    (sphere_subset_closedBall hz) horder hR
  have hcanonical (i : ℂ) :
      ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖ = 0 := by
    by_cases hi : divisor riemannXi (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor riemannXi (ball 0 R)).supportWithinDomain hi
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one himem hz,
        Real.log_one, mul_zero]
  have htrailing : meromorphicTrailingCoeffAt riemannXi z = riemannXi z :=
    (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi
  change Real.log ‖g z‖ = _ at hlog
  have hcanonicalSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) = 0 :=
    finsum_eq_zero_of_forall_eq_zero hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      exact divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  rw [hcanonicalSum, hsphereSum, htrailing] at hlog
  simp only [sub_zero, zero_add] at hlog
  have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((riemannXiCanonicalResidual_decomp n).ne_zero z
      (sphere_subset_closedBall hz))
  have hxipos : 0 < ‖riemannXi z‖ := norm_pos_iff.mpr hxi
  have hexp := congrArg Real.exp hlog
  simpa [Real.exp_log hgpos, Real.exp_log hxipos] using hexp

/-- A global xi growth bound transfers to the canonical residual throughout
the whole selected closed ball by the maximum modulus principle. -/
theorem norm_riemannXiCanonicalResidual_le_of_growth
    {A : ℝ} (_hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ ≤
      Real.exp (A * (xiCanonicalRadius n + 1) ^ 2) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DiffContOnCl ℂ g (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (riemannXiCanonicalResidual_decomp n).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_riemannXiCanonicalResidual_eq_on_sphere n hw]
    have hxi := hbound w
    have hwnorm : ‖w‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hw
    simpa [R, hwnorm] using hxi
  · rwa [closure_ball 0 hR.ne']

end

end RiemannGaussian
