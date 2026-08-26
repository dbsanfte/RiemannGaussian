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

/-- At the origin, a canonical factor has norm `R / ‖i‖`. -/
lemma norm_canonicalFactor_zero {R : ℝ} (hR : 0 < R) (i : ℂ) :
    ‖Complex.canonicalFactor R i 0‖ = R / ‖i‖ := by
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp [abs_of_pos hR]
  by_cases hi : ‖i‖ = 0
  · simp [hi]
  · field_simp

/-- The canonical residual is automatically normalized from below at the
origin. Every interior xi zero contributes a canonical factor of norm at
least one there, while `‖xi 0‖ = 1`. -/
theorem one_le_norm_riemannXiCanonicalResidual_zero (n : ℕ) :
    1 ≤ ‖riemannXiCanonicalResidual n 0‖ := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hzero : (0 : ℂ) ∈ closedBall 0 R := by simp [hR.le]
  have hxiAnalytic : AnalyticOnNhd ℂ riemannXi (ball 0 R) :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  have horder : meromorphicOrderAt riemannXi 0 = 0 :=
    (analyticAt_riemannXi 0).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr (by simp)
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    hzero horder hR
  have hcanonical (i : ℂ) :
      0 ≤ ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖ := by
    by_cases hi : divisor riemannXi (ball 0 R) i = 0
    · simp [hi]
    · have himem : i ∈ ball (0 : ℂ) R :=
        (divisor riemannXi (ball 0 R)).supportWithinDomain hi
      have hine : i ≠ 0 := by
        intro hi0
        subst i
        apply hi
        rw [hxiAnalytic.meromorphicOn.divisor_apply]
        · simp [horder]
        · simpa [mem_ball, dist_zero_right] using hR
      have hinorm : ‖i‖ < R := by
        simpa [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hine)).mpr hinorm.le
      exact mul_nonneg (by
        exact_mod_cast hxiAnalytic.divisor_nonneg i) (Real.log_nonneg hfactor)
  have hcanonicalSum :
      0 ≤ (∑ᶠ i : ℂ,
        ((divisor riemannXi (ball 0 R) i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i 0‖) :=
    finsum_nonneg hcanonical
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖0 - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      exact divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i => by simp)
  have htrailing : meromorphicTrailingCoeffAt riemannXi 0 = riemannXi 0 :=
    (analyticAt_riemannXi 0).meromorphicTrailingCoeffAt_of_ne_zero (by simp)
  change Real.log ‖g 0‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  have hlognonneg : 0 ≤ Real.log ‖g 0‖ := by
    rw [hlog]
    simpa using hcanonicalSum
  have hgpos : 0 < ‖g 0‖ := norm_pos_iff.mpr
    ((riemannXiCanonicalResidual_decomp n).ne_zero 0 hzero)
  exact (Real.log_nonneg_iff hgpos).mp hlognonneg

/-! ## A normalized analytic logarithm of the residual -/

/-- The zero-free residual has a logarithmic derivative primitive on its
open disk, normalized to vanish at the origin. -/
theorem exists_riemannXiCanonicalLog (n : ℕ) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      ∀ z ∈ ball 0 (xiCanonicalRadius n),
        HasDerivAt L (logDeriv (riemannXiCanonicalResidual n) z) z := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  have hdiff : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd z
      (ball_subset_closedBall hz)
    have hlog : AnalyticAt ℂ (logDeriv g) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((riemannXiCanonicalResidual_decomp n).ne_zero z
          (ball_subset_closedBall hz))
    exact hlog.differentiableAt.differentiableWithinAt
  simpa [R, g] using hdiff.isExactOn_ball.with_val_at 0 0

/-- A fixed normalized analytic logarithm of the canonical residual. -/
noncomputable def riemannXiCanonicalLog (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_riemannXiCanonicalLog n)

@[simp] theorem riemannXiCanonicalLog_zero (n : ℕ) :
    riemannXiCanonicalLog n 0 = 0 :=
  (Classical.choose_spec (exists_riemannXiCanonicalLog n)).1

theorem riemannXiCanonicalLog_hasDerivAt
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    HasDerivAt (riemannXiCanonicalLog n)
      (logDeriv (riemannXiCanonicalResidual n) z) z :=
  (Classical.choose_spec (exists_riemannXiCanonicalLog n)).2 z hz

/-- Exponentiating the normalized primitive recovers the residual, with the
normalizing constant given by its value at zero. -/
theorem exp_riemannXiCanonicalLog_mul_zero_eq
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    Complex.exp (riemannXiCanonicalLog n z) *
        riemannXiCanonicalResidual n 0 =
      riemannXiCanonicalResidual n z := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  let q : ℂ → ℂ := (fun w => Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := by
    exact mem_ball_self (by simpa [R] using xiCanonicalRadius_pos n)
  have hqdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := riemannXiCanonicalLog_hasDerivAt n (by simpa [R] using hw)
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    exact (by
      simpa [q, L, g] using
        (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt
          |>.differentiableWithinAt)
  have hqderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := riemannXiCanonicalLog_hasDerivAt n (by simpa [R] using hw)
    have hg := (riemannXiCanonicalResidual_decomp n).analyticOnNhd w
      (ball_subset_closedBall (by simpa [R] using hw))
    have hqHas : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w +
          Complex.exp (-L w) * deriv g w) w := by
      simpa [q, L, g] using hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hqHas.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w +
      Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply]
    have hgne : g w ≠ 0 :=
      (riemannXiCanonicalResidual_decomp n).ne_zero w
        (ball_subset_closedBall (by simpa [R, g] using hw))
    rw [mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ hgne]
    ring
  have hqeq : q 0 = q z :=
    isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
      hqdiff hqderiv hzero (by simpa [R] using hz)
  have hg0eq : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, riemannXiCanonicalLog_zero] using hqeq
  change Complex.exp (L z) * g 0 = g z
  rw [hg0eq, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The checked xi growth bound becomes a uniform upper bound for the real
part of the normalized analytic logarithm. -/
theorem riemannXiCanonicalLog_re_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    (riemannXiCanonicalLog n z).re ≤
      A * (xiCanonicalRadius n + 1) ^ 2 := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  have hid := congrArg norm (exp_riemannXiCanonicalLog_mul_zero_eq n hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hgBound : ‖g z‖ ≤ Real.exp (A * (R + 1) ^ 2) := by
    apply norm_riemannXiCanonicalResidual_le_of_growth hA hbound n
    exact ball_subset_closedBall (by simpa [R] using hz)
  apply Real.exp_le_exp.mp
  calc
    Real.exp (L z).re = Real.exp (L z).re * 1 := by ring
    _ ≤ Real.exp (L z).re * ‖g 0‖ :=
      mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
    _ = ‖g z‖ := hid
    _ ≤ Real.exp (A * (R + 1) ^ 2) := hgBound

/-- Borel--Carathéodory converts the one-sided real-part estimate into a
norm bound for the normalized logarithm throughout the canonical disk. -/
theorem norm_riemannXiCanonicalLog_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalLog n z‖ ≤
      2 * (A * (xiCanonicalRadius n + 1) ^ 2) * ‖z‖ /
        (xiCanonicalRadius n - ‖z‖) := by
  let R := xiCanonicalRadius n
  let L := riemannXiCanonicalLog n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero (M := A * (R + 1) ^ 2)
    (by positivity) hdiff
  · intro w hw
    exact riemannXiCanonicalLog_re_le_of_growth hA hbound n
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact riemannXiCanonicalLog_zero n

/-- Cauchy's estimate turns the Borel--Carathéodory bound into a polynomial
bound for the logarithmic derivative of the zero-free residual on the inner
quarter of the canonical disk. -/
theorem norm_logDeriv_riemannXiCanonicalResidual_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ xiCanonicalRadius n / 4) :
    ‖logDeriv (riemannXiCanonicalResidual n) z‖ ≤
      (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
        (xiCanonicalRadius n / 4) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  let M := A * (R + 1) ^ 2
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hr : 0 < R / 4 := by positivity
  have hzball : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    have hquarter : R / 4 < R := by linarith
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    exact hz'.trans_lt hquarter
  have hglobalDiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  have hlocalSubset : closedBall z (R / 4) ⊆ ball 0 R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ R / 4 + R / 4 := by
        exact add_le_add hw (by simpa [R] using hz)
      _ < R := by linarith
  have hlocalDiff : DiffContOnCl ℂ L (ball z (R / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hr.ne']
    exact hglobalDiff.mono hlocalSubset
  have hboundary : ∀ w ∈ sphere z (R / 4), ‖L w‖ ≤ 2 * M := by
    intro w hw
    have hwclosed : w ∈ closedBall z (R / 4) := sphere_subset_closedBall hw
    have hwball : w ∈ ball 0 R := hlocalSubset hwclosed
    have hwnorm : ‖w‖ ≤ R / 2 := by
      rw [mem_closedBall, dist_eq_norm] at hwclosed
      calc
        ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ R / 4 + R / 4 := by
          exact add_le_add hwclosed (by simpa [R] using hz)
        _ = R / 2 := by ring
    have hL := norm_riemannXiCanonicalLog_le_of_growth hA hbound n
      (by simpa [R] using hwball)
    have hden : 0 < R - ‖w‖ := by linarith
    have hratio : ‖w‖ / (R - ‖w‖) ≤ 1 :=
      (div_le_one hden).mpr (by linarith)
    calc
      ‖L w‖ ≤ 2 * M * ‖w‖ / (R - ‖w‖) := by
        simpa [L, M, R] using hL
      _ = (2 * M) * (‖w‖ / (R - ‖w‖)) := by ring
      _ ≤ (2 * M) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * M := by ring
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hr hlocalDiff hboundary
  rw [(riemannXiCanonicalLog_hasDerivAt n
    (by simpa [R] using hzball)).deriv] at hcauchy
  simpa [R, g, M] using hcauchy

end

end RiemannGaussian
