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

/-! ## The finite canonical factors -/

/-- Pointwise logarithmic differentiation of a finitely supported product of
integer powers. The nonvanishing hypotheses permit negative powers. -/
lemma logDeriv_finprod_zpow_apply_of_finite
    {ι : Type*} {F : ι → ℂ → ℂ} {d : ι → ℤ}
    (hd : (Function.support d).Finite) {z : ℂ}
    (hFne : ∀ i, d i ≠ 0 → F i z ≠ 0)
    (hFdiff : ∀ i, d i ≠ 0 → DifferentiableAt ℂ (F i) z) :
    logDeriv (∏ᶠ i, F i ^ d i) z =
      ∑ᶠ i, d i • logDeriv (F i) z := by
  classical
  have h₀ : ∏ᶠ i, F i ^ d i =
      ∏ i ∈ hd.toFinset, F i ^ d i :=
    finprod_eq_prod_of_mulSupport_subset _ <| by
      simp +contextual [Set.subset_def, not_imp_not]
  have hsub : Function.support (fun i ↦ d i • logDeriv (F i) z) ⊆
      hd.toFinset := by
    simp +contextual [-Function.support_mul, -mul_eq_zero,
      Set.subset_def, not_imp_not]
  calc
    logDeriv (∏ᶠ i, F i ^ d i) z =
        logDeriv (fun w ↦ ∏ i ∈ hd.toFinset, (F i ^ d i) w) z := by
      rw [h₀, Finset.prod_fn]
    _ = ∑ i ∈ hd.toFinset, logDeriv (F i ^ d i) z :=
      logDeriv_prod (fun i hi ↦ zpow_ne_zero _ (hFne i (by simpa using hi)))
        (fun i hi ↦ (hFdiff i (by simpa using hi)).zpow
          (.inl (hFne i (by simpa using hi))))
    _ = ∑ i ∈ hd.toFinset, d i • logDeriv (F i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Pi.pow_def]
      simpa [zsmul_eq_mul] using
        logDeriv_fun_zpow (hFdiff i (by simpa using hi)) (d i)
    _ = ∑ᶠ i, d i • logDeriv (F i) z :=
      (finsum_eq_sum_of_support_subset _ hsub).symm

/-- Exact logarithmic derivative of one canonical factor away from its pole. -/
lemma logDeriv_canonicalFactor_eq
    {R : ℝ} (hR : 0 < R) {i z : ℂ}
    (hi : i ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzi : z ≠ i) :
    logDeriv (Complex.canonicalFactor R i) z =
      (-starRingEnd ℂ i) / ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * z) -
        1 / (z - i) := by
  have hfactor : Complex.canonicalFactor R i z ≠ 0 :=
    Complex.canonicalFactor_ne_zero hi hz hzi
  have hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ i) * z ≠ 0 := by
    rw [Complex.canonicalFactor_apply, div_ne_zero_iff] at hfactor
    exact hfactor.1
  have hden : (R : ℂ) * (z - i) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hR.ne'
    · exact sub_ne_zero.mpr hzi
  have hnumderiv :
      deriv (fun w : ℂ ↦ (R : ℂ) ^ 2 - (starRingEnd ℂ i) * w) z =
        -starRingEnd ℂ i := by
    rw [deriv_fun_sub (by fun_prop) (by fun_prop)]
    simp
  have hdenderiv :
      deriv (fun w : ℂ ↦ (R : ℂ) * (w - i)) z = (R : ℂ) := by
    rw [deriv_const_mul_field, deriv_sub_const]
    simp
  rw [show Complex.canonicalFactor R i =
      fun w ↦ ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * w) /
        ((R : ℂ) * (w - i)) by rfl]
  rw [logDeriv_div z hnum hden (by fun_prop) (by fun_prop)]
  simp only [logDeriv_apply]
  rw [hnumderiv, hdenderiv]
  field_simp [hR.ne', hzi]

/-- On the inner quarter-disk, a canonical factor's logarithmic derivative
is controlled by a radial term and the reciprocal distance to its pole. -/
lemma norm_logDeriv_canonicalFactor_le
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {i z : ℂ}
    (hi : i ∈ ball 0 R) (hz : ‖z‖ ≤ R / 4)
    (hsep : δ ≤ ‖z - i‖) :
    ‖logDeriv (Complex.canonicalFactor R i) z‖ ≤ 2 / R + 1 / δ := by
  have hzi : z ≠ i := by
    intro h
    subst z
    simp at hsep
    linarith
  have hzclosed : z ∈ closedBall 0 R := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  rw [logDeriv_canonicalFactor_eq hR hi hzclosed hzi]
  have hiNorm : ‖i‖ ≤ R := by
    have hi' : ‖i‖ < R := by simpa [mem_ball, dist_zero_right] using hi
    exact hi'.le
  have hstar : ‖(starRingEnd ℂ) i‖ = ‖i‖ := by
    change ‖star i‖ = ‖i‖
    exact norm_star i
  have hprod : ‖(starRingEnd ℂ i) * z‖ ≤ R ^ 2 / 4 := by
    rw [norm_mul, hstar]
    calc
      ‖i‖ * ‖z‖ ≤ R * (R / 4) :=
        mul_le_mul hiNorm hz (norm_nonneg _) hR.le
      _ = R ^ 2 / 4 := by ring
  have hnumLower : R ^ 2 / 2 ≤
      ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ := by
    calc
      R ^ 2 / 2 ≤ R ^ 2 - ‖(starRingEnd ℂ i) * z‖ := by
        nlinarith [hprod]
      _ = ‖(R : ℂ) ^ 2‖ - ‖(starRingEnd ℂ i) * z‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      _ ≤ ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ :=
        norm_sub_norm_le _ _
  have hnumPos : 0 < ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ :=
    lt_of_lt_of_le (by positivity : 0 < R ^ 2 / 2) hnumLower
  have hfirst :
      ‖-starRingEnd ℂ i‖ /
          ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ ≤ 2 / R := by
    rw [norm_neg, hstar, div_le_iff₀ hnumPos]
    calc
      ‖i‖ ≤ R := hiNorm
      _ = (2 / R) * (R ^ 2 / 2) := by field_simp
      _ ≤ (2 / R) *
          ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ :=
        mul_le_mul_of_nonneg_left hnumLower (by positivity)
  have hsecond : 1 / ‖z - i‖ ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ hsep
  calc
    ‖(-starRingEnd ℂ i) /
          ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * z) -
        1 / (z - i)‖ ≤
        ‖(-starRingEnd ℂ i) /
          ((R : ℂ) ^ 2 - (starRingEnd ℂ i) * z)‖ +
            ‖1 / (z - i)‖ := norm_sub_le _ _
    _ = ‖-starRingEnd ℂ i‖ /
          ‖(R : ℂ) ^ 2 - (starRingEnd ℂ i) * z‖ +
            1 / ‖z - i‖ := by
      rw [norm_div, norm_div, norm_one]
    _ ≤ 2 / R + 1 / δ := add_le_add hfirst hsecond

/-- Because the selected canonical circle contains no xi zero, the open- and
closed-ball xi divisors agree pointwise. -/
lemma divisor_riemannXi_ball_eq_closedBall (n : ℕ) (z : ℂ) :
    divisor riemannXi (ball 0 (xiCanonicalRadius n)) z =
      divisor riemannXi (closedBall 0 (xiCanonicalRadius n)) z := by
  classical
  let R := xiCanonicalRadius n
  have hR : 0 < R := xiCanonicalRadius_pos n
  by_cases hb : z ∈ ball (0 : ℂ) R
  · rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hb,
      (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply
        (ball_subset_closedBall hb)]
  · by_cases hc : z ∈ closedBall (0 : ℂ) R
    · have hnorm : ‖z‖ = R := by
        rw [mem_ball, dist_zero_right] at hb
        rw [mem_closedBall, dist_zero_right] at hc
        exact le_antisymm hc (le_of_not_gt hb)
      have hxi : riemannXi z ≠ 0 :=
        (xiCanonicalRadius_spec n).2.2 z (by
          simpa [mem_sphere, dist_zero_right, R] using hnorm)
      have horder : meromorphicOrderAt riemannXi z = 0 :=
        (analyticAt_riemannXi z).meromorphicNFAt
          |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
      rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb,
        (analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply hc]
      simp [horder]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]

/-- Every nonzero coefficient in an interior xi divisor is supported at an
actual xi zero. -/
lemma riemannXi_eq_zero_of_divisor_ball_ne_zero
    {R : ℝ} {i : ℂ} (hi : divisor riemannXi (ball 0 R) i ≠ 0) :
    riemannXi i = 0 := by
  have himem : i ∈ ball (0 : ℂ) R :=
    (divisor riemannXi (ball 0 R)).supportWithinDomain hi
  by_contra hxi
  apply hi
  have horder : meromorphicOrderAt riemannXi i = 0 :=
    (analyticAt_riemannXi i).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  rw [(analyticOnNhd_riemannXi.mono (subset_univ _)).meromorphicOn.divisor_apply himem]
  simp [horder]

/-- Inside the canonical disk, away from a zero of xi, its logarithmic
derivative is the residual logarithmic derivative minus the finite sum of
the enclosed canonical zero factors. -/
theorem logDeriv_riemannXi_eq_residual_sub_canonical_sum
    (n : ℕ) {z : ℂ}
    (hz : z ∈ ball 0 (xiCanonicalRadius n)) (hxi : riemannXi z ≠ 0) :
    logDeriv riemannXi z =
      logDeriv (riemannXiCanonicalResidual n) z -
        ∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
          logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) z := by
  classical
  let R := xiCanonicalRadius n
  let d : ℂ → ℤ := fun i => divisor riemannXi (ball 0 R) i
  let P : ℂ → ℂ := ∏ᶠ i, Complex.canonicalFactor R i ^ d i
  let g := riemannXiCanonicalResidual n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdFinite : (Function.support d).Finite := by
    simpa [d] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hmulSupport : (fun i =>
      Complex.canonicalFactor R i ^ d i).HasFiniteMulSupport := by
    apply Set.Finite.subset hdFinite
    intro i hi
    by_contra hdi
    have hdi0 : d i = 0 := by simpa [Function.mem_support] using hdi
    simp [hdi0] at hi
  have hzeroOfSupport {i : ℂ} (hi : d i ≠ 0) : riemannXi i = 0 :=
    riemannXi_eq_zero_of_divisor_ball_ne_zero (by simpa [d] using hi)
  have himem {i : ℂ} (hi : d i ≠ 0) : i ∈ ball (0 : ℂ) R :=
    (divisor riemannXi (ball 0 R)).supportWithinDomain (by simpa [d] using hi)
  have hzi {i : ℂ} (hi : d i ≠ 0) : z ≠ i := by
    intro h
    subst i
    exact hxi (hzeroOfSupport hi)
  have hfactorNe {i : ℂ} (hi : d i ≠ 0) :
      Complex.canonicalFactor R i z ≠ 0 :=
    Complex.canonicalFactor_ne_zero (himem hi)
      (ball_subset_closedBall (by simpa [R] using hz)) (hzi hi)
  have hfactorDiff {i : ℂ} (hi : d i ≠ 0) :
      DifferentiableAt ℂ (Complex.canonicalFactor R i) z :=
    (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).differentiableAt
  have hPAnalytic : AnalyticAt ℂ P z := by
    dsimp [P]
    apply analyticAt_finprod
    intro i
    by_cases hi : d i = 0
    · rw [hi]
      change AnalyticAt ℂ (fun _ : ℂ ↦ (1 : ℂ)) z
      exact analyticAt_const
    · exact (Complex.analyticOnNhd_canonicalFactor R i z (hzi hi)).zpow
        (hfactorNe hi)
  have hPne : P z ≠ 0 := by
    dsimp [P]
    apply finprod_apply_ne_zero
    intro i
    by_cases hi : d i = 0
    · simp [hi]
    · exact zpow_ne_zero _ (hfactorNe hi)
  have hfactorEq : g =ᶠ[nhds z] P * riemannXi := by
    have hball : ball (0 : ℂ) R ∈ nhds z :=
      isOpen_ball.mem_nhds (by simpa [R] using hz)
    have hxiNe : ∀ᶠ w in nhds z, riemannXi w ≠ 0 :=
      (analyticAt_riemannXi z).continuousAt.eventually_ne hxi
    filter_upwards [hball, hxiNe] with w hw hwxi
    have horder : meromorphicOrderAt riemannXi w = 0 :=
      (analyticAt_riemannXi w).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hwxi
    have heq := (riemannXiCanonicalResidual_decomp n)
      |>.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
        (ball_subset_closedBall hw) horder hR
    have htrailing : meromorphicTrailingCoeffAt riemannXi w = riemannXi w :=
      (analyticAt_riemannXi w).meromorphicTrailingCoeffAt_of_ne_zero hwxi
    change g w = (P * riemannXi) w
    simpa [P, d, g, R,
      divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n,
      htrailing, finprod_apply hmulSupport] using heq
  have hproductLog :
      logDeriv P z = ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z := by
    dsimp [P]
    exact logDeriv_finprod_zpow_apply_of_finite hdFinite
      (fun i hi => hfactorNe hi) (fun i hi => hfactorDiff hi)
  have hmul := logDeriv_mul (f := P) (g := riemannXi) z
    hPne hxi hPAnalytic.differentiableAt (differentiable_riemannXi z)
  have hlog : logDeriv g z = logDeriv P z + logDeriv riemannXi z := by
    rw [(logDeriv_congr_nhds hfactorEq).self_of_nhds]
    exact hmul
  rw [hproductLog] at hlog
  change logDeriv riemannXi z = logDeriv g z -
    ∑ᶠ i, d i • logDeriv (Complex.canonicalFactor R i) z
  rw [hlog]
  ring

/-- A finitely supported sum of complex vectors with nonnegative integer
weights is bounded by the total weight times a uniform pointwise bound. -/
lemma norm_finsum_zsmul_le_of_nonneg
    {ι : Type*} {d : ι → ℤ} {f : ι → ℂ}
    (hd : (Function.support d).Finite)
    (hdnonneg : ∀ i, 0 ≤ d i) {C : ℝ}
    (hf : ∀ i, d i ≠ 0 → ‖f i‖ ≤ C) :
    ‖∑ᶠ i, d i • f i‖ ≤ ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
  classical
  have hsub : Function.support (fun i => d i • f i) ⊆ hd.toFinset := by
    intro i hi
    apply hd.mem_toFinset.mpr
    intro hdi
    apply hi
    simp [hdi]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  calc
    ‖∑ i ∈ hd.toFinset, d i • f i‖ ≤
        ∑ i ∈ hd.toFinset, ‖d i • f i‖ := norm_sum_le _ _
    _ = ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * ‖f i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_zsmul ℂ]
      rw [Complex.norm_int_of_nonneg (hdnonneg i)]
    _ ≤ ∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ) * C := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hdi : d i = 0
      · simp [hdi]
      · exact mul_le_mul_of_nonneg_left (hf i hdi) (by
          exact_mod_cast hdnonneg i)
    _ = (∑ i ∈ hd.toFinset, ((d i : ℤ) : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ = (∑ᶠ i, ((d i : ℤ) : ℝ)) * C := by
      congr 1
      symm
      exact finsum_eq_sum_of_support_subset _ (by
        intro i hi
        apply hd.mem_toFinset.mpr
        intro hdi
        apply hi
        simp [hdi])
    _ = ((∑ᶠ i, d i : ℤ) : ℝ) * C := by
      congr 1
      exact (map_finsum (Int.castRingHom ℝ) hd).symm

/-- Jensen's checked zero count bounds the total multiplicity of the interior
canonical divisor. -/
theorem sum_divisor_riemannXi_ball_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    ((∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤
      A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2 := by
  have heq :
      (∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i) =
        ∑ᶠ i, divisor riemannXi (closedBall 0 (xiCanonicalRadius n)) i := by
    apply finsum_congr
    intro i
    exact divisor_riemannXi_ball_eq_closedBall n i
  rw [heq]
  exact_mod_cast jensen_riemannXi_divisor_le hA
    (xiCanonicalRadius_pos n) hbound

/-- The full finite canonical-factor contribution is explicitly bounded by
the Jensen zero count times the reciprocal contour separation. -/
theorem norm_canonicalLogDerivSum_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : ‖z‖ ≤ xiCanonicalRadius n / 4)
    (hsep : ∀ i,
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 →
        δ ≤ ‖z - i‖) :
    ‖∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
        logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) z‖ ≤
      (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
        (2 / xiCanonicalRadius n + 1 / δ) := by
  let R := xiCanonicalRadius n
  let d : ℂ → ℤ := fun i => divisor riemannXi (ball 0 R) i
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdFinite : (Function.support d).Finite := by
    simpa [d] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  have hraw := norm_finsum_zsmul_le_of_nonneg hdFinite hdnonneg
    (C := 2 / R + 1 / δ)
    (fun i hi => norm_logDeriv_canonicalFactor_le hR hδ
      ((divisor riemannXi (ball 0 R)).supportWithinDomain
        (by simpa [d] using hi))
      (by simpa [R] using hz) (hsep i (by simpa [d, R] using hi)))
  have hcount := sum_divisor_riemannXi_ball_le_of_growth hA hbound n
  have hC : 0 ≤ 2 / R + 1 / δ := by positivity
  calc
    ‖∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
        logDeriv (Complex.canonicalFactor (xiCanonicalRadius n) i) z‖ ≤
        ((∑ᶠ i, divisor riemannXi
          (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) *
            (2 / xiCanonicalRadius n + 1 / δ) := by
      simpa [d, R] using hraw
    _ ≤ (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
        (2 / xiCanonicalRadius n + 1 / δ) :=
      mul_le_mul_of_nonneg_right (by simpa [R] using hcount)
        (by simpa [R] using hC)

/-! ## Transfer to the quantitatively separated spectral contours -/

/-- The affine completed/spectral coordinate equivalence is an isometry for
differences. -/
lemma norm_completedSpectralCoordinate_sub (z s : ℂ) :
    ‖completedSpectralCoordinate z - s‖ =
      ‖z - zetaSpectralCoordinate s‖ := by
  have h : completedSpectralCoordinate z - s =
      Complex.I * (z - zetaSpectralCoordinate s) := by
    unfold completedSpectralCoordinate zetaSpectralCoordinate
    ring_nf
    simp
    ring
  rw [h, norm_mul, Complex.norm_I, one_mul]

/-- Quantitative separation in the spectral coordinate transfers exactly to
the completed coordinate used by `riemannXi`. -/
theorem spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero
    (n : ℕ) (y : ℝ) {i : ℂ}
    (hi : divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0) :
    spectralBoundarySeparation n ≤
      ‖completedSpectralCoordinate
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I) - i‖ := by
  let ρ : NontrivialZetaZero :=
    ⟨i, (riemannXi_eq_zero_iff_isNontrivialZetaZero i).mp
      (riemannXi_eq_zero_of_divisor_ball_ne_zero hi)⟩
  calc
    spectralBoundarySeparation n ≤
        ‖((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I) - zetaSpectralCoordinate ρ.1‖ :=
      quantitativeSpectralBoundaryTruncation_dist_zero_ge n y ρ
    _ = ‖completedSpectralCoordinate
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I) - i‖ := by
      symm
      exact norm_completedSpectralCoordinate_sub _ i

/-- No point on a quantitatively separated vertical segment maps to a xi
zero. -/
theorem riemannXi_quantitativeCompletedCoordinate_ne_zero
    (n : ℕ) (y : ℝ) :
    riemannXi (completedSpectralCoordinate
      ((quantitativeSpectralBoundaryTruncation n : ℂ) +
        (y : ℂ) * Complex.I)) ≠ 0 := by
  let w : ℂ := (quantitativeSpectralBoundaryTruncation n : ℂ) +
    (y : ℂ) * Complex.I
  by_contra hxi
  let ρ : NontrivialZetaZero :=
    ⟨completedSpectralCoordinate w,
      (riemannXi_eq_zero_iff_isNontrivialZetaZero _).mp (by
        simpa [w] using hxi)⟩
  have hsep := quantitativeSpectralBoundaryTruncation_dist_zero_ge n y ρ
  have hcoord : zetaSpectralCoordinate ρ.1 = w := by
    simp [ρ]
  rw [hcoord] at hsep
  simp [w] at hsep
  exact (not_lt_of_ge hsep) (spectralBoundarySeparation_pos n)

/-- The whole selected unit-height spectral segment maps inside the inner
quarter of the much larger canonical disk. -/
theorem norm_quantitativeCompletedCoordinate_le_quarter
    (n : ℕ) {y : ℝ} (hylo : -1 ≤ y) (hyhi : y ≤ 1) :
    ‖completedSpectralCoordinate
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ ≤ xiCanonicalRadius n / 4 := by
  let T := quantitativeSpectralBoundaryTruncation n
  let s := completedSpectralCoordinate ((T : ℂ) + (y : ℂ) * Complex.I)
  have hTnonneg : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hThi : T < (n : ℝ) + 1 :=
    (quantitativeSpectralBoundaryTruncation_spec n).2.1
  have hyabs : |y| ≤ 1 := (abs_le).mpr ⟨hylo, hyhi⟩
  have hsreval : s.re = 1 / 2 - y := by
    dsimp [s, completedSpectralCoordinate]
    simp
    ring
  have hsre : |s.re| ≤ 3 / 2 := by
    rw [hsreval]
    calc
      |1 / 2 - y| ≤ |1 / 2| + |y| := abs_sub _ _
      _ ≤ 1 / 2 + 1 := by
        norm_num only [abs_of_nonneg]
        linarith
      _ = 3 / 2 := by norm_num
  have hsim : |s.im| = T := by
    have hsimval : s.im = T := by
      dsimp [s, completedSpectralCoordinate]
      simp
    rw [hsimval, abs_of_nonneg hTnonneg]
  have hRquarter : (n : ℝ) + 3 < xiCanonicalRadius n / 4 := by
    have hR := (xiCanonicalRadius_spec n).1
    linarith
  change ‖s‖ ≤ xiCanonicalRadius n / 4
  apply le_of_lt
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 3 / 2 + T := by rw [hsim]; exact add_le_add hsre le_rfl
    _ < (n : ℝ) + 3 := by linarith
    _ < xiCanonicalRadius n / 4 := hRquarter

/-- Combining the residual estimate, Jensen count, and quantitative zero
separation gives an explicit polynomial expression bounding xi's logarithmic
derivative on every selected vertical segment. -/
theorem norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) {y : ℝ} (hylo : -1 ≤ y) (hyhi : y ≤ 1) :
    ‖logDeriv riemannXi
        (completedSpectralCoordinate
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I))‖ ≤
      (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4) +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          (2 / xiCanonicalRadius n +
            1 / spectralBoundarySeparation n) := by
  let R := xiCanonicalRadius n
  let w : ℂ := (quantitativeSpectralBoundaryTruncation n : ℂ) +
    (y : ℂ) * Complex.I
  let s := completedSpectralCoordinate w
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hsquarter : ‖s‖ ≤ R / 4 := by
    simpa [s, w, R] using
      norm_quantitativeCompletedCoordinate_le_quarter n hylo hyhi
  have hsball : s ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    exact hsquarter.trans_lt (by linarith)
  have hxi : riemannXi s ≠ 0 := by
    simpa [s, w] using
      riemannXi_quantitativeCompletedCoordinate_ne_zero n y
  have hdecomp := logDeriv_riemannXi_eq_residual_sub_canonical_sum n
    (by simpa [R] using hsball) hxi
  have hres := norm_logDeriv_riemannXiCanonicalResidual_le_of_growth
    hA hbound n (by simpa [s, R] using hsquarter)
  have hsum := norm_canonicalLogDerivSum_le_of_growth hA hbound n
    (spectralBoundarySeparation_pos n) (by simpa [s, R] using hsquarter)
    (fun i hi => by
      simpa [s, w, R] using
        spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero n y
          (by simpa [R] using hi))
  calc
    ‖logDeriv riemannXi s‖ =
        ‖logDeriv (riemannXiCanonicalResidual n) s -
          ∑ᶠ i, divisor riemannXi (ball 0 R) i •
            logDeriv (Complex.canonicalFactor R i) s‖ := by
      rw [hdecomp]
    _ ≤ ‖logDeriv (riemannXiCanonicalResidual n) s‖ +
        ‖∑ᶠ i, divisor riemannXi (ball 0 R) i •
          logDeriv (Complex.canonicalFactor R i) s‖ := norm_sub_le _ _
    _ ≤ (2 * (A * (R + 1) ^ 2)) / (R / 4) +
        (A * (2 * R + 1) ^ 2 / Real.log 2) *
          (2 / R + 1 / spectralBoundarySeparation n) :=
      add_le_add (by simpa [R, s] using hres) (by simpa [R, s] using hsum)

/-- The spectral negative logarithmic derivative has the same norm as xi's
ordinary logarithmic derivative at the corresponding completed coordinate. -/
@[simp] lemma norm_xiSpectralNegativeLogDerivative (z : ℂ) :
    ‖xiSpectralNegativeLogDerivative z‖ =
      ‖logDeriv riemannXi (completedSpectralCoordinate z)‖ := by
  simp [xiSpectralNegativeLogDerivative, logDeriv_apply, norm_neg]

/-- A deliberately coarse but explicit exponential majorant for the
polynomial contour estimate.  The exponent `4` reflects the product of two
quadratic zero-count bounds. -/
theorem explicit_logDeriv_bound_le_exponential
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2))
    (n : ℕ) :
    (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4) +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          (2 / xiCanonicalRadius n +
            1 / spectralBoundarySeparation n) ≤
      (392 * A + 729 * (A / Real.log 2) *
          (13 + 75 * (A / Real.log 2))) *
        Real.exp (4 * quantitativeSpectralBoundaryTruncation n) := by
  let R := xiCanonicalRadius n
  let T := quantitativeSpectralBoundaryTruncation n
  let E := Real.exp T
  let B := A / Real.log 2
  let X := 2 * ((n : ℝ) + 2) + 1
  have hA0 : 0 ≤ A := (by linarith : 0 ≤ A)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT0 : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (quantitativeSpectralBoundaryTruncation_spec n).1.le
  have hEpos : 0 < E := by dsimp [E]; positivity
  have hEone : 1 ≤ E := by
    dsimp [E]
    exact Real.one_le_exp hT0
  have hE2one : 1 ≤ E ^ 2 := by nlinarith [sq_nonneg (E - 1)]
  have hE2nonneg : 0 ≤ E ^ 2 := sq_nonneg E
  have hE2E4 : E ^ 2 ≤ E ^ 4 := by
    calc
      E ^ 2 = E ^ 2 * 1 := by ring
      _ ≤ E ^ 2 * E ^ 2 :=
        mul_le_mul_of_nonneg_left hE2one hE2nonneg
      _ = E ^ 4 := by ring
  have hTexp : T + 1 ≤ E := by
    simpa [E] using Real.add_one_le_exp T
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hRupper : R ≤ 4 * T + 13 := by
    have hr := (xiCanonicalRadius_spec n).2.1
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [R, T]
    linarith
  have hRfour : 1 ≤ R / 4 := by
    have hr := (xiCanonicalRadius_spec n).1
    have hn : 0 ≤ (n : ℝ) := by positivity
    dsimp [R]
    linarith
  have hR1 : R + 1 ≤ 14 * E := by
    calc
      R + 1 ≤ 4 * T + 14 := by linarith
      _ ≤ 14 * (T + 1) := by linarith
      _ ≤ 14 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have htwoR1 : 2 * R + 1 ≤ 27 * E := by
    calc
      2 * R + 1 ≤ 8 * T + 27 := by linarith
      _ ≤ 27 * (T + 1) := by linarith
      _ ≤ 27 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hX : X ≤ 5 * E := by
    calc
      X ≤ 2 * T + 5 := by
        have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
        dsimp [X, T]
        linarith
      _ ≤ 5 * (T + 1) := by linarith
      _ ≤ 5 * E := mul_le_mul_of_nonneg_left hTexp (by norm_num)
  have hR1sq : (R + 1) ^ 2 ≤ (14 * E) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hR1
  have htwoR1sq : (2 * R + 1) ^ 2 ≤ (27 * E) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr htwoR1
  have hXsq : X ^ 2 ≤ (5 * E) ^ 2 :=
    (sq_le_sq₀ hX0 (by positivity)).mpr hX
  have hresidual :
      (2 * (A * (R + 1) ^ 2)) / (R / 4) ≤
        392 * A * E ^ 2 := by
    let N := 2 * (A * (R + 1) ^ 2)
    have hN : 0 ≤ N := by dsimp [N]; positivity
    calc
      (2 * (A * (R + 1) ^ 2)) / (R / 4) = N / (R / 4) := rfl
      _ ≤ N := (div_le_iff₀ (by positivity : 0 < R / 4)).mpr (by
        calc
          N = N * 1 := by ring
          _ ≤ N * (R / 4) := mul_le_mul_of_nonneg_left hRfour hN)
      _ ≤ 2 * A * (14 * E) ^ 2 := by
        dsimp [N]
        calc
          2 * (A * (R + 1) ^ 2) = (2 * A) * (R + 1) ^ 2 := by ring
          _ ≤ (2 * A) * (14 * E) ^ 2 :=
            mul_le_mul_of_nonneg_left hR1sq (by positivity)
          _ = 2 * A * (14 * E) ^ 2 := by ring
      _ = 392 * A * E ^ 2 := by ring
  have hcountFactor :
      A * (2 * R + 1) ^ 2 / Real.log 2 ≤
        729 * B * E ^ 2 := by
    calc
      A * (2 * R + 1) ^ 2 / Real.log 2 =
          B * (2 * R + 1) ^ 2 := by dsimp [B]; ring
      _ ≤ B * (27 * E) ^ 2 :=
        mul_le_mul_of_nonneg_left htwoR1sq hB
      _ = 729 * B * E ^ 2 := by ring
  have hsepRaw :=
    one_div_spectralBoundarySeparation_le_of_growth hA hbound n
  have hsep :
      1 / spectralBoundarySeparation n ≤
        3 * (25 * B * E ^ 2 + 4) := by
    calc
      1 / spectralBoundarySeparation n ≤
          3 * (A * X ^ 2 / Real.log 2 + 4) := by
        simpa [X] using hsepRaw
      _ = 3 * (B * X ^ 2 + 4) := by dsimp [B]; ring
      _ ≤ 3 * (B * (5 * E) ^ 2 + 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add (mul_le_mul_of_nonneg_left hXsq hB) le_rfl
      _ = 3 * (25 * B * E ^ 2 + 4) := by ring
  have htwoDiv : 2 / R ≤ 1 :=
    (div_le_one hR).mpr (by linarith)
  have hsecond :
      2 / R + 1 / spectralBoundarySeparation n ≤
        (13 + 75 * B) * E ^ 2 := by
    calc
      2 / R + 1 / spectralBoundarySeparation n ≤
          1 + 3 * (25 * B * E ^ 2 + 4) := add_le_add htwoDiv hsep
      _ = 13 + 75 * B * E ^ 2 := by ring
      _ ≤ 13 * E ^ 2 + 75 * B * E ^ 2 := by
        have h13 : 13 ≤ 13 * E ^ 2 := by nlinarith
        exact add_le_add h13 le_rfl
      _ = (13 + 75 * B) * E ^ 2 := by ring
  have hcanonical :
      (A * (2 * R + 1) ^ 2 / Real.log 2) *
          (2 / R + 1 / spectralBoundarySeparation n) ≤
        729 * B * (13 + 75 * B) * E ^ 4 := by
    have hsecond0 :
        0 ≤ 2 / R + 1 / spectralBoundarySeparation n := by
      have hsepPos := spectralBoundarySeparation_pos n
      positivity
    calc
      (A * (2 * R + 1) ^ 2 / Real.log 2) *
          (2 / R + 1 / spectralBoundarySeparation n) ≤
          (729 * B * E ^ 2) * ((13 + 75 * B) * E ^ 2) :=
        mul_le_mul hcountFactor hsecond hsecond0 (by positivity)
      _ = 729 * B * (13 + 75 * B) * E ^ 4 := by ring
  have hpoly :
      (2 * (A * (R + 1) ^ 2)) / (R / 4) +
          (A * (2 * R + 1) ^ 2 / Real.log 2) *
            (2 / R + 1 / spectralBoundarySeparation n) ≤
        (392 * A + 729 * B * (13 + 75 * B)) * E ^ 4 := by
    calc
      (2 * (A * (R + 1) ^ 2)) / (R / 4) +
          (A * (2 * R + 1) ^ 2 / Real.log 2) *
            (2 / R + 1 / spectralBoundarySeparation n) ≤
          392 * A * E ^ 2 +
            729 * B * (13 + 75 * B) * E ^ 4 :=
        add_le_add hresidual hcanonical
      _ ≤ 392 * A * E ^ 4 +
          729 * B * (13 + 75 * B) * E ^ 4 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hE2E4 (by positivity)) le_rfl
      _ = (392 * A + 729 * B * (13 + 75 * B)) * E ^ 4 := by ring
  have hEpow : E ^ 4 = Real.exp (4 * T) := by
    simpa [E] using (Real.exp_nat_mul T 4).symm
  simpa [R, T, B, hEpow] using hpoly

/-- Xi's logarithmic derivative satisfies the exponential bound required by
the Gaussian vertical-decay theorem.  This discharges the last analytic
predicate that had previously been left as an assumption. -/
theorem xiSpectralVerticalLogDerivativeExponentialBound :
    XiSpectralVerticalLogDerivativeExponentialBound := by
  rcases riemannXi_quadraticGrowth with ⟨A, hA, hbound⟩
  let B := A / Real.log 2
  let C := 392 * A + 729 * B * (13 + 75 * B)
  have hA0 : 0 ≤ A := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg hA0 (Real.log_pos (by norm_num)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply xiSpectralVerticalLogDerivativeExponentialBound_of_quantitative
    (C := C) (A := 4) hC
  intro n y hylo hyhi
  calc
    ‖xiSpectralNegativeLogDerivative
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ =
        ‖logDeriv riemannXi
          (completedSpectralCoordinate
            ((quantitativeSpectralBoundaryTruncation n : ℂ) +
              (y : ℂ) * Complex.I))‖ :=
      norm_xiSpectralNegativeLogDerivative _
    _ ≤ (2 * (A * (xiCanonicalRadius n + 1) ^ 2)) /
          (xiCanonicalRadius n / 4) +
        (A * (2 * xiCanonicalRadius n + 1) ^ 2 / Real.log 2) *
          (2 / xiCanonicalRadius n +
            1 / spectralBoundarySeparation n) :=
      norm_logDeriv_riemannXi_quantitativeCompletedCoordinate_le_of_growth
        hA hbound n hylo hyhi
    _ ≤ C * Real.exp
        (4 * quantitativeSpectralBoundaryTruncation n) := by
      simpa [C, B] using explicit_logDeriv_bound_le_exponential hA hbound n

/-! ## Unconditional Gaussian explicit formula and the positivity frontier -/

/-- The arithmetic Gaussian explicit formula is unconditionally identified
with the canonical multiplicity-aware symmetric zero sum. -/
theorem gaussianArithmeticExplicitFormulaIdentified :
    GaussianArithmeticExplicitFormulaIdentified :=
  gaussianArithmeticExplicitFormulaIdentified_of_logDerivativeExponentialBound
    xiSpectralVerticalLogDerivativeExponentialBound

/-- Pointwise form of the now-unconditional arithmetic/canonical Gaussian
explicit formula. -/
theorem gaussianArithmeticExplicitFormula_eq_canonical
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianArithmeticExplicitFormula ε t =
      canonicalZetaSymmetricGaussianZeroSum ε t :=
  gaussianArithmeticExplicitFormulaIdentified ε t hε

/-- This is the requested pre-positivity checkpoint: proving nonnegativity of
the fully explicit arithmetic expression for every positive Gaussian width
and every center is now exactly equivalent to the Riemann hypothesis. -/
theorem gaussianArithmeticExplicitFormula_nonnegative_iff_riemannHypothesis :
    ZetaSymmetricGaussianZeroSumNonnegative
        gaussianArithmeticExplicitFormula ↔
      RiemannHypothesis :=
  gaussianArithmeticExplicitFormula_nonnegative_iff_RH
    gaussianArithmeticExplicitFormulaIdentified

/-- Unconditional cofinal-width reduction of the remaining positivity
frontier: it suffices, and is necessary, to certify good widths unboundedly
far out. -/
theorem gaussianArithmeticGoodWidthsUnbounded_iff_riemannHypothesis :
    GaussianArithmeticGoodWidthsUnbounded ↔ RiemannHypothesis :=
  gaussianArithmeticGoodWidthsUnbounded_iff_RH
    gaussianArithmeticExplicitFormulaIdentified

end

end RiemannGaussian
