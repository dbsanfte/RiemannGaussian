import RiemannGaussian.GaussianXiLogLinearGrowth
import RiemannGaussian.RiemannXiSuzukiWeilVertical
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaLowerSubquadratic

/-!
# Near-linear lower control at the critical zeta endpoints

This module propagates the unconditional `exp(O(R log R))` growth of xi
through Jensen counting, quantitative contour separation, and the zero-free
canonical residual. The resulting explicit lower exponent is bounded by
`O(T log² T)` along the selected endpoints.

Consequently, for every fixed positive `epsilon`, Lean proves that the
negative part of `log |zeta(1/2 + iT_n)|`, divided by
`(T_n + 1)^(1 + epsilon)`, tends to zero. This improves the former fixed
quadratic normalization to every power strictly above one. It does not prove
the remaining `o(T)` frontier: eliminating the two logarithmic losses still
requires cancellation or rigidity not supplied by radial growth and pointwise
zero separation.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Log-linear xi growth bounds the number of distinct zeros in every
spectral window. -/
theorem spectralZetaZeroWindow_card_le_logLinear_of_growth
    {A T : ℝ} (hA : 1 ≤ A) (hT : 0 ≤ T)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1))) :
    ((spectralZetaZeroWindow T).card : ℝ) ≤
      A * xiLogLinearScale (2 * (T + 1) + 1) / Real.log 2 := by
  exact (spectralZetaZeroWindow_card_le_riemannXi_divisor hT).trans
    (by
      simpa using jensen_riemannXi_divisor_le_logLinear hA
        (by linarith : 0 < T + 1) hbound)

/-- The selected canonical disk inherits the multiplicity-aware log-linear
xi-divisor bound. -/
theorem sum_divisor_riemannXi_ball_le_logLinear_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) :
    ((∑ᶠ i, divisor riemannXi
        (ball 0 (xiCanonicalRadius n)) i : ℤ) : ℝ) ≤
      A * xiLogLinearScale (2 * xiCanonicalRadius n + 1) /
        Real.log 2 := by
  have heq :
      (∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i) =
        ∑ᶠ i, divisor riemannXi
          (closedBall 0 (xiCanonicalRadius n)) i := by
    apply finsum_congr
    intro i
    exact divisor_riemannXi_ball_eq_closedBall n i
  rw [heq]
  exact_mod_cast jensen_riemannXi_divisor_le_logLinear hA
    (xiCanonicalRadius_pos n) hbound

/-- The reciprocal selected-boundary separation is controlled at the
log-linear zero-count scale. -/
theorem one_div_spectralBoundarySeparation_le_logLinear_of_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) :
    1 / spectralBoundarySeparation n ≤
      3 *
        (A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
            Real.log 2 + 4) := by
  have hwindow := spectralZetaZeroWindow_card_le_logLinear_of_growth hA
    (show 0 ≤ (n : ℝ) + 1 by positivity) hbound
  have hwindow' :
      ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) ≤
        A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
          Real.log 2 := by
    convert hwindow using 1
    ring_nf
  have hobstructions :
      ((spectralBoundaryObstructions n).card : ℝ) ≤
        ((spectralZetaZeroWindow ((n : ℝ) + 1)).card : ℝ) + 2 := by
    exact_mod_cast spectralBoundaryObstructions_card_le n
  have hcard :
      ((spectralBoundaryObstructions n).card : ℝ) + 2 ≤
        A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
            Real.log 2 + 4 := by
    linarith
  rw [show 1 / spectralBoundarySeparation n =
      3 * (((spectralBoundaryObstructions n).card : ℝ) + 2) by
    unfold spectralBoundarySeparation
    field_simp]
  exact mul_le_mul_of_nonneg_left hcard (by norm_num)

/-- Unconditionally, one log-linear bound controls all reciprocal selected
boundary separations. -/
theorem exists_one_div_spectralBoundarySeparation_logLinear_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ n : ℕ,
      1 / spectralBoundarySeparation n ≤
        3 *
          (A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
              Real.log 2 + 4) := by
  rcases riemannXi_logLinearGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA,
    one_div_spectralBoundarySeparation_le_logLinear_of_growth hA hbound⟩

/-- The xi log-linear scale is nonnegative on nonnegative arguments. -/
lemma xiLogLinearScale_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ xiLogLinearScale R := by
  unfold xiLogLinearScale
  have hlog : 0 ≤ Real.log (R + 1) :=
    Real.log_nonneg (by linarith)
  positivity

/-- The xi log-linear scale is positive on positive arguments. -/
lemma xiLogLinearScale_pos {R : ℝ} (hR : 0 < R) :
    0 < xiLogLinearScale R := by
  unfold xiLogLinearScale
  have hlog : 0 ≤ Real.log (R + 1) :=
    Real.log_nonneg (by linarith)
  positivity

/-- Every selected truncation height remains positive after adding one. -/
lemma quantitativeSpectralBoundaryTruncation_add_one_pos (n : ℕ) :
    0 < quantitativeSpectralBoundaryTruncation n + 1 := by
  have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
    (Nat.cast_nonneg n).trans_lt
      (quantitativeSpectralBoundaryTruncation_spec n).1
  linarith

/-- The canonical xi residual inherits the log-linear exponential growth
bound on its disk. -/
lemma norm_riemannXiCanonicalResidual_le_of_logLinear_growth
    {A : ℝ} (_hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalResidual n z‖ ≤
      Real.exp
        (A * xiLogLinearScale (xiCanonicalRadius n + 1)) := by
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

/-- The real part of the normalized canonical logarithm is bounded by xi's
log-linear growth. -/
lemma riemannXiCanonicalLog_re_le_of_logLinear_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    (riemannXiCanonicalLog n z).re ≤
      A * xiLogLinearScale (xiCanonicalRadius n + 1) := by
  let R := xiCanonicalRadius n
  let g := riemannXiCanonicalResidual n
  let L := riemannXiCanonicalLog n
  have hid := congrArg norm (exp_riemannXiCanonicalLog_mul_zero_eq n hz)
  change ‖Complex.exp (L z) * g 0‖ = ‖g z‖ at hid
  rw [norm_mul, Complex.norm_exp] at hid
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hgBound : ‖g z‖ ≤
      Real.exp (A * xiLogLinearScale (R + 1)) := by
    apply norm_riemannXiCanonicalResidual_le_of_logLinear_growth hA hbound n
    exact ball_subset_closedBall (by simpa [R] using hz)
  apply Real.exp_le_exp.mp
  calc
    Real.exp (L z).re = Real.exp (L z).re * 1 := by ring
    _ ≤ Real.exp (L z).re * ‖g 0‖ :=
      mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
    _ = ‖g z‖ := hid
    _ ≤ Real.exp (A * xiLogLinearScale (R + 1)) := hgBound

/-- Borel--Carathéodory turns the real-part bound into a norm bound for the
canonical logarithm. -/
lemma norm_riemannXiCanonicalLog_le_of_logLinear_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) {z : ℂ} (hz : z ∈ ball 0 (xiCanonicalRadius n)) :
    ‖riemannXiCanonicalLog n z‖ ≤
      2 * (A * xiLogLinearScale (xiCanonicalRadius n + 1)) * ‖z‖ /
        (xiCanonicalRadius n - ‖z‖) := by
  let R := xiCanonicalRadius n
  let L := riemannXiCanonicalLog n
  have hR : 0 < R := xiCanonicalRadius_pos n
  have hdiff : DifferentiableOn ℂ L (ball 0 R) := by
    intro w hw
    exact (riemannXiCanonicalLog_hasDerivAt n
      (by simpa [R] using hw)).differentiableAt.differentiableWithinAt
  apply Complex.borelCaratheodory_zero
    (M := A * xiLogLinearScale (R + 1))
    (mul_pos (zero_lt_one.trans_le hA)
      (xiLogLinearScale_pos (by linarith))) hdiff
  · intro w hw
    exact riemannXiCanonicalLog_re_le_of_logLinear_growth hA hbound n
      (by simpa [R] using hw)
  · exact hR
  · simpa [R] using hz
  · exact riemannXiCanonicalLog_zero n

/-- Canonical decomposition gives a quantitative lower bound for xi at an
inner point separated from every zero in the enclosing divisor. -/
theorem exp_neg_xiCanonicalLogLinearLowerExponent_le_norm_riemannXi
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (A * xiLogLinearScale (‖w‖ + 1)))
    (n : ℕ) {z : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hz : ‖z‖ ≤ xiCanonicalRadius n / 4)
    (hxi : riemannXi z ≠ 0)
    (hsep : ∀ i,
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i ≠ 0 →
        delta ≤ ‖z - i‖) :
    Real.exp (- (
        2 * A * xiLogLinearScale (xiCanonicalRadius n + 1) +
        (A * xiLogLinearScale (2 * xiCanonicalRadius n + 1) / Real.log 2) *
          Real.log (1 + 2 * xiCanonicalRadius n / delta))) ≤
      ‖riemannXi z‖ := by
  let R : ℝ := xiCanonicalRadius n
  let g : ℂ → ℂ := riemannXiCanonicalResidual n
  let L : ℂ → ℂ := riemannXiCanonicalLog n
  let d : ℂ → ℤ := fun i ↦ divisor riemannXi (ball 0 R) i
  let C : ℝ := Real.log (1 + 2 * R / delta)
  let M : ℝ := 2 * A * xiLogLinearScale (R + 1)
  let N : ℝ := (A * xiLogLinearScale (2 * R + 1) / Real.log 2) * C
  have hR : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hzball : z ∈ ball 0 R := by
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt (by dsimp only [R] at hz ⊢; linarith)
  have hzclosed : z ∈ closedBall 0 R := ball_subset_closedBall hzball
  have hLraw := norm_riemannXiCanonicalLog_le_of_logLinear_growth
    hA hbound n hzball
  have hden : 0 < R - ‖z‖ := by
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hratio : ‖z‖ / (R - ‖z‖) ≤ 1 := by
    rw [div_le_one hden]
    have hz' : ‖z‖ ≤ R / 4 := by simpa [R] using hz
    linarith
  have hL : ‖L z‖ ≤ M := by
    calc
      ‖L z‖ ≤ 2 * (A * xiLogLinearScale (R + 1)) * ‖z‖ /
          (R - ‖z‖) := by simpa [L, R] using hLraw
      _ = (2 * A * xiLogLinearScale (R + 1)) *
          (‖z‖ / (R - ‖z‖)) := by ring
      _ ≤ (2 * A * xiLogLinearScale (R + 1)) * 1 := by
        exact mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (by positivity)
            (xiLogLinearScale_nonneg (by positivity)))
      _ = M := by simp [M]
  have hnormResidual := congrArg norm
    (exp_riemannXiCanonicalLog_mul_zero_eq n hzball)
  have hnormResidual' :
      Real.exp (L z).re * ‖g 0‖ = ‖g z‖ := by
    simpa [L, g, norm_mul, Complex.norm_exp] using hnormResidual
  have hLre : -‖L z‖ ≤ (L z).re :=
    (abs_le.mp (Complex.abs_re_le_norm (L z))).1
  have hg0 : 1 ≤ ‖g 0‖ := by
    simpa [g] using one_le_norm_riemannXiCanonicalResidual_zero n
  have hexpResidual : Real.exp (-M) ≤ ‖g z‖ := by
    calc
      Real.exp (-M) ≤ Real.exp (-‖L z‖) :=
        Real.exp_le_exp.mpr (neg_le_neg hL)
      _ ≤ Real.exp (L z).re := Real.exp_le_exp.mpr hLre
      _ = Real.exp (L z).re * 1 := by ring
      _ ≤ Real.exp (L z).re * ‖g 0‖ :=
        mul_le_mul_of_nonneg_left hg0 (Real.exp_pos _).le
      _ = ‖g z‖ := hnormResidual'
  have hlogResidual : -M ≤ Real.log ‖g z‖ := by
    calc
      -M = Real.log (Real.exp (-M)) := by rw [Real.log_exp]
      _ ≤ Real.log ‖g z‖ :=
        Real.log_le_log (Real.exp_pos _) hexpResidual
  have hdFinite : (Function.support d).Finite := by
    simpa [d, R] using
      (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hdnonneg : ∀ i, 0 ≤ d i := by
    intro i
    exact (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i
  have hC : 0 ≤ C := by
    apply Real.log_nonneg
    have hquot : 0 ≤ 2 * R / delta := by positivity
    linarith
  have hfactorLog : ∀ i, d i ≠ 0 →
      Real.log ‖Complex.canonicalFactor R i z‖ ≤ C := by
    intro i hi
    have hiBall : i ∈ ball 0 R :=
      (divisor riemannXi (ball 0 R)).supportWithinDomain
        (by simpa [d] using hi)
    have hsepi : delta ≤ ‖z - i‖ := by
      apply hsep i
      simpa [d, R] using hi
    have hfactor := norm_canonicalFactor_le_of_inner_of_separated
      hR hdelta hiBall (by simpa [R] using hz) hsepi
    have hzi : z ≠ i := by
      intro hzi
      subst i
      simpa using (hdelta.trans_le hsepi).ne'
    have hfactorPos : 0 < ‖Complex.canonicalFactor R i z‖ :=
      norm_pos_iff.mpr
        (Complex.canonicalFactor_ne_zero hiBall hzclosed hzi)
    apply Real.log_le_log hfactorPos
    exact hfactor.trans (by linarith)
  have hcanonicalRaw := finsum_intCast_mul_le_of_nonneg
    hdFinite hdnonneg hfactorLog
  have hcount := sum_divisor_riemannXi_ball_le_logLinear_of_growth hA hbound n
  have hcanonical :
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) ≤ N := by
    calc
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) ≤
        ((∑ᶠ i, d i : ℤ) : ℝ) * C := hcanonicalRaw
      _ ≤ (A * xiLogLinearScale (2 * R + 1) / Real.log 2) * C := by
        apply mul_le_mul_of_nonneg_right
        · simpa [d, R] using hcount
        · exact hC
      _ = N := by rfl
  have horder : meromorphicOrderAt riemannXi z = 0 :=
    (analyticAt_riemannXi z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hxi
  have hlog := (riemannXiCanonicalResidual_decomp n).log_norm_eq
    hzclosed horder hR
  have hsphereSum :
      (∑ᶠ i : ℂ,
        ((divisor riemannXi (sphere 0 R) i : ℤ) : ℝ) *
          Real.log ‖z - i‖) = 0 := by
    rw [show divisor riemannXi (sphere 0 R) = 0 by
      simpa [R] using
        divisor_riemannXi_sphere_xiCanonicalRadius_eq_zero n]
    exact finsum_eq_zero_of_forall_eq_zero (fun i ↦ by simp)
  have htrailing : meromorphicTrailingCoeffAt riemannXi z = riemannXi z :=
    (analyticAt_riemannXi z).meromorphicTrailingCoeffAt_of_ne_zero hxi
  change Real.log ‖g z‖ = _ at hlog
  rw [hsphereSum, htrailing] at hlog
  simp only [sub_zero] at hlog
  have hlogXi : Real.log ‖riemannXi z‖ =
      Real.log ‖g z‖ -
        (∑ᶠ i, ((d i : ℤ) : ℝ) *
          Real.log ‖Complex.canonicalFactor R i z‖) := by
    change Real.log ‖g z‖ =
      (∑ᶠ i, ((d i : ℤ) : ℝ) *
        Real.log ‖Complex.canonicalFactor R i z‖) +
          Real.log ‖riemannXi z‖ at hlog
    linarith
  have hlowerLog : -(M + N) ≤ Real.log ‖riemannXi z‖ := by
    rw [hlogXi]
    linarith
  have hlower := Real.exp_le_exp.mpr hlowerLog
  rw [Real.exp_log (norm_pos_iff.mpr hxi)] at hlower
  simpa only [M, N, C, R, neg_add_rev] using hlower

/-- The explicit log-linear-growth exponent controlling xi on the
quantitative vertical boundary. -/
noncomputable def xiQuantitativeBoundaryLogLinearLowerExponent
    (A : ℝ) (n : ℕ) : ℝ :=
  2 * A * xiLogLinearScale (xiCanonicalRadius n + 1) +
    (A * xiLogLinearScale (2 * xiCanonicalRadius n + 1) / Real.log 2) *
      Real.log
        (1 + 2 * xiCanonicalRadius n / spectralBoundarySeparation n)

/-- Spectral xi is bounded below by the explicit log-linear exponent
throughout the selected segment. -/
theorem exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤
        Real.exp (A * xiLogLinearScale (‖w‖ + 1)))
    (n : ℕ) {y : ℝ} (hylo : -1 ≤ y) (hyhi : y ≤ 1) :
    Real.exp (-xiQuantitativeBoundaryLogLinearLowerExponent A n) ≤
      ‖riemannXiSpectral
        ((quantitativeSpectralBoundaryTruncation n : ℂ) +
          (y : ℂ) * Complex.I)‖ := by
  let w : ℂ :=
    (quantitativeSpectralBoundaryTruncation n : ℂ) +
      (y : ℂ) * Complex.I
  let s : ℂ := completedSpectralCoordinate w
  have hlower :=
    exp_neg_xiCanonicalLogLinearLowerExponent_le_norm_riemannXi
      hA hbound n (z := s) (delta := spectralBoundarySeparation n)
        (spectralBoundarySeparation_pos n)
        (by simpa [s, w] using
          norm_quantitativeCompletedCoordinate_le_quarter n hylo hyhi)
        (by simpa [s, w] using
          riemannXi_quantitativeCompletedCoordinate_ne_zero n y)
        (fun i hi ↦ by
          simpa [s, w] using
            spectralBoundarySeparation_le_norm_completedCoordinate_sub_zero
              n y hi)
  simpa [xiQuantitativeBoundaryLogLinearLowerExponent,
    riemannXiSpectral, s, w] using hlower

/-- An unconditional log-linear-growth lower floor exists on every selected
vertical boundary. -/
theorem exists_riemannXiSpectral_quantitativeVerticalBoundary_logLinear_lower_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (n : ℕ) {y : ℝ}, -1 ≤ y → y ≤ 1 →
      Real.exp (-xiQuantitativeBoundaryLogLinearLowerExponent A n) ≤
        ‖riemannXiSpectral
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖ := by
  rcases riemannXi_logLinearGrowth with ⟨A, hA, hbound⟩
  exact ⟨A, hA, fun n y hylo hyhi ↦
    exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral
      hA hbound n hylo hyhi⟩

/-- A two-parameter linear bound on an argument and its translate gives an
explicit logarithmic majorant for the xi scale. -/
lemma xiLogLinearScale_le_mul_one_add_log_mul
    {u k c X : ℝ} (hu : 0 ≤ u) (hk : 0 ≤ k) (hc : 0 < c)
    (hX : 0 < X) (huk : u ≤ k * X) (huone : u + 1 ≤ c * X) :
    xiLogLinearScale u ≤
      k * X * (1 + Real.log c + Real.log X) := by
  have huonePos : 0 < u + 1 := by linarith
  have hlog := Real.log_le_log huonePos huone
  rw [Real.log_mul hc.ne' hX.ne'] at hlog
  unfold xiLogLinearScale
  exact mul_le_mul huk (by linarith)
    (by
      have : 0 ≤ Real.log (u + 1) :=
        Real.log_nonneg (by linarith)
      linarith)
    (mul_nonneg hk hX.le)

/-- An explicit `T log² T` majorant for the selected-boundary lower
exponent. -/
noncomputable def xiQuantitativeBoundaryLogLinearPolynomialLogMajorant
    (A : ℝ) (n : ℕ) : ℝ :=
  let X := quantitativeSpectralBoundaryTruncation n + 1
  let B := A / Real.log 2
  let D := 1 + 546 * (5 * B + 4)
  28 * A * X * (1 + Real.log 15 + Real.log X) +
    27 * B * X * (1 + Real.log 28 + Real.log X) *
      (Real.log D + 3 * Real.log X)

/-- The log-linear canonical lower exponent is bounded by the explicit
polynomial-logarithmic majorant. -/
lemma xiQuantitativeBoundaryLogLinearLowerExponent_le_polynomialLog
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) :
    xiQuantitativeBoundaryLogLinearLowerExponent A n ≤
      xiQuantitativeBoundaryLogLinearPolynomialLogMajorant A n := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let R : ℝ := xiCanonicalRadius n
  let delta : ℝ := spectralBoundarySeparation n
  let X : ℝ := T + 1
  let B : ℝ := A / Real.log 2
  let L6 : ℝ := 1 + Real.log 6 + Real.log X
  let D : ℝ := 1 + 546 * (5 * B + 4)
  have hA0 : 0 ≤ A := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hT0 : 0 ≤ T :=
    (Nat.cast_nonneg n).trans
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1.le)
  have hX1 : 1 ≤ X := by
    change 1 ≤ T + 1
    linarith
  have hXpos : 0 < X := zero_lt_one.trans_le hX1
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hRpos : 0 < R := by simpa [R] using xiCanonicalRadius_pos n
  have hdelta : 0 < delta := by
    simpa [delta] using spectralBoundarySeparation_pos n
  have hRupper : R ≤ 13 * X := by
    have hr := (xiCanonicalRadius_spec n).2.1
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [R, T, X]
    linarith
  have hRone : R + 1 ≤ 14 * X := by linarith
  have hRtwo : R + 1 + 1 ≤ 15 * X := by linarith
  have htwoRone : 2 * R + 1 ≤ 27 * X := by
    calc
      2 * R + 1 ≤ 2 * (13 * X) + 1 := by gcongr
      _ ≤ 27 * X := by linarith
  have htwoRtwo : 2 * R + 1 + 1 ≤ 28 * X := by linarith
  have hbase : 2 * ((n : ℝ) + 2) + 1 ≤ 5 * X := by
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [T, X]
    linarith
  have hbaseOne : 2 * ((n : ℝ) + 2) + 1 + 1 ≤ 6 * X := by
    have ht := (quantitativeSpectralBoundaryTruncation_spec n).1
    dsimp [T, X]
    linarith
  have hscaleRone : xiLogLinearScale (R + 1) ≤
      14 * X * (1 + Real.log 15 + Real.log X) :=
    xiLogLinearScale_le_mul_one_add_log_mul
      (by positivity) (by norm_num) (by norm_num) hXpos hRone hRtwo
  have hscaleTwoRone : xiLogLinearScale (2 * R + 1) ≤
      27 * X * (1 + Real.log 28 + Real.log X) :=
    xiLogLinearScale_le_mul_one_add_log_mul
      (by positivity) (by norm_num) (by norm_num) hXpos
        htwoRone htwoRtwo
  have hscaleBase : xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) ≤
      5 * X * L6 := by
    simpa [L6] using
      xiLogLinearScale_le_mul_one_add_log_mul
        (u := 2 * ((n : ℝ) + 2) + 1) (k := 5) (c := 6) (X := X)
        (by positivity) (by norm_num) (by norm_num) hXpos hbase hbaseOne
  have hL6one : 1 ≤ L6 := by
    dsimp [L6]
    have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    linarith
  have hXL6one : 1 ≤ X * L6 :=
    one_le_mul_of_one_le_of_one_le hX1 hL6one
  have hsepRaw := one_div_spectralBoundarySeparation_le_logLinear_of_growth
    hA hbound n
  have hsep : 1 / delta ≤ 3 * (5 * B + 4) * X * L6 := by
    calc
      1 / delta ≤
          3 *
            (A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
                Real.log 2 + 4) := by
        simpa [delta] using hsepRaw
      _ ≤ 3 * (B * (5 * X * L6) + 4) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hcoefficient :
            A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
                Real.log 2 ≤ B * (5 * X * L6) := by
          calc
            A * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) /
                Real.log 2 =
                B * xiLogLinearScale (2 * ((n : ℝ) + 2) + 1) := by
              dsimp [B]
              ring
            _ ≤ B * (5 * X * L6) :=
              mul_le_mul_of_nonneg_left hscaleBase hB0
        simpa [add_comm] using add_le_add_right hcoefficient 4
      _ ≤ 3 * (5 * B + 4) * X * L6 := by
        have hfour : 4 ≤ 4 * (X * L6) := by nlinarith
        calc
          3 * (B * (5 * X * L6) + 4) ≤
              3 * (B * (5 * X * L6) + 4 * (X * L6)) := by
            gcongr
          _ = 3 * (5 * B + 4) * X * L6 := by ring
  have hlog6le : Real.log 6 ≤ 5 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    norm_num
  have hlogXle : Real.log X ≤ X - 1 :=
    Real.log_le_sub_one_of_pos hXpos
  have hL6upper : L6 ≤ 7 * X := by
    dsimp [L6]
    nlinarith
  have hC0 : 0 ≤ 5 * B + 4 := by positivity
  have hquot : 2 * R / delta ≤ 546 * (5 * B + 4) * X ^ 3 := by
    rw [div_eq_mul_inv]
    calc
      2 * R * delta⁻¹ ≤
          2 * (13 * X) * (3 * (5 * B + 4) * X * L6) := by
        gcongr
        simpa [one_div] using hsep
      _ = 78 * (5 * B + 4) * X ^ 2 * L6 := by ring
      _ ≤ 78 * (5 * B + 4) * X ^ 2 * (7 * X) := by
        gcongr
      _ = 546 * (5 * B + 4) * X ^ 3 := by ring
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hlogArg :
      Real.log (1 + 2 * R / delta) ≤
        Real.log D + 3 * Real.log X := by
    calc
      Real.log (1 + 2 * R / delta) ≤ Real.log (D * X ^ 3) := by
        apply Real.log_le_log
        · positivity
        · calc
            1 + 2 * R / delta ≤
                1 + 546 * (5 * B + 4) * X ^ 3 := by linarith
            _ ≤ D * X ^ 3 := by
              have hXcube : 1 ≤ X ^ 3 := one_le_pow₀ hX1
              dsimp [D]
              nlinarith [mul_nonneg (by positivity :
                0 ≤ 546 * (5 * B + 4))
                (sub_nonneg.mpr hXcube)]
      _ = Real.log D + 3 * Real.log X := by
        rw [Real.log_mul hDpos.ne' (pow_ne_zero 3 hXpos.ne'),
          Real.log_pow]
        norm_num
  have hlogArg0 : 0 ≤ Real.log (1 + 2 * R / delta) := by
    apply Real.log_nonneg
    have : 0 ≤ 2 * R / delta := by positivity
    linarith
  have hmain :
      2 * A * xiLogLinearScale (R + 1) +
          (B * xiLogLinearScale (2 * R + 1)) *
            Real.log (1 + 2 * R / delta) ≤
        28 * A * X * (1 + Real.log 15 + Real.log X) +
          27 * B * X * (1 + Real.log 28 + Real.log X) *
            (Real.log D + 3 * Real.log X) := by
    apply add_le_add
    · calc
        2 * A * xiLogLinearScale (R + 1) ≤
            2 * A * (14 * X *
              (1 + Real.log 15 + Real.log X)) := by gcongr
        _ = 28 * A * X *
            (1 + Real.log 15 + Real.log X) := by ring
    · calc
        (B * xiLogLinearScale (2 * R + 1)) *
            Real.log (1 + 2 * R / delta) ≤
          (B * (27 * X * (1 + Real.log 28 + Real.log X))) *
            (Real.log D + 3 * Real.log X) := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hscaleTwoRone hB0)
                hlogArg hlogArg0 (by positivity)
        _ = 27 * B * X * (1 + Real.log 28 + Real.log X) *
            (Real.log D + 3 * Real.log X) := by ring
  dsimp [xiQuantitativeBoundaryLogLinearLowerExponent,
    xiQuantitativeBoundaryLogLinearPolynomialLogMajorant,
    R, T, delta, X, B, D] at hmain ⊢
  ring_nf at hmain ⊢
  exact hmain

/-- The explicit `T log² T` majorant is little-o of `T^(1+epsilon)` for every
positive `epsilon`. -/
lemma tendsto_xiQuantitativeBoundaryLogLinearPolynomialLogMajorant_div_rpow_zero
    (A : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryLogLinearPolynomialLogMajorant A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun n ↦ quantitativeSpectralBoundaryTruncation n + 1
  let B : ℝ := A / Real.log 2
  let D : ℝ := 1 + 546 * (5 * B + 4)
  let P : ℝ := 28 * A
  let Q : ℝ := 27 * B
  let a : ℝ := 1 + Real.log 15
  let b : ℝ := 1 + Real.log 28
  let d : ℝ := Real.log D
  have hX : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hXpos (n : ℕ) : 0 < X n := by
    have hT : 0 < quantitativeSpectralBoundaryTruncation n :=
      (Nat.cast_nonneg n).trans_lt
        (quantitativeSpectralBoundaryTruncation_spec n).1
    change 0 < quantitativeSpectralBoundaryTruncation n + 1
    linarith
  have hinv : Tendsto
      (fun n : ℕ ↦ 1 / X n ^ epsilon) atTop (nhds 0) := by
    have hraw := (tendsto_rpow_neg_atTop hepsilon).comp hX
    change Tendsto (fun n : ℕ ↦ X n ^ (-epsilon))
      atTop (nhds 0) at hraw
    refine hraw.congr' (Eventually.of_forall fun n ↦ ?_)
    rw [Real.rpow_neg (hXpos n).le]
    simp only [one_div]
  have hlog : Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ epsilon)
      atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ ↦ Real.log x / x ^ epsilon)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop hepsilon).tendsto_div_nhds_zero
    have hcomposed := hraw.comp hX
    change Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ epsilon)
      atTop (nhds 0) at hcomposed
    exact hcomposed
  have hlogSq : Tendsto
      (fun n : ℕ ↦ Real.log (X n) ^ 2 / X n ^ epsilon)
      atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ epsilon)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop 2 hepsilon).tendsto_div_nhds_zero
    have hcomposed := hraw.comp hX
    change Tendsto
      (fun n : ℕ ↦ Real.log (X n) ^ (2 : ℝ) / X n ^ epsilon)
      atTop (nhds 0) at hcomposed
    simpa only [Real.rpow_two] using hcomposed
  have hcombined : Tendsto
      (fun n : ℕ ↦
        (P * a + Q * b * d) * (1 / X n ^ epsilon) +
          (P + Q * (3 * b + d)) *
            (Real.log (X n) / X n ^ epsilon) +
          (3 * Q) *
            (Real.log (X n) ^ 2 / X n ^ epsilon))
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun n : ℕ ↦ (P * a + Q * b * d) * (1 / X n ^ epsilon))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hinv
    have hlinear : Tendsto
        (fun n : ℕ ↦ (P + Q * (3 * b + d)) *
          (Real.log (X n) / X n ^ epsilon))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hlog
    have hquadratic : Tendsto
        (fun n : ℕ ↦ (3 * Q) *
          (Real.log (X n) ^ 2 / X n ^ epsilon))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hlogSq
    simpa using (hconst.add hlinear).add hquadratic
  refine hcombined.congr' (Eventually.of_forall fun n ↦ ?_)
  have hpow : X n ^ (1 + epsilon) = X n * X n ^ epsilon := by
    rw [Real.rpow_add (hXpos n), Real.rpow_one]
  symm
  change
    (P * X n * (a + Real.log (X n)) +
        Q * X n * (b + Real.log (X n)) *
          (d + 3 * Real.log (X n))) /
      X n ^ (1 + epsilon) = _
  rw [hpow]
  field_simp [(hXpos n).ne',
    (Real.rpow_pos_of_pos (hXpos n) epsilon).ne']
  ring

/-- The quantitative log-linear lower exponent is nonnegative. -/
lemma xiQuantitativeBoundaryLogLinearLowerExponent_nonneg
    {A : ℝ} (hA : 1 ≤ A) (n : ℕ) :
    0 ≤ xiQuantitativeBoundaryLogLinearLowerExponent A n := by
  unfold xiQuantitativeBoundaryLogLinearLowerExponent
  have hA0 : 0 ≤ A := by linarith
  have hR : 0 < xiCanonicalRadius n := xiCanonicalRadius_pos n
  have hdelta : 0 < spectralBoundarySeparation n :=
    spectralBoundarySeparation_pos n
  have hlog : 0 ≤ Real.log
      (1 + 2 * xiCanonicalRadius n /
        spectralBoundarySeparation n) := by
    apply Real.log_nonneg
    have hquot : 0 ≤ 2 * xiCanonicalRadius n /
        spectralBoundarySeparation n := by positivity
    linarith
  have hscaleOne : 0 ≤ xiLogLinearScale (xiCanonicalRadius n + 1) :=
    xiLogLinearScale_nonneg (by positivity)
  have hscaleTwo :
      0 ≤ xiLogLinearScale (2 * xiCanonicalRadius n + 1) :=
    xiLogLinearScale_nonneg (by positivity)
  positivity

/-- The selected-boundary lower exponent is little-o of every fixed power
strictly above one. -/
lemma tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryLogLinearLowerExponent A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      exact div_nonneg
        (xiQuantitativeBoundaryLogLinearLowerExponent_nonneg hA n)
        (Real.rpow_nonneg
          (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _)
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
        (xiQuantitativeBoundaryLogLinearLowerExponent_le_polynomialLog
          hA hbound n)
      exact Real.rpow_nonneg
        (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _
  · exact
      tendsto_xiQuantitativeBoundaryLogLinearPolynomialLogMajorant_div_rpow_zero
        A hepsilon

/-- At the selected critical endpoints, the negative logarithm of spectral xi
is little-o of every fixed power strictly above one. -/
theorem tendsto_riemannXiSpectral_quantitativeCritical_log_negativePart_div_one_add_rpow_zero
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : ℕ ↦
        max 0
            (-Real.log ‖riemannXiSpectral
              (quantitativeSpectralBoundaryTruncation n : ℂ)‖) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0) := by
  rcases riemannXi_logLinearGrowth with ⟨A, hA, hbound⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      exact div_nonneg (le_max_left _ _)
        (Real.rpow_nonneg
          (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _)
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
      · apply max_le
        · exact xiQuantitativeBoundaryLogLinearLowerExponent_nonneg hA n
        · have hlower :=
            exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral
              hA hbound n (y := 0) (by norm_num) (by norm_num)
          have hlog := Real.log_le_log (Real.exp_pos _) hlower
          rw [Real.log_exp] at hlog
          have hlog' :
              -xiQuantitativeBoundaryLogLinearLowerExponent A n ≤
                Real.log ‖riemannXiSpectral
                  (quantitativeSpectralBoundaryTruncation n : ℂ)‖ := by
            simpa using hlog
          linarith
      · exact Real.rpow_nonneg
          (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _
  · exact
      tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero
        hA hbound hepsilon


/-- The critical zeta negative logarithm is controlled by the xi lower
exponent and elementary factors. -/
lemma criticalZeta_log_negativePart_le_logLinearLowerExponent
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    (n : ℕ) :
    max 0
        (-Real.log ‖riemannZeta
          (staticContourCriticalEndpoint
            (quantitativeSpectralBoundaryTruncation n))‖) ≤
      xiQuantitativeBoundaryLogLinearLowerExponent A n +
        2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) +
        Real.log staticContourCriticalGammaRUpperMass := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let s : ℂ := staticContourCriticalEndpoint T
  let E : ℝ := xiQuantitativeBoundaryLogLinearLowerExponent A n
  let G : ℝ := staticContourCriticalGammaRUpperMass
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hxi : riemannXi s ≠ 0 := by
    simpa [s, T] using
      riemannXi_staticContourCriticalEndpoint_quantitative_ne_zero n
  have hsre : 0 < s.re := by simp [s, staticContourCriticalEndpoint]
  have hsone : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, staticContourCriticalEndpoint] at hre
  have hlower :=
    exp_neg_xiQuantitativeBoundaryLogLinearLowerExponent_le_norm_riemannXiSpectral
      hA hbound n (y := 0) (by norm_num) (by norm_num)
  have hlower' : Real.exp (-E) ≤ ‖riemannXi s‖ := by
    simpa [E, s, T, riemannXiSpectral, completedSpectralCoordinate,
      staticContourCriticalEndpoint, mul_comm] using hlower
  have hxiLog : -E ≤ Real.log ‖riemannXi s‖ := by
    have hlog := Real.log_le_log (Real.exp_pos _) hlower'
    simpa using hlog
  have hsplit := log_norm_riemannXi_eq_polynomial_add_GammaR_add_zeta
    hsre hsone hxi
  have hpoly : Real.log ‖s * (1 - s)‖ ≤
      2 * Real.log (T + 1) := by
    simpa [s] using
      log_norm_staticContourCriticalPolynomial_le_two_log_add_one hT.le
  have hgamma : Real.log ‖Complex.Gammaℝ s‖ ≤ Real.log G := by
    simpa [s, G] using
      log_norm_GammaR_staticContourCriticalEndpoint_le_log_mass T
  have hE0 : 0 ≤ E := by
    simpa [E] using
      xiQuantitativeBoundaryLogLinearLowerExponent_nonneg hA n
  have hlogT0 : 0 ≤ Real.log (T + 1) :=
    Real.log_nonneg (by linarith)
  have hlogG0 : 0 ≤ Real.log G :=
    Real.log_nonneg (by
      simpa [G] using one_le_staticContourCriticalGammaRUpperMass)
  have hnegative : -Real.log ‖riemannZeta s‖ ≤
      E + 2 * Real.log (T + 1) + Real.log G := by
    linarith
  change max 0 (-Real.log ‖riemannZeta s‖) ≤
    E + 2 * Real.log (T + 1) + Real.log G
  exact max_le (by positivity) hnegative

/-- The complete critical-zeta negative-log majorant is little-o of every
fixed power strictly above one. -/
lemma tendsto_criticalZeta_logLinearNegativeMajorant_div_one_add_rpow_zero
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤
        Real.exp (A * xiLogLinearScale (‖z‖ + 1)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : ℕ ↦
        (xiQuantitativeBoundaryLogLinearLowerExponent A n +
            2 * Real.log
              (quantitativeSpectralBoundaryTruncation n + 1) +
            Real.log staticContourCriticalGammaRUpperMass) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun n ↦ quantitativeSpectralBoundaryTruncation n + 1
  have hX : Tendsto X atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hE : Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryLogLinearLowerExponent A n /
          X n ^ (1 + epsilon))
      atTop (nhds 0) := by
    change Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryLogLinearLowerExponent A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0)
    exact
      tendsto_xiQuantitativeBoundaryLogLinearLowerExponent_div_rpow_zero
        hA hbound hepsilon
  have hlog : Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ (1 + epsilon))
      atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ ↦ Real.log x / x ^ (1 + epsilon))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop (by linarith)).tendsto_div_nhds_zero
    have hcomposed := hraw.comp hX
    change Tendsto
      (fun n : ℕ ↦ Real.log (X n) / X n ^ (1 + epsilon))
      atTop (nhds 0) at hcomposed
    exact hcomposed
  have htwoLog : Tendsto
      (fun n : ℕ ↦ 2 * (Real.log (X n) / X n ^ (1 + epsilon)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hXpow : Tendsto
      (fun n : ℕ ↦ X n ^ (1 + epsilon)) atTop atTop := by
    have hraw := (tendsto_rpow_atTop (by linarith : 0 < 1 + epsilon)).comp hX
    change Tendsto (fun n : ℕ ↦ X n ^ (1 + epsilon))
      atTop atTop at hraw
    exact hraw
  have hconstant : Tendsto
      (fun n : ℕ ↦
        Real.log staticContourCriticalGammaRUpperMass /
          X n ^ (1 + epsilon))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hXpow
  have hsum : Tendsto
      (fun n : ℕ ↦
        xiQuantitativeBoundaryLogLinearLowerExponent A n /
            X n ^ (1 + epsilon) +
          2 * (Real.log (X n) / X n ^ (1 + epsilon)) +
          Real.log staticContourCriticalGammaRUpperMass /
            X n ^ (1 + epsilon))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hE.add htwoLog).add hconstant
  refine hsum.congr' (Eventually.of_forall fun n ↦ ?_)
  change
    xiQuantitativeBoundaryLogLinearLowerExponent A n /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon) +
        2 * (Real.log (quantitativeSpectralBoundaryTruncation n + 1) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon)) +
        Real.log staticContourCriticalGammaRUpperMass /
          (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon) =
      (xiQuantitativeBoundaryLogLinearLowerExponent A n +
          2 * Real.log (quantitativeSpectralBoundaryTruncation n + 1) +
          Real.log staticContourCriticalGammaRUpperMass) /
        (quantitativeSpectralBoundaryTruncation n + 1) ^ (1 + epsilon)
  ring

/-- At the selected nonzero critical endpoints, the negative logarithm of
zeta is little-o of `T^(1+epsilon)` for every positive `epsilon`. -/
theorem tendsto_criticalZeta_log_negativePart_div_quantitative_one_add_rpow_zero
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto
      (fun n : ℕ ↦
        max 0
            (-Real.log ‖riemannZeta
              (staticContourCriticalEndpoint
                (quantitativeSpectralBoundaryTruncation n))‖) /
          (quantitativeSpectralBoundaryTruncation n + 1) ^
            (1 + epsilon))
      atTop (nhds 0) := by
  rcases riemannXi_logLinearGrowth with ⟨A, hA, hbound⟩
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      exact div_nonneg (le_max_left _ _)
        (Real.rpow_nonneg
          (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _)
  · exact Eventually.of_forall fun n ↦ by
      apply div_le_div_of_nonneg_right
        (criticalZeta_log_negativePart_le_logLinearLowerExponent
          hA hbound n)
      exact Real.rpow_nonneg
        (quantitativeSpectralBoundaryTruncation_add_one_pos n).le _
  · exact
      tendsto_criticalZeta_logLinearNegativeMajorant_div_one_add_rpow_zero
        hA hbound hepsilon

end

end RiemannGaussian
