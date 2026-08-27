import RiemannGaussian.RiemannXiBoundaryHeatActionLimit

/-!
# Fixed-proper-time spectral heat at the real boundary

For each positive proper time, this file identifies the exact first-order
boundary value of the complete upper spectral-xi heat sum.  The derivative
of one reflected Gaussian pair at height zero is its positive boundary heat
density.  A uniform upper-divisor gap bounds every normalized approached term
by `4 / tau` times the already summable boundary Poisson density, so Tannery's
theorem passes the limit through the entire multiplicity-counted divisor.

The resulting finite Gaussian-weighted boundary density is zero exactly when
there are no upper spectral zeros, hence exactly when the Riemann hypothesis
holds.  This connects the fixed-proper-time residue sum derived from
`logDeriv riemannXiSpectral` to the cancellation-free boundary invariant
before any integration in proper time.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Squared distance from a vertical boundary approach to a spectral point. -/
theorem normSq_upperBoundaryApproachPoint_sub
    (x y : ℝ) (alpha : ℂ) :
    Complex.normSq (upperBoundaryApproachPoint x y - alpha) =
      Complex.normSq ((x : ℂ) - alpha) + y ^ 2 - 2 * y * alpha.im := by
  unfold upperBoundaryApproachPoint Complex.normSq
  simp
  ring

/-- The height derivative of one reflected heat pair at the real boundary is
its positive fixed-time boundary heat kernel. -/
theorem hasDerivAt_upperHalfPlaneHyperbolicHeatIntegrand_approach
    (x : ℝ) (alpha : ℂ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun y : ℝ ↦
        upperHalfPlaneHyperbolicHeatIntegrand
          (upperBoundaryApproachPoint x y) alpha tau)
      (4 * alpha.im * Real.exp
        (-(Complex.normSq ((x : ℂ) - alpha) * tau))) 0 := by
  let D := Complex.normSq ((x : ℂ) - alpha)
  let a := alpha.im
  have hy2 : HasDerivAt (fun y : ℝ ↦ y ^ 2) 0 0 := by
    simpa using! (hasDerivAt_pow 2 (0 : ℝ))
  have hlin : HasDerivAt (fun y : ℝ ↦ 2 * y * a) (2 * a) 0 := by
    simpa [mul_comm, mul_left_comm] using!
      (hasDerivAt_mul_const (x := (0 : ℝ)) (2 * a))
  have hpminus : HasDerivAt
      (fun y : ℝ ↦ -(D + y ^ 2 - 2 * y * a) * tau)
      (2 * a * tau) 0 := by
    have h := (((hasDerivAt_const (𝕜 := ℝ) 0 D).add hy2).sub
      hlin).neg.mul_const tau
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, zero_add,
      zero_sub, neg_neg] using! h
  have hpplus : HasDerivAt
      (fun y : ℝ ↦ -(D + y ^ 2 + 2 * y * a) * tau)
      (-(2 * a) * tau) 0 := by
    have h := (((hasDerivAt_const (𝕜 := ℝ) 0 D).add hy2).add
      hlin).neg.mul_const tau
    simpa only [Pi.add_apply, Pi.neg_apply, zero_add, neg_neg] using! h
  have hscaled := (hpminus.exp.sub hpplus.exp).const_mul tau⁻¹
  have hscaled' : HasDerivAt
      (fun y : ℝ ↦ tau⁻¹ *
        (Real.exp (-(D + y ^ 2 - 2 * y * a) * tau) -
          Real.exp (-(D + y ^ 2 + 2 * y * a) * tau)))
      (tau⁻¹ *
        (Real.exp (-(D + 0 ^ 2 - 2 * 0 * a) * tau) *
            (2 * a * tau) -
          Real.exp (-(D + 0 ^ 2 + 2 * 0 * a) * tau) *
            (-(2 * a) * tau))) 0 := by
    simpa only [Pi.sub_apply] using! hscaled
  rw [show (fun y : ℝ ↦
      upperHalfPlaneHyperbolicHeatIntegrand
        (upperBoundaryApproachPoint x y) alpha tau) =
      fun y : ℝ ↦ tau⁻¹ *
        (Real.exp (-(D + y ^ 2 - 2 * y * a) * tau) -
          Real.exp (-(D + y ^ 2 + 2 * y * a) * tau)) by
    funext y
    rw [upperHalfPlaneHyperbolicHeatIntegrand,
      normSq_upperBoundaryApproachPoint_sub,
      normSq_upperBoundaryApproachPoint_sub_conj]
    dsimp [D, a]
    ring_nf]
  apply hscaled'.congr_deriv
  dsimp [D, a]
  norm_num
  field_simp [htau.ne']
  ring

/-- Dividing one heat pair by its exact boundary factor `2*y` yields the
fixed-time boundary heat kernel as `y -> 0+`. -/
theorem tendsto_upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient
    (x : ℝ) (alpha : ℂ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun y : ℝ ↦
        upperHalfPlaneHyperbolicHeatIntegrand
          (upperBoundaryApproachPoint x y) alpha tau / (2 * y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (2 * alpha.im * Real.exp
        (-(Complex.normSq ((x : ℂ) - alpha) * tau)))) := by
  have hderiv :=
    hasDerivAt_upperHalfPlaneHyperbolicHeatIntegrand_approach
      x alpha htau
  have hslope := hderiv.tendsto_slope_zero_right
  have hzero : upperHalfPlaneHyperbolicHeatIntegrand
      (upperBoundaryApproachPoint x 0) alpha tau = 0 := by
    rw [upperBoundaryApproachPoint_zero,
      upperHalfPlaneHyperbolicHeatIntegrand]
    simp [Complex.normSq_apply]
  convert hslope.const_mul (2 : ℝ)⁻¹ using 1
  · funext y
    rw [hzero]
    simp only [zero_add, sub_zero, smul_eq_mul]
    field_simp
  · congr 1
    field_simp
    ring

/-- The Gaussian factor is retained in the elementary small-height bound. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_le_exp_mul_four_mul_im
    (z alpha : ℂ) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau ≤
      Real.exp (-(Complex.normSq (z - alpha) * tau)) *
        (4 * z.im * alpha.im) := by
  rw [upperHalfPlaneHyperbolicHeatIntegrand_eq_heightFactor]
  let q : ℝ := 4 * z.im * alpha.im
  have honeSub : 1 - Real.exp (-(q * tau)) ≤ q * tau := by
    linarith [Real.one_sub_le_exp_neg (q * tau)]
  have hquot : tau⁻¹ * (1 - Real.exp (-(q * tau))) ≤ q := by
    calc
      tau⁻¹ * (1 - Real.exp (-(q * tau))) ≤
          tau⁻¹ * (q * tau) :=
        mul_le_mul_of_nonneg_left honeSub (inv_nonneg.mpr htau.le)
      _ = q := by field_simp
  exact mul_le_mul_of_nonneg_left hquot (Real.exp_pos _).le

/-- After removing the exact linear boundary factor, one heat kernel is
bounded by its Gaussian times twice the root height. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient_le
    (x : ℝ) {y : ℝ} (hy : 0 < y) (alpha : ℂ)
    {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand
        (upperBoundaryApproachPoint x y) alpha tau / (2 * y) ≤
      2 * alpha.im *
        Real.exp (-(Complex.normSq
          (upperBoundaryApproachPoint x y - alpha) * tau)) := by
  have hheat :=
    upperHalfPlaneHyperbolicHeatIntegrand_le_exp_mul_four_mul_im
      (upperBoundaryApproachPoint x y) alpha htau
  rw [upperBoundaryApproachPoint_im] at hheat
  calc
    upperHalfPlaneHyperbolicHeatIntegrand
          (upperBoundaryApproachPoint x y) alpha tau / (2 * y) ≤
        (Real.exp (-(Complex.normSq
            (upperBoundaryApproachPoint x y - alpha) * tau)) *
          (4 * y * alpha.im)) / (2 * y) :=
      div_le_div_of_nonneg_right hheat (by positivity)
    _ = 2 * alpha.im *
        Real.exp (-(Complex.normSq
          (upperBoundaryApproachPoint x y - alpha) * tau)) := by
      field_simp [hy.ne']
      ring

/-- A boundary-to-root distance controls the corresponding distance from a
short vertical approach point. -/
theorem half_norm_boundary_sub_le_norm_approach_sub
    {x delta y : ℝ} {alpha : ℂ} (_hdelta : 0 < delta)
    (hgap : delta ≤ ‖(x : ℂ) - alpha‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    ‖(x : ℂ) - alpha‖ / 2 ≤
      ‖upperBoundaryApproachPoint x y - alpha‖ := by
  have htriangle :
      ‖(x : ℂ) - alpha‖ ≤
        ‖(x : ℂ) - upperBoundaryApproachPoint x y‖ +
          ‖upperBoundaryApproachPoint x y - alpha‖ := by
    calc
      ‖(x : ℂ) - alpha‖ =
          ‖((x : ℂ) - upperBoundaryApproachPoint x y) +
            (upperBoundaryApproachPoint x y - alpha)‖ := by
              congr 1
              ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_real_sub_upperBoundaryApproachPoint, abs_of_pos hy] at htriangle
  linarith

/-- Squaring the preceding distance comparison gives the factor four needed
for a boundary-density dominator. -/
theorem normSq_boundary_sub_le_four_mul_normSq_approach_sub
    {x delta y : ℝ} {alpha : ℂ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖(x : ℂ) - alpha‖)
    (hy : 0 < y) (hySmall : y < delta / 2) :
    Complex.normSq ((x : ℂ) - alpha) ≤
      4 * Complex.normSq (upperBoundaryApproachPoint x y - alpha) := by
  have hhalf := half_norm_boundary_sub_le_norm_approach_sub
    hdelta hgap hy hySmall
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg ((x : ℂ) - alpha),
    norm_nonneg (upperBoundaryApproachPoint x y - alpha)]

/-- The elementary maximum of `u * exp (-u)` gives a scale-exact Gaussian
bound at every positive proper time. -/
theorem mul_exp_neg_mul_le_inv (Q : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Q * Real.exp (-(Q * tau)) ≤ tau⁻¹ := by
  have hmul := Real.mul_exp_neg_le_exp_neg_one (Q * tau)
  have hexpOne : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  calc
    Q * Real.exp (-(Q * tau)) =
        tau⁻¹ * ((Q * tau) * Real.exp (-(Q * tau))) := by
      field_simp [htau.ne']
    _ ≤ tau⁻¹ * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr htau.le)
    _ ≤ tau⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hexpOne (inv_nonneg.mpr htau.le)
    _ = tau⁻¹ := mul_one _

/-- The boundary squared distance times the approached Gaussian has a
uniform `4/tau` bound. -/
theorem normSq_boundary_mul_exp_approach_le_four_inv
    {x delta y : ℝ} {alpha : ℂ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖(x : ℂ) - alpha‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {tau : ℝ} (htau : 0 < tau) :
    Complex.normSq ((x : ℂ) - alpha) *
        Real.exp (-(Complex.normSq
          (upperBoundaryApproachPoint x y - alpha) * tau)) ≤
      4 * tau⁻¹ := by
  let Q := Complex.normSq (upperBoundaryApproachPoint x y - alpha)
  have hDQ : Complex.normSq ((x : ℂ) - alpha) ≤ 4 * Q :=
    normSq_boundary_sub_le_four_mul_normSq_approach_sub
      hdelta hgap hy hySmall
  have hexpNonneg : 0 ≤ Real.exp (-(Q * tau)) := (Real.exp_pos _).le
  have hfirst : Complex.normSq ((x : ℂ) - alpha) *
      Real.exp (-(Q * tau)) ≤ 4 * (Q * Real.exp (-(Q * tau))) := by
    nlinarith
  have hQ : Q * Real.exp (-(Q * tau)) ≤ tau⁻¹ :=
    mul_exp_neg_mul_le_inv Q htau
  exact hfirst.trans (by nlinarith)

/-- The fixed-proper-time boundary heat density contributed by one upper
spectral zero. -/
def zetaUpperHyperbolicBoundaryHeatSummand
    (x tau : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (2 * (zetaSpectralCoordinate rho.1).im *
        Real.exp (-(Complex.normSq
          ((x : ℂ) - zetaSpectralCoordinate rho.1) * tau)))
  else 0

/-- Every fixed-time boundary heat summand is nonnegative. -/
theorem zetaUpperHyperbolicBoundaryHeatSummand_nonneg
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperHyperbolicBoundaryHeatSummand x tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
    positivity
  · rw [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]

/-- At positive proper time the boundary heat density is bounded by
`tau⁻¹` times the already summable boundary Poisson density. -/
theorem zetaUpperHyperbolicBoundaryHeatSummand_le_inv_mul_density
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicBoundaryHeatSummand x tau rho ≤
      tau⁻¹ * zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha := zetaSpectralCoordinate rho.1
    let D := Complex.normSq ((x : ℂ) - alpha)
    have hD : 0 < D := by
      dsimp [D, alpha]
      apply Complex.normSq_pos.mpr
      apply sub_ne_zero.mpr
      intro heq
      have him := congrArg Complex.im heq
      simp only [ofReal_im] at him
      linarith
    have hgauss : D * Real.exp (-(D * tau)) ≤ tau⁻¹ :=
      mul_exp_neg_mul_le_inv D htau
    have hkernel :
        2 * alpha.im * Real.exp (-(D * tau)) ≤
          tau⁻¹ * (2 * alpha.im / D) := by
      rw [show tau⁻¹ * (2 * alpha.im / D) =
          (tau⁻¹ * (2 * alpha.im)) / D by ring,
        le_div_iff₀ hD]
      have hscaled := mul_le_mul_of_nonneg_left hgauss
        (show 0 ≤ 2 * alpha.im by positivity)
      nlinarith
    rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    change (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * alpha.im * Real.exp (-(D * tau))) ≤
      tau⁻¹ * ((analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * alpha.im / D))
    calc
      _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) *
          (tau⁻¹ * (2 * alpha.im / D)) :=
        mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg _)
      _ = _ := by ring
  · rw [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]
    positivity

/-- Every positive-time boundary heat series is absolutely summable. -/
theorem summable_zetaUpperHyperbolicBoundaryHeatSummand
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Summable (zetaUpperHyperbolicBoundaryHeatSummand x tau) := by
  apply
    ((summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left
      tau⁻¹).of_nonneg_of_le
      (zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau)
  exact zetaUpperHyperbolicBoundaryHeatSummand_le_inv_mul_density x htau

/-- The complete finite fixed-time boundary heat density. -/
def riemannXiUpperHyperbolicBoundaryHeatTotal (x tau : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperHyperbolicBoundaryHeatSummand x tau rho

/-- On a short approach, the normalized heat kernel is dominated by
`4/tau` times its boundary Poisson kernel. -/
theorem upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient_le_density
    {x delta y : ℝ} {alpha : ℂ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖(x : ℂ) - alpha‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (halpha : 0 < alpha.im) {tau : ℝ} (htau : 0 < tau) :
    upperHalfPlaneHyperbolicHeatIntegrand
        (upperBoundaryApproachPoint x y) alpha tau / (2 * y) ≤
      (4 * tau⁻¹) *
        (2 * alpha.im /
          Complex.normSq ((x : ℂ) - alpha)) := by
  let D := Complex.normSq ((x : ℂ) - alpha)
  have hD : 0 < D := by
    dsimp [D]
    apply Complex.normSq_pos.mpr
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    simp only [ofReal_im] at him
    linarith
  have hDexp := normSq_boundary_mul_exp_approach_le_four_inv
    hdelta hgap hy hySmall htau
  have hkernel :
      2 * alpha.im *
          Real.exp (-(Complex.normSq
            (upperBoundaryApproachPoint x y - alpha) * tau)) ≤
        (4 * tau⁻¹) * (2 * alpha.im / D) := by
    rw [show (4 * tau⁻¹) * (2 * alpha.im / D) =
        ((4 * tau⁻¹) * (2 * alpha.im)) / D by ring,
      le_div_iff₀ hD]
    have hscaled := mul_le_mul_of_nonneg_left hDexp
      (show 0 ≤ 2 * alpha.im by positivity)
    dsimp [D] at hscaled ⊢
    nlinarith
  exact
    (upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient_le
      x hy alpha htau).trans hkernel

/-- The multiplicity-counted normalized heat summand has the same summable
boundary-density dominator. -/
theorem zetaUpperHyperbolicHeatSummand_boundaryQuotient_le_density
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicHeatSummand
        (upperBoundaryApproachPoint x y) tau rho / (2 * y) ≤
      (4 * tau⁻¹) * zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hkernel :=
      upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient_le_density
        hdelta (hgap rho hupper) hy hySmall hupper htau
    rw [zetaUpperHyperbolicHeatSummand, if_pos hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
            upperHalfPlaneHyperbolicHeatIntegrand
              (upperBoundaryApproachPoint x y)
              (zetaSpectralCoordinate rho.1) tau / (2 * y) =
          (analyticZetaZeroMultiplicity rho : ℝ) *
            (upperHalfPlaneHyperbolicHeatIntegrand
              (upperBoundaryApproachPoint x y)
              (zetaSpectralCoordinate rho.1) tau / (2 * y)) := by ring
      _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) *
          ((4 * tau⁻¹) *
            (2 * (zetaSpectralCoordinate rho.1).im /
              Complex.normSq
                ((x : ℂ) - zetaSpectralCoordinate rho.1))) :=
        mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg _)
      _ = (4 * tau⁻¹) *
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            (2 * (zetaSpectralCoordinate rho.1).im /
              Complex.normSq
                ((x : ℂ) - zetaSpectralCoordinate rho.1))) := by ring
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]
    norm_num

/-- Each normalized spectral heat term converges to its fixed-time boundary
heat density. -/
theorem tendsto_zetaUpperHyperbolicHeatSummand_boundaryQuotient
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun y : ℝ ↦ zetaUpperHyperbolicHeatSummand
        (upperBoundaryApproachPoint x y) tau rho / (2 * y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (zetaUpperHyperbolicBoundaryHeatSummand x tau rho)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hlimit :=
      tendsto_upperHalfPlaneHyperbolicHeatIntegrand_boundaryQuotient
        x (zetaSpectralCoordinate rho.1) htau
    rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
    simpa only [zetaUpperHyperbolicHeatSummand, if_pos hupper,
      mul_div_assoc] using
        hlimit.const_mul (analyticZetaZeroMultiplicity rho : ℝ)
  · simp only [zetaUpperHyperbolicHeatSummand, if_neg hupper,
      zetaUpperHyperbolicBoundaryHeatSummand, zero_div]
    exact tendsto_const_nhds

/-- Tannery's theorem passes the normalized fixed-time boundary limit through
the complete upper spectral divisor. -/
theorem tendsto_tsum_zetaUpperHyperbolicHeatSummand_boundaryQuotient
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun y : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaUpperHyperbolicHeatSummand
          (upperBoundaryApproachPoint x y) tau rho / (2 * y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  have hlimit := tendsto_tsum_of_dominated_convergence
    ((summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left
      (4 * tau⁻¹))
    (tendsto_zetaUpperHyperbolicHeatSummand_boundaryQuotient x htau)
    (by
      have hpositive : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), 0 < y :=
        eventually_nhdsWithin_of_forall fun _ hy ↦ hy
      have hsmall : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
          y < delta / 2 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
      filter_upwards [hpositive, hsmall] with y hy hySmall
      intro rho
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact
          zetaUpperHyperbolicHeatSummand_boundaryQuotient_le_density
            hdelta hgap hy hySmall htau rho
      · exact div_nonneg
          (zetaUpperHyperbolicHeatSummand_nonneg
            (by simpa using hy) htau rho)
          (by positivity))
  simpa only [riemannXiUpperHyperbolicBoundaryHeatTotal] using hlimit

/-- The complete fixed-time heat sum divided by `2*y` has the finite boundary
heat density as its exact vertical limit. -/
theorem tendsto_riemannXiUpperHyperbolicHeatSum_boundaryQuotient
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun y : ℝ ↦
        riemannXiUpperHyperbolicHeatSum
          (upperBoundaryApproachPoint x y) tau / (2 * y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  apply
    (tendsto_tsum_zetaUpperHyperbolicHeatSummand_boundaryQuotient
      x htau).congr'
  filter_upwards with y
  rw [riemannXiUpperHyperbolicHeatSum, tsum_div_const]

/-- The complete fixed-time boundary heat total is nonnegative. -/
theorem riemannXiUpperHyperbolicBoundaryHeatTotal_nonneg
    (x tau : ℝ) :
    0 ≤ riemannXiUpperHyperbolicBoundaryHeatTotal x tau := by
  unfold riemannXiUpperHyperbolicBoundaryHeatTotal
  exact tsum_nonneg
    (zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau)

/-- An upper spectral zero contributes strictly positive fixed-time boundary
heat at every real point and every proper time. -/
theorem zetaUpperHyperbolicBoundaryHeatSummand_pos
    (x tau : ℝ)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < zetaUpperHyperbolicBoundaryHeatSummand x tau rho := by
  rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
  exact mul_pos
    (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
    (mul_pos (by positivity) (Real.exp_pos _))

/-- One upper spectral zero makes every positive-time boundary heat total
strictly positive. -/
theorem riemannXiUpperHyperbolicBoundaryHeatTotal_pos_of_upper_zero
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < riemannXiUpperHyperbolicBoundaryHeatTotal x tau := by
  unfold riemannXiUpperHyperbolicBoundaryHeatTotal
  exact
    (summable_zetaUpperHyperbolicBoundaryHeatSummand x htau).tsum_pos
      (zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau) rho
      (zetaUpperHyperbolicBoundaryHeatSummand_pos x tau rho hupper)

/-- At every real point and positive proper time, the fixed-time boundary
heat total vanishes exactly under RH. -/
theorem riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hpos :=
      riemannXiUpperHyperbolicBoundaryHeatTotal_pos_of_upper_zero
        x htau rho hwupper
    linarith
  · intro hRH
    unfold riemannXiUpperHyperbolicBoundaryHeatTotal
    have hzero :
        zetaUpperHyperbolicBoundaryHeatSummand x tau = fun _ ↦ 0 := by
      funext rho
      have him : (zetaSpectralCoordinate rho.1).im = 0 :=
        (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
          rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
      rw [zetaUpperHyperbolicBoundaryHeatSummand, if_neg]
      linarith
    rw [hzero, tsum_zero]

/-- Direct fixed-proper-time boundary reformulation of RH. -/
theorem tendsto_riemannXiUpperHyperbolicHeatSum_boundaryQuotient_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
        (fun y : ℝ ↦
          riemannXiUpperHyperbolicHeatSum
            (upperBoundaryApproachPoint x y) tau / (2 * y))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have hlimit :=
      tendsto_riemannXiUpperHyperbolicHeatSum_boundaryQuotient x htau
    have hvalue :
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      tendsto_nhds_unique hlimit hzero
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp hvalue
  · intro hRH
    have hvalue :
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    simpa only [hvalue] using
      tendsto_riemannXiUpperHyperbolicHeatSum_boundaryQuotient x htau

end

end RiemannGaussian
