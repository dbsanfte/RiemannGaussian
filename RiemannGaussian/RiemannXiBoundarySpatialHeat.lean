import RiemannGaussian.RiemannXiBoundaryGaussianGram
import RiemannGaussian.RiemannXiUpperHeightTrace

/-!
# Spatial integration of the boundary heat Gram density

The reflected-pair boundary heat density still records both the real
ordinate and the off-critical height of every upper spectral zero.  This
file integrates over the real observation center.  The ordinary Gaussian
integral erases the ordinate exactly and leaves the positive height-only
transform

`sum_rho m(rho) * height(rho) * exp (-tau * height(rho)^2)`.

All complete-series statements are proved in `ℝ≥0∞`, because finiteness of
the unweighted total upper height is not assumed.  Tonelli gives the exact
spatial integral.  Since every off-critical height is strictly below `1/2`,
the height transform lies between `exp(-tau/4)` times the full height mass
and the full height mass.  Consequently Gaussian damping preserves both
vanishing and divergence, and the normalized spatial boundary heat tends to
the already formalized zero-time spectral height trace as `tau → 0+`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-counted upper height damped only by its transverse
Gaussian factor. -/
def zetaUpperSpectralHeightGaussianSummand
    (tau : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  zetaUpperSpectralHeightSummand rho *
    Real.exp (-(tau * (zetaSpectralCoordinate rho.1).im ^ 2))

/-- Every transverse height-Gaussian summand is nonnegative. -/
theorem zetaUpperSpectralHeightGaussianSummand_nonneg
    (tau : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperSpectralHeightGaussianSummand tau rho := by
  unfold zetaUpperSpectralHeightGaussianSummand
  exact mul_nonneg (zetaUpperSpectralHeightSummand_nonneg rho)
    (Real.exp_pos _).le

/-- Exact separation of one boundary heat term into its transverse height
weight and its translated Gaussian in the real center. -/
theorem zetaUpperHyperbolicBoundaryHeatSummand_eq_heightGaussian
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicBoundaryHeatSummand x tau rho =
      2 * zetaUpperSpectralHeightGaussianSummand tau rho *
        translatedGaussian tau (zetaSpectralCoordinate rho.1).re x := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper,
      zetaUpperSpectralHeightGaussianSummand,
      zetaUpperSpectralHeightSummand, if_pos hupper,
      translatedGaussian, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, zero_sub]
    have hexponent :
        -(((x - (zetaSpectralCoordinate rho.1).re) *
              (x - (zetaSpectralCoordinate rho.1).re) +
            (-(zetaSpectralCoordinate rho.1).im) *
              (-(zetaSpectralCoordinate rho.1).im)) * tau) =
          -(tau * (zetaSpectralCoordinate rho.1).im ^ 2) +
            (-tau * (x - (zetaSpectralCoordinate rho.1).re) ^ 2) := by
      ring
    rw [hexponent, Real.exp_add]
    ring
  · rw [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper,
      zetaUpperSpectralHeightGaussianSummand,
      zetaUpperSpectralHeightSummand, if_neg hupper]
    simp

/-- One boundary heat summand is integrable over its real observation
center. -/
theorem integrable_zetaUpperHyperbolicBoundaryHeatSummand
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    Integrable (fun x : ℝ ↦
      zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
  have hgauss := integrable_translatedGaussian htau
    (zetaSpectralCoordinate rho.1).re
  have hscaled := hgauss.const_mul
    (2 * zetaUpperSpectralHeightGaussianSummand tau rho)
  exact hscaled.congr (Eventually.of_forall fun x ↦
    (zetaUpperHyperbolicBoundaryHeatSummand_eq_heightGaussian
      x tau rho).symm)

/-- The ordinary spatial integral of one boundary heat term erases its real
spectral ordinate. -/
theorem integral_zetaUpperHyperbolicBoundaryHeatSummand
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    (∫ x : ℝ, zetaUpperHyperbolicBoundaryHeatSummand x tau rho) =
      2 * Real.sqrt (Real.pi / tau) *
        zetaUpperSpectralHeightGaussianSummand tau rho := by
  rw [integral_congr_ae (Eventually.of_forall fun x ↦
      zetaUpperHyperbolicBoundaryHeatSummand_eq_heightGaussian
        x tau rho),
    MeasureTheory.integral_const_mul,
    integral_translatedGaussian htau]
  ring

/-- Extended-real form of the one-term spatial Gaussian integral. -/
theorem lintegral_ofReal_zetaUpperHyperbolicBoundaryHeatSummand_center
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      (zetaUpperHyperbolicBoundaryHeatSummand x tau rho)) =
      ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau) *
        zetaUpperSpectralHeightGaussianSummand tau rho) := by
  have hint := integrable_zetaUpperHyperbolicBoundaryHeatSummand htau rho
  have hnonneg : 0 ≤ᵐ[volume]
      fun x : ℝ ↦ zetaUpperHyperbolicBoundaryHeatSummand x tau rho :=
    Eventually.of_forall fun x ↦
      zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau rho
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal
        (zetaUpperHyperbolicBoundaryHeatSummand x tau rho)) =
        ENNReal.ofReal
          (∫ x : ℝ,
            zetaUpperHyperbolicBoundaryHeatSummand x tau rho) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau) *
        zetaUpperSpectralHeightGaussianSummand tau rho) := by
      rw [integral_zetaUpperHyperbolicBoundaryHeatSummand htau]

/-- One boundary heat summand is continuous in the real observation
center. -/
theorem continuous_zetaUpperHyperbolicBoundaryHeatSummand_center
    (tau : ℝ) (rho : NontrivialZetaZero) :
    Continuous (fun x : ℝ ↦
      zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [zetaUpperHyperbolicBoundaryHeatSummand, if_pos hupper]
    fun_prop
  · simp only [zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
    fun_prop

/-- The complete transverse Gaussian transform of the upper spectral height
divisor. -/
def riemannXiUpperSpectralHeightGaussianMass (tau : ℝ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaUpperSpectralHeightGaussianSummand tau rho)

/-- The complete boundary heat density integrated over every real
observation center. -/
def riemannXiUpperHyperbolicBoundarySpatialHeatMass
    (tau : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ,
    ENNReal.ofReal (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)

/-- Tonelli identifies the full spatial boundary heat with the height-only
Gaussian transform and its exact normalization. -/
theorem riemannXiUpperHyperbolicBoundarySpatialHeatMass_eq_heightGaussianMass
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundarySpatialHeatMass tau =
      ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)) *
        riemannXiUpperSpectralHeightGaussianMass tau := by
  have hcoefficient : 0 ≤ 2 * Real.sqrt (Real.pi / tau) := by
    positivity
  unfold riemannXiUpperHyperbolicBoundarySpatialHeatMass
  calc
    (∫⁻ x : ℝ,
        ENNReal.ofReal
          (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) =
        ∫⁻ x : ℝ, ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
      apply lintegral_congr
      intro x
      exact ofReal_riemannXiUpperHyperbolicBoundaryHeatTotal_eq_tsum
        x htau
    _ = ∑' rho : NontrivialZetaZero,
          ∫⁻ x : ℝ, ENNReal.ofReal
            (zetaUpperHyperbolicBoundaryHeatSummand x tau rho) := by
      exact lintegral_tsum fun rho ↦
        (continuous_zetaUpperHyperbolicBoundaryHeatSummand_center
          tau rho).aemeasurable.ennreal_ofReal
    _ = ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau) *
            zetaUpperSpectralHeightGaussianSummand tau rho) := by
      apply tsum_congr
      exact
        lintegral_ofReal_zetaUpperHyperbolicBoundaryHeatSummand_center htau
    _ = ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)) *
          riemannXiUpperSpectralHeightGaussianMass tau := by
      unfold riemannXiUpperSpectralHeightGaussianMass
      simp_rw [ENNReal.ofReal_mul hcoefficient]
      exact ENNReal.tsum_mul_left

/-- Positive-time Gaussian damping never enlarges one upper-height term. -/
theorem zetaUpperSpectralHeightGaussianSummand_le_height
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    zetaUpperSpectralHeightGaussianSummand tau rho ≤
      zetaUpperSpectralHeightSummand rho := by
  unfold zetaUpperSpectralHeightGaussianSummand
  have hexp : Real.exp (-(tau *
      (zetaSpectralCoordinate rho.1).im ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr
      (mul_nonneg htau.le (sq_nonneg _))
  exact mul_le_of_le_one_right
    (zetaUpperSpectralHeightSummand_nonneg rho) hexp

/-- The universal spectral-height bound `|Im alpha| < 1/2` gives a uniform
lower Gaussian weight `exp(-tau/4)`. -/
theorem exp_neg_quarter_mul_height_le_zetaUpperSpectralHeightGaussianSummand
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    Real.exp (-tau / 4) * zetaUpperSpectralHeightSummand rho ≤
      zetaUpperSpectralHeightGaussianSummand tau rho := by
  unfold zetaUpperSpectralHeightGaussianSummand
  have himsq : (zetaSpectralCoordinate rho.1).im ^ 2 ≤ 1 / 4 := by
    have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
    rcases abs_lt.mp habs with ⟨hneg, hpos⟩
    have hmul : 0 <
        ((1 / 2 : ℝ) - (zetaSpectralCoordinate rho.1).im) *
          ((1 / 2 : ℝ) + (zetaSpectralCoordinate rho.1).im) :=
      mul_pos (sub_pos.mpr hpos) (by linarith)
    nlinarith
  have hexp : Real.exp (-tau / 4) ≤
      Real.exp (-(tau * (zetaSpectralCoordinate rho.1).im ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [mul_comm (Real.exp (-tau / 4))]
  exact mul_le_mul_of_nonneg_left hexp
    (zetaUpperSpectralHeightSummand_nonneg rho)

/-- The complete height-Gaussian mass is bounded above by the full height
mass. -/
theorem riemannXiUpperSpectralHeightGaussianMass_le_heightMass
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperSpectralHeightGaussianMass tau ≤
      riemannXiUpperSpectralHeightMass := by
  unfold riemannXiUpperSpectralHeightGaussianMass
    riemannXiUpperSpectralHeightMass
  apply ENNReal.tsum_le_tsum
  intro rho
  exact ENNReal.ofReal_le_ofReal
    (zetaUpperSpectralHeightGaussianSummand_le_height htau rho)

/-- The complete height-Gaussian mass retains at least the universal
`exp(-tau/4)` fraction of the full extended height mass. -/
theorem exp_neg_quarter_mul_heightMass_le_heightGaussianMass
    {tau : ℝ} (htau : 0 < tau) :
    ENNReal.ofReal (Real.exp (-tau / 4)) *
        riemannXiUpperSpectralHeightMass ≤
      riemannXiUpperSpectralHeightGaussianMass tau := by
  unfold riemannXiUpperSpectralHeightMass
    riemannXiUpperSpectralHeightGaussianMass
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rho
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal
    (exp_neg_quarter_mul_height_le_zetaUpperSpectralHeightGaussianSummand
      htau rho)

/-- At every positive time, vanishing of the height-only Gaussian transform
is exactly RH. -/
theorem riemannXiUpperSpectralHeightGaussianMass_eq_zero_iff_rh
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperSpectralHeightGaussianMass tau = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have hlower :=
      exp_neg_quarter_mul_heightMass_le_heightGaussianMass htau
    rw [hzero, nonpos_iff_eq_zero] at hlower
    have hcoefficient :
        ENNReal.ofReal (Real.exp (-tau / 4)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    have hheight : riemannXiUpperSpectralHeightMass = 0 :=
      (mul_eq_zero.mp hlower).resolve_left hcoefficient
    exact
      riemannXiUpperSpectralHeightMass_eq_zero_iff_riemannHypothesis.mp
        hheight
  · intro hRH
    have hheight : riemannXiUpperSpectralHeightMass = 0 :=
      riemannXiUpperSpectralHeightMass_eq_zero_iff_riemannHypothesis.mpr hRH
    apply le_antisymm
    · exact (riemannXiUpperSpectralHeightGaussianMass_le_heightMass
        htau).trans_eq hheight
    · exact bot_le

/-- Gaussian damping by the uniformly bounded off-critical height neither
creates nor removes divergence of the complete height mass. -/
theorem riemannXiUpperSpectralHeightGaussianMass_eq_top_iff_heightMass_eq_top
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperSpectralHeightGaussianMass tau = ∞ ↔
      riemannXiUpperSpectralHeightMass = ∞ := by
  constructor
  · intro htop
    have hle := riemannXiUpperSpectralHeightGaussianMass_le_heightMass htau
    rw [htop] at hle
    exact top_unique hle
  · intro htop
    have hle := exp_neg_quarter_mul_heightMass_le_heightGaussianMass htau
    rw [htop] at hle
    have hcoefficient :
        ENNReal.ofReal (Real.exp (-tau / 4)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    rw [ENNReal.mul_top hcoefficient] at hle
    exact top_unique hle

/-- Dividing out the exact spatial Gaussian mass leaves precisely the
height-only transform. -/
theorem riemannXiUpperHyperbolicBoundarySpatialHeatMass_normalized
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundarySpatialHeatMass tau /
        ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)) =
      riemannXiUpperSpectralHeightGaussianMass tau := by
  rw [riemannXiUpperHyperbolicBoundarySpatialHeatMass_eq_heightGaussianMass
    htau, mul_comm]
  apply ENNReal.mul_div_cancel_right
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  · exact ENNReal.ofReal_ne_top

/-- At every positive time, the full spatial boundary heat vanishes exactly
under RH. -/
theorem riemannXiUpperHyperbolicBoundarySpatialHeatMass_eq_zero_iff_rh
    {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundarySpatialHeatMass tau = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperHyperbolicBoundarySpatialHeatMass_eq_heightGaussianMass
    htau, mul_eq_zero]
  simp only [ENNReal.ofReal_eq_zero, not_le.mpr (by positivity :
    0 < 2 * Real.sqrt (Real.pi / tau)), false_or]
  exact riemannXiUpperSpectralHeightGaussianMass_eq_zero_iff_rh htau

/-- As proper time tends to zero, the height-only Gaussian transform tends
to the complete extended upper spectral height mass. -/
theorem tendsto_riemannXiUpperSpectralHeightGaussianMass_zero :
    Tendsto riemannXiUpperSpectralHeightGaussianMass
      (nhdsWithin 0 (Ioi 0))
      (nhds riemannXiUpperSpectralHeightMass) := by
  have hreal : Tendsto (fun tau : ℝ ↦ Real.exp (-tau / 4))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcontinuous : Continuous fun tau : ℝ ↦ Real.exp (-tau / 4) := by
      fun_prop
    have hAt0 : ContinuousAt (fun tau : ℝ ↦ Real.exp (-tau / 4)) 0 :=
      hcontinuous.continuousAt
    have hAt : Tendsto (fun tau : ℝ ↦ Real.exp (-tau / 4))
        (nhds 0) (nhds 1) := by
      simpa using hAt0.tendsto
    exact hAt.mono_left inf_le_left
  have hcoefficient : Tendsto
      (fun tau : ℝ ↦ ENNReal.ofReal (Real.exp (-tau / 4)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hlowerLimit : Tendsto
      (fun tau : ℝ ↦ ENNReal.ofReal (Real.exp (-tau / 4)) *
        riemannXiUpperSpectralHeightMass)
      (nhdsWithin 0 (Ioi 0))
      (nhds riemannXiUpperSpectralHeightMass) := by
    simpa using ENNReal.Tendsto.mul_const hcoefficient
      (Or.inl one_ne_zero)
  have hpositive : ∀ᶠ tau : ℝ in nhdsWithin 0 (Ioi 0), 0 < tau :=
    eventually_nhdsWithin_of_forall fun _ htau ↦ htau
  have hlower : ∀ᶠ tau : ℝ in nhdsWithin 0 (Ioi 0),
      ENNReal.ofReal (Real.exp (-tau / 4)) *
          riemannXiUpperSpectralHeightMass ≤
        riemannXiUpperSpectralHeightGaussianMass tau := by
    filter_upwards [hpositive] with tau htau
    exact exp_neg_quarter_mul_heightMass_le_heightGaussianMass htau
  have hupper : ∀ᶠ tau : ℝ in nhdsWithin 0 (Ioi 0),
      riemannXiUpperSpectralHeightGaussianMass tau ≤
        riemannXiUpperSpectralHeightMass := by
    filter_upwards [hpositive] with tau htau
    exact riemannXiUpperSpectralHeightGaussianMass_le_heightMass htau
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit tendsto_const_nhds hlower hupper

/-- The normalized spatial boundary heat tends to the complete extended
upper spectral height mass. -/
theorem tendsto_normalized_riemannXiUpperHyperbolicBoundarySpatialHeatMass_zero :
    Tendsto
      (fun tau : ℝ ↦
        riemannXiUpperHyperbolicBoundarySpatialHeatMass tau /
          ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)))
      (nhdsWithin 0 (Ioi 0))
      (nhds riemannXiUpperSpectralHeightMass) := by
  apply tendsto_riemannXiUpperSpectralHeightGaussianMass_zero.congr'
  filter_upwards [eventually_nhdsWithin_of_forall
    (fun _ htau ↦ htau : ∀ tau : ℝ, tau ∈ Ioi 0 → 0 < tau)] with tau htau
  exact
    (riemannXiUpperHyperbolicBoundarySpatialHeatMass_normalized htau).symm

/-- At the canonical observation height `1/4`, the existing zero-time heat
trace is exactly the unscaled upper spectral height mass. -/
theorem riemannXiUpperHyperbolicHeatTrace_I_div_four_eq_heightMass :
    riemannXiUpperHyperbolicHeatTrace (Complex.I / 4) =
      riemannXiUpperSpectralHeightMass := by
  rw [riemannXiUpperHyperbolicHeatTrace_eq_heightMass]
  · norm_num
  · norm_num

/-- The normalized spatial boundary heat therefore tends exactly to the
existing canonical zero-time hyperbolic heat trace. -/
theorem tendsto_normalized_boundarySpatialHeatMass_canonicalHeatTrace :
    Tendsto
      (fun tau : ℝ ↦
        riemannXiUpperHyperbolicBoundarySpatialHeatMass tau /
          ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicHeatTrace (Complex.I / 4))) := by
  rw [riemannXiUpperHyperbolicHeatTrace_I_div_four_eq_heightMass]
  exact
    tendsto_normalized_riemannXiUpperHyperbolicBoundarySpatialHeatMass_zero

end

end RiemannGaussian
