import RiemannGaussian.RiemannXiBoundaryBlaschkeRigidity

/-!
# Boundary limit of the complete Poisson--Blaschke variation

The complete elementary Blaschke derivative variation in the upper half-plane
has a genuine boundary value.  Along the vertical approach `x + I*y`, every
positive-height summand is dominated by its boundary density: moving upward
only increases the distance to the reflected pole.  The already-proved
boundary inverse-square summability therefore gives a Tannery dominated-
convergence passage for the complete divisor.

This identifies the cancellation-free boundary RH invariant as the normalized
zero-height limit of the existing Poisson/Blaschke chain.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Vertical approach to the real spectral boundary. -/
def upperBoundaryApproachPoint (x y : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * (y : ℂ)

@[simp]
theorem upperBoundaryApproachPoint_re (x y : ℝ) :
    (upperBoundaryApproachPoint x y).re = x := by
  simp [upperBoundaryApproachPoint]

@[simp]
theorem upperBoundaryApproachPoint_im (x y : ℝ) :
    (upperBoundaryApproachPoint x y).im = y := by
  simp [upperBoundaryApproachPoint]

@[simp]
theorem upperBoundaryApproachPoint_zero (x : ℝ) :
    upperBoundaryApproachPoint x 0 = (x : ℂ) := by
  simp [upperBoundaryApproachPoint]

/-- Moving a real boundary point vertically upward increases the squared
distance to a reflected upper-half-plane pole by `y^2 + 2*y*alpha.im`. -/
theorem normSq_upperBoundaryApproachPoint_sub_conj
    (x y : ℝ) (alpha : ℂ) :
    Complex.normSq
        (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) =
      Complex.normSq ((x : ℂ) - alpha) + y ^ 2 + 2 * y * alpha.im := by
  unfold upperBoundaryApproachPoint Complex.normSq
  simp
  ring

/-- Explicit derivative-variation formula on a positive vertical approach. -/
theorem zetaUpperBlaschkeDerivativeVariationSummand_approach_eq
    (x : ℝ) {y : ℝ} (hy : 0 < y) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    zetaUpperBlaschkeDerivativeVariationSummand
        (upperBoundaryApproachPoint x y) rho =
      (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * (zetaSpectralCoordinate rho.1).im /
          Complex.normSq
            (upperBoundaryApproachPoint x y -
              starRingEnd ℂ (zetaSpectralCoordinate rho.1))) := by
  rw [zetaUpperBlaschkeDerivativeVariationSummand, if_pos hupper,
    norm_deriv_elementaryUpperHalfPlaneBlaschke
      (by simpa using hy) hupper]

/-- Every positive-height approach summand is bounded by its boundary value. -/
theorem zetaUpperBlaschkeDerivativeVariationSummand_approach_le_boundary
    (x : ℝ) {y : ℝ} (hy : 0 < y) (rho : NontrivialZetaZero) :
    zetaUpperBlaschkeDerivativeVariationSummand
        (upperBoundaryApproachPoint x y) rho ≤
      zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBlaschkeDerivativeVariationSummand_approach_eq
      x hy rho hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    have hboundary :
        0 < Complex.normSq
          ((x : ℂ) - zetaSpectralCoordinate rho.1) := by
      apply Complex.normSq_pos.mpr
      apply sub_ne_zero.mpr
      intro heq
      have him := congrArg Complex.im heq
      simp only [ofReal_im] at him
      linarith
    have happ :
        0 < Complex.normSq
          (upperBoundaryApproachPoint x y -
            starRingEnd ℂ (zetaSpectralCoordinate rho.1)) := by
      exact Complex.normSq_pos.mpr
        (sub_conj_ne_zero_of_im_pos (by simpa using hy) hupper)
    have hden :
        Complex.normSq ((x : ℂ) - zetaSpectralCoordinate rho.1) ≤
          Complex.normSq
            (upperBoundaryApproachPoint x y -
              starRingEnd ℂ (zetaSpectralCoordinate rho.1)) := by
      rw [normSq_upperBoundaryApproachPoint_sub_conj]
      nlinarith [sq_nonneg y]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [div_le_div_iff₀ happ hboundary]
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  · rw [zetaUpperBlaschkeDerivativeVariationSummand,
      if_neg hupper, zetaUpperBlaschkeBoundaryDensitySummand,
      if_neg hupper]

/-- Each elementary derivative-variation summand tends to its positive
boundary density along `y -> 0+`. -/
theorem tendsto_zetaUpperBlaschkeDerivativeVariationSummand_approach
    (x : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun y : ℝ ↦ zetaUpperBlaschkeDerivativeVariationSummand
        (upperBoundaryApproachPoint x y) rho)
      (nhdsWithin 0 (Ioi 0))
      (nhds (zetaUpperBlaschkeBoundaryDensitySummand x rho)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let f : ℝ → ℝ := fun y ↦
      (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * (zetaSpectralCoordinate rho.1).im /
          (Complex.normSq
              ((x : ℂ) - zetaSpectralCoordinate rho.1) +
            y ^ 2 + 2 * y * (zetaSpectralCoordinate rho.1).im))
    have hden : Complex.normSq
        ((x : ℂ) - zetaSpectralCoordinate rho.1) ≠ 0 := by
      exact (Complex.normSq_pos.mpr
        (sub_ne_zero.mpr (by
          intro heq
          have him := congrArg Complex.im heq
          simp only [ofReal_im] at him
          linarith))).ne'
    have hf : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0)) := by
      have hcontinuous : ContinuousAt f 0 := by
        dsimp [f]
        fun_prop (disch := simp_all)
      exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
    have hvalue : f 0 = zetaUpperBlaschkeBoundaryDensitySummand x rho := by
      dsimp [f]
      rw [zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
      norm_num
    rw [← hvalue]
    apply hf.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [zetaUpperBlaschkeDerivativeVariationSummand_approach_eq
      x hy rho hupper]
    dsimp [f]
    rw [normSq_upperBoundaryApproachPoint_sub_conj]
  · simp only [zetaUpperBlaschkeDerivativeVariationSummand,
      zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]
    exact tendsto_const_nhds

/-- Tannery's theorem passes the vertical boundary limit through the complete
multiplicity-counted upper divisor. -/
theorem tendsto_tsum_zetaUpperBlaschkeDerivativeVariationSummand_approach
    (x : ℝ) :
    Tendsto
      (fun y : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaUpperBlaschkeDerivativeVariationSummand
          (upperBoundaryApproachPoint x y) rho)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperBlaschkeBoundaryDensityTotal x)) := by
  have hlimit := tendsto_tsum_of_dominated_convergence
    (summable_zetaUpperBlaschkeBoundaryDensitySummand x)
    (tendsto_zetaUpperBlaschkeDerivativeVariationSummand_approach x)
    (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      intro rho
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (zetaUpperBlaschkeDerivativeVariationSummand_nonneg
            (upperBoundaryApproachPoint x y) rho)]
      exact
        zetaUpperBlaschkeDerivativeVariationSummand_approach_le_boundary
          x hy rho)
  simpa only [riemannXiUpperBlaschkeBoundaryDensityTotal] using hlimit

/-- The existing finite real Blaschke-variation total converges to the
boundary density total along every vertical approach. -/
theorem tendsto_riemannXiUpperBlaschkeDerivativeVariationTotal_approach
    (x : ℝ) :
    Tendsto
      (fun y : ℝ ↦ riemannXiUpperBlaschkeDerivativeVariationTotal
        (upperBoundaryApproachPoint x y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperBlaschkeBoundaryDensityTotal x)) := by
  apply
    (tendsto_tsum_zetaUpperBlaschkeDerivativeVariationSummand_approach
      x).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact
    (riemannXiUpperBlaschkeDerivativeVariationTotal_eq_tsum
      (by simpa using hy)).symm

/-- Extended-real form of the same complete Blaschke-variation boundary
limit. -/
theorem tendsto_riemannXiUpperBlaschkeDerivativeVariationMass_approach
    (x : ℝ) :
    Tendsto
      (fun y : ℝ ↦ riemannXiUpperBlaschkeDerivativeVariationMass
        (upperBoundaryApproachPoint x y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (ENNReal.ofReal
        (riemannXiUpperBlaschkeBoundaryDensityTotal x))) := by
  apply (ENNReal.tendsto_ofReal
    (tendsto_riemannXiUpperBlaschkeDerivativeVariationTotal_approach x)).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact ofReal_riemannXiUpperBlaschkeDerivativeVariationTotal
    (by simpa using hy)

/-- The finite extended boundary value of the normalized complete Poisson
mass. -/
def riemannXiUpperHyperbolicPoissonBoundaryLimit (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (riemannXiUpperBlaschkeBoundaryDensityTotal x)

/-- The normalized Poisson boundary value vanishes exactly under RH, at every
real boundary point. -/
theorem riemannXiUpperHyperbolicPoissonBoundaryLimit_eq_zero_iff_rh
    (x : ℝ) :
    riemannXiUpperHyperbolicPoissonBoundaryLimit x = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have hnonpos : riemannXiUpperBlaschkeBoundaryDensityTotal x ≤ 0 := by
      exact ENNReal.ofReal_eq_zero.mp hzero
    have hdensity : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 :=
      le_antisymm hnonpos
        (riemannXiUpperBlaschkeBoundaryDensityTotal_nonneg x)
    exact
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mp
        hdensity
  · intro hRH
    have hdensity : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 :=
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mpr
        hRH
    simp [riemannXiUpperHyperbolicPoissonBoundaryLimit, hdensity]

/-- The Poisson mass divided by its exact observation-height factor.  For
`y > 0` this is literally the complete Blaschke derivative variation. -/
def riemannXiUpperHyperbolicPoissonBoundaryQuotient (x y : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * y))⁻¹ *
    riemannXiUpperHyperbolicPoissonDefectMass
      (upperBoundaryApproachPoint x y)

/-- At positive height, the normalized Poisson mass is exactly the complete
Blaschke derivative-variation mass. -/
theorem riemannXiUpperHyperbolicPoissonBoundaryQuotient_eq_variationMass
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    riemannXiUpperHyperbolicPoissonBoundaryQuotient x y =
      riemannXiUpperBlaschkeDerivativeVariationMass
        (upperBoundaryApproachPoint x y) := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hfactorZero : ENNReal.ofReal (2 * y) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hfactorTop : ENNReal.ofReal (2 * y) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold riemannXiUpperHyperbolicPoissonBoundaryQuotient
  rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
    hz, upperBoundaryApproachPoint_im, ← mul_assoc,
    ENNReal.inv_mul_cancel hfactorZero hfactorTop, one_mul]

/-- The normalized complete Poisson mass converges to the finite boundary
density total as the observation height tends to zero. -/
theorem tendsto_riemannXiUpperHyperbolicPoissonBoundaryQuotient
    (x : ℝ) :
    Tendsto
      (riemannXiUpperHyperbolicPoissonBoundaryQuotient x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicPoissonBoundaryLimit x)) := by
  unfold riemannXiUpperHyperbolicPoissonBoundaryLimit
  apply
    (tendsto_riemannXiUpperBlaschkeDerivativeVariationMass_approach x).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact
    (riemannXiUpperHyperbolicPoissonBoundaryQuotient_eq_variationMass
      x hy).symm

/-- Boundary bridge to the cancellation-free complex invariant: the
normalized Poisson mass tends to the embedded norm of the complete signed
boundary logarithmic derivative. -/
theorem tendsto_riemannXiUpperHyperbolicPoissonBoundaryQuotient_logDerivativeNorm
    (x : ℝ) :
    Tendsto
      (riemannXiUpperHyperbolicPoissonBoundaryQuotient x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (ENNReal.ofReal
        ‖riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)‖)) := by
  rw [norm_riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density x]
  exact tendsto_riemannXiUpperHyperbolicPoissonBoundaryQuotient x

end

end RiemannGaussian
