import RiemannGaussian.RiemannXiCompletePhaseDispersion

/-!
# Boundary Blaschke rigidity

On the real spectral axis, every selected upper-half-plane Blaschke
logarithmic-derivative term is a positive real multiple of `I`.  Even if a
real point is itself a critical-line zero, analyticity isolates that point and
gives a uniform gap from every selected upper zero.  Inverse-square divisor
summability therefore makes the boundary Poisson-density series convergent
at every real point.

The complete signed resultant on that boundary point is exactly `I` times
this nonnegative real sum.  It vanishes exactly when there are no upper
spectral zeros, hence exactly when RH holds.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Fixed real-boundary coefficient for comparing a gap-separated Cauchy
denominator with the spectral inverse-square weight. -/
def realBoundaryInverseSquareCoefficient (x delta : ℝ) : ℝ :=
  2 + (1 + 2 * x ^ 2) / delta ^ 2

/-- A gap from the real observation point makes its upper-zero Cauchy
denominator dominate `1 + alpha.re^2`. -/
theorem one_add_re_sq_le_realBoundaryInverseSquareCoefficient_mul_normSq
    {x delta : ℝ} {alpha : ℂ} (hdelta : 0 < delta)
    (hgap : delta ≤ ‖(x : ℂ) - alpha‖) :
    1 + alpha.re ^ 2 ≤
      realBoundaryInverseSquareCoefficient x delta *
        Complex.normSq ((x : ℂ) - alpha) := by
  let D : ℝ := Complex.normSq ((x : ℂ) - alpha)
  have hhorizontal : (x - alpha.re) ^ 2 ≤ D := by
    dsimp [D]
    simp [Complex.normSq_apply]
    nlinarith [sq_nonneg alpha.im]
  have hgapSq : delta ^ 2 ≤ D := by
    dsimp [D]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((x : ℂ) - alpha)]
  have hshift :
      alpha.re ^ 2 ≤ 2 * x ^ 2 + 2 * (x - alpha.re) ^ 2 := by
    nlinarith [sq_nonneg (2 * x - alpha.re)]
  have hconstant :
      1 + 2 * x ^ 2 ≤
        ((1 + 2 * x ^ 2) / delta ^ 2) * D := by
    calc
      1 + 2 * x ^ 2 =
          ((1 + 2 * x ^ 2) / delta ^ 2) * delta ^ 2 := by
        field_simp [hdelta.ne']
      _ ≤ ((1 + 2 * x ^ 2) / delta ^ 2) * D :=
        mul_le_mul_of_nonneg_left hgapSq (by positivity)
  unfold realBoundaryInverseSquareCoefficient
  nlinarith

/-- The multiplicity-counted positive boundary density contributed by one
upper spectral zero. -/
def zetaUpperBlaschkeBoundaryDensitySummand
    (x : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (2 * (zetaSpectralCoordinate rho.1).im /
        Complex.normSq
          ((x : ℂ) - zetaSpectralCoordinate rho.1))
  else 0

/-- Every boundary density summand is nonnegative. -/
theorem zetaUpperBlaschkeBoundaryDensitySummand_nonneg
    (x : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by positivity) (Complex.normSq_nonneg _))
  · rw [zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]

/-- One selected upper zero contributes strictly positive boundary density. -/
theorem zetaUpperBlaschkeBoundaryDensitySummand_pos
    (x : ℝ) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  have hne : (x : ℂ) ≠ zetaSpectralCoordinate rho.1 := by
    intro heq
    have him := congrArg Complex.im heq
    simp only [ofReal_im] at him
    linarith
  rw [zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
  apply mul_pos
  · exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  · exact div_pos (by positivity)
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hne))

/-- A uniform spectral gap bounds boundary density by the inverse-square
spectral-ordinate summand. -/
theorem zetaUpperBlaschkeBoundaryDensitySummand_le_inverseSquare
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (rho : NontrivialZetaZero) :
    zetaUpperBlaschkeBoundaryDensitySummand x rho ≤
      realBoundaryInverseSquareCoefficient x delta *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let D : ℝ := Complex.normSq ((x : ℂ) - alpha)
    let Q : ℝ := 1 + alpha.re ^ 2
    let C : ℝ := realBoundaryInverseSquareCoefficient x delta
    have hD : 0 < D := by
      dsimp [D]
      apply Complex.normSq_pos.mpr
      apply sub_ne_zero.mpr
      intro heq
      have him := congrArg Complex.im heq
      simp only [ofReal_im] at him
      dsimp [alpha] at him
      linarith
    have hQ : 0 < Q := by
      dsimp [Q]
      positivity
    have hden : Q ≤ C * D := by
      exact
        one_add_re_sq_le_realBoundaryInverseSquareCoefficient_mul_normSq
          hdelta (hgap rho hupper)
    have hrecip : 1 / D ≤ C / Q := by
      rw [div_le_div_iff₀ hD hQ]
      simpa only [one_mul] using hden
    have hhalf : alpha.im ≤ 1 / 2 := by
      dsimp [alpha]
      have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      exact (le_abs_self _).trans habs.le
    have hnum : 2 * alpha.im ≤ 1 := by linarith
    rw [zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    change (analyticZetaZeroMultiplicity rho : ℝ) *
        (2 * alpha.im / D) ≤
      C * ((analyticZetaZeroMultiplicity rho : ℝ) / Q)
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
          (2 * alpha.im / D) ≤
        (analyticZetaZeroMultiplicity rho : ℝ) * (1 / D) := by
          gcongr
      _ ≤ (analyticZetaZeroMultiplicity rho : ℝ) * (C / Q) :=
        mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg _)
      _ = C * ((analyticZetaZeroMultiplicity rho : ℝ) / Q) := by ring
  · rw [zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]
    exact mul_nonneg
      (by
        unfold realBoundaryInverseSquareCoefficient
        positivity)
      (div_nonneg (Nat.cast_nonneg _) (by positivity))

/-- Every real boundary point has a uniform positive distance from the upper
spectral divisor.  A possible zero at the boundary point itself lies on the
critical line and is excluded from the selected upper divisor; analyticity
isolates it from every other spectral zero. -/
theorem exists_uniform_upper_zetaSpectralCoordinate_gap_real (x : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ rho : NontrivialZetaZero,
        0 < (zetaSpectralCoordinate rho.1).im →
          delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ := by
  by_cases hxi : riemannXiSpectral (x : ℂ) ≠ 0
  · obtain ⟨delta, hdelta, hgap⟩ :=
      exists_uniform_zetaSpectralCoordinate_gap_of_ne_zero hxi
    exact ⟨delta, hdelta, fun rho _ ↦ hgap rho⟩
  · have hxzero : riemannXiSpectral (x : ℂ) = 0 := not_ne_iff.mp hxi
    obtain ⟨rho₀, hxrho⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero (x : ℂ)).mp hxzero
    have hfinite : analyticOrderAt riemannXiSpectral (x : ℂ) ≠ ⊤ := by
      rw [hxrho,
        analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
        analyticOrderAt_riemannXi_eq_riemannZeta]
      exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho₀
    have hfne : ∀ᶠ z in 𝓝[≠] (x : ℂ), riemannXiSpectral z ≠ 0 :=
      (analyticAt_riemannXiSpectral
        (x : ℂ)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
          fun hzero ↦ hfinite (analyticOrderAt_eq_top.mpr hzero)
    have hfne' : ∀ᶠ z in 𝓝 (x : ℂ),
        z ≠ (x : ℂ) → riemannXiSpectral z ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hfne
      exact hfne
    obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hfne'
    refine ⟨delta, hdelta, ?_⟩
    intro rho hupper
    by_contra hgap
    have hlt : ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ < delta :=
      lt_of_not_ge hgap
    have hmem : zetaSpectralCoordinate rho.1 ∈ ball (x : ℂ) delta := by
      simpa only [mem_ball, dist_eq, norm_sub_rev] using hlt
    have hne : zetaSpectralCoordinate rho.1 ≠ (x : ℂ) := by
      intro heq
      have him := congrArg Complex.im heq
      simp only [ofReal_im] at him
      linarith
    exact (hball hmem hne)
      ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩)

/-- At every real boundary point, including critical-line zeros, the complete
upper-divisor boundary density is summable. -/
theorem summable_zetaUpperBlaschkeBoundaryDensitySummand
    (x : ℝ) :
    Summable (zetaUpperBlaschkeBoundaryDensitySummand x) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (realBoundaryInverseSquareCoefficient x delta)).of_nonneg_of_le
      (zetaUpperBlaschkeBoundaryDensitySummand_nonneg x)
  intro rho
  exact
    zetaUpperBlaschkeBoundaryDensitySummand_le_inverseSquare
      hdelta hgap rho

/-- The finite positive real boundary density total. -/
def riemannXiUpperBlaschkeBoundaryDensityTotal (x : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperBlaschkeBoundaryDensitySummand x rho

/-- The complete real-boundary density total is nonnegative. -/
theorem riemannXiUpperBlaschkeBoundaryDensityTotal_nonneg (x : ℝ) :
    0 ≤ riemannXiUpperBlaschkeBoundaryDensityTotal x := by
  unfold riemannXiUpperBlaschkeBoundaryDensityTotal
  exact tsum_nonneg (zetaUpperBlaschkeBoundaryDensitySummand_nonneg x)

/-- One upper spectral zero makes the complete boundary density strictly
positive at every real point. -/
theorem riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_upper_zero
    (x : ℝ) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < riemannXiUpperBlaschkeBoundaryDensityTotal x := by
  unfold riemannXiUpperBlaschkeBoundaryDensityTotal
  exact
    (summable_zetaUpperBlaschkeBoundaryDensitySummand x).tsum_pos
      (zetaUpperBlaschkeBoundaryDensitySummand_nonneg x) rho
      (zetaUpperBlaschkeBoundaryDensitySummand_pos x rho hupper)

/-- If RH fails, the complete boundary density is strictly positive at every
real point. -/
theorem riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_not_rh
    (x : ℝ) (hRH : ¬ RiemannHypothesis) :
    0 < riemannXiUpperBlaschkeBoundaryDensityTotal x := by
  obtain ⟨w, hwzero, hwupper⟩ :=
    exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
  obtain ⟨rho, rfl⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
  exact
    riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_upper_zero
      x rho hwupper

/-- At every real point, vanishing of the complete positive boundary density
is equivalent to RH. -/
theorem riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh
    (x : ℝ) :
    riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    have hpos :=
      riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_not_rh x hRH
    linarith
  · intro hRH
    unfold riemannXiUpperBlaschkeBoundaryDensityTotal
    have hzero : zetaUpperBlaschkeBoundaryDensitySummand x = fun _ ↦ 0 := by
      funext rho
      have him : (zetaSpectralCoordinate rho.1).im = 0 :=
        (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
          rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
      rw [zetaUpperBlaschkeBoundaryDensitySummand, if_neg]
      linarith
    rw [hzero, tsum_zero]

/-- At a real boundary point, the paired Cauchy logarithmic derivative of one
upper-half-plane zero is a positive real multiple of `I`. -/
theorem one_div_real_sub_sub_one_div_real_sub_conj
    {x : ℝ} {alpha : ℂ} (halpha : 0 < alpha.im) :
    1 / ((x : ℂ) - alpha) -
        1 / ((x : ℂ) - starRingEnd ℂ alpha) =
      (((2 * alpha.im /
        Complex.normSq ((x : ℂ) - alpha) : ℝ) : ℂ) * Complex.I) := by
  have hleft : (x : ℂ) - alpha ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    simp only [ofReal_im] at him
    linarith
  have hright : (x : ℂ) - starRingEnd ℂ alpha ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    simp only [ofReal_im, conj_im] at him
    linarith
  have hnum :
      alpha - starRingEnd ℂ alpha =
        ((2 * alpha.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hden :
      ((x : ℂ) - alpha) *
          ((x : ℂ) - starRingEnd ℂ alpha) =
        (Complex.normSq ((x : ℂ) - alpha) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sub, conj_ofReal]
    ring
  calc
    1 / ((x : ℂ) - alpha) -
        1 / ((x : ℂ) - starRingEnd ℂ alpha) =
      (alpha - starRingEnd ℂ alpha) /
        (((x : ℂ) - alpha) *
          ((x : ℂ) - starRingEnd ℂ alpha)) := by
            field_simp [hleft, hright]
            ring
    _ = (((2 * alpha.im /
          Complex.normSq ((x : ℂ) - alpha) : ℝ) : ℂ) * Complex.I) := by
      rw [hnum, hden]
      push_cast
      ring

/-- The selected multiplicity-counted logarithmic-derivative term agrees
exactly with `I` times its nonnegative real boundary density. -/
theorem zetaUpperBlaschkeSelectedLogDerivativeSummand_real_eq_density_mul_I
    (x : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperBlaschkeSelectedLogDerivativeSummand (x : ℂ) rho =
      (zetaUpperBlaschkeBoundaryDensitySummand x rho : ℂ) * Complex.I := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    unfold zetaUpperBlaschkeLogDerivativeSummand
    rw [one_div_real_sub_sub_one_div_real_sub_conj hupper]
    push_cast
    ring
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper]
    simp

/-- The selected complete logarithmic-derivative series has sum `I` times
the complete positive boundary density at every real point. -/
theorem hasSum_zetaUpperBlaschkeSelectedLogDerivativeSummand_real
    (x : ℝ) :
    HasSum (zetaUpperBlaschkeSelectedLogDerivativeSummand (x : ℂ))
      ((riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) * Complex.I) := by
  have hreal :
      HasSum (zetaUpperBlaschkeBoundaryDensitySummand x)
        (riemannXiUpperBlaschkeBoundaryDensityTotal x) := by
    exact (summable_zetaUpperBlaschkeBoundaryDensitySummand x).hasSum
  have hcomplex :
      HasSum (fun rho : NontrivialZetaZero ↦
        (zetaUpperBlaschkeBoundaryDensitySummand x rho : ℂ))
        (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) :=
    Complex.hasSum_ofReal.mpr hreal
  exact (hcomplex.mul_right Complex.I).congr_fun fun rho ↦
    zetaUpperBlaschkeSelectedLogDerivativeSummand_real_eq_density_mul_I x rho

/-- On the real spectral boundary, the complete signed Blaschke logarithmic
derivative is exactly `I` times a convergent nonnegative real sum. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I
    (x : ℝ) :
    riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ) =
      (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) * Complex.I := by
  unfold riemannXiUpperBlaschkeCompleteLogDerivative
  exact
    (hasSum_zetaUpperBlaschkeSelectedLogDerivativeSummand_real x).tsum_eq

/-- The boundary complete logarithmic derivative has zero real part. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_re_eq_zero
    (x : ℝ) :
    (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)).re = 0 := by
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I x]
  simp

/-- The imaginary part of the boundary complete logarithmic derivative is
exactly the complete positive boundary density. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_im_eq_density
    (x : ℝ) :
    (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)).im =
      riemannXiUpperBlaschkeBoundaryDensityTotal x := by
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I x]
  simp

/-- There is no boundary phase cancellation: the norm of the complete signed
resultant is exactly its positive density total. -/
theorem norm_riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density
    (x : ℝ) :
    ‖riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)‖ =
      riemannXiUpperBlaschkeBoundaryDensityTotal x := by
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I x,
    norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (riemannXiUpperBlaschkeBoundaryDensityTotal_nonneg x)]

/-- Single-invariant boundary rigidity: at every real point, the complete
signed Blaschke logarithmic derivative vanishes exactly when RH holds. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_zero_iff_rh
    (x : ℝ) :
    riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ) = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density_mul_I x]
  constructor
  · intro hzero
    have hcast : (riemannXiUpperBlaschkeBoundaryDensityTotal x : ℂ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right Complex.I_ne_zero
    have hreal : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 := by
      exact_mod_cast hcast
    exact
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mp
        hreal
  · intro hRH
    have hreal : riemannXiUpperBlaschkeBoundaryDensityTotal x = 0 :=
      (riemannXiUpperBlaschkeBoundaryDensityTotal_eq_zero_iff_rh x).mpr
        hRH
    rw [hreal]
    simp

/-- Concrete origin criterion: one fixed boundary value of the complete
signed Blaschke logarithmic derivative vanishes exactly when RH holds. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_at_zero_eq_zero_iff_rh :
    riemannXiUpperBlaschkeCompleteLogDerivative 0 = 0 ↔
      RiemannHypothesis := by
  simpa using
    riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_zero_iff_rh 0

/-- Under failure of RH, the boundary complete signed logarithmic derivative
is nonzero at every real point. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_ne_zero_of_not_rh
    (x : ℝ) (hRH : ¬ RiemannHypothesis) :
    riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ) ≠ 0 := by
  intro hzero
  exact hRH
    ((riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_zero_iff_rh
      x).mp hzero)

/-- Under failure of RH, the boundary resultant has strictly positive
imaginary part at every real point. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_real_im_pos_of_not_rh
    (x : ℝ) (hRH : ¬ RiemannHypothesis) :
    0 < (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)).im := by
  rw [riemannXiUpperBlaschkeCompleteLogDerivative_real_im_eq_density x]
  exact riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_not_rh x hRH

/-- Under failure of RH, the imaginary part of the fixed origin boundary
resultant is strictly positive. -/
theorem riemannXiUpperBlaschkeCompleteLogDerivative_at_zero_im_pos_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    0 < (riemannXiUpperBlaschkeCompleteLogDerivative 0).im := by
  simpa using
    riemannXiUpperBlaschkeCompleteLogDerivative_real_im_pos_of_not_rh 0 hRH

end

end RiemannGaussian
