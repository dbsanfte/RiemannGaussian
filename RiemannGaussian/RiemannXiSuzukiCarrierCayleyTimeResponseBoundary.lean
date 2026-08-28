import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponse
import RiemannGaussian.RiemannXiBoundaryFixedTimeHeat

/-!
# Boundary continuity of the complete Suzuki initial response

The complete signed Suzuki initial velocity was defined as `-i` times the
complete upper-divisor Blaschke logarithmic derivative.  This file proves
that it has its literal complex boundary value along every vertical approach
`x + i y`, `y -> 0+`.

The proof is a dominated-convergence argument over the genuine xi divisor.
A previously established uniform gap separates each real point from every
selected upper zero, even when the point itself is a critical-line zero.  On
a sufficiently short vertical segment, one Cauchy denominator stays at least
half its boundary size and the reflected denominator can only grow.  Hence
the norm of each approached signed term is bounded by twice its summable
positive boundary density.

No boundary interchange or noncollision premise is assumed in the final
theorem.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Each selected signed Blaschke summand is continuous along a vertical
approach to the real boundary. -/
theorem tendsto_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach
    (x : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun y : ℝ ↦ zetaUpperBlaschkeSelectedLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho)
      (nhdsWithin 0 (Ioi 0))
      (nhds (zetaUpperBlaschkeSelectedLogDerivativeSummand
        (x : ℂ) rho)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [show zetaUpperBlaschkeSelectedLogDerivativeSummand
          (x : ℂ) rho =
        zetaUpperBlaschkeLogDerivativeSummand (x : ℂ) rho by
      rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper]]
    simp only [zetaUpperBlaschkeSelectedLogDerivativeSummand,
      if_pos hupper]
    have hupperDen :
        (x : ℂ) - zetaSpectralCoordinate rho.1 ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [sub_im, ofReal_im, zero_sub, zero_im] at him
      linarith
    have hlowerDen :
        (x : ℂ) - starRingEnd ℂ
            (zetaSpectralCoordinate rho.1) ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [sub_im, ofReal_im, conj_im, zero_sub, neg_eq_zero,
        zero_im] at him
      linarith
    have hsummandContinuous : ContinuousAt
        (fun z : ℂ ↦ zetaUpperBlaschkeLogDerivativeSummand z rho)
        (x : ℂ) := by
      unfold zetaUpperBlaschkeLogDerivativeSummand
      fun_prop
    have happ : ContinuousAt
        (fun y : ℝ ↦ upperBoundaryApproachPoint x y) 0 := by
      unfold upperBoundaryApproachPoint
      fun_prop
    have hcontinuous : ContinuousAt
        ((fun z : ℂ ↦ zetaUpperBlaschkeLogDerivativeSummand z rho) ∘
          fun y : ℝ ↦ upperBoundaryApproachPoint x y) 0 :=
      hsummandContinuous.comp_of_eq happ
        (upperBoundaryApproachPoint_zero x)
    change Tendsto
      ((fun z : ℂ ↦ zetaUpperBlaschkeLogDerivativeSummand z rho) ∘
        fun y : ℝ ↦ upperBoundaryApproachPoint x y)
      (nhdsWithin 0 (Ioi 0))
      (nhds (zetaUpperBlaschkeLogDerivativeSummand (x : ℂ) rho))
    have ht : Tendsto
        ((fun z : ℂ ↦ zetaUpperBlaschkeLogDerivativeSummand z rho) ∘
          fun y : ℝ ↦ upperBoundaryApproachPoint x y)
        (nhdsWithin 0 (Ioi 0))
        (nhds (((fun z : ℂ ↦ zetaUpperBlaschkeLogDerivativeSummand z rho) ∘
          fun y : ℝ ↦ upperBoundaryApproachPoint x y) 0)) :=
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Function.comp_apply, upperBoundaryApproachPoint_zero] using ht
  · simp only [zetaUpperBlaschkeSelectedLogDerivativeSummand,
      if_neg hupper]
    exact tendsto_const_nhds

/-- Along a sufficiently short positive vertical approach, the norm of one
selected signed logarithmic-derivative term is bounded by twice its positive
boundary density. -/
theorem norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_le
    {x delta y : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero) :
    ‖zetaUpperBlaschkeSelectedLogDerivativeSummand
        (upperBoundaryApproachPoint x y) rho‖ ≤
      2 * zetaUpperBlaschkeBoundaryDensitySummand x rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · let alpha : ℂ := zetaSpectralCoordinate rho.1
    let r : ℝ := ‖(x : ℂ) - alpha‖
    let A : ℝ := ‖upperBoundaryApproachPoint x y - alpha‖
    let B : ℝ := ‖upperBoundaryApproachPoint x y - starRingEnd ℂ alpha‖
    have hr : 0 < r := by
      dsimp [r, alpha]
      rw [norm_pos_iff]
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [sub_im, ofReal_im, zero_sub, zero_im] at him
      linarith
    have hhalf : r / 2 ≤ A := by
      exact half_norm_boundary_sub_le_norm_approach_sub
        hdelta (hgap rho hupper) hy hySmall
    have hA : 0 < A := by linarith
    have hz : 0 < (upperBoundaryApproachPoint x y).im := by
      simpa using hy
    have hB : 0 < B := by
      dsimp [B]
      rw [norm_pos_iff]
      exact sub_conj_ne_zero_of_im_pos hz hupper
    have hboundaryReflected : r ≤ B := by
      have hsq :
          Complex.normSq ((x : ℂ) - alpha) ≤
            Complex.normSq
              (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) := by
        rw [normSq_upperBoundaryApproachPoint_sub_conj]
        dsimp [alpha]
        nlinarith
      dsimp [r, B]
      rw [Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq] at hsq
      nlinarith [norm_nonneg ((x : ℂ) - alpha),
        norm_nonneg
          (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha)]
    have hproduct : r ^ 2 / 2 ≤ A * B := by
      have hmul := mul_le_mul hhalf hboundaryReflected
        (norm_nonneg ((x : ℂ) - alpha)) hA.le
      dsimp [r, A, B] at hmul ⊢
      nlinarith
    have hupperDen :
        upperBoundaryApproachPoint x y - alpha ≠ 0 := by
      exact norm_pos_iff.mp hA
    have hlowerDen :
        upperBoundaryApproachPoint x y - starRingEnd ℂ alpha ≠ 0 := by
      exact norm_pos_iff.mp hB
    have hdiff :
        1 / (upperBoundaryApproachPoint x y - alpha) -
            1 / (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha) =
          (alpha - starRingEnd ℂ alpha) /
            ((upperBoundaryApproachPoint x y - alpha) *
              (upperBoundaryApproachPoint x y - starRingEnd ℂ alpha)) := by
      field_simp [hupperDen, hlowerDen]
      ring
    have hnum : ‖alpha - starRingEnd ℂ alpha‖ = 2 * alpha.im := by
      have hid :
          alpha - starRingEnd ℂ alpha =
            ((2 * alpha.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp
          ring
      rw [hid, norm_mul, Complex.norm_real, norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hinv : 1 / (A * B) ≤ 2 / r ^ 2 := by
      have hAB : 0 < A * B := mul_pos hA hB
      have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr
      rw [div_le_div_iff₀ hAB hrSq]
      nlinarith
    rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_pos hupper,
      zetaUpperBlaschkeBoundaryDensitySummand, if_pos hupper]
    unfold zetaUpperBlaschkeLogDerivativeSummand
    rw [hdiff, norm_mul, norm_div, norm_mul, Complex.norm_natCast,
      hnum, Complex.normSq_eq_norm_sq]
    change
      (analyticZetaZeroMultiplicity rho : ℝ) *
          (2 * alpha.im / (A * B)) ≤
        2 * ((analyticZetaZeroMultiplicity rho : ℝ) *
          (2 * alpha.im / r ^ 2))
    calc
      (analyticZetaZeroMultiplicity rho : ℝ) *
            (2 * alpha.im / (A * B)) =
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            (2 * alpha.im)) * (1 / (A * B)) := by ring
      _ ≤ ((analyticZetaZeroMultiplicity rho : ℝ) *
            (2 * alpha.im)) * (2 / r ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * ((analyticZetaZeroMultiplicity rho : ℝ) *
          (2 * alpha.im / r ^ 2)) := by ring
  · rw [zetaUpperBlaschkeSelectedLogDerivativeSummand, if_neg hupper,
      norm_zero, zetaUpperBlaschkeBoundaryDensitySummand, if_neg hupper,
      mul_zero]

/-- The complete signed Blaschke logarithmic derivative converges to its
literal complex boundary value along every vertical approach. -/
theorem tendsto_riemannXiUpperBlaschkeCompleteLogDerivative_approach
    (x : ℝ) :
    Tendsto
      (fun y : ℝ ↦ riemannXiUpperBlaschkeCompleteLogDerivative
        (upperBoundaryApproachPoint x y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ))) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  have hlimit := tendsto_tsum_of_dominated_convergence
    ((summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left 2)
    (tendsto_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach x)
    (by
      have hpositive : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), 0 < y :=
        eventually_nhdsWithin_of_forall fun _ hy ↦ hy
      have hsmall : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
          y < delta / 2 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
      filter_upwards [hpositive, hsmall] with y hy hySmall
      intro rho
      exact
        norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_le
          hdelta hgap hy hySmall rho)
  simpa only [riemannXiUpperBlaschkeCompleteLogDerivative] using hlimit

/-- The complete complex Suzuki initial velocity is vertically continuous
at every real boundary point. -/
theorem tendsto_riemannXiSuzukiOffAxisSignedPInitialVelocity_approach
    (x : ℝ) :
    Tendsto
      (fun y : ℝ ↦ riemannXiSuzukiOffAxisSignedPInitialVelocity
        (upperBoundaryApproachPoint x y))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ))) := by
  unfold riemannXiSuzukiOffAxisSignedPInitialVelocity
  exact tendsto_const_nhds.mul
    (tendsto_riemannXiUpperBlaschkeCompleteLogDerivative_approach x)

end

end RiemannGaussian
