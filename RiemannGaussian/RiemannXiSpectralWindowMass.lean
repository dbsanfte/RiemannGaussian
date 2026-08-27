import RiemannGaussian.RiemannXiCriticalLineDeviation

/-!
# Cofinal finite windows for the complete spectral masses

The complete upper-height, absolute critical-line displacement, and
logarithmic-defect masses are extended nonnegative sums over the full
nontrivial zeta divisor.  This file realizes each one as the limit of an
explicit finite sum over the cofinal symmetric spectral windows already used
in the xi contour argument.  No finiteness of any complete mass is assumed.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-counted upper spectral height in one finite symmetric
spectral window. -/
def riemannXiUpperSpectralHeightWindow (T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)

/-- The multiplicity-counted absolute critical-line displacement in one
finite symmetric spectral window. -/
def riemannXiAbsoluteCriticalLineDeviationWindow (T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal (zetaAbsoluteSpectralHeightSummand rho)

/-- The multiplicity-counted logarithmic pseudo-hyperbolic defect at `z` in
one finite symmetric spectral window. -/
def riemannXiUpperHyperbolicLogDefectWindow (z : ℂ) (T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal (zetaUpperHyperbolicLogDefectSummand z rho)

/-- Each nonnegative symmetric spectral window is invariant under critical-
line reflection. -/
theorem conjugatePartner_mem_spectralZetaZeroWindow_iff
    {T : ℝ} (hT : 0 ≤ T) (rho : NontrivialZetaZero) :
    NontrivialZetaZero.conjugatePartner rho ∈ spectralZetaZeroWindow T ↔
      rho ∈ spectralZetaZeroWindow T := by
  rw [mem_spectralZetaZeroWindow hT,
    mem_spectralZetaZeroWindow hT,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner]
  simp

/-- At every finite stage, absolute critical-line displacement is already
exactly twice upper spectral height.  Thus the full extended-real identity is
visible before taking the cofinal limit. -/
theorem riemannXiAbsoluteCriticalLineDeviationWindow_eq_two_mul_upperHeightWindow
    {T : ℝ} (hT : 0 ≤ T) :
    riemannXiAbsoluteCriticalLineDeviationWindow T =
      2 * riemannXiUpperSpectralHeightWindow T := by
  unfold riemannXiAbsoluteCriticalLineDeviationWindow
    riemannXiUpperSpectralHeightWindow
  calc
    (∑ rho ∈ spectralZetaZeroWindow T,
        ENNReal.ofReal (zetaAbsoluteSpectralHeightSummand rho)) =
        ∑ rho ∈ spectralZetaZeroWindow T,
          (ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) +
            ENNReal.ofReal
              (zetaUpperSpectralHeightSummand
                (NontrivialZetaZero.conjugatePartner rho))) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      rw [← ENNReal.ofReal_add
        (zetaUpperSpectralHeightSummand_nonneg rho)
        (zetaUpperSpectralHeightSummand_nonneg
          (NontrivialZetaZero.conjugatePartner rho)),
        upperHeight_add_conjugatePartner_eq_absoluteSpectralHeight]
    _ = (∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)) +
        ∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal
            (zetaUpperSpectralHeightSummand
              (NontrivialZetaZero.conjugatePartner rho)) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)) +
        ∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) := by
      congr 1
      refine Finset.sum_bij
        (fun rho _hrho ↦ NontrivialZetaZero.conjugatePartner rho)
        ?_ ?_ ?_ ?_
      · intro rho hrho
        exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hrho
      · intro rho₁ _hrho₁ rho₂ _hrho₂ heq
        exact NontrivialZetaZero.conjugatePartnerEquiv.injective heq
      · intro rho hrho
        refine ⟨NontrivialZetaZero.conjugatePartner rho, ?_, ?_⟩
        · exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hrho
        · simp
      · intro rho _hrho
        rfl
    _ = 2 * ∑ rho ∈ spectralZetaZeroWindow T,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) := by
      ring

/-- Cofinal finite spectral windows exhaust the complete upper-height mass,
including when the limit is infinite. -/
theorem tendsto_riemannXiUpperSpectralHeightWindow :
    Tendsto riemannXiUpperSpectralHeightWindow atTop
      (nhds riemannXiUpperSpectralHeightMass) := by
  unfold riemannXiUpperSpectralHeightWindow
    riemannXiUpperSpectralHeightMass
  exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop

/-- Cofinal finite spectral windows exhaust the complete absolute
critical-line displacement mass, including when the limit is infinite. -/
theorem tendsto_riemannXiAbsoluteCriticalLineDeviationWindow :
    Tendsto riemannXiAbsoluteCriticalLineDeviationWindow atTop
      (nhds riemannXiAbsoluteCriticalLineDeviationMass) := by
  unfold riemannXiAbsoluteCriticalLineDeviationWindow
    riemannXiAbsoluteCriticalLineDeviationMass
  exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop

/-- Cofinal finite spectral windows exhaust the complete logarithmic defect
at every observation point, including when the limit is infinite. -/
theorem tendsto_riemannXiUpperHyperbolicLogDefectWindow (z : ℂ) :
    Tendsto (riemannXiUpperHyperbolicLogDefectWindow z) atTop
      (nhds (riemannXiUpperHyperbolicLogDefectMass z)) := by
  unfold riemannXiUpperHyperbolicLogDefectWindow
    riemannXiUpperHyperbolicLogDefectMass
  exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop

end

end RiemannGaussian
