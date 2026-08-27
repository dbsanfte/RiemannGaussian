import RiemannGaussian.RiemannXiBoundaryHeatIntegration

/-!
# Boundary limits of the spectral-xi heat residues

The fixed-time heat coefficients were originally derived as genuine local
residues of `logDeriv riemannXiSpectral`.  This file carries that complex
residue series itself to the real boundary.  Each normalized local residue
converges to its boundary heat residue, the complete boundary residue series
is summable, and the entire normalized interior residue sum converges to it.

This makes the connection to the spectral-xi logarithmic derivative explicit
at the complete-series level rather than only after forgetting to real-valued
heat sums.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complex fixed-time boundary residue contributed by one spectral
zero. -/
def riemannXiUpperHyperbolicBoundaryHeatResidue
    (x tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (zetaUpperHyperbolicBoundaryHeatSummand x tau rho : ℂ)

/-- A genuine interior heat-weighted spectral-xi residue, divided by `2*y`,
converges to its complex boundary heat residue. -/
theorem tendsto_riemannXiUpperHyperbolicHeatResidue_boundaryQuotient
    (x : ℝ) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun y : ℝ ↦
        riemannXiUpperHyperbolicHeatResidue
            (upperBoundaryApproachPoint x y) tau rho /
          ((2 * y : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatResidue x tau rho)) := by
  have hreal :=
    tendsto_zetaUpperHyperbolicHeatSummand_boundaryQuotient x htau rho
  have hcomplex : Tendsto
      (fun y : ℝ ↦ ((zetaUpperHyperbolicHeatSummand
        (upperBoundaryApproachPoint x y) tau rho / (2 * y) : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((zetaUpperHyperbolicBoundaryHeatSummand x tau rho : ℝ) : ℂ)) :=
    tendsto_ofReal_iff.mpr hreal
  apply hcomplex.congr'
  filter_upwards with y
  rw [riemannXiUpperHyperbolicHeatResidue_eq_ofReal]
  push_cast
  rfl

/-- The complete complex boundary residue series sums to the embedded real
boundary heat total. -/
theorem hasSum_riemannXiUpperHyperbolicBoundaryHeatResidue
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasSum (riemannXiUpperHyperbolicBoundaryHeatResidue x tau)
      (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) := by
  exact Complex.hasSum_ofReal.mpr
    (summable_zetaUpperHyperbolicBoundaryHeatSummand x htau).hasSum

/-- The complete complex fixed-time boundary heat-residue sum. -/
def riemannXiUpperHyperbolicBoundaryHeatResidueTotal
    (x tau : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    riemannXiUpperHyperbolicBoundaryHeatResidue x tau rho

/-- The complex boundary residue total is exactly the embedded positive real
boundary heat total. -/
theorem riemannXiUpperHyperbolicBoundaryHeatResidueTotal_eq_ofReal
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundaryHeatResidueTotal x tau =
      (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) := by
  exact
    (hasSum_riemannXiUpperHyperbolicBoundaryHeatResidue x htau).tsum_eq

/-- Vanishing of the complete complex boundary residue total is exactly
RH. -/
theorem riemannXiUpperHyperbolicBoundaryHeatResidueTotal_eq_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    riemannXiUpperHyperbolicBoundaryHeatResidueTotal x tau = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperHyperbolicBoundaryHeatResidueTotal_eq_ofReal
    x htau, Complex.ofReal_eq_zero]
  exact riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh x htau

/-- The complete interior heat-weighted residue series divided termwise by
the exact boundary factor. -/
def riemannXiUpperHyperbolicHeatResidueBoundaryQuotient
    (x tau y : ℝ) : ℂ :=
  ∑' rho : NontrivialZetaZero,
    riemannXiUpperHyperbolicHeatResidue
        (upperBoundaryApproachPoint x y) tau rho /
      ((2 * y : ℝ) : ℂ)

/-- At positive height the normalized complex residue series is the embedded
normalized real spectral heat sum. -/
theorem riemannXiUpperHyperbolicHeatResidueBoundaryQuotient_eq
    (x : ℝ) {tau y : ℝ} (htau : 0 < tau) (hy : 0 < y) :
    riemannXiUpperHyperbolicHeatResidueBoundaryQuotient x tau y =
      (riemannXiUpperHyperbolicHeatSum
          (upperBoundaryApproachPoint x y) tau : ℂ) /
        ((2 * y : ℝ) : ℂ) := by
  unfold riemannXiUpperHyperbolicHeatResidueBoundaryQuotient
  exact ((hasSum_riemannXiUpperHyperbolicHeatResidue
    (by simpa using hy) htau).div_const ((2 * y : ℝ) : ℂ)).tsum_eq

/-- The entire normalized complex spectral-xi residue series converges to the
complete boundary heat residue total. -/
theorem tendsto_riemannXiUpperHyperbolicHeatResidueBoundaryQuotient
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (riemannXiUpperHyperbolicHeatResidueBoundaryQuotient x tau)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ)) := by
  have hreal :=
    tendsto_riemannXiUpperHyperbolicHeatSum_boundaryQuotient x htau
  have hcomplex : Tendsto
      (fun y : ℝ ↦ ((riemannXiUpperHyperbolicHeatSum
        (upperBoundaryApproachPoint x y) tau / (2 * y) : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ)) :=
    tendsto_ofReal_iff.mpr hreal
  apply hcomplex.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [riemannXiUpperHyperbolicHeatResidueBoundaryQuotient_eq
    x htau hy]
  push_cast
  rfl

end

end RiemannGaussian
