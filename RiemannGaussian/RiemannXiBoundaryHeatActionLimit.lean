import RiemannGaussian.RiemannXiBoundaryPoissonLimit

/-!
# Boundary limit of the complete proper-time heat action

The complete logarithmic proper-time heat action is squeezed between the
Poisson mass and a gap coefficient times that mass.  The upper-divisor gap at
every real boundary point persists, with half its size, along sufficiently
short vertical approaches.  The comparison coefficient then tends to one.

Consequently the heat action divided by its exact linear boundary factor
`2*y` converges to the same finite cancellation-free boundary invariant as
the normalized Poisson mass.  This remains true when the boundary point is a
critical-line zero of spectral xi.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

@[simp]
theorem norm_real_sub_upperBoundaryApproachPoint (x y : ℝ) :
    ‖(x : ℂ) - upperBoundaryApproachPoint x y‖ = |y| := by
  simp [upperBoundaryApproachPoint, Real.norm_eq_abs]

/-- Half of a real boundary gap survives at every positive approach height
smaller than half the original gap. -/
theorem half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
    {x delta : ℝ} (_hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    {y : ℝ} (hy : 0 < y) (hySmall : y < delta / 2)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    delta / 2 ≤
      ‖upperBoundaryApproachPoint x y - zetaSpectralCoordinate rho.1‖ := by
  have htriangle :
      ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ ≤
        ‖(x : ℂ) - upperBoundaryApproachPoint x y‖ +
          ‖upperBoundaryApproachPoint x y -
            zetaSpectralCoordinate rho.1‖ := by
    calc
      ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖ =
          ‖((x : ℂ) - upperBoundaryApproachPoint x y) +
            (upperBoundaryApproachPoint x y -
              zetaSpectralCoordinate rho.1)‖ := by
                congr 1
                ring
      _ ≤ ‖(x : ℂ) - upperBoundaryApproachPoint x y‖ +
          ‖upperBoundaryApproachPoint x y -
            zetaSpectralCoordinate rho.1‖ := norm_add_le _ _
  rw [norm_real_sub_upperBoundaryApproachPoint, abs_of_pos hy] at htriangle
  have hboundary := hgap rho hupper
  linarith

/-- A sufficiently short positive vertical approach cannot meet any spectral
xi zero, even if its boundary endpoint is itself a critical-line zero. -/
theorem riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    {y : ℝ} (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 := by
  intro hzero
  obtain ⟨rho, heq⟩ :=
    (riemannXiSpectral_eq_zero_iff_exists_zetaZero
      (upperBoundaryApproachPoint x y)).mp hzero
  have hupper : 0 < (zetaSpectralCoordinate rho.1).im := by
    rw [← heq, upperBoundaryApproachPoint_im]
    exact hy
  have hseparated :=
    half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
      hdelta hgap hy hySmall rho hupper
  rw [heq, sub_self, norm_zero] at hseparated
  linarith

/-- Gap coefficient governing the boundary heat-action squeeze. -/
def riemannXiUpperHyperbolicBoundaryGapCoefficient
    (delta y : ℝ) : ℝ :=
  1 + 2 * y / (delta / 2) ^ 2

/-- The complete proper-time heat action divided by its exact linear
boundary factor. -/
def riemannXiUpperHyperbolicHeatActionBoundaryQuotient
    (x y : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * y))⁻¹ *
    riemannXiUpperHyperbolicHeatAction
      (upperBoundaryApproachPoint x y)

/-- The boundary gap gives the logarithmic-defect upper comparison throughout
a sufficiently short positive vertical approach. -/
theorem riemannXiUpperHyperbolicLogDefectMass_approach_le_gap_mul_poisson
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    {y : ℝ} (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperHyperbolicLogDefectMass
        (upperBoundaryApproachPoint x y) ≤
      ENNReal.ofReal
          (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
        riemannXiUpperHyperbolicPoissonDefectMass
          (upperBoundaryApproachPoint x y) := by
  unfold riemannXiUpperHyperbolicBoundaryGapCoefficient
  have happroachGap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta / 2 ≤ ‖upperBoundaryApproachPoint x y -
          zetaSpectralCoordinate rho.1‖ := by
    intro rho hupper
    exact
      half_boundaryGap_le_norm_upperBoundaryApproachPoint_sub
        hdelta hgap hy hySmall rho hupper
  simpa only [upperBoundaryApproachPoint_im] using
    (riemannXiUpperHyperbolicLogDefectMass_le_gapCoefficient_mul_poissonMass
      (z := upperBoundaryApproachPoint x y) (delta := delta / 2)
      (by simpa using hy) (by positivity) happroachGap)

/-- On every sufficiently short positive approach, the normalized Poisson
mass is below the normalized proper-time heat action. -/
theorem riemannXiUpperHyperbolicPoissonBoundaryQuotient_le_heatActionBoundaryQuotient
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    {y : ℝ} (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperHyperbolicPoissonBoundaryQuotient x y ≤
      riemannXiUpperHyperbolicHeatActionBoundaryQuotient x y := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi :
      riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  unfold riemannXiUpperHyperbolicPoissonBoundaryQuotient
    riemannXiUpperHyperbolicHeatActionBoundaryQuotient
  simpa only [mul_comm] using
    (mul_le_mul_left
      (riemannXiUpperHyperbolicPoissonDefectMass_le_heatAction hz hxi)
      (ENNReal.ofReal (2 * y))⁻¹)

/-- The same normalized heat action is at most the boundary gap coefficient
times the normalized Poisson mass. -/
theorem riemannXiUpperHyperbolicHeatActionBoundaryQuotient_le_gap_mul_poisson
    {x delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        delta ≤ ‖(x : ℂ) - zetaSpectralCoordinate rho.1‖)
    {y : ℝ} (hy : 0 < y) (hySmall : y < delta / 2) :
    riemannXiUpperHyperbolicHeatActionBoundaryQuotient x y ≤
      ENNReal.ofReal
          (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
        riemannXiUpperHyperbolicPoissonBoundaryQuotient x y := by
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy
  have hxi :
      riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdelta hgap hy hySmall
  have haction :
      riemannXiUpperHyperbolicHeatAction
          (upperBoundaryApproachPoint x y) ≤
        ENNReal.ofReal
            (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
          riemannXiUpperHyperbolicPoissonDefectMass
            (upperBoundaryApproachPoint x y) := by
    rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
    exact
      riemannXiUpperHyperbolicLogDefectMass_approach_le_gap_mul_poisson
        hdelta hgap hy hySmall
  unfold riemannXiUpperHyperbolicHeatActionBoundaryQuotient
    riemannXiUpperHyperbolicPoissonBoundaryQuotient
  calc
    (ENNReal.ofReal (2 * y))⁻¹ *
        riemannXiUpperHyperbolicHeatAction
          (upperBoundaryApproachPoint x y) ≤
      (ENNReal.ofReal (2 * y))⁻¹ *
        (ENNReal.ofReal
            (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
          riemannXiUpperHyperbolicPoissonDefectMass
            (upperBoundaryApproachPoint x y)) :=
      (by
        simpa only [mul_comm] using
          (mul_le_mul_left haction (ENNReal.ofReal (2 * y))⁻¹))
    _ = ENNReal.ofReal
          (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
        ((ENNReal.ofReal (2 * y))⁻¹ *
          riemannXiUpperHyperbolicPoissonDefectMass
            (upperBoundaryApproachPoint x y)) := by
      ac_rfl

/-- For every positive boundary gap, the comparison coefficient tends to one
as the observation height tends to zero. -/
theorem tendsto_riemannXiUpperHyperbolicBoundaryGapCoefficient
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun y : ℝ ↦ ENNReal.ofReal
        (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hcontinuous : ContinuousAt
      (riemannXiUpperHyperbolicBoundaryGapCoefficient delta) 0 := by
    unfold riemannXiUpperHyperbolicBoundaryGapCoefficient
    fun_prop (disch := positivity)
  have hreal : Tendsto
      (riemannXiUpperHyperbolicBoundaryGapCoefficient delta)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa [riemannXiUpperHyperbolicBoundaryGapCoefficient, hdelta.ne'] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  simpa using ENNReal.tendsto_ofReal hreal

/-- The complete proper-time heat action, normalized by `2*y`, has exactly
the finite Poisson--Blaschke boundary limit at every real spectral point. -/
theorem tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient
    (x : ℝ) :
    Tendsto
      (riemannXiUpperHyperbolicHeatActionBoundaryQuotient x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicPoissonBoundaryLimit x)) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  have hpoisson :=
    tendsto_riemannXiUpperHyperbolicPoissonBoundaryQuotient x
  have hcoefficient :=
    tendsto_riemannXiUpperHyperbolicBoundaryGapCoefficient hdelta
  have hupperLimit : Tendsto
      (fun y : ℝ ↦
        ENNReal.ofReal
            (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
          riemannXiUpperHyperbolicPoissonBoundaryQuotient x y)
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicPoissonBoundaryLimit x)) := by
    simpa only [one_mul] using
      (ENNReal.Tendsto.mul hcoefficient (by simp) hpoisson (by simp))
  have hpositive : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), 0 < y :=
    eventually_nhdsWithin_of_forall fun _ hy ↦ hy
  have hsmall : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0), y < delta / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have hlower : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
      riemannXiUpperHyperbolicPoissonBoundaryQuotient x y ≤
        riemannXiUpperHyperbolicHeatActionBoundaryQuotient x y := by
    filter_upwards [hpositive, hsmall] with y hy hySmall
    exact
      riemannXiUpperHyperbolicPoissonBoundaryQuotient_le_heatActionBoundaryQuotient
        hdelta hgap hy hySmall
  have hupper : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
      riemannXiUpperHyperbolicHeatActionBoundaryQuotient x y ≤
        ENNReal.ofReal
            (riemannXiUpperHyperbolicBoundaryGapCoefficient delta y) *
          riemannXiUpperHyperbolicPoissonBoundaryQuotient x y := by
    filter_upwards [hpositive, hsmall] with y hy hySmall
    exact
      riemannXiUpperHyperbolicHeatActionBoundaryQuotient_le_gap_mul_poisson
        hdelta hgap hy hySmall
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hpoisson hupperLimit hlower hupper

/-- The normalized complete heat action therefore tends to the embedded norm
of the cancellation-free complete boundary logarithmic derivative. -/
theorem tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient_logDerivativeNorm
    (x : ℝ) :
    Tendsto
      (riemannXiUpperHyperbolicHeatActionBoundaryQuotient x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (ENNReal.ofReal
        ‖riemannXiUpperBlaschkeCompleteLogDerivative (x : ℂ)‖)) := by
  rw [norm_riemannXiUpperBlaschkeCompleteLogDerivative_real_eq_density x]
  exact tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient x

/-- Exact heat-action boundary reformulation of RH: at any one real spectral
point, the normalized complete proper-time action tends to zero exactly under
RH. -/
theorem tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient_zero_iff_rh
    (x : ℝ) :
    Tendsto
        (riemannXiUpperHyperbolicHeatActionBoundaryQuotient x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    have hlimit :=
      tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient x
    have hvalue : riemannXiUpperHyperbolicPoissonBoundaryLimit x = 0 :=
      tendsto_nhds_unique hlimit hzero
    exact
      (riemannXiUpperHyperbolicPoissonBoundaryLimit_eq_zero_iff_rh x).mp
        hvalue
  · intro hRH
    have hvalue : riemannXiUpperHyperbolicPoissonBoundaryLimit x = 0 :=
      (riemannXiUpperHyperbolicPoissonBoundaryLimit_eq_zero_iff_rh x).mpr
        hRH
    simpa only [hvalue] using
      tendsto_riemannXiUpperHyperbolicHeatActionBoundaryQuotient x

end

end RiemannGaussian
