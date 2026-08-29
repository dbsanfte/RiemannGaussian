import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaBoundaryHeatFlux

/-!
# A single diagonal exhaustion by heat-weighted paired-eta fluxes

The preceding module recovers the complete boundary-heat detector by first
shrinking a common puncture radius in each finite zero window and then
expanding the window. This module converts those two successive limits into
one rigorously selected diagonal sequence.

At stage `n`, Lean chooses a positive common radius smaller than
`1 / (n + 1)`. The radius lies in the simultaneous `L¹` regime for every
selected eta-flux integrand and makes the finite flux differ from its exact
heat-residue window by less than `1 / (n + 1)`. Consequently the radii and
errors both tend to zero, while the literal finite eta fluxes converge along
the same sequence to `2 * pi` times the complete detector.

This is a diagonal selection theorem, not a uniform small-radius estimate or
an interchange of limits. Its value is to expose one concrete sequence on
which the remaining global arithmetic cancellation/coercivity problem can be
stated without nested limiting notation.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The positive error and radius tolerance used at diagonal stage `n`. -/
def pairedEtaBoundaryHeatFluxDiagonalTolerance (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

/-- Every diagonal tolerance is strictly positive. -/
theorem pairedEtaBoundaryHeatFluxDiagonalTolerance_pos (n : ℕ) :
    0 < pairedEtaBoundaryHeatFluxDiagonalTolerance n := by
  unfold pairedEtaBoundaryHeatFluxDiagonalTolerance
  positivity

/-- The diagonal tolerances tend to zero. -/
theorem tendsto_pairedEtaBoundaryHeatFluxDiagonalTolerance_zero :
    Tendsto pairedEtaBoundaryHeatFluxDiagonalTolerance atTop (nhds 0) := by
  have hdenominator : Tendsto (fun n : ℕ => (n : ℝ) + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  have hinverse := tendsto_inv_atTop_zero.comp hdenominator
  exact hinverse.congr' (Eventually.of_forall fun n => by
    simp [Function.comp_apply,
      pairedEtaBoundaryHeatFluxDiagonalTolerance])

/-- At every finite stage there is a positive common radius below the stage
tolerance which simultaneously makes every selected eta-flux integrand
integrable, keeps every circle in the positive eta half-plane and off the eta
divisor, and approximates the exact finite heat-residue window within that
tolerance. -/
theorem exists_pairedEtaBoundaryHeatFluxDiagonalRadius
    (x tau : ℝ) (n : ℕ) :
    ∃ r : ℝ,
      0 < r ∧
      r < pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
      dist
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ) r)
          (2 * Real.pi *
            (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
              x tau (n : ℝ)).re) <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
      (∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        IntervalIntegrable
          (fun theta : ℝ =>
            let s := circleMap rho.1 r theta
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (s - 1 / 2)).re *
              ((circleMap 0 r theta).re *
                  (pairedEtaLogDerivativeRealNumerator s /
                    pairedEtaCoreNormSq s) -
                (circleMap 0 r theta).im *
                  (pairedEtaLogDerivativeImaginaryNumerator s /
                    pairedEtaCoreNormSq s)))
          volume 0 (2 * Real.pi)) ∧
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ), ∀ theta : ℝ,
        0 < (circleMap rho.1 r theta).re ∧
          pairedEtaCore (circleMap rho.1 r theta) ≠ 0 := by
  have htolerance := pairedEtaBoundaryHeatFluxDiagonalTolerance_pos n
  have hclose : ∀ᶠ r : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      dist
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ) r)
          (2 * Real.pi *
            (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
              x tau (n : ℝ)).re) <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n :=
    (Metric.tendsto_nhds.mp
      (tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau (n : ℝ))) _ htolerance
  have hrange : Set.Ioo (0 : ℝ)
      (pairedEtaBoundaryHeatFluxDiagonalTolerance n) ∈
        nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsGT htolerance
  have hrangeEventually : ∀ᶠ r : ℝ in
      nhdsWithin (0 : ℝ) (Set.Ioi 0),
      r ∈ Set.Ioo 0 (pairedEtaBoundaryHeatFluxDiagonalTolerance n) :=
    hrange
  have hintegrable : ∀ᶠ r : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        IntervalIntegrable
          (fun theta : ℝ =>
            let s := circleMap rho.1 r theta
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (s - 1 / 2)).re *
              ((circleMap 0 r theta).re *
                  (pairedEtaLogDerivativeRealNumerator s /
                    pairedEtaCoreNormSq s) -
                (circleMap 0 r theta).im *
                  (pairedEtaLogDerivativeImaginaryNumerator s /
                    pairedEtaCoreNormSq s)))
          volume 0 (2 * Real.pi) := by
    rw [Finset.eventually_all]
    intro rho _
    exact
      eventually_intervalIntegrable_pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux
        x tau rho
  have hgeometry : ∀ᶠ r : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ), ∀ theta : ℝ,
        0 < (circleMap rho.1 r theta).re ∧
          pairedEtaCore (circleMap rho.1 r theta) ≠ 0 := by
    rw [Finset.eventually_all]
    intro rho _
    exact eventually_forall_circleMap_pairedEtaCore_ne_zero_re_pos rho
  obtain ⟨r, hclose_r, hrange_r, hintegrable_r, hgeometry_r⟩ :=
    (hclose.and
      (hrangeEventually.and (hintegrable.and hgeometry))).exists
  exact
    ⟨r, hrange_r.1, hrange_r.2, hclose_r, hintegrable_r, hgeometry_r⟩

/-- A classically selected common puncture radius at each diagonal stage. -/
noncomputable def pairedEtaBoundaryHeatFluxDiagonalRadius
    (x tau : ℝ) (n : ℕ) : ℝ :=
  Classical.choose (exists_pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)

/-- The selected diagonal radius satisfies positivity, quantitative decay,
finite-window approximation, simultaneous `L¹` integrability, and complete
zero-free positive-half-plane circle geometry. -/
theorem pairedEtaBoundaryHeatFluxDiagonalRadius_spec
    (x tau : ℝ) (n : ℕ) :
    0 < pairedEtaBoundaryHeatFluxDiagonalRadius x tau n ∧
    pairedEtaBoundaryHeatFluxDiagonalRadius x tau n <
      pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
    dist
        (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
        (2 * Real.pi *
          (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
            x tau (n : ℝ)).re) <
      pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
    (∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      IntervalIntegrable
        (fun theta : ℝ =>
          let s := circleMap rho.1
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) theta
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (s - 1 / 2)).re *
            ((circleMap 0
                  (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
                  theta).re *
                (pairedEtaLogDerivativeRealNumerator s /
                  pairedEtaCoreNormSq s) -
              (circleMap 0
                  (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
                  theta).im *
                (pairedEtaLogDerivativeImaginaryNumerator s /
                  pairedEtaCoreNormSq s)))
        volume 0 (2 * Real.pi)) ∧
    ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ), ∀ theta : ℝ,
      0 < (circleMap rho.1
          (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) theta).re ∧
        pairedEtaCore
          (circleMap rho.1
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) theta) ≠ 0 := by
  exact Classical.choose_spec
    (exists_pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)

/-- The selected common puncture radii tend to zero. -/
theorem tendsto_pairedEtaBoundaryHeatFluxDiagonalRadius_zero
    (x tau : ℝ) :
    Tendsto (pairedEtaBoundaryHeatFluxDiagonalRadius x tau)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      (pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n).1.le
  · exact Eventually.of_forall fun n =>
      (pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n).2.1.le
  · exact tendsto_pairedEtaBoundaryHeatFluxDiagonalTolerance_zero

/-- Along the selected diagonal radii, the distance between the literal
finite eta flux and its exact finite heat-residue value tends to zero. -/
theorem tendsto_pairedEtaBoundaryHeatFluxDiagonalError_zero
    (x tau : ℝ) :
    Tendsto
      (fun n : ℕ =>
        dist
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
          (2 * Real.pi *
            (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
              x tau (n : ℝ)).re))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => dist_nonneg
  · exact Eventually.of_forall fun n =>
      (pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n).2.2.1.le
  · exact tendsto_pairedEtaBoundaryHeatFluxDiagonalTolerance_zero

/-- At positive heat time, the exact heat-residue targets along natural
window heights converge to `2 * pi` times the complete detector. -/
theorem tendsto_pairedEtaBoundaryHeatFluxDiagonalWindowTarget
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ => 2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
          x tau (n : ℝ)).re)
      atTop
      (nhds (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  exact
    (tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindowLimit
      x htau).comp tendsto_natCast_atTop_atTop

/-- A single sequence of literal finite, simultaneously integrable paired-eta
radial fluxes converges to `2 * pi` times the complete fixed-time boundary-
heat detector. No limit interchange or uniform puncture estimate is used. -/
theorem tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxDiagonal
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
      atTop
      (nhds (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have htarget :=
    tendsto_pairedEtaBoundaryHeatFluxDiagonalWindowTarget x htau
  have hdist : Tendsto
      (fun n : ℕ =>
        dist
          (2 * Real.pi *
            (suzukiChebyshevLaplaceBoundaryHeatResidueWindow
              x tau (n : ℝ)).re)
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)))
      atTop (nhds 0) := by
    simpa only [dist_comm] using
      tendsto_pairedEtaBoundaryHeatFluxDiagonalError_zero x tau
  exact htarget.congr_dist hdist

end
end RiemannGaussian
