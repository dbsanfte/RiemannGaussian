import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteAreaIntegrability
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# One common finite-hole geometry for arithmetic boundary heat

The finite-window Cauchy--Green theorem was assembled from termwise shrinking
squares.  This file constructs a literal planar region with all finite holes
removed at once.  The holes are a finite union of complex metric balls with a
common radius.  Their total area tends to zero, so absolute continuity of the
Bochner integral proves that the integral over the multiply punctured region
converges to the genuine through-divisor area established in the preceding
module.

For every positive radius the holes contain the entire selected xi divisor.
Thus the actual arithmetic source and its checked finite principal-part
regularization have exactly the same integral on the punctured region.  The
remaining comparison with the earlier *termwise square* approximation is a
separate limit-identification theorem and is not assumed here.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Topology ENNReal

/-! ## Generic finite unions of shrinking planar holes -/

/-- The union of common-radius open complex balls centered at a finite
family of points. -/
def finiteOpenBallHoles {ι : Type*} (W : Finset ι) (c : ι → ℂ)
    (q : ℝ) : Set ℂ :=
  ⋃ rho ∈ W, Metric.ball (c rho) q

/-- A finite union of complex open balls is measurable. -/
theorem measurableSet_finiteOpenBallHoles {ι : Type*}
    (W : Finset ι) (c : ι → ℂ) (q : ℝ) :
    MeasurableSet (finiteOpenBallHoles W c q) := by
  unfold finiteOpenBallHoles
  exact Finset.measurableSet_biUnion W fun _ _ => measurableSet_ball

/-- The planar volume of a finite union of common-radius balls tends to zero
with the radius.  Overlap is allowed; finite subadditivity and the exact
complex-ball volume formula suffice. -/
theorem tendsto_volume_finiteOpenBallHoles_zero {ι : Type*}
    (W : Finset ι) (c : ι → ℂ) :
    Tendsto (fun q : ℝ => volume (finiteOpenBallHoles W c q))
      (𝓝[>] 0) (𝓝 0) := by
  have hball (rho : ι) :
      Tendsto (fun q : ℝ => volume (Metric.ball (c rho) q))
        (𝓝[>] 0) (𝓝 0) := by
    simp only [Complex.volume_ball]
    have h : Tendsto
        (fun q : ℝ => ENNReal.ofReal q ^ 2 * NNReal.pi)
        (𝓝 0) (𝓝 (ENNReal.ofReal 0 ^ 2 * NNReal.pi)) := by
      exact ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.pow (ENNReal.tendsto_ofReal tendsto_id)) (by simp)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hsum : Tendsto
      (fun q : ℝ => ∑ rho ∈ W, volume (Metric.ball (c rho) q))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_finsetSum W fun rho _ => hball rho
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun q => measure_biUnion_finset_le W
      (fun rho => Metric.ball (c rho) q)

/-- The genuine set integral over a planar region after removing every ball
in a finite common-radius family. -/
def finiteBallExcisionIntegral {ι : Type*}
    (R : Set ℂ) (W : Finset ι) (c : ι → ℂ) (q : ℝ)
    (g : ℂ → ℂ) : ℂ :=
  ∫ z in R \ finiteOpenBallHoles W c q, g z ∂volume

/-- Removing a finite union of shrinking holes from a measurable region does
not change the limiting integral of a function integrable on that region. -/
theorem tendsto_finiteBallExcisionIntegral {ι : Type*}
    (R : Set ℂ) (W : Finset ι) (c : ι → ℂ) (g : ℂ → ℂ)
    (hRmeas : MeasurableSet R) (hg : IntegrableOn g R volume) :
    Tendsto (fun q : ℝ => finiteBallExcisionIntegral R W c q g)
      (𝓝[>] 0) (𝓝 (∫ z in R, g z ∂volume)) := by
  have hsmall : Tendsto
      (fun q : ℝ => ∫ z in finiteOpenBallHoles W c q,
        R.indicator g z ∂volume)
      (𝓝[>] 0) (𝓝 0) :=
    (hg.integrable_indicator hRmeas).tendsto_setIntegral_nhds_zero
      (tendsto_volume_finiteOpenBallHoles_zero W c)
  have hsmall' : Tendsto
      (fun q : ℝ => ∫ z in R ∩ finiteOpenBallHoles W c q, g z ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [setIntegral_indicator hRmeas, inter_comm] using hsmall
  have hconst : Tendsto (fun _ : ℝ => ∫ z in R, g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in R, g z ∂volume)) :=
    tendsto_const_nhds
  have hlimit := hconst.sub hsmall'
  have hlimit' : Tendsto
      (fun q : ℝ => (∫ z in R, g z ∂volume) -
        ∫ z in R ∩ finiteOpenBallHoles W c q, g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z in R, g z ∂volume)) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards with q
  unfold finiteBallExcisionIntegral
  have hset : R \ finiteOpenBallHoles W c q =
      R \ (R ∩ finiteOpenBallHoles W c q) := by
    ext z
    simp
  rw [hset]
  rw [setIntegral_sdiff
    (hRmeas.inter (measurableSet_finiteOpenBallHoles W c q)) hg
    inter_subset_left]

/-! ## The complete finite xi window -/

/-- One literal multiply perforated planar area integral for the actual
finite-window arithmetic Cauchy--Green source. -/
def suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
    (x tau T l r b u q : ℝ) : ℂ :=
  finiteBallExcisionIntegral ([[l, r]] ×ℂ [[b, u]])
    (spectralZetaZeroWindow T) suzukiChebyshevLaplaceZeroCoordinate q
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)

/-- The single rectangle with all finite xi holes removed converges to the
genuine through-divisor rectangular area of the actual arithmetic source. -/
theorem tendsto_suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T) :
    Tendsto
      (fun q : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
          x tau T l r b u q)
      (𝓝[>] 0)
      (𝓝 (rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau))) := by
  have hgeom := tendsto_finiteBallExcisionIntegral
    ([[l, r]] ×ℂ [[b, u]]) (spectralZetaZeroWindow T)
    suzukiChebyshevLaplaceZeroCoordinate
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
    (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet
    (integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
      x tau l r b u hT hrectangle)
  rw [←
    rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_eq_setIntegral
      x tau l r b u hT hlr hbu hrectangle] at hgeom
  simpa [suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral]
    using hgeom

/-- At every positive radius, omission from the finite ball union implies
omission from the complete finite shifted xi divisor. -/
theorem not_mem_suzukiChebyshevLaplaceZeroWindow_of_not_mem_finiteOpenBallHoles
    {T q : ℝ} (hq : 0 < q) {z : ℂ}
    (hz : z ∉ finiteOpenBallHoles (spectralZetaZeroWindow T)
      suzukiChebyshevLaplaceZeroCoordinate q) :
    z ∉ suzukiChebyshevLaplaceZeroWindow T := by
  intro hzW
  rcases Finset.mem_image.mp hzW with ⟨rho, hrho, heq⟩
  apply hz
  unfold finiteOpenBallHoles
  simp only [mem_iUnion]
  refine ⟨rho, hrho, ?_⟩
  rw [heq]
  simpa [Metric.mem_ball] using hq

/-- On every positive-radius multiply punctured rectangle, the actual
arithmetic source has exactly the same integral as the checked finite sum of
principal-part sources plus one analytic-remainder source. -/
theorem exists_suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral_sourceDecomposition
    (x tau T l r b u : ℝ) (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      ∀ q : ℝ, 0 < q →
        suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
            x tau T l r b u q =
          finiteBallExcisionIntegral ([[l, r]] ×ℂ [[b, u]])
            (spectralZetaZeroWindow T)
            suzukiChebyshevLaplaceZeroCoordinate q (fun z =>
              (∑ rho ∈ spectralZetaZeroWindow T,
                suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
                  x tau (analyticZetaZeroMultiplicity rho : ℂ)
                  (suzukiChebyshevLaplaceZeroCoordinate rho) z) +
              suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
                x tau F z) := by
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finitePrincipalPartDecomposition
      x tau hT
  refine ⟨F, hF, ?_⟩
  intro q hq
  unfold suzukiChebyshevLaplaceBoundaryHeatFiniteBallExcisionAreaIntegral
    finiteBallExcisionIntegral
  apply setIntegral_congr_fun
  · exact (isCompact_uIcc.reProdIm isCompact_uIcc).measurableSet.diff
      (measurableSet_finiteOpenBallHoles _ _ _)
  · intro z hz
    exact hdecomp z
      (not_mem_suzukiChebyshevLaplaceZeroWindow_of_not_mem_finiteOpenBallHoles
        hq hz.2)

end

end RiemannGaussian
