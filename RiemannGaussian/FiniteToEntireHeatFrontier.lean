import RiemannGaussian.FiniteToEntireHardyReductio
import RiemannGaussian.HyperbolicHeatBridge

/-!
# The finite-to-entire Gaussian heat frontier

This file composes the exact hyperbolic heat representation with the checked
finite Hardy reductio.  If RH fails, the same root-pinned polynomial sequence
that carries the canonical Hardy frontier also carries, at every stage, a
multiplicity-counted Gaussian heat action.  Its truncated integrals converge
to the total logarithmic hyperbolic defect, and those limiting masses share
one fixed strictly positive lower bound.

No convergence of the root multisets or heat actions as the polynomial degree
tends to infinity is asserted.  Identifying a limiting arithmetic or entire
heat object is the remaining passage.
-/

open Filter Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Failure of RH produces an entire sequence of finite canonical heat
frontiers with one positive lower bound independent of the stage. -/
theorem exists_uniform_canonicalHeatAction_frontier_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        ∀ n,
          Tendsto
              (upperHalfPlaneHyperbolicHeatAction z
                (canonicalInsideInfluenceDiskRoots (B n) z))
              ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop)
              (nhds (canonicalInsideInfluenceDiskHeatMass (B n) z)) ∧
            -2 * Real.log (pairHyperbolicThreshold eta z.im) ≤
              canonicalInsideInfluenceDiskHeatMass (B n) z := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  have hthresholdPos : 0 < pairHyperbolicThreshold eta z.im :=
    pairHyperbolicThreshold_pos heta hz
  have hthresholdLtOne : pairHyperbolicThreshold eta z.im < 1 :=
    pairHyperbolicThreshold_lt_one heta hz
  have hthresholdLogNeg :
      Real.log (pairHyperbolicThreshold eta z.im) < 0 :=
    Real.log_neg hthresholdPos hthresholdLtOne
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, by nlinarith, ?_⟩
  intro n
  have hstage := canonicalInsideInfluenceDiskHeatAction_frontier
    (hfrontier n).separable heta hz (hfrontier n).homotopyRoot
  exact ⟨hstage.1, hstage.2.2⟩

end

end RiemannGaussian
