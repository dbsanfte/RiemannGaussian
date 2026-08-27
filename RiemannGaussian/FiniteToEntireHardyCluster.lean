import RiemannGaussian.FiniteToEntireTheta
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# A subsequential finite-to-entire Hardy scalar

The finite Hardy frontier supplies a uniformly contractive residual-inner
value at the fixed pinned upper root.  Since the closed ball in `ℂ` is
compact, these values have a convergent subsequence.  The resulting scalar
retains the explicit gap

`‖s‖ ≤ eta / sqrt (eta^2 + z.im^2) < 1`.

The final theorem composes this compactness step with failure of RH and the
zero-free theta convergence theorem.  This constructs a genuine limiting
cancelled scalar, but does not assert that it is independent of the chosen
subsequence or identify it with an arithmetic or entire-function invariant.
Those are the remaining rigidity problems.
-/

open Filter Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- A sequence carrying the canonical finite Hardy frontier has a
subsequence whose residual-inner values at the pinned root converge.  The
limit retains the same uniform quantitative gap below one. -/
theorem exists_pinnedHardyScalarCluster_of_canonicalFiniteHardyFrontier
    {B : ℕ → ℝ[X]} {eta : ℝ} (heta : 0 < eta) {z : ℂ}
    (hz : 0 < z.im)
    (hfrontier : ∀ n, CanonicalFiniteHardyFrontier (B n) eta z) :
    ∃ s : ℂ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
      Tendsto
        (fun n ↦ lowerRootInnerValue
          (finiteEPolynomial (B (phi n)) eta) z)
        atTop (𝓝 s) ∧
      ‖s‖ ≤ eta / Real.sqrt (eta ^ 2 + z.im ^ 2) ∧
      ‖s‖ < 1 := by
  let c := eta / Real.sqrt (eta ^ 2 + z.im ^ 2)
  let u : ℕ → ℂ := fun n ↦
    lowerRootInnerValue (finiteEPolynomial (B n) eta) z
  have hu : ∀ n, u n ∈ Metric.closedBall (0 : ℂ) c := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_lowerRootInnerValue_le_closed_bound_of_finiteE_root
      (hfrontier n).separable heta hz (hfrontier n).homotopyRoot
  obtain ⟨s, hs, phi, hphi, hlimit⟩ :=
    (isCompact_closedBall (0 : ℂ) c).tendsto_subseq hu
  have hsc : ‖s‖ ≤ c := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hs
  have hc : c < 1 := by
    exact eta_div_sqrt_eta_sq_add_height_sq_lt_one heta hz
  exact ⟨s, phi, hphi, hlimit, hsc, hsc.trans_lt hc⟩

/-- If RH fails, one sequence simultaneously carries the complete finite
Hardy frontier, the zero-free locally uniform theta limit, and a convergent
subsequence of cancelled residual-inner values whose limit is uniformly
separated from the unit circle. -/
theorem exists_hardyScalarCluster_theta_limit_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        (∀ U : Set ℂ, IsOpen U →
          (∀ w ∈ U, analyticEValue riemannXiSpectral eta w ≠ 0) →
          TendstoLocallyUniformlyOn
            (fun n ↦ finiteThetaValue (B n) eta)
            (analyticThetaValue riemannXiSpectral eta) atTop U) ∧
        ∃ s : ℂ, ∃ phi : ℕ → ℕ,
          StrictMono phi ∧
          Tendsto
            (fun n ↦ lowerRootInnerValue
              (finiteEPolynomial (B (phi n)) eta) z)
            atTop (𝓝 s) ∧
          ‖s‖ ≤ eta / Real.sqrt (eta ^ 2 + z.im ^ 2) ∧
          ‖s‖ < 1 := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier, htheta⟩ :=
    exists_canonicalFiniteHardyFrontier_theta_limit_of_not_rh hRH
  obtain ⟨s, phi, hphi, hlimit, hbound, hstrict⟩ :=
    exists_pinnedHardyScalarCluster_of_canonicalFiniteHardyFrontier
      heta hz hfrontier
  exact ⟨eta, heta, z, hz, B, hB, hfrontier, htheta,
    s, phi, hphi, hlimit, hbound, hstrict⟩

end

end RiemannGaussian
