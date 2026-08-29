import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteRouche

/-!
# Zero persistence for finite paired-eta sums

The preceding local Rouché theorem proves exact equality of contour windings.
This module turns that nonzero winding into actual zeros of the finite
paired-eta sums. The key analytic lemma is elementary but essential: the
logarithmic derivative of an entire function that is nonzero throughout a
closed disk has zero circle integral by Cauchy--Goursat.

Since every nontrivial zeta zero has positive analytic multiplicity, the exact
finite eta winding from the preceding module cannot vanish. Hence every
sufficiently long finite eta sum has a zero in the corresponding isolating
disk. A diagonal choice then gives growing truncation indices and genuine
finite-sum zeros converging to each nontrivial zeta zero.

This is a divisor-persistence theorem, not a zero-location estimate: the
finite zeros converge equally well to on-line and off-line zeta zeros.
-/

open Complex Filter Metric Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- If an entire function has no zero on a closed disk, the circle integral
of its logarithmic derivative is zero. -/
theorem circleIntegral_logDeriv_eq_zero_of_differentiable_of_ne_zero_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ z ∈ closedBall c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = 0 := by
  have hlogAnalytic : ∀ z ∈ closedBall c R,
      AnalyticAt ℂ (logDeriv f) z := by
    intro z hz
    have hfAnalytic : AnalyticAt ℂ f z := hf.analyticAt z
    simpa only [logDeriv] using
      hfAnalytic.deriv.div hfAnalytic (hzero z hz)
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR countable_empty
  · intro z hz
    exact (hlogAnalytic z hz).continuousAt.continuousWithinAt
  · intro z hz
    exact
      (hlogAnalytic z (ball_subset_closedBall hz.1)).differentiableAt

/-- Below every prescribed positive radius around a nontrivial zeta zero,
there is an isolating disk in which every sufficiently long finite eta sum
has an actual zero. The limiting eta core has no other zero in the closed
disk. -/
theorem exists_lt_eventually_exists_pairedEtaCorePartialSum_zero
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧
      (∀ z ∈ closedBall rho.1 R,
        z ≠ rho.1 → pairedEtaCore z ≠ 0) ∧
      ∀ᶠ N : ℕ in atTop, ∃ z ∈ ball rho.1 R,
        pairedEtaCorePartialSum N z = 0 := by
  obtain ⟨R, hR, hRlt, hcoreZero, heventually⟩ :=
    exists_lt_eventually_pairedEtaCorePartialSum_logDeriv_eq_multiplicity
      rho hr
  refine ⟨R, hR, hRlt, hcoreZero, ?_⟩
  filter_upwards [heventually] with N hN
  have htargetNe :
      (analyticZetaZeroMultiplicity rho : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I ≠ 0 := by
    have hmNat : analyticZetaZeroMultiplicity rho ≠ 0 :=
      Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho)
    have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
      exact_mod_cast hmNat
    have htwoPi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    exact mul_ne_zero (mul_ne_zero hm htwoPi) Complex.I_ne_zero
  have hexistsClosed : ∃ z ∈ closedBall rho.1 R,
    pairedEtaCorePartialSum N z = 0 := by
    by_contra hnone
    push Not at hnone
    have hintegralZero :=
      circleIntegral_logDeriv_eq_zero_of_differentiable_of_ne_zero_closedBall
        (differentiable_pairedEtaCorePartialSum N) hR.le hnone
    exact htargetNe (hN.2.symm.trans hintegralZero)
  obtain ⟨z, hzClosed, hzZero⟩ := hexistsClosed
  have hzDistNe : dist z rho.1 ≠ R := by
    intro hzDist
    exact hN.1 z (mem_sphere.mpr hzDist) hzZero
  have hzBall : z ∈ ball rho.1 R := by
    rw [mem_ball]
    exact lt_of_le_of_ne (mem_closedBall.mp hzClosed) hzDistNe
  exact ⟨z, hzBall, hzZero⟩

/-- Every nontrivial zeta zero is the limit of genuine zeros of a sequence of
finite paired-eta sums whose truncation indices tend to infinity. The
distance at stage `n` is strictly below `1 / (n + 1)`, and the truncation
index is at least `n`. -/
theorem exists_pairedEtaCorePartialSum_zero_sequence_tendsto
    (rho : NontrivialZetaZero) :
    ∃ N : ℕ → ℕ, ∃ z : ℕ → ℂ,
      Tendsto N atTop atTop ∧
      Tendsto z atTop (nhds rho.1) ∧
      (∀ n, n ≤ N n) ∧
      (∀ n, dist (z n) rho.1 <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n) ∧
      ∀ n, pairedEtaCorePartialSum (N n) (z n) = 0 := by
  have hstage : ∀ n : ℕ, ∃ N : ℕ, ∃ z : ℂ,
      n ≤ N ∧
      dist z rho.1 < pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
      pairedEtaCorePartialSum N z = 0 := by
    intro n
    obtain ⟨R, hR, hRlt, _, heventually⟩ :=
      exists_lt_eventually_exists_pairedEtaCorePartialSum_zero
        rho (pairedEtaBoundaryHeatFluxDiagonalTolerance_pos n)
    obtain ⟨N, hNge, z, hzBall, hzZero⟩ :=
      ((eventually_ge_atTop n).and heventually).exists
    refine ⟨N, z, hNge, ?_, hzZero⟩
    exact (mem_ball.mp hzBall).trans hRlt
  choose N z hNge hzDist hzZero using hstage
  have hNtendsto : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop m] with n hn
    exact hn.trans (hNge n)
  have hztendsto : Tendsto z atTop (nhds rho.1) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero'
      (g := pairedEtaBoundaryHeatFluxDiagonalTolerance)
    · exact Eventually.of_forall fun _ => dist_nonneg
    · exact Eventually.of_forall fun n => (hzDist n).le
    · exact tendsto_pairedEtaBoundaryHeatFluxDiagonalTolerance_zero
  exact ⟨N, z, hNtendsto, hztendsto, hNge, hzDist, hzZero⟩

end

end RiemannGaussian
