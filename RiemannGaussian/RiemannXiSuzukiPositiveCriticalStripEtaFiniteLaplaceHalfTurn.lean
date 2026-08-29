import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplacePartition

/-!
# The half-turn obstruction for finite eta roots

The positive Laplace measure underlying a finite paired-eta sum is supported
between logarithmic times `0` and `log (2N)`. Centering this support at its
midpoint sharpens the elementary phase obstruction from an uncentered quarter
turn to a half turn.

Concretely, if `|y| * log (2N) <= pi`, then after rotating the Fourier transform
all phases from the interiors of the supporting intervals lie strictly inside
the right half-plane. Its real part is therefore strictly positive, so the
transform cannot vanish. Lean proves the centered
rotation identity, the positivity theorem on every constituent interval, and
the resulting lower bound at every positive-real-part finite eta zero. The
bound is finally propagated to actual finite roots converging to every
nontrivial zeta zero.

This is an unconditional finite positive-measure theorem. Its lower bound is
only of order `1 / log N`, so it does not itself restrict the location of the
limiting zeta zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The tilted cosine moment after centering the logarithmic support at
`log (2N) / 2`. -/
def pairedEtaFiniteCenteredTiltedCosineMoment
    (N : ℕ) (sigma y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Real.exp (-sigma * t) *
        Real.cos (y * (t - Real.log (2 * N) / 2))

/-- Centering is exactly the real rotation of the two uncentered tilted
moments. -/
theorem pairedEtaFiniteCenteredTiltedCosineMoment_eq_rotation
    (N : ℕ) (sigma y : ℝ) :
    pairedEtaFiniteCenteredTiltedCosineMoment N sigma y =
      Real.cos (y * (Real.log (2 * N) / 2)) *
          pairedEtaFiniteTiltedCosineMoment N sigma y +
        Real.sin (y * (Real.log (2 * N) / 2)) *
          pairedEtaFiniteTiltedSineMoment N sigma y := by
  unfold pairedEtaFiniteCenteredTiltedCosineMoment
    pairedEtaFiniteTiltedCosineMoment
    pairedEtaFiniteTiltedSineMoment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show y * (t - Real.log (2 * N) / 2) =
      y * t - y * (Real.log (2 * N) / 2) by ring,
    Real.cos_sub]
  ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

/-- At a positive-real-part finite eta zero, the centered tilted cosine
moment vanishes exactly. -/
theorem pairedEtaFiniteCenteredTiltedCosineMoment_eq_zero_of_partialSum_eq_zero
    {N : ℕ} {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaCorePartialSum N
      ((sigma : ℂ) + (y : ℂ) * Complex.I) = 0) :
    pairedEtaFiniteCenteredTiltedCosineMoment N sigma y = 0 := by
  obtain ⟨hcosine, hsine⟩ :=
    pairedEtaFiniteTiltedMoments_eq_zero_of_partialSum_eq_zero
      hsigma hzero
  rw [pairedEtaFiniteCenteredTiltedCosineMoment_eq_rotation,
    hcosine, hsine]
  ring

/-- If the total phase spread is at most `pi`, the centered tilted cosine
integral on each paired eta interval is strictly positive. -/
theorem pairedEtaFiniteCenteredTiltedCosineInterval_pos_of_phase_le_pi
    {N n : ℕ} (hn : n < N) (sigma y : ℝ)
    (hphase : |y| * Real.log (2 * N) ≤ Real.pi) :
    0 < ∫ t : ℝ in
        Real.log (2 * n + 1)..Real.log (2 * n + 2),
      Real.exp (-sigma * t) *
        Real.cos (y * (t - Real.log (2 * N) / 2)) := by
  have hcont : Continuous (fun t : ℝ ↦
      Real.exp (-sigma * t) *
        Real.cos (y * (t - Real.log (2 * N) / 2))) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _)
  · intro t htMem
    have hoddNonneg : 0 ≤ Real.log (2 * n + 1) := by
      apply Real.log_nonneg
      norm_num
    have hargUpper : (2 : ℝ) * n + 2 ≤ 2 * N := by
      exact_mod_cast (show 2 * n + 2 ≤ 2 * N by omega)
    have hlogUpper : Real.log (2 * n + 2) ≤ Real.log (2 * N) := by
      exact Real.log_le_log (by positivity) hargUpper
    have htPos : 0 < t := hoddNonneg.trans_lt htMem.1
    have htLt : t < Real.log (2 * N) :=
      htMem.2.trans_le hlogUpper
    have hcenterAbs :
        |t - Real.log (2 * N) / 2| < Real.log (2 * N) / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have hphaseAt :
        |y * (t - Real.log (2 * N) / 2)| < Real.pi / 2 := by
      by_cases hy : y = 0
      · subst y
        norm_num
        exact Real.pi_pos
      · rw [abs_mul]
        calc
          |y| * |t - Real.log (2 * N) / 2| <
              |y| * (Real.log (2 * N) / 2) :=
            mul_lt_mul_of_pos_left hcenterAbs (abs_pos.mpr hy)
          _ = (|y| * Real.log (2 * N)) / 2 := by ring
          _ ≤ Real.pi / 2 :=
            (div_le_div_iff_of_pos_right
              (by norm_num : (0 : ℝ) < 2)).2 hphase
    exact mul_pos (Real.exp_pos _) <|
      Real.cos_pos_of_mem_Ioo (abs_lt.mp hphaseAt)
  · exact pairedEtaFiniteLogInterval_pos n

/-- A nonempty finite eta partition has strictly positive centered cosine
moment whenever its total phase spread is at most `pi`. -/
theorem pairedEtaFiniteCenteredTiltedCosineMoment_pos_of_phase_le_pi
    {N : ℕ} (hN : 0 < N) (sigma y : ℝ)
    (hphase : |y| * Real.log (2 * N) ≤ Real.pi) :
    0 < pairedEtaFiniteCenteredTiltedCosineMoment N sigma y := by
  unfold pairedEtaFiniteCenteredTiltedCosineMoment
  apply Finset.sum_pos
  · intro n hn
    exact
      pairedEtaFiniteCenteredTiltedCosineInterval_pos_of_phase_le_pi
        (Finset.mem_range.mp hn) sigma y hphase
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)

/-- Every positive-real-part zero of a nonempty finite eta sum must accumulate
at least a half turn of Fourier phase over its logarithmic support. -/
theorem pi_lt_abs_y_mul_log_of_pairedEtaCorePartialSum_eq_zero
    {N : ℕ} (hN : 0 < N) {sigma y : ℝ} (hsigma : 0 < sigma)
    (hzero : pairedEtaCorePartialSum N
      ((sigma : ℂ) + (y : ℂ) * Complex.I) = 0) :
    Real.pi < |y| * Real.log (2 * N) := by
  by_contra hphase
  have hphaseLe : |y| * Real.log (2 * N) ≤ Real.pi :=
    le_of_not_gt hphase
  have hpositive :=
    pairedEtaFiniteCenteredTiltedCosineMoment_pos_of_phase_le_pi
      hN sigma y hphaseLe
  have hmomentZero :=
    pairedEtaFiniteCenteredTiltedCosineMoment_eq_zero_of_partialSum_eq_zero
      hsigma hzero
  exact hpositive.ne' hmomentZero

/-- Every nontrivial zeta zero is approached by genuine finite positive
Laplace partition zeros which, eventually, satisfy both exact tilted Fourier
cancellations and the sharp elementary half-turn phase obstruction. -/
theorem exists_pairedEtaFiniteLaplaceHalfTurnZero_sequence_tendsto
    (rho : NontrivialZetaZero) :
    ∃ N : ℕ → ℕ, ∃ z : ℕ → ℂ,
      Tendsto N atTop atTop ∧
      Tendsto z atTop (nhds rho.1) ∧
      (∀ n, n ≤ N n) ∧
      (∀ n, dist (z n) rho.1 <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n) ∧
      (∀ n, pairedEtaCorePartialSum (N n) (z n) = 0) ∧
      ∀ᶠ n : ℕ in atTop,
        0 < (z n).re ∧
        pairedEtaFiniteTiltedCosineMoment
          (N n) (z n).re (z n).im = 0 ∧
        pairedEtaFiniteTiltedSineMoment
          (N n) (z n).re (z n).im = 0 ∧
        Real.pi < |(z n).im| * Real.log (2 * N n) := by
  obtain ⟨N, z, hNtendsto, hztendsto, hNge, hzDist, hzZero⟩ :=
    exists_pairedEtaCorePartialSum_zero_sequence_tendsto rho
  refine ⟨N, z, hNtendsto, hztendsto, hNge, hzDist, hzZero, ?_⟩
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < (z n).re :=
    hztendsto.eventually <|
      (Complex.isOpen_re_gt 0).mem_nhds
        (NontrivialZetaZero.zero_lt_re rho)
  filter_upwards [hpositive, eventually_ge_atTop 1] with n hnRe hnOne
  have hNpos : 0 < N n := by
    have hnLe := hNge n
    omega
  have hzZeroCoordinates :
      pairedEtaCorePartialSum (N n)
        (((z n).re : ℂ) + ((z n).im : ℂ) * Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using hzZero n
  have hmoments :=
    pairedEtaFiniteTiltedMoments_eq_zero_of_partialSum_eq_zero
      hnRe hzZeroCoordinates
  exact ⟨hnRe, hmoments.1, hmoments.2,
    pi_lt_abs_y_mul_log_of_pairedEtaCorePartialSum_eq_zero
      hNpos hnRe hzZeroCoordinates⟩

end

end RiemannGaussian
