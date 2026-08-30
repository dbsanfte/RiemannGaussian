import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailSharpAsymptotic
import Mathlib.Analysis.Complex.Liouville

/-!
# Quantitative all-order asymptotics of centered eta tails

The sharp centered-tail limit was obtained by locally uniform holomorphic
convergence, which alone does not retain a rate after differentiation.  This
module starts from the explicit Euler second-difference bound for the
normalized zeroth tail and applies Cauchy's derivative estimate on the disk
of radius `Re(s)/2`.

For every order `k` and every `Re(s)>0`, the normalized shifted moment differs
from `k!/(2*s^(k+1))` by at most an explicit constant times
`(2N+1)^(-1)`.  The same bound is then transferred exactly to the complex-
power-normalized literal centered tail.  This quantified remainder is the
input needed to take consecutive cutoff differences rigorously.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

open ProbabilityTheory

/-- The zeroth shifted-moment error is exactly the normalized core-tail error
divided by the spectral parameter. -/
theorem pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_eq
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaShiftedLogTailLaplaceMoment 0 s N - (1 / 2) / s =
      (pairedEtaCoreNormalizedTail N s - 1 / 2) / s := by
  rw [←
    pairedEtaCoreNormalizedLaplaceTail_eq_shiftedLogTailLaplaceMoment_zero
      hs N]
  unfold pairedEtaCoreNormalizedLaplaceTail
  ring

/-- Explicit zeroth-order error bound after translating the eta tail to its
first omitted odd endpoint. -/
theorem norm_pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaShiftedLogTailLaplaceMoment 0 s N - (1 / 2) / s‖ ≤
      ‖s + 1‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  rw [pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_eq hs,
    norm_div]
  calc
    ‖pairedEtaCoreNormalizedTail N s - 1 / 2‖ / ‖s‖ ≤
        (‖s‖ * ‖s + 1‖ *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ))) / ‖s‖ :=
      div_le_div_of_nonneg_right
        (norm_pairedEtaCoreNormalizedTail_sub_half_le hs N)
        (norm_nonneg s)
    _ = ‖s + 1‖ *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      field_simp [norm_ne_zero_iff.mpr hsne]

/-- Every point in the closed disk of radius `Re(s)/2` about a positive-half-
plane point still has positive real part. -/
private theorem re_pos_of_mem_closedBall_half_re
    {s z : ℂ} (hs : 0 < s.re)
    (hz : z ∈ closedBall s (s.re / 2)) :
    0 < z.re := by
  have hdist : ‖z - s‖ ≤ s.re / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hreabs : |z.re - s.re| ≤ s.re / 2 := by
    calc
      |z.re - s.re| = |(z - s).re| := by
        rw [Complex.sub_re]
      _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _
      _ ≤ s.re / 2 := hdist
  have hlower := neg_le_of_abs_le hreabs
  linarith

/-- Iterated differentiation of the normalized zeroth-error function is the
signed error in the corresponding shifted centered moment. -/
theorem iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_eq
    (k N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv k
        (fun w : ℂ =>
          pairedEtaShiftedLogTailLaplaceMoment 0 w N - (1 / 2) / w) s =
      (-1 : ℂ) ^ k *
        (pairedEtaShiftedLogTailLaplaceMoment k s N -
          (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)) := by
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hmoment : ContDiffAt ℂ k
      (fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N) s :=
    (analyticOnNhd_pairedEtaShiftedLogTailLaplaceMoment_zero N s hs).contDiffAt
  have hlimitAnalytic : AnalyticAt ℂ (fun w : ℂ => (1 / 2) / w) s :=
    analyticAt_const.div analyticAt_id hsne
  change iteratedDeriv k
      ((fun w => pairedEtaShiftedLogTailLaplaceMoment 0 w N) -
        (fun w : ℂ => (1 / 2) / w)) s = _
  rw [iteratedDeriv_sub hmoment hlimitAnalytic.contDiffAt,
    iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero_eq_moment k N hs,
    iteratedDeriv_half_div_id,
    pairedEtaCenteredTailAsymptoticValue_eq]
  ring

/-- The explicit Cauchy-estimate constant for the normalized order-`k`
centered eta-tail remainder at `s`. -/
def pairedEtaCenteredTailQuantitativeAsymptoticConstant
    (k : ℕ) (s : ℂ) : ℝ :=
  (k.factorial : ℝ) * (‖s‖ + s.re / 2 + 1) /
    (s.re / 2) ^ k

/-- Cauchy's derivative estimate transports the explicit zeroth-order Euler
remainder to every shifted centered moment with an explicit one-endpoint-
power saving. -/
theorem norm_pairedEtaShiftedLogTailLaplaceMoment_sub_asymptoticValue_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaShiftedLogTailLaplaceMoment k s N -
        (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)‖ ≤
      pairedEtaCenteredTailQuantitativeAsymptoticConstant k s *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  let R : ℝ := s.re / 2
  let endpointError : ℝ :=
    (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ))
  let C : ℝ := (‖s‖ + R + 1) * endpointError
  let f : ℂ → ℂ := fun w =>
    pairedEtaShiftedLogTailLaplaceMoment 0 w N - (1 / 2) / w
  have hR : 0 < R := by dsimp [R]; linarith
  have hdiff : DiffContOnCl ℂ f (ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    have hzpos : 0 < z.re := by
      apply re_pos_of_mem_closedBall_half_re hs
      simpa only [R] using hz
    have hzne : z ≠ 0 := by
      intro hzero
      rw [hzero] at hzpos
      norm_num at hzpos
    exact
      ((analyticOnNhd_pairedEtaShiftedLogTailLaplaceMoment_zero N z hzpos).sub
        (analyticAt_const.div analyticAt_id hzne)).differentiableAt.differentiableWithinAt
  have hsphere : ∀ z ∈ sphere s R, ‖f z‖ ≤ C := by
    intro z hz
    have hzclosed : z ∈ closedBall s R := sphere_subset_closedBall hz
    have hzpos : 0 < z.re := by
      apply re_pos_of_mem_closedBall_half_re hs
      simpa only [R] using hzclosed
    have hdist : ‖z - s‖ = R := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    have hznorm : ‖z‖ ≤ ‖s‖ + R := by
      calc
        ‖z‖ = ‖(z - s) + s‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
        _ = ‖s‖ + R := by rw [hdist]; ring
    have hzplus : ‖z + 1‖ ≤ ‖s‖ + R + 1 := by
      calc
        ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖s‖ + R) + 1 := by simpa using add_le_add_right hznorm 1
    change
      ‖pairedEtaShiftedLogTailLaplaceMoment 0 z N - (1 / 2) / z‖ ≤ C
    calc
      ‖pairedEtaShiftedLogTailLaplaceMoment 0 z N - (1 / 2) / z‖ ≤
          ‖z + 1‖ * endpointError := by
        simpa only [endpointError] using
          norm_pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_le
            hzpos N
      _ ≤ (‖s‖ + R + 1) * endpointError :=
        mul_le_mul_of_nonneg_right hzplus
          (Real.rpow_nonneg (by positivity) _)
      _ = C := by rfl
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      k hR hdiff hsphere
  have hderiv :=
    iteratedDeriv_pairedEtaShiftedLogTailLaplaceMoment_zero_sub_half_div_eq
      k N hs
  have hnorm : ‖iteratedDeriv k f s‖ =
      ‖pairedEtaShiftedLogTailLaplaceMoment k s N -
        (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)‖ := by
    dsimp only [f]
    rw [hderiv, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    ‖pairedEtaShiftedLogTailLaplaceMoment k s N -
          (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)‖ =
        ‖iteratedDeriv k f s‖ := hnorm.symm
    _ ≤ (k.factorial : ℝ) * C / R ^ k := hcauchy
    _ = pairedEtaCenteredTailQuantitativeAsymptoticConstant k s *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      unfold pairedEtaCenteredTailQuantitativeAsymptoticConstant
      dsimp only [C, R, endpointError]
      ring

/-- Exact endpoint normalization transfers the quantitative shifted-moment
remainder to every literal cutoff-centered eta tail. -/
theorem
    norm_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail_sub_asymptoticValue_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ s *
          pairedEtaLogLaplaceMomentCutoffCenteredTail k s N -
        (((k.factorial : ℕ) : ℂ) * (s ^ (k + 1))⁻¹ / 2)‖ ≤
      pairedEtaCenteredTailQuantitativeAsymptoticConstant k s *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  rw [pairedEtaOddEndpoint_cpow_mul_cutoffCenteredTail_eq_shiftedMoment]
  exact
    norm_pairedEtaShiftedLogTailLaplaceMoment_sub_asymptoticValue_le
      k hs N

end

end RiemannGaussian
