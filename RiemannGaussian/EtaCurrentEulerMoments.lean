import RiemannGaussian.EtaCurrentEndpointSeries

/-!
# Quantitative Euler terms for the actual completed finite eta moments

Below the exact zero multiplicity, the finite prefix is the negative of
the genuine centered tail. Its checked Euler estimate yields an explicit
complex endpoint term with one additional inverse-cutoff power in the
error. Completion and endpoint phase are retained before taking norms.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The evaluated constant of the normalized centered eta tail. -/
def pairedEtaCurrentEulerMomentValue (rho : NontrivialZetaZero) (k : ℕ) : ℂ :=
  (k.factorial : ℂ) * (rho.1 ^ (k + 1))⁻¹ / 2

/-- The negative completed Euler endpoint term for the successor prefix. -/
def pairedEtaCurrentEulerMoment (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  -(pairedEtaXiCompletionFactor rho.1 * rho.1) *
    Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ)) *
      pairedEtaCurrentEulerMomentValue rho k

/-- The explicit amplitude of the completed Euler moment. -/
def pairedEtaCurrentEulerMomentAmplitude (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * ‖pairedEtaCurrentEulerMomentValue rho k‖

/-- The completion-weighted constant in the actual centered-tail Euler error. -/
def pairedEtaCurrentEulerMomentErrorConstant (rho : NontrivialZetaZero) (k : ℕ) : ℝ :=
  ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1

/-- The literal complex prefix error is exactly the completed and phased
shifted-tail error, with its negative zero-tail sign retained. -/
theorem pairedEtaFiniteCompletedMoment_sub_euler (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k =
      -(pairedEtaXiCompletionFactor rho.1 * rho.1) *
        Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ)) *
          (pairedEtaShiftedLogTailLaplaceMoment k rho.1 (N + 2) - pairedEtaCurrentEulerMomentValue rho k) := by
  have ht := pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_neg_partial_of_lt_multiplicity rho hk (N + 2)
  have hp : pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 (N + 2) =
      -pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 (N + 2) := by linear_combination ht
  unfold pairedEtaFiniteCompletedMoment pairedEtaCurrentEulerMoment
  rw [hp, pairedEtaLogLaplaceMomentCutoffCenteredTail_eq_exp_mul_shifted]
  ring

/-- The literal successor endpoint exponential retains the positive
zero-coordinate decay used by the arithmetic series estimates. -/
theorem norm_pairedEtaCurrent_successor_exp_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 2) : ℂ))‖ ≤
      pairedEtaCurrentMomentDecay rho N := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hq : 0 < ((2 * (N + 2) + 1 : ℕ) : ℝ) := by positivity
  rw [pairedEtaLogTailCutoff, show -rho.1.re * Real.log (((2 * (N + 2) + 1 : ℕ) : ℝ)) =
      Real.log (((2 * (N + 2) + 1 : ℕ) : ℝ)) * (-rho.1.re) by ring,
    ← Real.rpow_def_of_pos hq]
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast (show 2 * (N + 1) + 1 ≤ 2 * (N + 2) + 1 by omega))
    (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)

/-- The completed quantitative Euler error constant is nonnegative. -/
theorem pairedEtaCurrentEulerMomentErrorConstant_nonneg (rho : NontrivialZetaZero) (k : ℕ) :
    0 ≤ pairedEtaCurrentEulerMomentErrorConstant rho k := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  unfold pairedEtaCurrentEulerMomentErrorConstant pairedEtaCenteredTailQuantitativeAsymptoticConstant
  positivity

/-- Every completed endpoint model retains its explicit amplitude and
its actual horizontal decay. -/
theorem norm_pairedEtaCurrentEulerMoment_le (rho : NontrivialZetaZero) (N k : ℕ) :
    ‖pairedEtaCurrentEulerMoment rho N k‖ ≤
      pairedEtaCurrentEulerMomentAmplitude rho k * pairedEtaCurrentMomentDecay rho N := by
  unfold pairedEtaCurrentEulerMoment pairedEtaCurrentEulerMomentAmplitude
  rw [norm_mul, norm_mul, norm_neg]
  calc
    _ ≤ (‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * pairedEtaCurrentMomentDecay rho N) *
        ‖pairedEtaCurrentEulerMomentValue rho k‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (norm_pairedEtaCurrent_successor_exp_le rho N) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The actual lower finite moment differs from its complex Euler term
by an explicit extra inverse-cutoff power, at every cutoff. -/
theorem norm_pairedEtaFiniteCompletedMoment_sub_euler_le (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k‖ ≤
      pairedEtaCurrentEulerMomentErrorConstant rho k * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hC : 0 ≤ pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 := by
    unfold pairedEtaCenteredTailQuantitativeAsymptoticConstant
    positivity
  have he := norm_pairedEtaShiftedLogTailLaplaceMoment_sub_asymptoticValue_le k hs (N + 2)
  have hinv : (((2 * (N + 2) + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
    rw [Real.rpow_neg_one]
    have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1)
      (show (N + 1 : ℝ) ≤ ((2 * (N + 2) + 1 : ℕ) : ℝ) by
        exact_mod_cast (show N + 1 ≤ 2 * (N + 2) + 1 by omega))
    simpa only [one_div] using hi
  have he' : ‖pairedEtaShiftedLogTailLaplaceMoment k rho.1 (N + 2) - pairedEtaCurrentEulerMomentValue rho k‖ ≤
      pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 / (N + 1 : ℝ) :=
    he.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv hC)
  rw [pairedEtaFiniteCompletedMoment_sub_euler rho hk, norm_mul, norm_mul, norm_neg]
  calc
    _ ≤ (‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * pairedEtaCurrentMomentDecay rho N) *
        (pairedEtaCenteredTailQuantitativeAsymptoticConstant k rho.1 / (N + 1 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (norm_pairedEtaCurrent_successor_exp_le rho N) (norm_nonneg _))
        he' (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pairedEtaCurrentMomentDecay_bounds rho N).1)
    _ = _ := by unfold pairedEtaCurrentEulerMomentErrorConstant; ring

end

end RiemannGaussian
