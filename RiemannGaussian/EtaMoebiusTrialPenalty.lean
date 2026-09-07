import RiemannGaussian.EtaMoebiusTrialCoefficients
import RiemannGaussian.EtaCanonicalTranslateFamily
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Vanishing coefficient cost for an exact growing Möbius trial family

Stage `k` uses the original `2^k` physical scales and eta cutoff
`4*(2^k)^2`. Its Möbius cutoff is `k+1`, with the explicit logarithmic
taper and exact harmonic correction. The complete regularization cost
is at most `(k+1)^2/2^k`, which tends to zero. This does not prove
convergence of the full residual or of the canonical deficit.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The exact balanced logarithmic Möbius coefficients on the unchanged dyadic physical grid. -/
def pairedEtaDyadicMoebiusTrialCoefficient (k : ℕ) : Fin (pairedEtaDyadicTranslateDimension k) → ℝ :=
  pairedEtaMoebiusTrialCoefficient (pairedEtaDyadicTranslateDimension k) (k + 1)
    (pairedEtaMoebiusTrialLogWeight (k + 1))

/-- The full diagonal allowance which pays for the entire omitted coefficient tail. -/
def pairedEtaDyadicMoebiusTrialPenalty (k : ℕ) : ℝ :=
  pairedEtaTranslateRegularization (pairedEtaDyadicTranslateDimension k) (pairedEtaDyadicTranslateCutoff k) *
    ∑ j, pairedEtaDyadicMoebiusTrialCoefficient k j ^ 2

/-- A completely explicit vanishing upper bound for the actual growing coefficient cost. -/
def pairedEtaDyadicMoebiusTrialAllowance (k : ℕ) : ℝ := (k + 1 : ℝ) ^ 2 / (2 : ℝ) ^ k

/-- Every arithmetic cutoff of the specified trial family fits the original dyadic grid. -/
theorem pairedEtaDyadicMoebiusTrial_cutoff_le_dimension (k : ℕ) :
    k + 1 ≤ pairedEtaDyadicTranslateDimension k := by
  unfold pairedEtaDyadicTranslateDimension
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

/-- Every full coefficient vector in the exact trial family has zero signed total mass. -/
theorem sum_pairedEtaDyadicMoebiusTrialCoefficient_eq_zero (k : ℕ) :
    (∑ j, pairedEtaDyadicMoebiusTrialCoefficient k j) = 0 :=
  sum_pairedEtaMoebiusTrialCoefficient_eq_zero (pairedEtaDyadicMoebiusTrial_cutoff_le_dimension k) _

/-- The exact logarithmic Möbius trial has an absolute coefficient sum at most twice its arithmetic cutoff. -/
theorem pairedEtaDyadicMoebiusTrialCoefficient_sum_abs_le (k : ℕ) :
    (∑ j, |pairedEtaDyadicMoebiusTrialCoefficient k j|) ≤ 2 * (k + 1 : ℝ) := by
  simpa only [pairedEtaDyadicMoebiusTrialCoefficient, Nat.cast_add, Nat.cast_one] using pairedEtaMoebiusTrialCoefficient_sum_abs_le
    (pairedEtaDyadicTranslateDimension k) (k + 1) (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)

/-- The exact logarithmic trial has a coefficient-square sum at most four times the square of its arithmetic cutoff. -/
theorem pairedEtaDyadicMoebiusTrialCoefficient_sum_sq_le (k : ℕ) :
    (∑ j, pairedEtaDyadicMoebiusTrialCoefficient k j ^ 2) ≤ 4 * (k + 1 : ℝ) ^ 2 := by
  simpa only [pairedEtaDyadicMoebiusTrialCoefficient, Nat.cast_add, Nat.cast_one] using pairedEtaMoebiusTrialCoefficient_sum_sq_le
    (pairedEtaDyadicTranslateDimension k) (k + 1) (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)

/-- The original regularization at its specified quadratic eta cutoff is at most one quarter of the inverse dimension. -/
theorem pairedEtaTranslateRegularization_quadratic_le {d : ℕ} (hd : 1 ≤ d) :
    pairedEtaTranslateRegularization d (4 * d ^ 2) ≤ 1 / (4 * (d : ℝ)) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  unfold pairedEtaTranslateRegularization
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (2 * (d : ℝ) - 1)]

/-- The full regularization cost of the exact trial family is nonnegative. -/
theorem pairedEtaDyadicMoebiusTrialPenalty_nonneg (k : ℕ) : 0 ≤ pairedEtaDyadicMoebiusTrialPenalty k :=
  mul_nonneg (pairedEtaTranslateRegularization_pos _ _).le (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

/-- The actual coefficient penalty has an unconditional polynomial-over-exponential bound at every stage. -/
theorem pairedEtaDyadicMoebiusTrialPenalty_le (k : ℕ) :
    pairedEtaDyadicMoebiusTrialPenalty k ≤ pairedEtaDyadicMoebiusTrialAllowance k := by
  have hd := pairedEtaDyadicTranslateDimension_pos k
  have hl := pairedEtaTranslateRegularization_quadratic_le (show 1 ≤ pairedEtaDyadicTranslateDimension k by omega)
  calc
    _ ≤ pairedEtaTranslateRegularization (pairedEtaDyadicTranslateDimension k) (pairedEtaDyadicTranslateCutoff k) *
        (4 * (k + 1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (pairedEtaDyadicMoebiusTrialCoefficient_sum_sq_le k)
        (pairedEtaTranslateRegularization_pos _ _).le
    _ ≤ (1 / (4 * (pairedEtaDyadicTranslateDimension k : ℝ))) * (4 * (k + 1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hl (by positivity)
    _ = _ := by
      unfold pairedEtaDyadicTranslateDimension pairedEtaDyadicMoebiusTrialAllowance
      push_cast
      ring

/-- The exact polynomial-over-exponential allowance tends to zero along all dyadic stages. -/
theorem pairedEtaDyadicMoebiusTrialAllowance_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusTrialAllowance atTop (𝓝 0) := by
  have h := ((tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)).const_mul (2 : ℝ)
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] at h
  convert h using 1
  ext k
  unfold pairedEtaDyadicMoebiusTrialAllowance
  rw [pow_succ]
  ring

/-- The complete regularization penalty of the actual arithmetic coefficient family tends to zero, without assuming any residual estimate. -/
theorem pairedEtaDyadicMoebiusTrialPenalty_tendsto_zero :
    Tendsto pairedEtaDyadicMoebiusTrialPenalty atTop (𝓝 0) :=
  squeeze_zero pairedEtaDyadicMoebiusTrialPenalty_nonneg pairedEtaDyadicMoebiusTrialPenalty_le
    pairedEtaDyadicMoebiusTrialAllowance_tendsto_zero

end

end RiemannGaussian
