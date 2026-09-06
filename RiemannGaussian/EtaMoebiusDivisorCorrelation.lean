import RiemannGaussian.EtaDivisorGcdBound
import RiemannGaussian.EtaMoebiusDyadicCorrelation

/-!
# The complete divisor covariance of the actual completed eta terms

The arbitrary-window correlation retains the literal Möbius coefficients,
both complex physical endpoint powers, and the reduced parity colours.
Its exact decomposition separates the full gcd covariance, the unfinished
arithmetic period, and the actual complex endpoint error before taking norms.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The signed real completion coefficient of two literal Möbius columns. -/
def pairedEtaCompletedMoebiusDivisorCoefficient (rho : NontrivialZetaZero) (d e : ℕ) : ℝ :=
  (μ d : ℝ) * (μ e : ℝ) * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4

/-- The complex leading pair keeps both arithmetic signs and its exact
completion amplitude before averaging the quotient phases. -/
theorem pairedEtaCompletedMoebiusParityPair_eq_divisorCoefficient
    (rho : NontrivialZetaZero) (M d e : ℕ) :
    pairedEtaCompletedMoebiusParityPair rho M d e =
      (pairedEtaCompletedMoebiusDivisorCoefficient rho d e : ℂ) *
        (pairedEtaDivisorParityProduct d e M : ℂ) := by
  have hx := Complex.mul_conj' (pairedEtaXiCompletionFactor rho.1)
  unfold pairedEtaCompletedMoebiusParityPair pairedEtaCompletedMoebiusParityPhase
    pairedEtaCompletedMoebiusDivisorCoefficient pairedEtaDivisorParityProduct
  push_cast
  simp only [map_div₀, map_mul, map_intCast, map_ofNat]
  linear_combination ((μ d : ℂ) * (μ e : ℂ) *
    (pairedEtaDirichletSign (M / d) : ℂ) * (pairedEtaDirichletSign (M / e) : ℂ) / 4) * hx

/-- Both Möbius coefficients have absolute value at most one. -/
theorem abs_pairedEtaCompletedMoebiusDivisorCoefficient_le
    (rho : NontrivialZetaZero) (d e : ℕ) :
    |pairedEtaCompletedMoebiusDivisorCoefficient rho d e| ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 := by
  have hd : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have he : |(μ e : ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
  unfold pairedEtaCompletedMoebiusDivisorCoefficient
  simp only [abs_div, abs_mul, abs_pow, abs_norm]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have h := mul_le_mul hd he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_right h
    (sq_nonneg ‖pairedEtaXiCompletionFactor rho.1‖)

/-- The literal completed pair averaged on an arbitrary integer window. -/
def pairedEtaCompletedMoebiusDivisorCorrelation (rho : NontrivialZetaZero) (A L d e : ℕ) : ℂ :=
  (∑ r ∈ Finset.range L, pairedEtaCompletedMoebiusEndpointPair rho (A + r) d e) / L

/-- The leading complex average keeps the exact signed coefficient and
the full raw phase average, including unfinished arithmetic periods. -/
theorem pairedEtaCompletedMoebiusParityPair_average_eq
    (rho : NontrivialZetaZero) (A L d e : ℕ) :
    (∑ r ∈ Finset.range L, pairedEtaCompletedMoebiusParityPair rho (A + r) d e) / (L : ℂ) =
      (pairedEtaCompletedMoebiusDivisorCoefficient rho d e : ℂ) *
        (pairedEtaDivisorParityAverage A L d e : ℂ) := by
  simp_rw [pairedEtaCompletedMoebiusParityPair_eq_divisorCoefficient]
  rw [← Finset.mul_sum]
  unfold pairedEtaDivisorParityAverage
  push_cast
  ring

/-- The actual correlation splits exactly into its signed gcd main term,
its literal window remainder, and its completed complex endpoint error. -/
theorem pairedEtaCompletedMoebiusDivisorCorrelation_eq_covariance_add_errors
    (rho : NontrivialZetaZero) (A L d e : ℕ) :
    pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e =
      ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
        pairedEtaDivisorParityCovariance d e : ℝ) : ℂ) +
      ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
        (pairedEtaDivisorParityAverage A L d e - pairedEtaDivisorParityCovariance d e) : ℝ) : ℂ) +
      (∑ r ∈ Finset.range L,
        (pairedEtaCompletedMoebiusEndpointPair rho (A + r) d e -
          pairedEtaCompletedMoebiusParityPair rho (A + r) d e)) / L := by
  rw [Finset.sum_sub_distrib, sub_div,
    pairedEtaCompletedMoebiusParityPair_average_eq]
  unfold pairedEtaCompletedMoebiusDivisorCorrelation
  push_cast
  ring

/-- The true endpoint error has a uniform average bound at every positive
starting cutoff; no divisor-dependent normalization has been discarded. -/
theorem norm_pairedEtaCompletedMoebiusDivisorCorrelation_endpoint_error_le
    (rho : NontrivialZetaZero) {A L d e : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ‖(∑ r ∈ Finset.range L,
      (pairedEtaCompletedMoebiusEndpointPair rho (A + r) d e -
        pairedEtaCompletedMoebiusParityPair rho (A + r) d e)) / (L : ℂ)‖ ≤
      pairedEtaCompletedMoebiusPairPhaseError rho d e A := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hLR).mpr
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _r ∈ Finset.range L, pairedEtaCompletedMoebiusPairPhaseError rho d e A := by
      apply Finset.sum_le_sum
      intro r hr
      exact (norm_pairedEtaCompletedMoebiusEndpointPair_sub_parity_le rho (by omega) hd he).trans
        (pairedEtaCompletedMoebiusPairPhaseError_antitone rho d e hA (by omega))
    _ = _ := by simp [mul_comm]

/-- An explicit arbitrary-window error for every actual completed divisor
pair. The nonzero gcd covariance is retained as the main term. -/
theorem norm_pairedEtaCompletedMoebiusDivisorCorrelation_sub_covariance_le
    (rho : NontrivialZetaZero) {A L d e : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ‖pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e -
      ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
        pairedEtaDivisorParityCovariance d e : ℝ) : ℂ)‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * d * e / (L : ℝ) +
        pairedEtaCompletedMoebiusPairPhaseError rho d e A := by
  rw [pairedEtaCompletedMoebiusDivisorCorrelation_eq_covariance_add_errors]
  have heq (a b c : ℂ) : a + b + c - a = b + c := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add _
    (norm_pairedEtaCompletedMoebiusDivisorCorrelation_endpoint_error_le rho hA hL hd he)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h := mul_le_mul (abs_pairedEtaCompletedMoebiusDivisorCoefficient_le rho d e)
    (abs_pairedEtaDivisorParityAverage_sub_covariance_le A hL hd he)
    (abs_nonneg _) (by positivity)
  convert h using 1
  ring

/-- The actual correlation has a scalar bound only after its complete
signed gcd decomposition and both error terms have been retained. -/
theorem norm_pairedEtaCompletedMoebiusDivisorCorrelation_le
    (rho : NontrivialZetaZero) {A L d e : ℕ}
    (hA : 1 ≤ A) (hL : 0 < L) (hd : 1 ≤ d) (he : 1 ≤ e) :
    ‖pairedEtaCompletedMoebiusDivisorCorrelation rho A L d e‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 * pairedEtaDivisorParityCovariance d e +
      (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 * d * e / (L : ℝ) +
        pairedEtaCompletedMoebiusPairPhaseError rho d e A) := by
  apply (norm_le_insert' _
    ((pairedEtaCompletedMoebiusDivisorCoefficient rho d e *
      pairedEtaDivisorParityCovariance d e : ℝ) : ℂ)).trans
  apply add_le_add _
    (norm_pairedEtaCompletedMoebiusDivisorCorrelation_sub_covariance_le rho hA hL hd he)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pairedEtaDivisorParityCovariance_nonneg d e)]
  exact mul_le_mul_of_nonneg_right
    (abs_pairedEtaCompletedMoebiusDivisorCoefficient_le rho d e)
    (pairedEtaDivisorParityCovariance_nonneg d e)

end

end RiemannGaussian
