import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevDrift

/-!
# Logarithmic-average coordinate for the Suzuki arithmetic frontier

The fixed-endpoint error is built from the same weighted Chebyshev mass and
log-moment as the logarithmically averaged error

`log(b) * sum Lambda(n) / sqrt(n) -
  sum Lambda(n) * log(n) / sqrt(n) - 4 * sqrt(b)`.

This file makes that relation exact.  At every natural endpoint the new
coordinate is proved equal to the literal finite von-Mangoldt sum with kernel
`log(b / n)`.  The endpoint error is its negative, with the precise
lower-order offset `-log(b) - 4`.  Consequently both the exact entropy
frontier and its sufficient quadratic majorant are rewritten as quantitative
upper bounds for one logarithmic average.

No sign bound for that average is assumed or proved here.  In particular, the
identities isolate rather than discharge the conjecture-strength arithmetic
obligation.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## The logarithmic-average statistic -/

/-- The weighted Chebyshev logarithmic-average error after subtracting its
continuous square-root main term. -/
def suzukiChebyshevLogAverageError (b : ℝ) : ℝ :=
  Real.log b * suzukiChebyshevWeightedMass b -
    suzukiChebyshevWeightedLogMoment b -
      4 * b ^ (1 / 2 : ℝ)

/-- The fixed-endpoint error is exactly the negative logarithmic-average
error with its complete lower-order offset. -/
theorem suzukiChebyshevEndpointCenteredError_eq_neg_logAverage_sub_log_sub_four
    (b : ℝ) :
    suzukiChebyshevEndpointCenteredError b =
      -suzukiChebyshevLogAverageError b - Real.log b - 4 := by
  unfold suzukiChebyshevEndpointCenteredError
    suzukiChebyshevLogAverageError
    suzukiChebyshevWeightedMassError
    suzukiChebyshevWeightedLogMomentError
    suzukiChebyshevContinuousMass
    suzukiChebyshevContinuousLogMoment
  ring

/-- Nonnegativity of the fixed-endpoint error is precisely a quantitative
negative bound for the logarithmic average. -/
theorem suzukiChebyshevEndpointCenteredError_nonnegative_iff_logAverage_le
    (b : ℝ) :
    0 ≤ suzukiChebyshevEndpointCenteredError b ↔
      suzukiChebyshevLogAverageError b ≤ -Real.log b - 4 := by
  rw [suzukiChebyshevEndpointCenteredError_eq_neg_logAverage_sub_log_sub_four]
  constructor <;> intro h <;> linarith

/-! ## Literal finite-sum form -/

/-- At every natural endpoint the logarithmic-average coordinate is the
literal weighted von-Mangoldt log average, written without a quotient. -/
theorem suzukiChebyshevLogAverageError_nat_eq_sum_log_sub_log
    (cutoff : ℕ) :
    suzukiChebyshevLogAverageError (((cutoff + 1 : ℕ) : ℝ)) =
      (∑ n ∈ Finset.Ioc 1 (cutoff + 1),
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (Real.log (((cutoff + 1 : ℕ) : ℝ)) - Real.log n)) -
        4 * (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
  unfold suzukiChebyshevLogAverageError
  rw [← screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass,
    screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum,
    ← screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment,
    screwPrefixMoment_suzukiPrime_eq_suzukiChebyshevLogMomentSum]
  simp_rw [suzukiChebyshevMassKernel_nat_eq,
    suzukiChebyshevLogMomentKernel_nat_eq]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply congrArg (fun value : ℝ => value -
    4 * (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)))
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The same natural-endpoint formula in Suzuki's quotient-log kernel. -/
theorem suzukiChebyshevLogAverageError_nat_eq_sum_log_div
    (cutoff : ℕ) :
    suzukiChebyshevLogAverageError (((cutoff + 1 : ℕ) : ℝ)) =
      (∑ n ∈ Finset.Ioc 1 (cutoff + 1),
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            Real.log ((((cutoff + 1 : ℕ) : ℝ) / n))) -
        4 * (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
  rw [suzukiChebyshevLogAverageError_nat_eq_sum_log_sub_log]
  apply congrArg (fun value : ℝ => value -
    4 * (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)))
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by
      have := (Finset.mem_Ioc.mp hn).1
      omega)
  have hendpointPos : (0 : ℝ) < ((cutoff + 1 : ℕ) : ℝ) := by
    positivity
  rw [Real.log_div hendpointPos.ne' hnPos.ne']

/-- The cumulative signed mass-error work from the discrete drift law is
exactly the logarithmic-average error plus an elementary logarithmic offset
and the cumulative smooth drift.  Thus the two apparent arithmetic
frontiers are the same statistic in different coordinates. -/
theorem
    suzukiChebyshevCumulativeMassErrorWork_eq_logAverage_add_logOffset_add_drift
    (count : ℕ) :
    suzukiChebyshevCumulativeMassErrorWork count =
      suzukiChebyshevLogAverageError (((count + 2 : ℕ) : ℝ)) +
        Real.log (((count + 2 : ℕ) : ℝ)) - Real.log 2 +
        4 * (2 : ℝ) ^ (1 / 2 : ℝ) +
        suzukiChebyshevCumulativeSmoothEndpointDrift count := by
  have hwork :=
    suzukiChebyshevEndpointCenteredError_eq_initial_add_cumulativeDrift_sub_work
      count
  rw [suzukiChebyshevEndpointCenteredError_eq_neg_logAverage_sub_log_sub_four]
    at hwork
  linarith

/-! ## Exact and quadratic frontier coordinates -/

/-- The exact canonical gap condition in logarithmic-average coordinates.
The entropy term remains the exact nonnegative Legendre cost. -/
theorem
    suzukiFirstTailResetTransportGap_succ_nonnegative_iff_logAverage_entropy_bound
    (count : ℕ) :
    0 ≤ curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) ↔
      suzukiChebyshevLogAverageError (((count + 2 : ℕ) : ℝ)) +
          Real.log (((count + 2 : ℕ) : ℝ)) + 4 +
          4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
            suzukiChebyshevRelativeEntropy
              (suzukiChebyshevCorrectedMassRatio
                (suzukiFirstTailChebyshevCenter count)
                (((count + 2 : ℕ) : ℝ))) ≤
        suzukiChebyshevLegendreLowerOrder
          (suzukiFirstTailChebyshevCenter count)
          (suzukiChebyshevCorrectedMassRatio
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ))) := by
  rw [suzukiFirstTailResetTransportGap_succ_nonnegative_iff_entropy_le,
    suzukiChebyshevEndpointCenteredError_eq_neg_logAverage_sub_log_sub_four]
  constructor <;> intro h <;> linarith

/-- The sufficient quadratic premise is equivalently one explicit upper
bound for the logarithmic average plus the corrected mass-error cost. -/
theorem
    suzukiChebyshevQuadraticMassCost_le_endpointError_add_lowerOrder_iff_logAverage_bound
    (count : ℕ) :
    (suzukiChebyshevQuadraticMassCost
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) ≤
        suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)))) ↔
      suzukiChebyshevLogAverageError (((count + 2 : ℕ) : ℝ)) +
          Real.log (((count + 2 : ℕ) : ℝ)) + 4 +
          suzukiChebyshevQuadraticMassCost
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ)) ≤
        suzukiChebyshevLegendreLowerOrder
          (suzukiFirstTailChebyshevCenter count)
          (suzukiChebyshevCorrectedMassRatio
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ))) := by
  rw [suzukiChebyshevEndpointCenteredError_eq_neg_logAverage_sub_log_sub_four]
  constructor <;> intro h <;> linarith

end

end RiemannGaussian
