import RiemannGaussian.EtaMomentMoebiusTransform
import RiemannGaussian.EtaCurrentEulerMoments

/-!
# Exact transport of the literal moment center to its divisor endpoint

The actual discarded eta support gives a finite binomial center transport,
with all integrability obligations discharged. Below the analytic zero
multiplicity this identity applies to the original finite prefix. The
unpaired extension retains its odd last endpoint and full complex power.
-/

open Complex MeasureTheory
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Changing the center of the literal eta tail keeps every lower
moment, with the exact binomial coefficient and complex center power. -/
theorem pairedEtaCenteredTail_shift_center (k : ℕ) {s : ℂ} (hs : 0 < s.re)
    (a : ℝ) (N : ℕ) :
    (∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
      ∂pairedEtaLogTailMeasure N) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
        ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j) *
          pairedEtaLogLaplaceMomentCutoffCenteredTail j s N := by
  symm
  calc
    _ = ∑ j ∈ Finset.range (k + 1), ∫ t : ℝ,
        ((k.choose j : ℂ) * ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j)) *
          ((((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ j) * Complex.exp (-s * t))
            ∂pairedEtaLogTailMeasure N := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      rfl
    _ = ∫ t : ℝ, ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j)) *
          ((((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ j) * Complex.exp (-s * t))
            ∂pairedEtaLogTailMeasure N := by
      rw [integral_finsetSum]
      intro j hj
      exact (integrable_pairedEtaLogLaplaceMomentCutoffCenteredTail_integrand j hs N).const_mul _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      have hp : (((t - a : ℝ) : ℂ) ^ k) =
          ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
            ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j) *
              ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ j := by
        rw [show ((t - a : ℝ) : ℂ) =
          ((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) +
            ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) by push_cast; ring, add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hp, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- At every real center, the finite prefix below the actual zero
multiplicity is the negative of its literal support tail. -/
theorem pairedEtaCenteredPartialSum_eq_neg_tail (rho : NontrivialZetaZero)
    {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho) (a : ℝ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCenteredPartialSum k rho.1 a N =
      -(∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-rho.1 * t)
        ∂pairedEtaLogTailMeasure N) := by
  have h := pairedEtaLogLaplaceMomentCenteredFullSum_eq_partial_add_tail k
    (NontrivialZetaZero.zero_lt_re rho) a N
  rw [pairedEtaLogLaplaceMomentCenteredFullSum_eq_zero_of_lt_multiplicity rho hk a] at h
  linear_combination -h

/-- Endpoint normalization of the original prefix retains every
shifted-tail moment at its actual center displacement. -/
theorem pairedEtaCenteredPartialSum_endpoint_eq_shifted (rho : NontrivialZetaZero)
    {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho) (a : ℝ) (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℂ) ^ rho.1 * pairedEtaLogLaplaceMomentCenteredPartialSum k rho.1 a N =
      -(∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
        ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j) *
          pairedEtaShiftedLogTailLaplaceMoment j rho.1 N) := by
  rw [pairedEtaCenteredPartialSum_eq_neg_tail rho hk a N, mul_neg,
    pairedEtaCenteredTail_shift_center k (NontrivialZetaZero.zero_lt_re rho) a N]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hp : ((2 * N + 1 : ℕ) : ℂ) ^ rho.1 *
      pairedEtaLogLaplaceMomentCutoffCenteredTail j rho.1 N =
        pairedEtaShiftedLogTailLaplaceMoment j rho.1 N := by
    simpa only [Complex.ofReal_natCast] using
      pairedEtaOddEndpoint_cpow_mul_cutoffCenteredTail_eq_shiftedMoment j rho.1 N
  linear_combination ((k.choose j : ℂ) *
    ((pairedEtaLogTailCutoff N - a : ℝ) : ℂ) ^ (k - j)) * hp

/-- The unpaired original moment keeps its odd last endpoint alongside
the complete shifted-tail expansion, at every integer divisor cutoff. -/
theorem pairedEtaUnpairedCenteredMomentPrefix_endpoint_eq_shifted
    (rho : NontrivialZetaZero) {k : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (a : ℝ) (M : ℕ) :
    (pairedEtaUnpairedOddEndpoint M : ℂ) ^ rho.1 *
      pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M =
        -(∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) *
          ((Real.log (pairedEtaUnpairedOddEndpoint M : ℝ) - a : ℝ) : ℂ) ^ (k - j) *
            pairedEtaShiftedLogTailLaplaceMoment j rho.1 (M / 2)) +
        if Odd M then pairedEtaCenteredMomentEndpointPolynomial k rho.1 a
          (Real.log (pairedEtaUnpairedOddEndpoint M : ℝ)) else 0 := by
  rw [pairedEtaUnpairedCenteredMomentPrefix_eq_paired_add_endpoint k
    (NontrivialZetaZero.coe_ne_zero rho), mul_add]
  have hp := pairedEtaCenteredPartialSum_endpoint_eq_shifted rho hk a (M / 2)
  change (pairedEtaUnpairedOddEndpoint M : ℂ) ^ rho.1 *
      pairedEtaLogLaplaceMomentCenteredPartialSum k rho.1 a (M / 2) = _ at hp
  rw [hp]
  congr 1
  by_cases ho : Odd M
  · rw [if_pos ho, if_pos ho]
    have hQ : pairedEtaUnpairedOddEndpoint M = M := by
      have hm := Nat.odd_iff.mp ho
      unfold pairedEtaUnpairedOddEndpoint
      omega
    have hM : (M : ℂ) ≠ 0 := by
      have hm : 0 < M := ho.pos
      exact_mod_cast hm.ne'
    rw [hQ, ← mul_assoc, ← Complex.cpow_add _ _ hM, add_neg_cancel, Complex.cpow_zero, one_mul]
  · rw [if_neg ho, if_neg ho, mul_zero]

end

end RiemannGaussian
