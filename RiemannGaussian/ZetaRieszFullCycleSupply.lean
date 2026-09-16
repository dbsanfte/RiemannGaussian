/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTargetProfile
import RiemannGaussian.ZetaRieszCycleCapacity
import RiemannGaussian.ZetaRieszRefinedMatching

/-!
# All nonunit squarefree cofactors and every complex polynomial filter

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszFullCycleSupply
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszTargetProfile
open ZetaRieszRetainedFraction
open ZetaRieszCycleCapacity

/-- The exact-target arithmetic supply bound extends to every full
complex polynomial filter, retaining its actual norm and support mask. -/
theorem norm_full_prime_partner_ge_target (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {q n : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    ‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (q * n)‖ *
      max 0 (|targetProfile L n x| - targetProfileError x q n) ≤
        ‖bandWeight L P N t (q * n)‖ := by
  rw [ZetaArithmeticBandCorrelation.bandWeight_eq_amplitude_mul_riesz,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_prime_profile_ge_target L x hq hqn hn hcard) (norm_nonneg _)

/-- Full-polynomial exact cycles use the two flanking primes' actual
shared cofactor supply, while the central original atom is unrestricted.
The complete complex orientation is checked explicitly, and every prior
spent fraction remains separate. This also permits cross-prime-count
cancellations without completing or changing the original carrier. -/
theorem full_cycle_after_previous_ge_target_margin (L x : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (es : List (ℕ × ℕ × ℕ)) (i : ℕ) {q r n : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hcycle : ZetaRieszCycleCore.positiveCycle (bandWeight L P N t i)
      (bandWeight L P N t (q * n)) (bandWeight L P N t (r * n))) :
    let f := bandWeight L P N t
    let zp := ZetaRieszMassTransport.ray (f i)
    let zq := ZetaRieszMassTransport.ray (f (q * n))
    let zr := ZetaRieszMassTransport.ray (f (r * n))
    let supply := fun v => ‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (v * n)‖ *
      max 0 (|targetProfile L n x| - targetProfileError x v n)
    rayCapacity zp zq zr (retainedFraction f es i * ‖f i‖)
      (retainedFraction f es (q * n) * supply q)
      (retainedFraction f es (r * n) * supply r) *
      (ZetaRieszCycleCore.area zq zr + ZetaRieszCycleCore.area zr zp + ZetaRieszCycleCore.area zp zq) ≤
        ZetaRieszCycleCore.cycleSaving (ZetaRieszCycleIteration.cycleResidual f es i)
          (ZetaRieszCycleIteration.cycleResidual f es (q * n))
          (ZetaRieszCycleIteration.cycleResidual f es (r * n)) := by
  exact cycleSaving_retained_rayCapacity (bandWeight L P N t) es i (q * n) (r * n) hcycle
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_max_left _ _))
    (mul_nonneg (norm_nonneg _) (le_max_left _ _)) (le_refl _)
    (norm_full_prime_partner_ge_target L x P N t hq hqn hn hcard)
    (norm_full_prime_partner_ge_target L x P N t hr hrn hn hcard)


/-- Prime cofactors use their sharp half-divisor slope; composite
squarefree cofactors retain the stronger quarter-divisor slope. -/
def cofactorTargetError (x : ℝ) (q n : ℕ) : ℝ :=
  if n.Prime then |Real.log q - x| / 2 *
    ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|
  else targetProfileError x q n

/-- Every nonunit squarefree shared cofactor has an independently proved
exact-target error, including the previously omitted prime cofactors. -/
theorem abs_prime_profile_sub_cofactor_target_le (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hn1 : n ≠ 1) :
    |VaughanLogAverage.riesz L (q * n) - targetProfile L n x| ≤ cofactorTargetError x q n := by
  unfold cofactorTargetError
  split_ifs with hnp
  · rw [riesz_prime_eq_target L hq hqn]
    unfold targetProfile
    rw [sub_sub_sub_cancel_left]
    have he := ZetaRieszCenteredCofactor.riesz_cutoff_lipschitz_centered (L - x) (L - Real.log q) hn1
    simpa only [sub_sub_sub_cancel_left] using he
  · exact abs_prime_profile_sub_target_le L x hq hqn hn
      (ZetaRieszRefinedMatching.two_le_prime_count hn hn1 hnp)

/-- The exact-target absolute supply bound covers prime and composite
shared cofactors without any prime-count restriction on the central atom. -/
theorem abs_prime_profile_ge_cofactor_target (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hn1 : n ≠ 1) :
    max 0 (|targetProfile L n x| - cofactorTargetError x q n) ≤
      |VaughanLogAverage.riesz L (q * n)| := by
  have he := abs_prime_profile_sub_cofactor_target_le L x hq hqn hn hn1
  have ht := abs_add_le (VaughanLogAverage.riesz L (q * n) - targetProfile L n x)
    (-VaughanLogAverage.riesz L (q * n))
  have heq : VaughanLogAverage.riesz L (q * n) - targetProfile L n x +
      -VaughanLogAverage.riesz L (q * n) = -targetProfile L n x := by ring
  rw [heq, abs_neg, abs_neg] at ht
  exact max_le (abs_nonneg _) (by linarith)

/-- Every actual full-polynomial prime partner receives its independently
proved supply floor, whether the shared cofactor is prime or composite. -/
theorem norm_full_prime_partner_ge_cofactor_target (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {q n : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hn1 : n ≠ 1) :
    ‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (q * n)‖ *
      max 0 (|targetProfile L n x| - cofactorTargetError x q n) ≤
        ‖bandWeight L P N t (q * n)‖ := by
  rw [ZetaArithmeticBandCorrelation.bandWeight_eq_amplitude_mul_riesz,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_prime_profile_ge_cofactor_target L x hq hqn hn hn1) (norm_nonneg _)

/-- The exact full-polynomial cycle bound now includes all nonunit
squarefree partner cofactors, retaining separate arithmetic errors and
spent capacities while leaving the central atom unrestricted. -/
theorem full_cycle_after_previous_ge_cofactor_target (L x : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (es : List (ℕ × ℕ × ℕ)) (i : ℕ) {q r n : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (hcycle : ZetaRieszCycleCore.positiveCycle (bandWeight L P N t i)
      (bandWeight L P N t (q * n)) (bandWeight L P N t (r * n))) :
    let f := bandWeight L P N t
    let zp := ZetaRieszMassTransport.ray (f i)
    let zq := ZetaRieszMassTransport.ray (f (q * n))
    let zr := ZetaRieszMassTransport.ray (f (r * n))
    let supply := fun v => ‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (v * n)‖ *
      max 0 (|targetProfile L n x| - cofactorTargetError x v n)
    rayCapacity zp zq zr (retainedFraction f es i * ‖f i‖)
      (retainedFraction f es (q * n) * supply q)
      (retainedFraction f es (r * n) * supply r) *
      (ZetaRieszCycleCore.area zq zr + ZetaRieszCycleCore.area zr zp + ZetaRieszCycleCore.area zp zq) ≤
        ZetaRieszCycleCore.cycleSaving (ZetaRieszCycleIteration.cycleResidual f es i)
          (ZetaRieszCycleIteration.cycleResidual f es (q * n))
          (ZetaRieszCycleIteration.cycleResidual f es (r * n)) := by
  exact cycleSaving_retained_rayCapacity (bandWeight L P N t) es i (q * n) (r * n) hcycle
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_max_left _ _))
    (mul_nonneg (norm_nonneg _) (le_max_left _ _)) (le_refl _)
    (norm_full_prime_partner_ge_cofactor_target L x P N t hq hqn hn hn1)
    (norm_full_prime_partner_ge_cofactor_target L x P N t hr hrn hn hn1)


end
end RiemannGaussian.ZetaRieszFullCycleSupply
