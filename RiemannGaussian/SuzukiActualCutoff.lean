/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiSignedLegendreRemainder
import RiemannGaussian.SuzukiLogarithmicWork

/-!
# The actual-cutoff arithmetic target without a canonical entropy burden

The finite mass potential equals the negative actual logarithmic-average
error plus its affine logarithmic correction, minus a nonnegative entropy
term. That entropy belongs to minimization at the canonical center.

The original signed Laplace signal can instead be bounded directly at its
actual integer cutoffs. Within every integer cell, the full signed change
is retained exactly, and its upper error is at most `12 / sqrt(floor x)`.
Thus an eventual logarithmic upper bound on one literal finite prime sum
suffices for the same RH conclusion, without a bound on the entropy term.

The finite-prime upper bound remains open. This module proves the comparison
and the rounding allowance; it does not assume the arithmetic estimate as
an axiom or assert an unconditional RH theorem.
-/

open Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The corrected prime mass relative to the actual endpoint's square-root
mass, with no implicit minimization center. -/
def suzukiActualEndpointMassRatio (count : ℕ) : ℝ :=
  (suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant) /
    (2 * Real.sqrt ((count + 2 : ℕ) : ℝ))

/-- The logarithm in the actual-endpoint mass ratio has a positive argument. -/
theorem suzukiActualEndpointMassRatio_pos (count : ℕ) :
    0 < suzukiActualEndpointMassRatio count := by
  unfold suzukiActualEndpointMassRatio
  apply div_pos
  · linarith [suzukiOldPrimeMass_pos count, suzukiArchimedeanSlopeConstant_neg]
  · positivity

/-- Exact comparison of the canonical mass potential and the original
actual-cutoff statistic. The extra nonlinear term is a nonnegative entropy
penalty, not part of the direct logarithmic-average target. -/
theorem suzukiMassLegendrePotential_eq_actualEndpoint_sub_entropy (count : ℕ) :
    suzukiMassLegendrePotential count =
      -suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanSlopeConstant * Real.log ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanIntercept -
        4 * Real.sqrt ((count + 2 : ℕ) : ℝ) *
          suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio count) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let m := suzukiOldPrimeMass count - suzukiArchimedeanSlopeConstant
  let q := suzukiActualEndpointMassRatio count
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hq : 0 < q := suzukiActualEndpointMassRatio_pos count
  have hprod : q * Real.sqrt b = m / 2 := by
    dsimp [q, m, b, suzukiActualEndpointMassRatio]
    field_simp
  have hlog : Real.log (m / 2) = Real.log q + Real.log b / 2 := by
    rw [← hprod, Real.log_mul hq.ne' hs.ne', Real.log_sqrt hb.le]
  have hM : suzukiChebyshevWeightedMass b = suzukiOldPrimeMass count := by
    simpa [b, Nat.add_assoc] using
      (screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass (count + 1)).symm
  have hP : suzukiChebyshevWeightedLogMoment b =
      screwPrefixMoment suzukiPrimeLocation suzukiPrimeWeight (count + 1) := by
    simpa [b, Nat.add_assoc] using
      (screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment (count + 1)).symm
  change suzukiMassLegendrePotential count = -suzukiChebyshevLogAverageError b +
    suzukiArchimedeanSlopeConstant * Real.log b + suzukiArchimedeanIntercept -
      4 * Real.sqrt b * suzukiChebyshevRelativeEntropy q
  unfold suzukiMassLegendrePotential suzukiChebyshevLogAverageError
    suzukiChebyshevRelativeEntropy
  rw [hM, hP, ← Real.sqrt_eq_rpow]
  change _ - 2 * m * (Real.log (m / 2) - 1) + _ = _
  rw [hlog]
  have hmass : suzukiOldPrimeMass count = m + suzukiArchimedeanSlopeConstant := by
    dsimp [m]
    ring
  rw [hmass]
  nlinarith only [hprod, congrArg (fun u : ℝ ↦ 4 * u * Real.log q) hprod]

/-- Controlling the mass potential from below additionally pays a
nonnegative entropy term. The direct actual-endpoint statistic does not
require that stronger lower estimate. -/
theorem suzukiMassLegendrePotential_le_actualEndpoint (count : ℕ) :
    suzukiMassLegendrePotential count ≤
      -suzukiChebyshevLogAverageError ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanSlopeConstant * Real.log ((count + 2 : ℕ) : ℝ) +
        suzukiArchimedeanIntercept := by
  rw [suzukiMassLegendrePotential_eq_actualEndpoint_sub_entropy]
  have h := suzukiChebyshevRelativeEntropy_nonnegative
    (suzukiActualEndpointMassRatio_pos count).le
  have hp : 0 ≤ 4 * Real.sqrt ((count + 2 : ℕ) : ℝ) *
      suzukiChebyshevRelativeEntropy (suzukiActualEndpointMassRatio count) := by positivity
  linarith

private theorem weightedMass_nat_eq_sum {N : ℕ} (hN : 1 ≤ N) :
    suzukiChebyshevWeightedMass (N : ℝ) =
      ∑ n ∈ Finset.Ioc 1 N, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  have h := suzukiChebyshevMassAbel_eq (by exact_mod_cast hN : (1 : ℝ) ≤ N)
  change _ = suzukiChebyshevWeightedMass (N : ℝ) at h
  simpa [Nat.floor_natCast, suzukiChebyshevMassKernel_nat_eq, div_eq_mul_inv, mul_comm] using h.symm

/-- Exact signed motion inside an integer cutoff cell. The common prime
prefix, its logarithmic increment, and the square-root main term are kept
together before the rounding allowance is estimated. -/
theorem suzukiChebyshevLogAverageError_cell_eq {x : ℝ} (hx : 1 ≤ x) :
    suzukiChebyshevLogAverageError x =
      suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ) +
        Real.log (x / (⌊x⌋₊ : ℝ)) * suzukiChebyshevWeightedMass (⌊x⌋₊ : ℝ) -
        4 * (Real.sqrt x - Real.sqrt (⌊x⌋₊ : ℝ)) := by
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (zero_le_one.trans hx)).mpr (by exact_mod_cast hx)
  have hNr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hNp : (0 : ℝ) < ⌊x⌋₊ := zero_lt_one.trans_le hNr
  rw [suzukiChebyshevLogAverageError_eq_sum_log_sub_log_of_one_le hx,
    suzukiChebyshevLogAverageError_eq_sum_log_sub_log_of_one_le hNr,
    Nat.floor_natCast, weightedMass_nat_eq_sum hN,
    Real.log_div hxp.ne' hNp.ne', ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Finset.mul_sum]
  have he : (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (Real.log x - Real.log n)) =
      ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (Real.log (⌊x⌋₊ : ℝ) - Real.log n) +
        (Real.log x - Real.log (⌊x⌋₊ : ℝ)) *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n)) := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he, Finset.sum_add_distrib]
  ring

/-- Rounding to the actual integer cutoff costs at most a vanishing
`12 / sqrt(floor x)` in the required upper direction. No canonical-center
or entropy bound is needed. -/
theorem suzukiChebyshevLogAverageError_le_floor_add_inv_sqrt {x : ℝ} (hx : 1 ≤ x) :
    suzukiChebyshevLogAverageError x ≤
      suzukiChebyshevLogAverageError (⌊x⌋₊ : ℝ) + 12 / Real.sqrt (⌊x⌋₊ : ℝ) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have hNr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hNp : (0 : ℝ) < ⌊x⌋₊ := zero_lt_one.trans_le hNr
  have hNx := Nat.floor_le hx0
  have hxN := Nat.lt_floor_add_one x
  have hq : 0 < x / (⌊x⌋₊ : ℝ) := div_pos (zero_lt_one.trans_le hx) hNp
  have hlog0 : 0 ≤ Real.log (x / (⌊x⌋₊ : ℝ)) :=
    Real.log_nonneg ((one_le_div hNp).mpr hNx)
  have hlog : Real.log (x / (⌊x⌋₊ : ℝ)) ≤ 1 / (⌊x⌋₊ : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hq
    have hb : x / (⌊x⌋₊ : ℝ) - 1 ≤ 1 / (⌊x⌋₊ : ℝ) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hNp).mpr
      have he : (1 / (⌊x⌋₊ : ℝ) + 1) * (⌊x⌋₊ : ℝ) = 1 + (⌊x⌋₊ : ℝ) := by
        field_simp
      rw [he]
      linarith
    exact h.trans hb
  have hmass := suzukiChebyshevWeightedMass_le_twelve_sqrt hNr
  have hcost := (mul_le_mul_of_nonneg_left hmass hlog0).trans
    (mul_le_mul_of_nonneg_right hlog (by positivity : (0 : ℝ) ≤ 12 * Real.sqrt (⌊x⌋₊ : ℝ)))
  have he : (1 / (⌊x⌋₊ : ℝ)) * (12 * Real.sqrt (⌊x⌋₊ : ℝ)) =
      12 / Real.sqrt (⌊x⌋₊ : ℝ) := by
    have hs : 0 < Real.sqrt (⌊x⌋₊ : ℝ) := Real.sqrt_pos.mpr hNp
    field_simp
    nlinarith only [Real.sq_sqrt hNp.le]
  rw [he] at hcost
  have hroot := Real.sqrt_le_sqrt hNx
  rw [suzukiChebyshevLogAverageError_cell_eq hx]
  linarith

/-- A logarithmic upper bound at the integer endpoints controls all real
cutoffs, with an explicit fixed allowance for interpolation. -/
theorem suzukiLogAverage_real_upper_of_nat_upper {C D : ℝ} (hD : 0 ≤ D)
    (h : ∀ N : ℕ, 1 ≤ N → suzukiChebyshevLogAverageError (N : ℝ) ≤ C + D * Real.log N)
    {x : ℝ} (hx : 1 ≤ x) :
    suzukiChebyshevLogAverageError x ≤ C + 12 + D * Real.log x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have hNr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hroot : (1 : ℝ) ≤ Real.sqrt (⌊x⌋₊ : ℝ) := by
    simpa using Real.sqrt_le_sqrt hNr
  have hdiv : 12 / Real.sqrt (⌊x⌋₊ : ℝ) ≤ (12 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (⌊x⌋₊ : ℝ))).mpr
    linarith
  have hlog := Real.log_le_log (zero_lt_one.trans_le hNr) (Nat.floor_le hx0)
  have hmul := mul_le_mul_of_nonneg_left hlog hD
  have hfloor := h ⌊x⌋₊ hN
  have hcell := suzukiChebyshevLogAverageError_le_floor_add_inv_sqrt hx
  linarith

/-- A direct logarithmic upper bound for the actual integer-cutoff error
already implies RH. There is no additional canonical entropy premise. -/
theorem riemannHypothesis_of_suzuki_logAverage_nat_upper {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ N : ℕ, 1 ≤ N → suzukiChebyshevLogAverageError (N : ℝ) ≤ C + D * Real.log N) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_affine_lower_bound
    (C := C + 12) (by linarith) hD
  intro t ht
  have he := suzukiLogAverage_real_upper_of_nat_upper hD h
    (Real.one_le_exp_iff.mpr ht.le)
  rw [Real.log_exp] at he
  unfold suzukiChebyshevLogAverageLaplaceSignal
  linarith

/-- The direct RH target as a literal finite von-Mangoldt sum at every
integer cutoff. This implication does not prove the displayed upper bound. -/
theorem riemannHypothesis_of_suzuki_finite_logAverage_upper {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : ∀ N : ℕ,
      (∑ n ∈ Finset.Ioc 1 (N + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        Real.log ((((N + 1 : ℕ) : ℝ) / n))) ≤
        4 * Real.sqrt ((N + 1 : ℕ) : ℝ) + C + D * Real.log ((N + 1 : ℕ) : ℝ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_logAverage_nat_upper hC hD
  intro N hN
  cases N with
  | zero => omega
  | succ N =>
    rw [suzukiChebyshevLogAverageError_nat_eq_sum_log_div,
      ← Real.sqrt_eq_rpow]
    linarith [h N]

/-- Finitely many initial cutoffs are absorbed into one explicit finite
allowance. Only an eventual logarithmic upper bound is needed. -/
theorem riemannHypothesis_of_suzuki_logAverage_eventually_nat_upper {C D : ℝ}
    (hD : 0 ≤ D)
    (h : ∀ᶠ N : ℕ in atTop,
      suzukiChebyshevLogAverageError (N : ℝ) ≤ C + D * Real.log N) :
    RiemannHypothesis := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  let B := |C| + ∑ n ∈ Finset.range K, |suzukiChebyshevLogAverageError (n : ℝ)|
  have hsum : 0 ≤ ∑ n ∈ Finset.range K, |suzukiChebyshevLogAverageError (n : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCB : C ≤ B := by dsimp [B]; linarith [le_abs_self C]
  apply riemannHypothesis_of_suzuki_logAverage_nat_upper hB hD
  intro N hN
  by_cases hNK : K ≤ N
  · exact (hK N hNK).trans (by linarith)
  · have hm : N ∈ Finset.range K := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum
      (f := fun n : ℕ ↦ |suzukiChebyshevLogAverageError (n : ℝ)|)
      (fun _ _ ↦ abs_nonneg _) hm
    have hlog : 0 ≤ D * Real.log (N : ℝ) :=
      mul_nonneg hD (Real.log_nonneg (by exact_mod_cast hN))
    have habs := le_abs_self (suzukiChebyshevLogAverageError (N : ℝ))
    dsimp [B]
    linarith [abs_nonneg C]

/-- The direct open arithmetic obligation needs only hold eventually:
one upper bound on the complete finite logarithmic prime average, with all
prime powers and the original cutoff preserved, suffices for RH. -/
theorem riemannHypothesis_of_suzuki_finite_logAverage_eventually_upper {C D : ℝ}
    (hD : 0 ≤ D)
    (h : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.Ioc 1 N, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        Real.log ((N : ℝ) / n)) ≤
        4 * Real.sqrt (N : ℝ) + C + D * Real.log (N : ℝ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_logAverage_eventually_nat_upper hD
  filter_upwards [h, eventually_ge_atTop 1] with N hsum hN
  rw [suzukiChebyshevLogAverageError_eq_sum_log_div_of_one_le
    (by exact_mod_cast hN : (1 : ℝ) ≤ N), Nat.floor_natCast, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ (4 * Real.sqrt (N : ℝ) + C + D * Real.log (N : ℝ)) -
        4 * Real.sqrt (N : ℝ) := sub_le_sub_right hsum _
    _ = _ := by ring

end

end RiemannGaussian
