/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeHeatRecurrence

/-!
# Controlling the upper neighbour at the same quadratic heat width

The complete residual decay extends to every fixed offset in moment order
while keeping the original width schedule. The exact pole average is at
most one, so the full neighbouring heat is eventually bounded by the actual
multiplicity plus one. This pays for the closed recurrence's upper neighbour
with an explicit inverse-order allowance. No independent lower bound for
the surviving signed prime expression is assumed or obtained.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Topology
open GaussianSimplePoleHeat GaussianCentralTailBound

/-- Residual decay holds at every fixed offset in moment order while
keeping the unshifted quadratic width. This supplies the shared-width
estimate needed by the exact adjacent-order recurrence. -/
theorem tendsto_clearedPrimeRemainderHeat_sharedWidth {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) (j : ℕ) :
    Tendsto (fun N ↦ normalizedClearedPrimeRemainderHeat D S rho (N + j)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, A, hA, hbound⟩ := exists_normalizedClearedPrimeRemainderHeat_bound hD S hS rho hrho
  have hu := clearedPrimeSourceDistance_pos rho
  have hg := clearedPrimeCentralGeometry rho hrho
  have hr : 0 < clearedPrimeCentralRadius rho := hu.trans hg.2.1
  have hratio : clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho < 1 :=
    (div_lt_one hr).mpr hg.2.1
  have hcentral := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity :
    0 ≤ clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) hratio).const_mul
      (C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ j)
  have houter := (tendsto_pow_mul_tailAllowance_quadraticWidth hg.1 hc hu
    (by positivity : 0 < 4 * clearedPrimeSourceDistance rho)
    (normalizedPrimeTailClearingPolynomial D S rho).natDegree).const_mul
      (A * (4 * clearedPrimeSourceDistance rho) ^ j)
  have hlim : Tendsto (fun N ↦ C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ (N + j) +
      A * (4 * clearedPrimeSourceDistance rho) ^ (N + j) *
        tailAllowance (clearedPrimeCentralWindow rho)
          (normalizedPrimeTailClearingPolynomial D S rho).natDegree
          (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
    simpa only [pow_add, mul_zero, zero_mul, add_zero, mul_assoc, mul_comm, mul_left_comm] using hcentral.add houter
  apply squeeze_zero_norm' _ hlim
  filter_upwards [(tendsto_quadraticWidth c (clearedPrimeSourceDistance rho)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
  exact hbound (N + j) _ (quadraticWidth_pos hc hu N) hN.le

/-- At any positive width, the complete prime heat norm is at most the
actual multiplicity plus its full residual norm. The unit pole bound is
proved from the exact positive gamma average. -/
theorem norm_normalizedClearedPrimeHeat_le_multiplicity_add_residual {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (N : ℕ)
    {B : ℝ} (hB : 0 < B) :
    ‖normalizedClearedPrimeHeat D S rho N B‖ ≤ (analyticZetaZeroMultiplicity rho : ℝ) +
      ‖normalizedClearedPrimeRemainderHeat D S rho N B‖ := by
  have hu := clearedPrimeSourceDistance_pos rho
  rw [normalizedClearedPrimeHeat_eq_source_add_remainder hD S hS rho N hB]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real,
    Real.norm_of_nonneg (attenuation_nonneg N hu.le)]
  have ha := attenuation_le_one N hu hB.le
  have hm : 0 ≤ (analyticZetaZeroMultiplicity rho : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The complete prime heat at any fixed neighbouring order has the
same eventual multiplicity-plus-one bound on the unshifted width schedule. -/
theorem eventually_norm_clearedPrimeHeat_sharedWidth_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∀ᶠ N in atTop, ‖normalizedClearedPrimeHeat D S rho (N + j)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)‖ ≤ (analyticZetaZeroMultiplicity rho : ℝ) + 1 := by
  have hlim := (tendsto_clearedPrimeRemainderHeat_sharedWidth hD S hS rho hrho hc j).norm
  have hsmall : ∀ᶠ N in atTop, ‖normalizedClearedPrimeRemainderHeat D S rho (N + j)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)‖ < 1 := by
    exact hlim.eventually (gt_mem_nhds (by simp only [norm_zero]; norm_num))
  filter_upwards [hsmall] with N hN
  exact (norm_normalizedClearedPrimeHeat_le_multiplicity_add_residual hD S hS rho (N + j)
    (quadraticWidth_pos hc (clearedPrimeSourceDistance_pos rho) N)).trans (by linarith)

/-- The upper neighbour in the exact normalized recurrence has an
explicit inverse-order allowance, for the actual prime heat at the same
width as the lower orders. Its full source and residual have both been paid. -/
theorem eventually_norm_clearedPrimeHeat_upper_coupling_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      ‖(2 * (c : ℂ) / ((N : ℂ) + 1)) * normalizedClearedPrimeHeat D S rho (N + 2)
        (quadraticWidth c (clearedPrimeSourceDistance rho) N)‖ ≤
      (2 * c * ((analyticZetaZeroMultiplicity rho : ℝ) + 1)) / ((N : ℝ) + 1) := by
  filter_upwards [eventually_norm_clearedPrimeHeat_sharedWidth_le hD S hS rho hrho hc 2] with N hN
  have he : 2 * (c : ℂ) / ((N : ℂ) + 1) = ((2 * c / ((N : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
  have hp : 0 ≤ 2 * c / ((N : ℝ) + 1) := by positivity
  rw [norm_mul, he, Complex.norm_real, Real.norm_of_nonneg hp]
  apply (mul_le_mul_of_nonneg_left hN hp).trans_eq
  ring

/-- The complete upper-order contribution in the shared-width
recurrence tends to zero. This is stronger than decay of its coefficient
alone and does not identify neighbouring width schedules. -/
theorem tendsto_clearedPrimeHeat_upper_coupling {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦ (2 * (c : ℂ) / ((N : ℂ) + 1)) * normalizedClearedPrimeHeat D S rho (N + 2)
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_clearedPrimeHeat_upper_coupling_le hD S hS rho hrho hc)
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
    (2 * c * ((analyticZetaZeroMultiplicity rho : ℝ) + 1))
  simpa only [mul_zero, mul_one_div] using h

/-- Under the hypothetical right-half zero, the complete extra-factor
heat equals the signed adjacent-order difference up to a proved vanishing
upper-neighbour allowance. The two surviving orders still use the same
original width; this supplies no independent arithmetic lower bound. -/
theorem tendsto_clearedPrimeHeat_extraFactor_sub_difference {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N ↦
      (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        clearedHeatPrimeResponse (quadraticWidth c (clearedPrimeSourceDistance rho) N)
          ((Polynomial.X - Polynomial.C rho.1) * normalizedPrimeTailClearingPolynomial D S rho)
          D S (N + 1) (zetaWronskianMomentCenter rho) -
      (normalizedClearedPrimeHeat D S rho (N + 1) (quadraticWidth c (clearedPrimeSourceDistance rho) N) -
        normalizedClearedPrimeHeat D S rho N (quadraticWidth c (clearedPrimeSourceDistance rho) N)))
      atTop (𝓝 0) := by
  have he (N : ℕ) := normalizedClearedPrimeHeat_three_order_quadraticWidth hc hD S hS rho N
  dsimp only at he
  simp_rw [he, add_sub_cancel_left]
  exact tendsto_clearedPrimeHeat_upper_coupling hD S hS rho hrho hc

end
end RiemannGaussian.SquarefreeEulerQuadratic
