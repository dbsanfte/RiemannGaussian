/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeClearedHeatGrowth
import RiemannGaussian.GaussianCentralTailBound

/-!
# Decay of the complete cleared residual at quadratic heat widths

The actual residual has geometric decay on a fixed central neighborhood
and a global polynomial Euler-line envelope with exponential order growth.
Gaussian localization combines these proved estimates, so its whole
mass-normalized heat tends to zero on the explicit quadratic schedule.
The full corrected prime heat consequently retains a nonzero negative
source. The independent signed arithmetic lower bound remains open.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter MeasureTheory Topology
open GaussianPolynomialTransport GaussianSimplePoleHeat GaussianCentralTailBound

/-- The original source-normalized residual heat is exactly the complete
Gaussian average of the original normalized residual moments. -/
theorem normalizedClearedPrimeRemainderHeat_eq_average (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) (N : ℕ) (B : ℝ) :
    normalizedClearedPrimeRemainderHeat D S rho N B = GaussianCentralTailBound.average B
      (fun y : ℝ ↦ (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)) := by
  unfold normalizedClearedPrimeRemainderHeat GaussianCentralTailBound.average
  have he (y : ℝ) : (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      ((clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)) =
      (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        ((Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
          signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- Every complete residual Gaussian average satisfies the sum of its
proved central geometric error and its proved global outer-tail error.
The constants and polynomial degree are common to all orders and widths. -/
theorem exists_normalizedClearedPrimeRemainderHeat_bound {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (B : ℝ), 0 < B → B ≤ 1 →
      ‖normalizedClearedPrimeRemainderHeat D S rho N B‖ ≤
        C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ N +
        A * (4 * clearedPrimeSourceDistance rho) ^ N *
          tailAllowance (clearedPrimeCentralWindow rho)
            (normalizedPrimeTailClearingPolynomial D S rho).natDegree B := by
  obtain ⟨C, hC, hcentral⟩ := exists_clearedPrimeRemainder_central_bound D S rho hrho
  obtain ⟨A, hA, hglobal⟩ := exists_clearedPrimeRemainder_global_bound hD S hS rho
  have hu := clearedPrimeSourceDistance_pos rho
  have hg := clearedPrimeCentralGeometry rho hrho
  have hr : 0 < clearedPrimeCentralRadius rho := hu.trans hg.2.1
  refine ⟨C, hC, A, hA, fun N B hB hB1 ↦ ?_⟩
  rw [normalizedClearedPrimeRemainderHeat_eq_average]
  apply norm_average_le _ hB hB1 hg.1.le (by positivity) (by positivity) _ (hcentral N) (hglobal N)
  convert! (integrable_clearedPrimeRemainder_heat hD S hS rho N hB).const_mul
    ((clearedPrimeSourceDistance rho : ℂ) ^ (N + 1)) using 1
  ext y
  ring

/-- The entire actual residual heat tends to zero as the factorial
order grows on any fixed positive quadratic relative-width schedule.
Both the central and outer frequency ranges are discharged. -/
theorem tendsto_normalizedClearedPrimeRemainderHeat_quadraticWidth {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N ↦ normalizedClearedPrimeRemainderHeat D S rho N
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, A, hA, hbound⟩ := exists_normalizedClearedPrimeRemainderHeat_bound hD S hS rho hrho
  have hu := clearedPrimeSourceDistance_pos rho
  have hg := clearedPrimeCentralGeometry rho hrho
  have hr : 0 < clearedPrimeCentralRadius rho := hu.trans hg.2.1
  have hratio : clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho < 1 :=
    (div_lt_one hr).mpr hg.2.1
  have hcentral := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity :
    0 ≤ clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) hratio).const_mul C
  have houter := (tendsto_pow_mul_tailAllowance_quadraticWidth hg.1 hc hu
    (by positivity : 0 < 4 * clearedPrimeSourceDistance rho)
    (normalizedPrimeTailClearingPolynomial D S rho).natDegree).const_mul A
  have hlim : Tendsto (fun N ↦ C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ N +
      A * (4 * clearedPrimeSourceDistance rho) ^ N *
        tailAllowance (clearedPrimeCentralWindow rho)
          (normalizedPrimeTailClearingPolynomial D S rho).natDegree
          (quadraticWidth c (clearedPrimeSourceDistance rho) N)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, mul_assoc] using hcentral.add houter
  apply squeeze_zero_norm' _ hlim
  filter_upwards [(tendsto_quadraticWidth c (clearedPrimeSourceDistance rho)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN
  exact hbound N _ (quadraticWidth_pos hc hu N) hN.le

/-- The full actual corrected prime heat retains the negative selected
source up to an arbitrarily small eventual error on the explicit schedule.
This is the source-side bound; an independent arithmetic lower bound that
conflicts with it has not been supplied. -/
theorem eventually_normalizedClearedPrimeHeat_re_le {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      (normalizedClearedPrimeHeat D S rho N (quadraticWidth c (clearedPrimeSourceDistance rho) N)).re ≤
        -(analyticZetaZeroMultiplicity rho : ℝ) * Real.exp (-c) + ε := by
  have hlim := tendsto_normalizedClearedPrimeRemainderHeat_quadraticWidth hD S hS rho hrho hc
  have hnorm : ∀ᶠ N in atTop, ‖normalizedClearedPrimeRemainderHeat D S rho N
      (quadraticWidth c (clearedPrimeSourceDistance rho) N)‖ < ε := by
    exact hlim.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using hε))
  filter_upwards [hnorm] with N hN
  have hb := normalizedClearedPrimeHeat_re_le hD S hS rho N hc
  have hre := re_le_norm (normalizedClearedPrimeRemainderHeat D S rho N
    (quadraticWidth c (clearedPrimeSourceDistance rho) N))
  linarith

/-- The retained whole arithmetic source is eventually bounded above
by a strictly negative constant, with the actual multiplicity present. -/
theorem eventually_normalizedClearedPrimeHeat_re_le_negative {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N in atTop,
      (normalizedClearedPrimeHeat D S rho N (quadraticWidth c (clearedPrimeSourceDistance rho) N)).re ≤
        -(analyticZetaZeroMultiplicity rho : ℝ) * Real.exp (-c) / 2 := by
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) :=
    Nat.cast_pos.mpr (analyticZetaZeroMultiplicity_positive rho)
  have h := eventually_normalizedClearedPrimeHeat_re_le hD S hS rho hrho hc
    (show 0 < (analyticZetaZeroMultiplicity rho : ℝ) * Real.exp (-c) / 2 by positivity)
  filter_upwards [h] with N hN
  linarith

end
end RiemannGaussian.SquarefreeEulerQuadratic
