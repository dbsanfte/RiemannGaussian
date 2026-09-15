/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhysicalAnnulus
import RiemannGaussian.ZetaArithmeticDeviationBounds

/-!
# A smaller signed carrier throughout the right-half source range

The actual carrier retains all older masks, the exact physical lower cutoff and the full exposed-zero multiplicity source inside the tighter deviation window. The additional deletion is uniform even for moving radii and heights. The independent signed bound inside the window remains open.
-/

namespace RiemannGaussian.ZetaRieszDeviationCarrier
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open LogarithmicDeviation
open ZetaArithmeticDeviationBounds

/-- The full carrier retains every older support mask, the selected
deviation interval and its exact physical lower endpoint at every radius. -/
def physicalDeviationBand (u x₀ x₁ : ℝ) (N : ℕ) : Finset ℕ :=
  (deviationBand (ZetaRieszPhysicalAnnulus.annulusBand u N) x₀ x₁ N).filter
    (fun n => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n)

/-- The original signed Riesz coefficient, floor-defined length and
complete factorial filter on the smaller actual support. -/
def physicalDeviationResponse (P : Polynomial ℂ) (u y x₀ x₁ : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ physicalDeviationBand u x₀ x₁ N,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Every selected label keeps all earlier arithmetic restrictions and
both genuine logarithmic boundaries, together with the physical cutoff. -/
theorem mem_physicalDeviationBand (u x₀ x₁ : ℝ) (N n : ℕ) :
    n ∈ physicalDeviationBand u x₀ x₁ N ↔
      (n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N ∧
        x₀ * N < Real.log n ∧ Real.log n ≤ x₁ * N) ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n := by
  simp only [physicalDeviationBand, deviationBand, Finset.mem_filter]

/-- The complete lower physical prefix is deleted exactly. No bound
or sign is lost when it is intersected with the new logarithmic window. -/
theorem physicalDeviationResponse_eq_window (P : Polynomial ℂ) (u y x₀ x₁ : ℝ) (N : ℕ) :
    physicalDeviationResponse P u y x₀ x₁ N =
      ∑ n ∈ deviationBand (ZetaRieszPhysicalAnnulus.annulusBand u N) x₀ x₁ N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  exact ZetaRieszPhysicalProductBounds.sum_filter_physical_lower _
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) u N

/-- The actual carrier loses only an independently vanishing error on
every admissible deviation interval. This includes arbitrary moving
heights and does not assume hypothetical zeros or a signed floor. -/
theorem tendsto_annulus_sub_physicalDeviation (P : Polynomial ℂ) (y : ℕ → ℝ)
    {u x₀ x₁ : ℝ} (hu : 0 < u) (hx₀ : 0 < x₀) (hx₀2 : x₀ < 2) (hx₁ : 2 < x₁)
    (hcost₀ : Real.log (2 * u) < deviationCost x₀)
    (hcost₁ : Real.log (2 * u) < deviationCost x₁) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszPhysicalAnnulus.annulusResponse P N (y N)
        (SquarefreeVaughanLogSource.length u N) u -
        physicalDeviationResponse P u (y N) x₀ x₁ N)) atTop (nhds 0) := by
  have h := tendsto_sub_deviationBand (ZetaRieszPhysicalAnnulus.annulusBand u)
    (fun N => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (fun N n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P y hu hx₀ hx₀2 hx₁ hcost₀ hcost₁
  apply h.congr'
  filter_upwards [] with N
  rw [physicalDeviationResponse_eq_window]
  rfl

/-- Any admissible deviation interval retains the complete negative
multiplicity source of the actual carrier. The cutoff costs are explicit
scalar premises; no independent bound on the remaining sum is asserted. -/
theorem tendsto_physicalDeviation_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) (hx₀2 : x₀ < 2) (hx₁ : 2 < x₁)
    (hcost₀ : Real.log (2 * (3 / 2 - rho.1.re)) < deviationCost x₀)
    (hcost₁ : Real.log (2 * (3 / 2 - rho.1.re)) < deviationCost x₁) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      physicalDeviationResponse 1 (3 / 2 - rho.1.re) rho.1.im x₀ x₁ N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszPhysicalAnnulus.tendsto_normalizedAnnulus rho hrho hexposed).sub
    (tendsto_annulus_sub_physicalDeviation 1 (fun _ => rho.1.im)
      hu hx₀ hx₀2 hx₁ hcost₀ hcost₁)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold ZetaRieszPhysicalAnnulus.normalizedAnnulus
  ring

/-- The strictly smaller universal window carries the actual source
for EVERY exposed right-half zero, with no additional local-u hypothesis.
Multiplicity and all earlier arithmetic masks remain explicit. -/
theorem tendsto_universal_physicalDeviation_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      physicalDeviationResponse 1 (3 / 2 - rho.1.re) rho.1.im (9 / 20) (11 / 2) N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  obtain ⟨hl, hh⟩ := universal_costs hu (by linarith : (3 / 2 - rho.1.re : ℝ) ≤ 1)
  exact tendsto_physicalDeviation_exposed rho hrho hexposed
    (by norm_num) (by norm_num) (by norm_num) hl hh

/-- The actual narrowed source retains the original sign, full
logarithmic product phase and nonnegative factorial envelope. -/
theorem re_physicalDeviation_eq_cosine_sum (u y x₀ x₁ : ℝ) (N : ℕ) :
    ((u : ℂ) ^ (N + 1) * physicalDeviationResponse 1 u y x₀ x₁ N).re =
      u ^ (N + 1) * ∑ n ∈ physicalDeviationBand u x₀ x₁ N,
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n).re *
          (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
            Real.cos (y * Real.log n) := by
  simp only [physicalDeviationResponse, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.re_sum, ZetaRieszCosineCarrier.re_coefficient_filter_one]

/-- The entire actual additional deletion is uniform across 0<=u<=1,
including arbitrary moving radii and heights. It retains every older
arithmetic mask and the actual floor at each order. This does not assert
uniformity of the earlier source transport or bound the retained sum. -/
theorem tendsto_universal_annulus_error_moving_radius (P : Polynomial ℂ) (u y : ℕ → ℝ)
    (hu : ∀ N, 0 ≤ u N ∧ u N ≤ 1) :
    Tendsto (fun N : ℕ => (u N : ℂ) ^ (N + 1) *
      (ZetaRieszPhysicalAnnulus.annulusResponse P N (y N)
        (SquarefreeVaughanLogSource.length (u N) N) (u N) -
        physicalDeviationResponse P (u N) (y N) (9 / 20) (11 / 2) N)) atTop (nhds 0) := by
  have h := tendsto_sub_deviationBand_moving_radius (x₀ := 9 / 20) (x₁ := 11 / 2)
    (fun N => ZetaRieszPhysicalAnnulus.annulusBand (u N) N)
    (fun N => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length (u N) N))
    (fun N n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos (u N) N) n)
    P y u (by norm_num : (0 : ℝ) < 1) hu (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [mul_one] using universal_lower_cost)
    (by simpa only [mul_one] using universal_upper_cost)
  apply h.congr'
  filter_upwards [] with N
  rw [physicalDeviationResponse_eq_window]
  rfl

end
end RiemannGaussian.ZetaRieszDeviationCarrier
