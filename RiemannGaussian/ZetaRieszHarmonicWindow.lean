/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWingHighOrders
import RiemannGaussian.ZetaArithmeticDeviationBounds

/-!
# Paying the outer logarithmic tails of the harmonic remainder

The whole lower-prime-count response is retained on a smaller logarithmic
window. Its discarded parts have one geometric bound, uniform in height,
count threshold and source radius. The surviving signed response remains
coupled to the original wing, or to its unpaid middle after the two proved
wing estimates. No floor for that joint response is assumed in the source
transport theorems.
-/

namespace RiemannGaussian.ZetaRieszHarmonicWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open LogarithmicDeviation ZetaArithmeticDeviationBounds
open ZetaRieszPrimeCountFrequency

/-- Both endpoints pay the entire original harmonic-cost radius range.
These are strict scalar estimates, including its limiting radius. -/
theorem annular_window_costs :
    Real.log (2 * Real.exp (-(2 / 3 : ℝ))) < deviationCost (25 / 16) ∧
      Real.log (2 * Real.exp (-(2 / 3 : ℝ))) < deviationCost (5 / 2) := by
  have hl : Real.log (25 / 16 : ℝ) < 43 / 96 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 43 / 96) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hh : Real.log (5 / 2 : ℝ) < 11 / 12 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 12) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h₀ := log_rate_eq_deviation (Real.exp_pos (-(2 / 3 : ℝ)))
    (by norm_num : (0 : ℝ) < 25 / 16)
  have h₁ := log_rate_eq_deviation (Real.exp_pos (-(2 / 3 : ℝ)))
    (by norm_num : (0 : ℝ) < 5 / 2)
  rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h₀ h₁
  constructor <;> linarith

/-- The radius range of the proved wing reserve pays the still narrower
window 7N/4 < log n <= 9N/4, with strict margins at both endpoints. -/
theorem reserve_window_costs :
    Real.log (2 * Real.exp (-(11 / 16 : ℝ))) < deviationCost (7 / 4) ∧
      Real.log (2 * Real.exp (-(11 / 16 : ℝ))) < deviationCost (9 / 4) := by
  have hl : Real.log (7 / 4 : ℝ) < 9 / 16 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 16) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hh : Real.log (9 / 4 : ℝ) < 13 / 16 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 16) 7
    norm_num [Finset.sum_range_succ] at h
    linarith
  have h₀ := log_rate_eq_deviation (Real.exp_pos (-(11 / 16 : ℝ)))
    (by norm_num : (0 : ℝ) < 7 / 4)
  have h₁ := log_rate_eq_deviation (Real.exp_pos (-(11 / 16 : ℝ)))
    (by norm_num : (0 : ℝ) < 9 / 4)
  rw [Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h₀ h₁
  constructor <;> linarith

/-- Exactly the integer support of the retained lower-count frequency
response, with all old masks and both count endpoints unchanged. -/
def fewBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card < K)

/-- The original complete signed lower-count sum, before narrowing its
logarithmic support. Its coefficient includes the actual endpoint length. -/
def fewResponse (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ fewBand u N K, SquarefreeVaughanLogSource.coefficient
    (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The finite sum is the entire existing frequency integral; no
frequency truncation or extra squarefree hypothesis is introduced. -/
theorem fewResponse_eq_integral (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) :
    fewResponse P u y N K = (1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in Set.Ioi 0, fewPrimeFrequency P u y N K xi := by
  exact ZetaRieszPrimeFourier.sum_original_eq_primePair_integral _ _ _

/-- Only the logarithmic support is narrowed. All arithmetic masks,
count bounds, signs and product phases remain in the finite response. -/
def windowResponse (P : Polynomial ℂ) (u y a b : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ deviationBand (fewBand u N K) a b N,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Exact support of the still-unpaid lower-count sum, including the
strict lower endpoint and the closed upper endpoint. -/
theorem mem_windowBand (u a b : ℝ) (N K n : ℕ) :
    n ∈ deviationBand (fewBand u N K) a b N ↔
      (n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N ∧
        3 ≤ n.primeFactors.card ∧ n.primeFactors.card < K) ∧
      a * N < Real.log n ∧ Real.log n ≤ b * N := by
  simp only [deviationBand, fewBand, Finset.mem_filter]

/-- The whole removed lower-count response has one strict geometric
bound, uniform in all heights, count thresholds and radii up to U.
The estimate includes every frequency and the complete fixed filter. -/
theorem exists_uniform_window_error (P : Polynomial ℂ) {U a b : ℝ}
    (hU : 0 < U) (ha : 0 < a) (ha2 : a < 2) (hb : 2 < b)
    (hca : Real.log (2 * U) < deviationCost a)
    (hcb : Real.log (2 * U) < deviationCost b) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ U →
        ‖(u : ℂ) ^ (N + 1) *
          (fewResponse P u y N K - windowResponse P u y a b N K)‖ ≤ r ^ N * C := by
  obtain ⟨r, C, hr0, hr1, hC, h⟩ := exists_uniform_deviation_bound P hU ha ha2 hb hca hcb
  refine ⟨r, C, hr0, hr1, hC, ?_⟩
  intro N K y u hu huU
  exact h N (fewBand u N K)
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) y u hu huU

/-- The original harmonic range therefore needs no lower-count integer
outside 25N/16 < log n <= 5N/2. Its complete deletion is geometric and
independent of zeros, uniformly at every height and count threshold. -/
theorem exists_annular_window_error (P : Polynomial ℂ) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ Real.exp (-(2 / 3 : ℝ)) →
        ‖(u : ℂ) ^ (N + 1) * (fewResponse P u y N K -
          windowResponse P u y (25 / 16) (5 / 2) N K)‖ ≤ r ^ N * C :=
  exists_uniform_window_error P (Real.exp_pos _) (by norm_num) (by norm_num)
    (by norm_num) annular_window_costs.1 annular_window_costs.2

/-- On the wing-reserve radius interval, only 7N/4 < log n <= 9N/4
survives. This is a bound for both complete discarded arithmetic sums. -/
theorem exists_reserve_window_error (P : Polynomial ℂ) :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N K : ℕ) (y u : ℝ), 0 ≤ u → u ≤ Real.exp (-(11 / 16 : ℝ)) →
        ‖(u : ℂ) ^ (N + 1) * (fewResponse P u y N K -
          windowResponse P u y (7 / 4) (9 / 4) N K)‖ ≤ r ^ N * C :=
  exists_uniform_window_error P (Real.exp_pos _) (by norm_num) (by norm_num)
    (by norm_num) reserve_window_costs.1 reserve_window_costs.2

/-- The uniform bound pays the whole deletion on the existing cofinal
schedule, with arbitrary moving heights and source radii. -/
theorem tendsto_window_error (P : Polynomial ℂ) (u y : ℕ → ℝ) {U a b : ℝ}
    (hU : 0 < U) (hu : ∀ j, 0 ≤ u j ∧ u j ≤ U)
    (ha : 0 < a) (ha2 : a < 2) (hb : 2 < b)
    (hca : Real.log (2 * U) < deviationCost a)
    (hcb : Real.log (2 * U) < deviationCost b) :
    Tendsto (fun j : ℕ => (u j : ℂ) ^ (dyadicMomentOrder j + 1) *
      (fewResponse P (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j) -
        windowResponse P (u j) (y j) a b (dyadicMomentOrder j) (dyadicPrimeCount j)))
      atTop (𝓝 0) := by
  obtain ⟨r, C, hr0, hr1, _, h⟩ := exists_uniform_window_error P hU ha ha2 hb hca hcb
  apply squeeze_zero_norm (fun j => h (dyadicMomentOrder j) (dyadicPrimeCount j)
    (y j) (u j) (hu j).1 (hu j).2)
  simpa only [Function.comp_def, zero_mul] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp tendsto_dyadicMomentOrder).mul_const C

/-- The joint target throughout the original harmonic-cost range.
The whole original tapered wing remains coupled to the smaller count sum. -/
def annularRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    (windowResponse 1 u y (25 / 16) (5 / 2) (dyadicMomentOrder j) (dyadicPrimeCount j) +
      ZetaRieszCompletedCarrier.taperedWing u y (dyadicMomentOrder j))

/-- The exact harmonic source survives the independently paid outer
tails throughout the original radius range, with full multiplicity. -/
theorem tendsto_annularRemainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (annularRemainder (3 / 2 - rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have he := tendsto_window_error 1 (fun _ => 3 / 2 - rho.1.re) (fun _ => rho.1.im)
    (Real.exp_pos _) (fun _ => ⟨hu, huh.le⟩) (by norm_num) (by norm_num) (by norm_num)
    annular_window_costs.1 annular_window_costs.2
  have hs := (ZetaRieszPrimeCountMass.tendsto_few_add_wing_source rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  apply hs.congr'
  filter_upwards [] with j
  rw [fewResponse_eq_integral]
  unfold annularRemainder
  ring

/-- The smaller joint target on the wing-reserve range: the narrowed
lower-count response and exactly the remaining middle wing. -/
def remainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    (windowResponse 1 u y (7 / 4) (9 / 4) (dyadicMomentOrder j) (dyadicPrimeCount j) +
      ZetaRieszWingHighOrders.unpaidWing u y (dyadicMomentOrder j))

/-- Narrowing the count sum removes an independently vanishing error
from the current fixed joint target. The wing is unchanged in this step. -/
theorem tendsto_remainder_error (u y : ℝ) (hu : 0 ≤ u)
    (huh : u < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j => ZetaRieszWingHighOrders.remainder u y j - remainder u y j)
      atTop (𝓝 0) := by
  have he := tendsto_window_error 1 (fun _ => u) (fun _ => y) (Real.exp_pos _)
    (fun _ => ⟨hu, huh.le⟩) (by norm_num) (by norm_num) (by norm_num)
    reserve_window_costs.1 reserve_window_costs.2
  apply he.congr'
  filter_upwards [] with j
  rw [fewResponse_eq_integral]
  unfold ZetaRieszWingHighOrders.remainder remainder
  ring

/-- The exact source and positive reserve survive with only the
narrowed lower-count sum and middle wing left in the unpaid remainder. -/
theorem tendsto_remainder_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j : ℕ => remainder (3 / 2 - rho.1.re) rho.1.im j +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1) *
        ZetaRieszWingReserve.reserve (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) ≤ 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hs := (ZetaRieszWingHighOrders.tendsto_remainder_add_reserve rho hrho hexposed huh).sub
    (tendsto_remainder_error _ rho.1.im hu huh)
  simp only [sub_zero] at hs
  exact hs.congr' (Filter.Eventually.of_forall fun _ => by ring)

/-- An independent cofinal floor for this exact smaller joint target
would close the simple exposed-zero case. Its premise remains open. -/
theorem false_of_remainder_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    {eta : ℝ}
    (heta : eta < 1 - RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) + 15 / 544)
    (hfloor : ∃ᶠ j in atTop, -eta ≤ (remainder (3 / 2 - rho.1.re) rho.1.im j).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_remainder_add_reserve rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, one_mul, Complex.add_re,
    Complex.neg_re, Complex.one_re, Complex.ofReal_re] at hs
  have hr := tendsto_dyadicMomentOrder.eventually
    (ZetaRieszWingReserve.eventually_re_reserve_ge rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, mul_one] at hr
  have hfreq := (hfloor.and_eventually hr).mono (fun _ hj => add_le_add hj.1 hj.2)
  have hc := ge_of_tendsto_of_frequently hs hfreq
  linarith

end
end RiemannGaussian.ZetaRieszHarmonicWindow
