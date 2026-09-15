/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedFrequency
import RiemannGaussian.ZetaRieszHeadOrders
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity
import RiemannGaussian.ZetaRieszCentralHarmonicCost

/-!
# Paying the complete low-frequency arithmetic cost

Keep the original nonlinear sum and prove an independent, uniform bound for
its entire low-frequency allowance. The required bandwidth shrinks with the
order; the complementary frequencies and tapered wing remain unpaid.
-/

namespace RiemannGaussian.ZetaRieszFrequencyDecay
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSignedFrequency ZetaRieszCentralPrimeLayers

/-- The real amplitude introduced by the complete three-prime quotient
has polynomial logarithmic growth, uniformly in every physical length at
least one. -/
theorem three_log_amplitude_le {x L H : ℝ} (hx : 0 ≤ x) (hxH : x ≤ H)
    (hL : 1 ≤ L) :
    x / L * |L - x / 2| * x ^ 3 ≤ (1 + H) ^ 5 := by
  have hL0 : 0 < L := by linarith
  have hg : |L - x / 2| ≤ L + x / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hdiv : x / L ≤ x := div_le_self hx hL
  have ham : x / L * |L - x / 2| ≤ x * (1 + x) := by
    calc
      _ ≤ x / L * (L + x / 2) := mul_le_mul_of_nonneg_left hg (div_nonneg hx hL0.le)
      _ = x + (x / L) * (x / 2) := by field_simp
      _ ≤ x + x * (x / 2) := by
        have h := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ x / 2 by positivity)
        linarith
      _ ≤ _ := by nlinarith
  calc
    _ ≤ (x * (1 + x)) * x ^ 3 := mul_le_mul_of_nonneg_right ham (by positivity)
    _ = (1 + x) * x ^ 4 := by ring
    _ ≤ (1 + H) * (1 + H) ^ 4 := by gcongr <;> linarith
    _ = _ := by ring

/-- The higher-prime cost has the same polynomial bound, without a
maximum on the prime count. -/
theorem higher_log_amplitude_le {x L H : ℝ} (hx : 0 ≤ x) (hxH : x ≤ H)
    (hL : 1 ≤ L) : x / L * x ^ 4 ≤ (1 + H) ^ 5 := by
  calc
    _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_right (div_le_self hx hL) (by positivity)
    _ ≤ (1 + H) * (1 + H) ^ 4 := by gcongr <;> linarith
    _ = _ := by ring

/-- The exact finite filter cost and convergent positive Dirichlet mass
used to pay the frequency allowance. -/
def frequencyTiltMass (P : Polynomial ℂ) (q : ℝ) : ℝ :=
  (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
    ∑' n : ℕ, zetaPrimeExpWeight (3 / 2 - q) n

/-- The tilt mass is nonnegative for a positive tilt. -/
theorem frequencyTiltMass_nonneg (P : Polynomial ℂ) {q : ℝ} (hq : 0 < q) :
    0 ≤ frequencyTiltMass P q := by
  unfold frequencyTiltMass
  exact mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
    (tsum_nonneg fun _ => (Real.exp_pos _).le)

/-- Every positive finite integer selection has one height-independent
factorial-filter norm budget. The Dirichlet series is genuinely summable. -/
theorem sum_norm_filter_le_tilt (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {q : ℝ} (hq : 0 < q) (hqhalf : q < 1 / 2) :
    (∑ n ∈ S, ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖) ≤
      q⁻¹ ^ N * frequencyTiltMass P q := by
  let F : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hF : 0 ≤ F := Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ ∑ n ∈ S, (q⁻¹ ^ N * F) * zetaPrimeExpWeight (3 / 2 - q) n := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y)
        (show (1 : ℝ) ≤ n by exact_mod_cast hS n hn) hq
      simpa only [show (3 / 2 + Complex.I * (y : ℂ)).re = 3 / 2 by simp,
        zetaPrimeExpWeight, F, mul_assoc, mul_left_comm, mul_comm] using h
    _ = (q⁻¹ ^ N * F) * ∑ n ∈ S, zetaPrimeExpWeight (3 / 2 - q) n :=
      (Finset.mul_sum S (fun n => zetaPrimeExpWeight (3 / 2 - q) n) (q⁻¹ ^ N * F)).symm
    _ ≤ (q⁻¹ ^ N * F) * ∑' n : ℕ, zetaPrimeExpWeight (3 / 2 - q) n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_zetaPrimeExpWeight (by linarith : 1 < 3 / 2 - q)).sum_le_tsum
        S (fun _ _ => (Real.exp_pos _).le)
    _ = _ := by unfold frequencyTiltMass; dsimp [F]; ring

/-- Every actual three-prime frequency cost is bounded by a convergent
tilt mass times a polynomial in its logarithmic support. No prime phase
or source assumption is needed for this complete allowance. -/
theorem threeFrequencyCost_le_tilt (S : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L H q : ℝ} (hL : 1 ≤ L) (hH : 0 ≤ H) (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hcard : ∀ n ∈ S, n.primeFactors.card = 3) (hlog : ∀ n ∈ S, Real.log n ≤ H) :
    threeFrequencyCost S (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) L ≤
      (1 + H) ^ 5 * (q⁻¹ ^ N * frequencyTiltMass P q) := by
  let T := S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬n.Prime)
  have hf : ∀ n ∈ T,
      (Real.log n / L * |L - Real.log n / 2|) *
        (∏ p ∈ n.primeFactors, Real.log p) ≤ (1 + H) ^ 5 := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hp := prime_log_product_le hmem.2.1
    rw [hcard n hmem.1] at hp
    exact (mul_le_mul_of_nonneg_left hp
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (by linarith)) (abs_nonneg _))).trans
        (three_log_amplitude_le (Real.log_natCast_nonneg n) (hlog n hmem.1) hL)
  calc
    _ ≤ ∑ n ∈ T, (1 + H) ^ 5 * ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
      unfold threeFrequencyCost
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ = (Real.log n / L * |L - Real.log n / 2| *
          (∏ p ∈ n.primeFactors, Real.log p)) *
            ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hf n hn) (norm_nonneg _)
    _ = (1 + H) ^ 5 * ∑ n ∈ T, ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_norm_filter_le_tilt T (fun _ hn => Nat.pos_of_ne_zero
        (Finset.mem_filter.mp hn).2.1.ne_zero) P N y hq hqhalf) (by positivity)

/-- The complete higher-prime frequency cost has the same polynomial
allowance. Every prime count at least four is covered by the preceding
quotient cancellation theorem. -/
theorem higherFrequencyCost_le_tilt (S : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {L H q : ℝ} (hL : 1 ≤ L) (hH : 0 ≤ H) (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hlog : ∀ n ∈ S, Real.log n ≤ H) :
    higherFrequencyCost S (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) L ≤
      (1 + H) ^ 5 * (q⁻¹ ^ N * frequencyTiltMass P q) := by
  let T := S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬n.Prime)
  calc
    _ ≤ ∑ n ∈ T, (1 + H) ^ 5 * ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
      unfold higherFrequencyCost
      apply Finset.sum_le_sum
      intro n hn
      have h := higher_log_amplitude_le (Real.log_natCast_nonneg n)
        (hlog n (Finset.mem_filter.mp hn).1) hL
      calc
        _ = (Real.log n / L * (Real.log n) ^ 4) *
          ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = (1 + H) ^ 5 * ∑ n ∈ T, ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_norm_filter_le_tilt T (fun _ hn => Nat.pos_of_ne_zero
        (Finset.mem_filter.mp hn).2.1.ne_zero) P N y hq hqhalf) (by positivity)

/-- Both actual finite costs have a single height-uniform bound, with
all integer masks and the full polynomial filter retained. -/
theorem nonlinearFrequencyCost_le (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {q : ℝ} (hq : 0 < q) (hqhalf : q < 1 / 2) :
    nonlinearFrequencyCost P u y N ≤
      2048 * ((N : ℝ) + 1) ^ 5 * (q⁻¹ ^ N * frequencyTiltMass P q) := by
  have hL := ZetaRieszHeadOrders.one_le_length u N
  have h3 := threeFrequencyCost_le_tilt
    ((centralUnpairedBand u N).filter (fun n => n.primeFactors.card = 3)) P N y
    hL (show 0 ≤ (8 / 3 : ℝ) * N by positivity) hq hqhalf
    (fun _ hn => (Finset.mem_filter.mp hn).2)
    (fun _ hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2)
  have h4 := higherFrequencyCost_le_tilt
    ((centralUnpairedBand u N).filter (fun n => 4 ≤ n.primeFactors.card)) P N y
    hL (show 0 ≤ (8 / 3 : ℝ) * N by positivity) hq hqhalf
    (fun _ hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2)
  have hp : (1 + (8 / 3 : ℝ) * N) ^ 5 ≤ 1024 * ((N : ℝ) + 1) ^ 5 := by
    calc
      _ ≤ (4 * ((N : ℝ) + 1)) ^ 5 := by gcongr; have := Nat.cast_nonneg (α := ℝ) N; linarith
      _ = _ := by ring
  have hm := frequencyTiltMass_nonneg P hq
  apply (add_le_add h3 h4).trans
  nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ q⁻¹ ^ N * frequencyTiltMass P q)]

/-- A geometrically shrinking fraction of the natural frequency window.
Its bandwidth is explicit at every order, including zero. -/
def geometricFrequencyCutoff (r : ℝ) (N : ℕ) : ℝ :=
  3 / (8 * ((N : ℝ) + 1)) * r ^ N

/-- The shrinking window remains positive and stays inside the actual
central support's valid frequency range, uniformly in the radius. -/
theorem geometricFrequencyCutoff_valid {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ) :
    0 < geometricFrequencyCutoff r N ∧
      geometricFrequencyCutoff r N * ((8 / 3 : ℝ) * N) ≤ 1 := by
  have hd := natural_frequency_window N
  have hp : r ^ N ≤ 1 := pow_le_one₀ hr.le hr1
  constructor
  · unfold geometricFrequencyCutoff
    positivity
  · calc
      _ ≤ (3 / (8 * ((N : ℝ) + 1))) * ((8 / 3 : ℝ) * N) := by
        unfold geometricFrequencyCutoff
        gcongr
        simpa using mul_le_mul_of_nonneg_left hp hd.1.le
      _ ≤ 1 := hd.2

/-- The entire explicit low-frequency allowance, including both growing
arithmetic costs, has one common polynomial-times-geometric bound on a
bounded radius interval. The complementary frequencies are not included. -/
theorem frequency_allowance_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u U r q : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hr : 0 < r)
    (hq : 0 < q) (hqhalf : q < 1 / 2) :
    u ^ (N + 1) * geometricFrequencyCutoff r N ^ 3 / (3 * Real.pi) *
      nonlinearFrequencyCost P u y N ≤
        (36 * U / Real.pi * frequencyTiltMass P q) *
          (((N : ℝ) + 1) ^ 2 * (U * r ^ 3 / q) ^ N) := by
  have hU : 0 ≤ U := hu.trans huU
  have hd : 0 ≤ geometricFrequencyCutoff r N := by unfold geometricFrequencyCutoff; positivity
  have hm := frequencyTiltMass_nonneg P hq
  have hC : 0 ≤ nonlinearFrequencyCost P u y N :=
    add_nonneg (threeFrequencyCost_nonneg _ _ (SquarefreeVaughanLogSource.length_pos u N))
      (higherFrequencyCost_nonneg _ _ (SquarefreeVaughanLogSource.length_pos u N))
  calc
    _ ≤ U ^ (N + 1) * geometricFrequencyCutoff r N ^ 3 / (3 * Real.pi) *
        nonlinearFrequencyCost P u y N := by gcongr
    _ ≤ U ^ (N + 1) * geometricFrequencyCutoff r N ^ 3 / (3 * Real.pi) *
        (2048 * ((N : ℝ) + 1) ^ 5 * (q⁻¹ ^ N * frequencyTiltMass P q)) :=
      mul_le_mul_of_nonneg_left (nonlinearFrequencyCost_le P u y N hq hqhalf) (by
        unfold geometricFrequencyCutoff
        positivity)
    _ = _ := by
      unfold geometricFrequencyCutoff
      simp only [mul_pow, div_pow, inv_pow]
      rw [show (r ^ N) ^ 3 = (r ^ 3) ^ N by rw [← pow_mul, Nat.mul_comm N 3, pow_mul],
        pow_succ U N]
      field_simp
      ring

/-- A common strict geometric rate proves decay of the complete finite
allowance, even when both source radius and height move arbitrarily with
the order. This is independent of hypothetical zeros. -/
theorem tendsto_frequency_allowance_moving (P : Polynomial ℂ)
    (u y : ℕ → ℝ) {U r q : ℝ} (hu : ∀ N, 0 ≤ u N) (huU : ∀ N, u N ≤ U)
    (hU : 0 < U) (hr : 0 < r) (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hrate : U * r ^ 3 < q) :
    Tendsto (fun N : ℕ => u N ^ (N + 1) * geometricFrequencyCutoff r N ^ 3 /
      (3 * Real.pi) * nonlinearFrequencyCost P (u N) (y N) N) atTop (𝓝 0) := by
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (show 0 < U * r ^ 3 / q by positivity) ((div_lt_one hq).mpr hrate)
  apply squeeze_zero (fun N => ?_)
    (fun N => frequency_allowance_le P (y N) N (hu N) (huU N) hr hq hqhalf)
    (by simpa only [mul_zero] using ht.const_mul (36 * U / Real.pi * frequencyTiltMass P q))
  have hC : 0 ≤ nonlinearFrequencyCost P (u N) (y N) N :=
    add_nonneg (threeFrequencyCost_nonneg _ _ (SquarefreeVaughanLogSource.length_pos (u N) N))
      (higherFrequencyCost_nonneg _ _ (SquarefreeVaughanLogSource.length_pos (u N) N))
  have huN := hu N
  unfold geometricFrequencyCutoff
  positivity

/-- A whole analytic family of geometric bandwidths works: every
positive rate with 2 U r^3<1 admits a genuinely summable tilt. This is a
parameter theorem, not a search for isolated filter coefficients. -/
theorem exists_frequency_tilt {U r : ℝ} (hU : 0 < U) (hr : 0 < r)
    (hrate : 2 * U * r ^ 3 < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 / 2 ∧ U * r ^ 3 < q := by
  refine ⟨(U * r ^ 3 + 1 / 2) / 2, ?_, ?_, ?_⟩ <;> nlinarith [pow_pos hr 3]

/-- Every bandwidth rate satisfying the cubic criterion removes the
entire low-frequency sector with independently vanishing source-normalized
error, even at arbitrary moving radii and heights. -/
theorem tendsto_nonlinear_low_frequency_moving (P : Polynomial ℂ)
    (u y : ℕ → ℝ) {U r : ℝ} (hu : ∀ N, 0 ≤ u N) (huU : ∀ N, u N ≤ U)
    (hU : 0 < U) (hr : 0 < r) (hr1 : r ≤ 1) (hrate : 2 * U * r ^ 3 < 1) :
    Tendsto (fun N : ℕ => (u N : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..geometricFrequencyCutoff r N,
        nonlinearFrequency P (u N) (y N) N xi)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrateq⟩ := exists_frequency_tilt hU hr hrate
  apply squeeze_zero_norm (fun N => norm_nonlinear_low_frequency_le P (y N) N
    (hu N) (geometricFrequencyCutoff_valid hr hr1 N).1.le
      (geometricFrequencyCutoff_valid hr hr1 N).2)
    (tendsto_frequency_allowance_moving P u y hu huU hU hr hq hqhalf hrateq)

/-- The whole original three-prime plus higher-prime response is
approximated by its complementary frequency integral with a proved
vanishing error. The retained integral is still signed and unbounded. -/
theorem tendsto_nonlinear_sub_high_frequency_moving (P : Polynomial ℂ)
    (u y : ℕ → ℝ) {U r : ℝ} (hu : ∀ N, 0 ≤ u N) (huU : ∀ N, u N ≤ U)
    (hU : 0 < U) (hr : 0 < r) (hr1 : r ≤ 1) (hrate : 2 * U * r ^ 3 < 1) :
    Tendsto (fun N : ℕ => (u N : ℂ) ^ (N + 1) *
      (centralThreePrimeResponse P (u N) (y N) N + centralHigherPrimeResponse P (u N) (y N) N -
        (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi (geometricFrequencyCutoff r N),
          nonlinearFrequency P (u N) (y N) N xi)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrateq⟩ := exists_frequency_tilt hU hr hrate
  apply squeeze_zero_norm (fun N => norm_nonlinear_sub_high_frequency_le P (y N) N
    (hu N) (geometricFrequencyCutoff_valid hr hr1 N).1.le
      (geometricFrequencyCutoff_valid hr hr1 N).2)
    (tendsto_frequency_allowance_moving P u y hu huU hU hr hq hqhalf hrateq)

/-- A concrete common allowance works across all right-half radii:
the natural window times (3/4)^N has complete error bounded by a fixed
filter-dependent constant times (N+1)^2 (27/28)^N. -/
theorem norm_nonlinear_sub_high_frequency_universal (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) *
      (centralThreePrimeResponse P u y N + centralHigherPrimeResponse P u y N -
        (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi (geometricFrequencyCutoff (3 / 4) N),
          nonlinearFrequency P u y N xi)‖ ≤
      (36 / Real.pi * frequencyTiltMass P (7 / 16)) *
        (((N : ℝ) + 1) ^ 2 * (27 / 28 : ℝ) ^ N) := by
  have hd := geometricFrequencyCutoff_valid (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) N
  apply (norm_nonlinear_sub_high_frequency_le P y N hu hd.1.le hd.2).trans
  have h := frequency_allowance_le P y N hu hu1 (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (0 : ℝ) < 7 / 16) (by norm_num : (7 / 16 : ℝ) < 1 / 2)
  norm_num at h ⊢
  exact h

/-- The source-conditioned obstruction is now wholly in the retained
coupled complementary frequencies and the tapered wing. The independently
paid low-frequency sector leaves the exact unrestricted multiplicity source
unchanged, on the original annular source range. -/
theorem tendsto_high_frequency_add_wing_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ((1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi (geometricFrequencyCutoff (3 / 4) N),
        nonlinearFrequency 1 (3 / 2 - rho.1.re) rho.1.im N xi) +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ZetaRieszCompletedCarrier.taperedWing (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re ≤ (1 : ℝ) := by linarith
  have he := tendsto_nonlinear_sub_high_frequency_moving 1
    (fun _ => 3 / 2 - rho.1.re) (fun _ => rho.1.im) (fun _ => hu) (fun _ => hu1)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) ≤ 1) (by norm_num : 2 * (1 : ℝ) * (3 / 4) ^ 3 < 1)
  have h := (ZetaRieszCentralHarmonicCost.tendsto_three_unpaid_exact_source
    rho hrho hexposed huh).sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end
end RiemannGaussian.ZetaRieszFrequencyDecay
