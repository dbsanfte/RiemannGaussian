/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCancellingSector
import RiemannGaussian.ZetaRieszPrimeCountMass

namespace RiemannGaussian.ZetaRieszWeightedCount
noncomputable section
open RiemannGaussian Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeCountMass
/-- Every dominated squarefree coefficient family has the full absolute prime-count mass bound, retaining all filter shifts. -/
theorem norm_squarefree_sum_le_mass (D : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ D, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {q : ℝ} (hq : 0 < q)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N) :
    ‖∑ n ∈ D, a n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
      ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log n) := by
  let C := 32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
    ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  calc
    _ ≤ ∑ n ∈ D, ‖a n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ D, C * ((2 : ℝ) ^ n.primeFactors.card *
        Real.exp (-(3 / 2 - q) * Real.log n)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := hband hn
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      have hc := (ha n hn).trans
        ((ZetaRieszSmoothHead.logMajorant_le_prime_count (hD n hn)).trans
          (mul_le_mul_of_nonneg_right (ZetaRieszSmoothHead.log_le_of_mem_band hb) (by positivity)))
      have hk := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y) hn1 hq
      have h := mul_le_mul hc hk (norm_nonneg _) (by positivity)
      rw [norm_mul]
      apply h.trans_eq
      have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
      rw [hs]
      dsimp [C]
      ring
    _ = _ := (Finset.mul_sum ..).symm

/-- Arbitrary dominated coefficients inherit the complete height-uniform high-count arithmetic allowance. -/
theorem norm_normalized_many_sum_le (D : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ D, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u U q r : ℝ} (hu : 0 ≤ u) (huU : u ≤ U)
    (hq : 0 < q) (hqhalf : q < 1 / 2) (hr : 1 ≤ r)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand N)
    {K : ℕ} (hK : ∀ n ∈ D, K ≤ n.primeFactors.card) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ D, a n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((N : ℝ) * (U / q) ^ N) * Real.exp (2 * r * countMass (3 / 2 - q)) / r ^ K := by
  have hs := norm_squarefree_sum_le_mass D a ha P N y hq hD hband
  have hm := many_prime_mass_le D hD hK (by linarith : 1 < 3 / 2 - q) hr
  have hU : 0 ≤ U := hu.trans huU
  have hf : 0 ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hM : 0 ≤ ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card *
      Real.exp (-(3 / 2 - q) * Real.log n) := Finset.sum_nonneg fun _ _ => by positivity
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  calc
    _ ≤ u ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ∑ n ∈ D, (2 : ℝ) ^ n.primeFactors.card * Real.exp (-(3 / 2 - q) * Real.log n)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ U ^ (N + 1) * ((32 * (N : ℝ) * Real.log 2 * q⁻¹ ^ N *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (Real.exp (2 * r * countMass (3 / 2 - q)) / r ^ K)) := by gcongr
    _ = _ := by rw [pow_succ U N, div_pow]; simp only [inv_pow]; ring

/-- The high-count power saving remains valid with arbitrary bounded coefficient multipliers on the original schedule. -/
theorem norm_normalized_many_dyadic_le (D : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ D, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (P : Polynomial ℂ) (j : ℕ) (y : ℝ)
    {u U q : ℝ} (hu : 0 ≤ u) (huU : u ≤ U)
    (hq : 0 < q) (hqhalf : q < 1 / 2)
    (hD : ∀ n ∈ D, Squarefree n) (hband : D ⊆ zetaPrimeLogBand (dyadicMomentOrder j))
    (hK : ∀ n ∈ D, dyadicPrimeCount j ≤ n.primeFactors.card) :
    ‖(u : ℂ) ^ (dyadicMomentOrder j + 1) * ∑ n ∈ D,
      a n *
        zetaPrimeFilterKernel P (dyadicMomentOrder j) (3 / 2 + Complex.I * y) n‖ ≤
      (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((dyadicMomentOrder j : ℝ) * (16 * U / (17 * q)) ^ dyadicMomentOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) := by
  have hr : (1 : ℝ) ≤ dyadicPrimeCount j := by
    exact_mod_cast (show 1 ≤ dyadicPrimeCount j by have := four_le_dyadicPrimeCount j; omega)
  have hU := hu.trans huU
  have hF : 0 ≤ ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k := Finset.sum_nonneg fun _ _ => by positivity
  apply (norm_normalized_many_sum_le D a ha P (dyadicMomentOrder j) y hu huU hq hqhalf hr hD hband hK).trans
  calc
    _ ≤ (32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        ((dyadicMomentOrder j : ℝ) * (U / q) ^ dyadicMomentOrder j) *
          Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) /
            (17 / 16 : ℝ) ^ dyadicMomentOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (dyadic_count_power_saving j)
    _ = _ := by
      have he : 16 * U / (17 * q) = (U / q) / (17 / 16) := by field_simp
      rw [he]
      simp only [div_pow, inv_pow, mul_comm]
      ring

/-- Every dominated high-count squarefree subband vanishes at source scale, with arbitrary moving coefficients, heights and radii. -/
theorem tendsto_normalized_many_sum (P : Polynomial ℂ) (D : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (ha : ∀ j n, n ∈ D j → ‖a j n‖ ≤ zetaMoebiusLogMajorant n)
    (u y : ℕ → ℝ) {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 17 / 32)
    (hD : ∀ j, ∀ n ∈ D j, Squarefree n)
    (hband : ∀ j, D j ⊆ zetaPrimeLogBand (dyadicMomentOrder j))
    (hK : ∀ j, ∀ n ∈ D j, dyadicPrimeCount j ≤ n.primeFactors.card) :
    Tendsto (fun j => (u j : ℂ) ^ (dyadicMomentOrder j + 1) * ∑ n ∈ D j,
      a j n *
        zetaPrimeFilterKernel P (dyadicMomentOrder j) (3 / 2 + Complex.I * y j) n)
      atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrate⟩ := exists_many_prime_tilt hU hU1
  let R : ℝ := 16 * U / (17 * q)
  let C : ℝ := 32 * U * Real.log 2 * ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R < 1 := (div_lt_one (by positivity)).mpr hrate
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  let s : ℝ := (1 + R) / (2 * R)
  have hs : 1 < s := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * R)).mpr
    linarith
  have hRs : R * s = (1 + R) / 2 := by dsimp [s]; field_simp
  have hRs0 : 0 < R * s := mul_pos hR (by linarith)
  have hRs1 : R * s < 1 := by rw [hRs]; linarith
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hRs0 hRs1).comp
    tendsto_dyadicMomentOrder
  have hl : Tendsto (fun j => C * (((dyadicMomentOrder j : ℝ) + 1) *
      (R * s) ^ dyadicMomentOrder j)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, mul_zero] using ht.const_mul C
  apply squeeze_zero_norm' (a := fun j => C * (((dyadicMomentOrder j : ℝ) + 1) *
    (R * s) ^ dyadicMomentOrder j)) _ hl
  filter_upwards [eventually_exp_count_le_geometric (2 * countMass (3 / 2 - q)) hs] with j hj
  have hb := norm_normalized_many_dyadic_le (D j) (a j) (ha j) P j (y j) (hu j) (huU j)
    hq hqhalf (hD j) (hband j) (hK j)
  have he : Real.exp (2 * (dyadicPrimeCount j : ℝ) * countMass (3 / 2 - q)) ≤
      s ^ dyadicMomentOrder j := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hj
  apply hb.trans
  calc
    _ ≤ C * ((dyadicMomentOrder j : ℝ) * R ^ dyadicMomentOrder j) * s ^ dyadicMomentOrder j :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = C * ((dyadicMomentOrder j : ℝ) * (R * s) ^ dyadicMomentOrder j) := by rw [mul_pow]; ring
    _ ≤ _ := by gcongr; linarith



open ZetaRieszJointAllocation

/-- The exact joint finite coefficient vanishes outside squarefree support. -/
theorem coefficient_zero_of_not_squarefree (u : ℝ) (N K n : ℕ) (hn : ¬Squarefree n) :
    finiteCoefficient u N K n = 0 := by
  simp [finiteCoefficient, SquarefreeVaughanLogSource.coefficient, hn]

/-- The original residual finite support with only the independently paid high-count labels removed. -/
def lowCountBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (literalWindow N \ cancellingSector u N K).filter (fun n => n.primeFactors.card < K)

/-- The same signed finite coefficients on the remaining lower-count support. -/
def lowCountResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ lowCountBand u N K, finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- All squarefree high-count labels of the exact residual, including the companion mask correction. -/
def highCountBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (literalWindow N \ cancellingSector u N K).filter (fun n => Squarefree n ∧ K ≤ n.primeFactors.card)

/-- The exact discarded difference consists of the whole squarefree high-count correction. -/
theorem remaining_sub_lowCount (u y : ℝ) (N K : ℕ) :
    remainingResponse u y N K - lowCountResponse u y N K =
      ∑ n ∈ highCountBand u N K, finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  simp only [remainingResponse, lowCountResponse, lowCountBand, highCountBand,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hs : Squarefree n
  · by_cases hk : n.primeFactors.card < K
    · simp [hs, hk, Nat.not_le_of_lt hk]
    · simp [hs, hk, Nat.le_of_not_gt hk]
  · simp [coefficient_zero_of_not_squarefree u N K n hs]

/-- The complete high-count companion correction independently vanishes on the original source schedule. -/
theorem tendsto_remaining_sub_lowCount (u y : ℕ → ℝ) {U : ℝ}
    (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 17/32) :
    Tendsto (fun j => (u j:ℂ)^(dyadicMomentOrder j+1) *
      (remainingResponse (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j) -
        lowCountResponse (u j) (y j) (dyadicMomentOrder j) (dyadicPrimeCount j))) atTop (𝓝 0) := by
  have ht := tendsto_normalized_many_sum (1 : Polynomial ℂ)
    (fun j => highCountBand (u j) (dyadicMomentOrder j) (dyadicPrimeCount j))
    (fun j => finiteCoefficient (u j) (dyadicMomentOrder j) (dyadicPrimeCount j))
    (fun j n _ => norm_finiteCoefficient_le _ _ _ _) u y hu huU hU hU1
    (fun j n hn => (Finset.mem_filter.mp hn).2.1)
    (fun j n hn => by
      have hnW : n ∈ literalWindow (dyadicMomentOrder j) :=
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1
      exact (Finset.mem_filter.mp hnW).1)
    (fun j n hn => (Finset.mem_filter.mp hn).2.2)
  simpa only [remaining_sub_lowCount, filter_one_eq] using ht

/-- The residual on the original dyadic schedule after high-count companion terms are paid. -/
def lowCountRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u:ℂ)^(dyadicMomentOrder j+1) * lowCountResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- The unchanged source and positive reserve survive high-count companion deletion; the joint arithmetic floor remains open. -/
theorem tendsto_lowCount_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im:ℂ))-tau.1‖)
    (huh : 3/2-rho.1.re < Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => lowCountRemainder (3/2-rho.1.re) rho.1.im j +
      ((3/2-rho.1.re:ℝ):ℂ)^(dyadicMomentOrder j+1) *
        ZetaRieszWingReserve.reserve (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho:ℂ) + (analyticZetaZeroMultiplicity rho:ℂ)^2 *
        (RieszHarmonicCostBounds.paidHarmonicCost (3/2-rho.1.re):ℂ))) := by
  have hu : 0 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hU : Real.exp (-(11/16:ℝ)) < 17/32 := lt_of_le_of_lt radius_ceiling (by norm_num)
  have he := tendsto_remaining_sub_lowCount (fun _ => 3/2-rho.1.re) (fun _ => rho.1.im)
    (fun _ => hu) (fun _ => huh.le) (Real.exp_pos _) hU
  have hs := (tendsto_remaining_add_reserve rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  apply hs.congr' (Eventually.of_forall (fun j => ?_))
  dsimp only [remainingRemainder, lowCountRemainder]
  ring

end
end RiemannGaussian.ZetaRieszWeightedCount
