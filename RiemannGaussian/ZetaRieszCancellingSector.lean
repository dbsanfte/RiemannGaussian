/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllocationConcentration

/-!
# An independently vanishing sector of the signed arithmetic remainder

The coefficient saving survives the complete arithmetic sum and source normalization, uniformly in height and count cutoff throughout the reserve range. Only this proved sector is removed. The complementary signed sum still carries the source; its independent cofinal floor remains open.
-/

namespace RiemannGaussian.ZetaRieszJointAllocation
noncomputable section
open scoped BigOperators Classical

/-- An exact rational upper bound for the proved reserve-range radius ceiling. -/
theorem radius_ceiling : Real.exp (-(11/16:ℝ)) ≤ (503/1000:ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 11/16) 8
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- The source-normalized geometric rate after combining allocation cancellation with a summable arithmetic tilt. -/
def sectorRate : ℝ := (503/1000:ℝ)*(2048/1023:ℝ)*Real.exp (-(1/140:ℝ))

/-- The uniform source-normalized sector rate is nonnegative and strictly below one. -/
theorem sectorRate_bounds : 0 ≤ sectorRate ∧ sectorRate < 1 := by
  constructor
  · unfold sectorRate; positivity
  · rw [sectorRate, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have h := Real.add_one_le_exp (1/140:ℝ)
    linarith

/-- The saved coefficients have a summable full-arithmetic moment bound, uniform in height and finite support. -/
theorem norm_sum_small_coefficients (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 3*Real.exp (-(N:ℝ)/140)*zetaMoebiusLogMajorant n)
    (y : ℝ) :
    ‖∑ n ∈ S, a n * zetaPrimeLogKernel N (3/2 + Complex.I*y) n‖ ≤
      3*Real.exp (-(N:ℝ)/140)*(2048/1023:ℝ)^N*zetaMoebiusLogMajorantMass (2049/2048) := by
  let e : ℝ := 3*Real.exp (-(N:ℝ)/140)
  have he : 0 < e := by dsimp [e]; positivity
  let b : ℕ → ℂ := fun n => a n / (e:ℂ)
  have hb : ∀ n ∈ S, ‖b n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n hn
    rw [show b n = a n/(e:ℂ) from rfl, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
    apply (div_le_iff₀ he).mpr
    simpa only [e, mul_comm] using ha n hn
  have hh := ZetaArithmeticLogWindow.norm_sum_moment_of_log_bound S b hb N 0 y
    (2049/2048) (1023/2048) 0 (by norm_num) (by norm_num)
    (fun n _ => by norm_num)
  norm_num only [Nat.add_zero, Real.exp_zero, mul_one, pow_zero, inv_div] at hh
  have hs : (∑ n ∈ S, a n * zetaPrimeLogKernel N (3/2 + Complex.I*y) n) =
      (e:ℂ) * ∑ n ∈ S, b n * zetaPrimeLogKernel N (3/2 + Complex.I*y) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [b]
    have hec : (e:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
    field_simp
  rw [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  exact (mul_le_mul_of_nonneg_left hh he.le).trans_eq (by dsimp only [e]; ring)

/-- The coefficient saving survives source normalization throughout the reserve radius interval. -/
theorem normalized_sector_bound (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 3*Real.exp (-(N:ℝ)/140)*zetaMoebiusLogMajorant n)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    ‖(u:ℂ)^(N+1) * ∑ n ∈ S, a n * zetaPrimeLogKernel N (3/2 + Complex.I*y) n‖ ≤
      sectorRate^N * ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)) := by
  have hmass : 0 ≤ zetaMoebiusLogMajorantMass (2049/2048) := by
    unfold zetaMoebiusLogMajorantMass
    exact tsum_nonneg (fun n => mul_nonneg (zetaMoebiusLogMajorant_nonneg n) (Real.exp_pos _).le)
  have h := norm_sum_small_coefficients N S a ha y
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  calc
    _ ≤ (503/1000:ℝ)^(N+1) *
        (3*Real.exp (-(N:ℝ)/140)*(2048/1023:ℝ)^N*zetaMoebiusLogMajorantMass (2049/2048)) :=
      mul_le_mul (pow_le_pow_left₀ hu (huU.trans radius_ceiling) _) h (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-(N:ℝ)/140) = Real.exp (-(1/140:ℝ))^N := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he, sectorRate, mul_pow, mul_pow, pow_succ]
      ring

/-- The literal finite retained sector with an eligible selected prime and the proved cofactor-log ratio. -/
def cancellingSector (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (literalWindow N).filter (fun n =>
    n ∈ LogarithmicDeviation.deviationBand (ZetaRieszHarmonicWindow.fewBand u N K) (7/4) (9/4) N ∧
    Squarefree n ∧ 1<n ∧ ¬n.Prime ∧ ∃ p ∈ n.primeFactors,
      p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N ∧ eligibleCofactor p (n/p) ∧
      (17/64:ℝ) ≤ Real.log (n/p:ℕ)/Real.log n ∧ Real.log (n/p:ℕ)/Real.log n ≤ (11/32:ℝ))

/-- The whole selected sector of the actual signed remainder has a geometric bound uniform in height, radius and prime-count threshold. -/
theorem actual_sector_geometric (N K : ℕ) (hN : 320 ≤ N) (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    ‖(u:ℂ)^(N+1) * ∑ n ∈ cancellingSector u N K,
      finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2 + Complex.I*y) n‖ ≤
      sectorRate^N * ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048)) := by
  apply normalized_sector_bound N _ _ ?_ y hu huU
  intro n hn
  obtain ⟨_, hnS, hns, hn1, hnp, p, hp, hpA, hel, hlo, hhi⟩ := Finset.mem_filter.mp hn
  exact finite_coefficient_sector_bound u N K hN hnS hns hn1 hnp hp hpA hel hlo hhi


open Filter Topology ZetaRieszPrimeCountFrequency

/-- The exact finite signed response after removing only the independently vanishing allocation sector. -/
def remainingResponse (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ literalWindow N \ cancellingSector u N K,
    finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The removed part is exactly the proved cancellation sector, with no changed coefficients or masks. -/
theorem finite_sub_remaining (u y : ℝ) (N K : ℕ) :
    finiteResponse u y N K - remainingResponse u y N K =
      ∑ n ∈ cancellingSector u N K,
        finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  have hsub : cancellingSector u N K ⊆ literalWindow N := Finset.filter_subset _ _
  have hs := Finset.sum_sdiff
    (f := fun n => finiteCoefficient u N K n * zetaPrimeLogKernel N (3/2+Complex.I*y) n) hsub
  dsimp only [finiteResponse, remainingResponse]
  linear_combination -hs

/-- The removed sector vanishes for arbitrary changing heights and count cutoffs at every fixed eligible radius. -/
theorem tendsto_removed_sector (K : ℕ → ℕ) (y : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    Tendsto (fun N => (u:ℂ)^(N+1) *
      (finiteResponse u (y N) N (K N) - remainingResponse u (y N) N (K N))) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one sectorRate_bounds.1 sectorRate_bounds.2).mul_const
    ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))
  simp only [zero_mul] at ht
  apply squeeze_zero_norm' (a := fun N => sectorRate^N *
    ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) ?_ ht
  filter_upwards [eventually_ge_atTop 320] with N hN
  rw [finite_sub_remaining]
  exact actual_sector_geometric N (K N) hN (y N) hu huU

/-- The uncancelled finite response on the original dyadic source schedule. -/
def remainingRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u:ℂ)^(dyadicMomentOrder j+1) * remainingResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)

/-- The dyadic source loses only an independently vanishing error when the proved sector is removed. -/
theorem tendsto_finite_sub_remaining (y : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => finiteRemainder u y j - remainingRemainder u y j) atTop (𝓝 0) := by
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one sectorRate_bounds.1 sectorRate_bounds.2).comp
    tendsto_dyadicMomentOrder).mul_const ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))
  simp only [Function.comp_def, zero_mul] at ht
  apply squeeze_zero_norm' (a := fun j => sectorRate^(dyadicMomentOrder j) *
    ((1509/1000:ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) ?_ ht
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 320)] with j hj
  have hb := actual_sector_geometric (dyadicMomentOrder j) (dyadicPrimeCount j) hj y hu huU
  dsimp only [finiteRemainder, remainingRemainder]
  rw [← mul_sub, finite_sub_remaining]
  exact hb

/-- The exact exposed-zero source and positive reserve remain after the proved sector is removed; the independent floor remains open. -/
theorem tendsto_remaining_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im:ℂ))-tau.1‖)
    (huh : 3/2-rho.1.re < Real.exp (-(11/16:ℝ))) :
    Tendsto (fun j => remainingRemainder (3/2-rho.1.re) rho.1.im j +
      ((3/2-rho.1.re:ℝ):ℂ)^(dyadicMomentOrder j+1) *
        ZetaRieszWingReserve.reserve (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho:ℂ) + (analyticZetaZeroMultiplicity rho:ℂ)^2 *
        (RieszHarmonicCostBounds.paidHarmonicCost (3/2-rho.1.re):ℂ))) := by
  have hu : 0 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he := tendsto_finite_sub_remaining rho.1.im hu huh.le
  have hs := (tendsto_finite_add_reserve rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall (fun _ => by ring))


end
end RiemannGaussian.ZetaRieszJointAllocation
