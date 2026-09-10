/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusWeightedFourier
import RiemannGaussian.ZetaMoebiusFourierEnergy
import Mathlib.Analysis.PSeries

/-!
# Independent decay outside the weighted Möbius resonant region

The fixed Dirichlet reweighting has bounded arithmetic mass. The full
cyclic second difference of its quarter-line kernel has independent
geometric decay, including its initial and terminal exceptional samples.
The exact signed resonant interaction remains available as the carrier
of the selected-zero source.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The positive exponential sampling weight is summable beyond one,
including its explicitly totalized value at the unused zero index. -/
theorem summable_zetaPrimeExpWeight {σ : ℝ} (hσ : 1 < σ) :
    Summable (zetaPrimeExpWeight σ) := by
  have hr : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-σ)) := Real.summable_nat_rpow.mpr (by linarith)
  apply (summable_nat_add_iff 1).mp
  apply ((summable_nat_add_iff 1).mpr hr).congr
  intro n
  rw [Real.rpow_def_of_pos (by positivity)]
  unfold zetaPrimeExpWeight
  congr 1
  ring

/-- The finite spatial mass used for the second-difference envelope. -/
def zetaQuarterKernelSpatialMass : ℝ := ∑' n, zetaPrimeExpWeight (9 / 8) n

/-- Every spatial term is nonnegative. -/
theorem zetaQuarterKernelSpatialMass_nonneg : 0 ≤ zetaQuarterKernelSpatialMass :=
  tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)

/-- The upper two cyclic samples have a geometric bound uniform in the
ordinate. The factor two pays for a sample as low as half the endpoint. -/
theorem norm_zetaQuarterKernel_near_upper_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {x : ℝ} (hx : 1 ≤ x) (hM : ((2 ^ (32 * N) : ℕ) : ℝ) ≤ 2 * x) :
    ‖zetaPrimeFilterKernel p N (1 / 4 + I * y) x‖ ≤
      2 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by
  have hx0 := zero_lt_one.trans_le hx
  have hlogM : Real.log ((2 ^ (32 * N) : ℕ) : ℝ) = 32 * (N : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    push_cast
    rfl
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ (32 * N) : ℕ) : ℝ)) hM
  rw [hlogM, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hl
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have he : Real.exp (-(1 / 8 : ℝ) * Real.log x) ≤ 2 * (1 / 16 : ℝ) ^ N := by
    calc
      _ ≤ Real.exp (Real.log 2 - 4 * (N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 2 * (1 / 16 : ℝ) ^ N := by
        have h4 : Real.exp (4 * Real.log 2) = 16 := by
          have h := Real.exp_nat_mul (Real.log 2) 4
          norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
          exact h
        rw [Real.exp_sub, Real.exp_log (by norm_num),
          show 4 * (N : ℝ) * Real.log 2 = (N : ℝ) * (4 * Real.log 2) by ring,
          Real.exp_nat_mul, h4]
        rw [div_eq_mul_inv, ← inv_pow]
        norm_num
  have h := norm_zetaPrimeFilterKernel_le_tilt p N (1 / 4 + I * y) hx
    (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num at h
  apply h.trans
  calc
    _ ≤ (8 : ℝ) ^ N * (2 * (1 / 16 : ℝ) ^ N) *
          ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by
      gcongr
      simpa only [neg_mul] using he
    _ = _ := by
      have hp : (8 : ℝ) ^ N * (1 / 16 : ℝ) ^ N = (1 / 2 : ℝ) ^ N := by
        rw [← mul_pow]
        norm_num
      calc
        _ = 2 * ((8 : ℝ) ^ N * (1 / 16 : ℝ) ^ N) *
            ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by ring
        _ = _ := by rw [hp]

/-- The one initial exceptional second-difference sample also has
geometric moment decay, for every polynomial and ordinate. -/
theorem norm_zetaQuarterKernel_two_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaPrimeFilterKernel p N (1 / 4 + I * y) 2‖ ≤
      2 * (8 / 9 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k := by
  have h := norm_zetaPrimeFilterKernel_le_tilt p N (1 / 4 + I * y)
    (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 9 / 8)
  norm_num at h
  have he : Real.exp ((7 / 8 : ℝ) * Real.log 2) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
      _ = _ := Real.exp_log (by norm_num)
  apply h.trans
  calc
    _ ≤ (8 / 9 : ℝ) ^ N * 2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k := by gcongr
    _ = _ := by ring

/-- The entire cyclic second-difference mass decays geometrically,
including every exceptional sample, with no factor from the growing
number of arithmetic indices. -/
theorem sum_norm_cyclicSecond_quarterKernel_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hN : 2 ≤ N) :
    (∑ j, ‖(cyclicDifference^[2] (zetaQuarterKernelSamples p N y)) j‖) ≤
      (8 / 9 : ℝ) ^ (N - 2) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by
  let M : ℕ := 2 ^ (32 * N)
  let f := zetaQuarterKernelSamples p N y
  have hM : 2 ≤ M := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (by omega : 1 ≤ 32 * N)
  have hf {n : ℕ} (hn : 0 < n) (hm : n ≤ M) :
      f n = zetaPrimeFilterKernel p N (1 / 4 + I * y) n :=
    zetaQuarterKernelSamples_nat p N y hn (by change n < M + 1; omega)
  have h0 : f 0 = 0 := by simp [f, zetaQuarterKernelSamples]
  have h1 : f 1 = 0 := by
    have he := hf (n := 1) (by omega) (by omega)
    rw [Nat.cast_one] at he
    rw [he]
    simpa only [Nat.cast_one, Nat.sub_add_cancel (by omega : 1 ≤ N)] using
      zetaPrimeFilterKernel_one_succ p (N - 1) (1 / 4 + I * y)
  have hi : (∑ n ∈ Finset.Ico 1 (M - 1),
      ‖f ((n + 2 : ℕ) : ZMod (M + 1)) - 2 * f ((n + 1 : ℕ) : ZMod (M + 1)) + f n‖) ≤
        (8 / 9 : ℝ) ^ (N - 2) * zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico 1 (M - 1), (8 / 9 : ℝ) ^ (N - 2) *
          zetaPrimeExpWeight (9 / 8) n * zetaQuarterKernelSecondConstant p y := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        rw [hf (by omega : 0 < n + 2) (by omega), hf (by omega : 0 < n + 1) (by omega),
          hf (by omega : 0 < n) (by omega)]
        have h := norm_zetaQuarterKernel_second_difference_le p (N - 2) y
          (by exact_mod_cast hn'.1 : (1 : ℝ) ≤ n)
        simpa only [Nat.sub_add_cancel hN, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
          zetaPrimeExpWeight] using h
      _ = (8 / 9 : ℝ) ^ (N - 2) * zetaQuarterKernelSecondConstant p y *
          ∑ n ∈ Finset.Ico 1 (M - 1), zetaPrimeExpWeight (9 / 8) n := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum (Finset.Ico 1 (M - 1)) (fun _ _ ↦ (Real.exp_pos _).le)
          (summable_zetaPrimeExpWeight (by norm_num)))
        (mul_nonneg (by positivity) (zetaQuarterKernelSecondConstant_nonneg p y))
  have hupper : ‖f M‖ ≤ 2 * (1 / 2 : ℝ) ^ N *
      ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by
    rw [hf (by omega) le_rfl]
    apply norm_zetaQuarterKernel_near_upper_le p N y
    · exact_mod_cast (show 1 ≤ M by omega)
    · change (M : ℝ) ≤ 2 * M
      linarith [Nat.cast_nonneg (α := ℝ) M]
  have hprevious : ‖f (M - 1 : ℕ)‖ ≤ 2 * (1 / 2 : ℝ) ^ N *
      ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k := by
    rw [hf (by omega) (by omega)]
    apply norm_zetaQuarterKernel_near_upper_le p N y
    · exact_mod_cast (show 1 ≤ M - 1 by omega)
    · change (M : ℝ) ≤ 2 * ((M - 1 : ℕ) : ℝ)
      exact_mod_cast (show M ≤ 2 * (M - 1) by omega)
  have hpow : (8 / 9 : ℝ) ^ N ≤ (8 / 9 : ℝ) ^ (N - 2) := by
    have h := pow_add (8 / 9 : ℝ) (N - 2) 2
    rw [Nat.sub_add_cancel hN] at h
    nlinarith [show 0 ≤ (8 / 9 : ℝ) ^ (N - 2) by positivity]
  have htwo : ‖f 2‖ ≤ 2 * (8 / 9 : ℝ) ^ (N - 2) *
      ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k := by
    have he := hf (n := 2) (by omega) hM
    norm_num only [Nat.cast_ofNat] at he
    rw [he]
    apply (norm_zetaQuarterKernel_two_le p N y).trans
    gcongr
  apply (sum_norm_cyclicDifference_twice_le M hM f h0 h1).trans
  calc
    _ ≤ (8 / 9 : ℝ) ^ (N - 2) * zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
        2 * (8 / 9 : ℝ) ^ (N - 2) * (∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        2 * (1 / 2 : ℝ) ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) +
        3 * (2 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) := by
      gcongr
    _ = _ := by ring

/-- The complete cyclic difference allowance tends to zero for every
fixed polynomial and ordinate. All derivative and boundary premises have
been discharged for the actual quarter-line samples. -/
theorem tendsto_sum_norm_cyclicSecond_quarterKernel (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ ∑ j, ‖(cyclicDifference^[2] (zetaQuarterKernelSamples p N y)) j‖)
      atTop (𝓝 0) := by
  have ha := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 8 / 9)
    (by norm_num : (8 / 9 : ℝ) < 1)).comp (tendsto_sub_atTop_nat 2)
  have hb := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N ↦ Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)))
    (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦ sum_norm_cyclicSecond_quarterKernel_le p N y hN⟩)
  have h := (ha.mul_const (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
    2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k)).add
      ((hb.const_mul 8).mul_const (∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k))
  simpa using h

/-- Every fixed positive symbol gap has an independently vanishing
weighted arithmetic interaction, uniformly over the moving divisor cutoff. -/
theorem tendsto_zetaMoebiusWeightedFourierPart_compl (p : Polynomial ℂ)
    (D : ℕ → ℕ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N ↦ zetaMoebiusWeightedFourierPart p (D N) N y
      (zetaMoebiusResonantModes N δ)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaMoebiusWeightedFourierPart_compl_le p (D N) N 2 y hδ)
  simpa only [mul_zero] using (tendsto_sum_norm_cyclicSecond_quarterKernel p y).const_mul
    (δ⁻¹ ^ 2 * zetaMoebiusLogMajorantMass (5 / 4))

/-- An explicit geometric threshold shrinks the retained resonant
region while still leaving room for the independently proved decay. -/
def zetaMoebiusResonanceThreshold (N : ℕ) : ℝ := (31 / 32 : ℝ) ^ N

/-- The moving symbol threshold is always strictly positive. -/
theorem zetaMoebiusResonanceThreshold_pos (N : ℕ) : 0 < zetaMoebiusResonanceThreshold N := by
  unfold zetaMoebiusResonanceThreshold
  positivity

/-- The retained frequency threshold tends to zero geometrically. -/
theorem tendsto_zetaMoebiusResonanceThreshold :
    Tendsto zetaMoebiusResonanceThreshold atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private theorem shrinking_gap_budget_eq (p : Polynomial ℂ) (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    (zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 *
      ((8 / 9 : ℝ) ^ (N - 2) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        8 * (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) =
      (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) * (8192 / 8649 : ℝ) ^ N +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) * (512 / 961 : ℝ) ^ N := by
  have hs : (8 / 9 : ℝ) ^ (N - 2) = (81 / 64 : ℝ) * (8 / 9 : ℝ) ^ N := by
    have h := pow_add (8 / 9 : ℝ) (N - 2) 2
    rw [Nat.sub_add_cancel hN] at h
    nlinarith
  have ha : (zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 * (8 / 9 : ℝ) ^ N =
      (8192 / 8649 : ℝ) ^ N := by
    rw [zetaMoebiusResonanceThreshold, ← inv_pow, pow_right_comm, ← mul_pow]
    norm_num
  have hb : (zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ N =
      (512 / 961 : ℝ) ^ N := by
    rw [zetaMoebiusResonanceThreshold, ← inv_pow, pow_right_comm, ← mul_pow]
    norm_num
  rw [hs]
  calc
    _ = (81 / 64 : ℝ) *
        (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
          2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
          ((zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 * (8 / 9 : ℝ) ^ N) +
        (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) *
          ((zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 * (1 / 2 : ℝ) ^ N) := by ring
    _ = _ := by rw [ha, hb]

/-- An explicit geometric error bound for the actual interaction outside
the shrinking resonant region, uniform over all divisor cutoffs. -/
theorem norm_zetaMoebiusWeightedFourierPart_shrinking_compl_le (p : Polynomial ℂ)
    (D N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaMoebiusWeightedFourierPart p D N y
      (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))ᶜ‖ ≤
      zetaMoebiusLogMajorantMass (5 / 4) *
        ((81 / 64 : ℝ) *
          (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
            2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) * (8192 / 8649 : ℝ) ^ N +
          (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k) * (512 / 961 : ℝ) ^ N) := by
  have h := mul_le_mul_of_nonneg_left (sum_norm_cyclicSecond_quarterKernel_le p N y hN)
    (mul_nonneg (sq_nonneg ((zetaMoebiusResonanceThreshold N)⁻¹))
      (zetaMoebiusLogMajorantMass_nonneg (5 / 4)))
  apply (norm_zetaMoebiusWeightedFourierPart_compl_le p D N 2 y
    (zetaMoebiusResonanceThreshold_pos N)).trans
  rw [← shrinking_gap_budget_eq p N y hN]
  simpa only [mul_left_comm, mul_assoc] using h

/-- The complete difference allowance still vanishes after paying for
the shrinking symbol gap. Both geometric rates are strictly below one. -/
theorem tendsto_shrinking_gap_cyclicSecond_quarterKernel (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ (zetaMoebiusResonanceThreshold N)⁻¹ ^ 2 *
      ∑ j, ‖(cyclicDifference^[2] (zetaQuarterKernelSamples p N y)) j‖) atTop (𝓝 0) := by
  have ha := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 8192 / 8649)
    (by norm_num : (8192 / 8649 : ℝ) < 1)
  have hb := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 512 / 961)
    (by norm_num : (512 / 961 : ℝ) < 1)
  have h := (ha.const_mul ((81 / 64 : ℝ) *
    (zetaQuarterKernelSecondConstant p y * zetaQuarterKernelSpatialMass +
      2 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k))).add
      (hb.const_mul (8 * ∑ k ∈ p.support, ‖p.coeff k‖ * (8 : ℝ) ^ k))
  simp only [mul_zero, add_zero] at h
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun N ↦ mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))))
    ?_ h
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [← shrinking_gap_budget_eq p N y hN]
  exact mul_le_mul_of_nonneg_left (sum_norm_cyclicSecond_quarterKernel_le p N y hN) (sq_nonneg _)

/-- Even outside the geometrically shrinking resonant region, the
actual weighted arithmetic interaction tends to zero for every moving
divisor schedule. No conjectural cancellation premise is used. -/
theorem tendsto_zetaMoebiusWeightedFourierPart_shrinking_compl (p : Polynomial ℂ)
    (D : ℕ → ℕ) (y : ℝ) :
    Tendsto (fun N ↦ zetaMoebiusWeightedFourierPart p (D N) N y
      (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N))ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaMoebiusWeightedFourierPart_compl_le p (D N) N 2 y
    (zetaMoebiusResonanceThreshold_pos N))
  have h := (tendsto_shrinking_gap_cyclicSecond_quarterKernel p y).mul_const
    (zetaMoebiusLogMajorantMass (5 / 4))
  simpa only [zero_mul, mul_right_comm] using h

/-- Every hypothetical right-half zero retains its full negative
multiplicity in the geometrically shrinking resonant interaction. The
complement has been independently proved negligible, not assumed away. -/
theorem tendsto_zetaRightHalfMoebius_shrinking_resonance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusWeightedFourierPart (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N rho.1.im
        (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).mul_const (3 / 2 - rho.1.re)
  simp only [← pow_succ, zero_mul] at hp
  have hpc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  simp only [Function.comp_def, Complex.ofReal_pow, Complex.ofReal_zero] at hpc
  have hc := hpc.mul (tendsto_zetaMoebiusWeightedFourierPart_shrinking_compl
    (zetaRightHalfPoleJetFilter rho hrho)
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))) rho.1.im)
  have h := (tendsto_zetaRightHalfMoebiusBand rho hrho).sub hc
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaMoebiusBandFilter_eq_weighted_fourier_parts _ _ _ _
    (zetaMoebiusResonantModes N (zetaMoebiusResonanceThreshold N)), mul_add, add_sub_cancel_right]

end
end RiemannGaussian
