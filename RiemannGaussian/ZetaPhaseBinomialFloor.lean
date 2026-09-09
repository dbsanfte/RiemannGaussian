/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseAutocorrelation

/-!
# An arithmetic floor from the binomial phase test

The degree-ten binomial test retains all ten nonzero return lags. Their
actual geometric prime-power costs are bounded exactly, using integer
fourth powers. This gives an all-family arithmetic inequality and a
stronger floor for the already defined exact phase optimizer.

No phase coefficients are fitted or changed. The resulting zero exclusion
is an improvement of the existing near-edge test, not a proof of the
global signed Suzuki inequality or of RH.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

private theorem binomial_ten_values : zetaPhaseBinomialTest 10 =
    ![(1 : ℝ), 10, 45, 120, 210, 252, 210, 120, 45, 10, 1] := by
  funext i
  fin_cases i <;> norm_num [zetaPhaseBinomialTest, Nat.choose]

private theorem binomial_ten_lag_nonneg (k : ℕ) :
    0 ≤ zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) k := by
  unfold zetaPhaseReturnCorrelation
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    by
      simp only [zetaPhaseBinomialTest]
      split_ifs <;> positivity

set_option maxRecDepth 4096 in
private theorem binomial_ten_lag_fourth (k : ℕ) (hk : k ∈ Finset.range 10) :
    zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1) ^ 4 *
      (2 : ℝ) ^ (5 * (k + 1)) ≤ 2480640 ^ 4 := by
  have hn : ∀ j : Fin 10,
      (∑ i : Fin 11, ∑ l : Fin 11,
        if Nat.dist i.val l.val = j.val + 1 then
          (10 : ℕ).choose i.val * (10 : ℕ).choose l.val else 0) ^ 4 *
            2 ^ (5 * (j.val + 1)) ≤ 2480640 ^ 4 := by
    decide
  dsimp only [zetaPhaseReturnCorrelation, zetaPhaseBinomialTest]
  exact_mod_cast hn ⟨k, Finset.mem_range.mp hk⟩

private theorem exp_quarter_nat_log_two (k : ℕ) :
    Real.exp ((5 / 4 : ℝ) * (k : ℝ) * Real.log 2) ^ 4 = (2 : ℝ) ^ (5 * k) := by
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (4 : ℝ) * (5 / 4 * (k : ℝ) * Real.log 2) =
    ((5 * k : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Every lag of the binomial test fits the unchanged amplitudes of
the first ten powers of two, uniformly throughout the stated strip. -/
theorem zetaPhaseBinomialTest_ten_cost {σ : ℝ} (hσle : σ ≤ 5 / 4)
    (k : ℕ) (hk : k ∈ Finset.range 10) :
    (Real.log 2 / 2480640) *
      zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1) ≤
        zetaPhasePrimeWeight σ (2 ^ (k + 1)) := by
  let L := zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1)
  have hL : 0 ≤ L := binomial_ten_lag_nonneg _
  have he : L * Real.exp ((5 / 4 : ℝ) * (k + 1 : ℕ) * Real.log 2) ≤ 2480640 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) ≤ 2480640)
    rw [mul_pow, exp_quarter_nat_log_two]
    exact binomial_ten_lag_fourth k hk
  have hexp : Real.exp (σ * (k + 1 : ℕ) * Real.log 2) ≤
      Real.exp ((5 / 4 : ℝ) * (k + 1 : ℕ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hσle (by positivity)) (by positivity)
  have heσ := (mul_le_mul_of_nonneg_left hexp hL).trans he
  have hscaled := mul_le_mul_of_nonneg_right heσ
    (Real.exp_pos (-(σ * (k + 1 : ℕ) * Real.log 2))).le
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hscaled
  calc
    _ ≤ (Real.log 2 / 2480640) *
        (2480640 * Real.exp (-(σ * (k + 1 : ℕ) * Real.log 2))) :=
      mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = Real.log 2 * Real.exp (-(σ * (k + 1 : ℕ) * Real.log 2)) := by ring
    _ = _ := by
      rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_pow, Real.log_pow]
      congr 2
      norm_num
      ring

/-- An explicit lower bound for every summable nonnegative phase
spectrum with nonnegative kernel. Its dependence on the zero-frequency
mass and total coefficient mass is exact and no optimizer is assumed. -/
theorem zetaPhase_binomial_primePower_floor {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {σ : ℝ} (hσ : 1 < σ) (hσle : σ ≤ 5 / 4) (y : ℝ) :
    (Real.log 2 / 2480640) * (1048576 * a r - 184756 * (∑' n, a n)) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have h := zetaPhase_returnCorrelation_primePower_floor ha hs hP r hr hσ Nat.prime_two
    (zetaPhaseBinomialTest 10) (v := Real.log 2 / 2480640) (by positivity)
    (zetaPhaseBinomialTest_ten_cost hσle) y
  rw [binomial_ten_values] at h
  norm_num [Fin.sum_univ_succ] at h
  nlinarith only [h]

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The existing exact optimizer has a positive binomial Gram source,
using the proved coefficient enclosures rather than numerical guesses. -/
theorem phaseContactExactFamily_binomial_source_lower :
    (46790 : ℝ) ≤ 1048576 * phaseContactExactFamily 0 -
      184756 * (∑' n, phaseContactExactFamily n) := by
  have h0 : (18453 / 100000 : ℝ) ≤ phaseContactExactFamily 0 := by
    have he := phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
    change phaseContactExactFamily 0 = phaseContactExactCoefficients 0 at he
    rw [he]
    have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 0)).1
    norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
    linarith
  have hA : (∑' n, phaseContactExactFamily n) ≤ (397 / 500 : ℝ) := by
    have he := (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
      (fun _ ↦ 1)).tsum_eq
    simp only [mul_one] at he
    change (∑' n, phaseContactExactFamily n) = _ at he
    rw [he]
    calc
      _ ≤ ∑ i : Fin 9, (phaseContactPrimalCenter i + 1 / 10 ^ 15) := by
        apply Finset.sum_le_sum
        intro i _
        linarith [(abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le i)).2]
      _ ≤ (397 / 500 : ℝ) := by
        norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ, Fin.sum_univ_succ]
  linarith

/-- The binomial test raises the independent arithmetic floor to
`1/80` throughout the same strip and at every height. The exact phase
optimizer and every actual prime-power coefficient remain unchanged. -/
theorem phaseContactExact_binomial_arithmetic_floor {σ : ℝ}
    (hσ : 1 < σ) (hσle : σ ≤ 5 / 4) (y : ℝ) :
    (1 / 80 : ℝ) ≤ ∑' m, zetaPhasePrimeWeight σ m *
      phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  have h := zetaPhase_binomial_primePower_floor (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable phaseContactExactFamily_kernel_nonneg
    0 (by norm_num) hσ hσle y
  have hs := mul_le_mul_of_nonneg_left phaseContactExactFamily_binomial_source_lower
    (show 0 ≤ Real.log 2 / 2480640 by positivity)
  have hb : (1 / 80 : ℝ) ≤ (Real.log 2 / 2480640) * 46790 := by
    linarith [Real.log_two_gt_d9]
  exact hb.trans (hs.trans h)

/-- The stronger arithmetic floor is retained in the literal zero
inequality, together with multiplicity, the exact source, all height
costs, and the oscillatory pole correction. -/
theorem phaseContactExact_binomial_zero_budget (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) + (1 - rho.1.re) / 80 ≤
      448 * (1 - rho.1.re) * (∑' n, phaseContactExactFamily n *
        localZetaLogHeight ((n : ℝ) * rho.1.im)) +
        (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
          (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := phaseContactExact_binomial_arithmetic_floor
    (by linarith : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re))
    (by linarith : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4) rho.1.im
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  nlinarith only [hm, h]

/-- Every zero near the right edge now pays the larger `d/80`
arithmetic reserve, with the other explicit constants unchanged. -/
theorem phaseContactExact_binomial_zero_source (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) / 80 ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phaseContactExact_binomial_zero_budget rho hrho
  have hd : 0 ≤ 1 - rho.1.re := (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (sub_nonneg.mpr hm)
  have hheight := mul_le_mul_of_nonneg_left (phaseContactExactFamily_height_le rho.1.im)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 448) hd)
  have hpole := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  simp only [div_eq_mul_inv] at hpole h ⊢
  nlinarith [phaseContactExactRoot_source_lower]

/-- The improved independent inequality gives a literal zeta
nonvanishing test. The strict numerical inequality describes the
excluded region and is not assumed for every point right of one half. -/
theorem phaseContactExact_binomial_exclusion (s : ℂ) (hs : 15 / 16 ≤ s.re)
    (hy : 1 ≤ |s.im|)
    (hgap : 448 * (1 - s.re) * ((61 / 100 : ℝ) * localZetaLogHeight s.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
      (11 / 625 : ℝ) + (1 - s.re) / 80) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  exact (not_lt_of_ge (phaseContactExact_binomial_zero_source rho hs)) hgap

end
end RiemannGaussian
