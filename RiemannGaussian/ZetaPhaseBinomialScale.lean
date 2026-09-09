/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseBinomialFloor

/-!
# Keeping the prime scale in the binomial phase floor

The fourth return is a largest normalized cost throughout `1 ≤ σ ≤ 5/4`.
Checking the two endpoint costs suffices because each relative lag cost
is monotone in `σ`. Consequently the arithmetic reserve retains the factor
`exp (-4 * (σ - 1) * log 2)` instead of replacing it by its strip minimum.

The return test still applies to every admissible real-frequency family.
Its specialization strengthens the literal near-edge zero inequality;
the global signed bound needed for RH remains open.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian
noncomputable section

private theorem lag_cost_between {L C x lo hi σ : ℝ} (hL : 0 ≤ L)
    (hlo : lo ≤ σ) (hhi : σ ≤ hi)
    (hl : L * Real.exp (lo * x) ≤ C) (hh : L * Real.exp (hi * x) ≤ C) :
    L * Real.exp (σ * x) ≤ C := by
  by_cases hx : 0 ≤ x
  · exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hx)) hL).trans hh
  · exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo (le_of_not_ge hx))) hL).trans hl

private theorem exp_nat_log_two (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem exp_four_log_two : Real.exp ((4 : ℝ) * Real.log 2) = 16 := by
  have h := exp_nat_log_two 4
  norm_num at h
  exact h

private theorem exp_five_log_two : Real.exp ((5 : ℝ) * Real.log 2) = 32 := by
  have h := exp_nat_log_two 5
  norm_num at h
  exact h

private theorem lag_nonneg (k : ℕ) :
    0 ≤ zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) k := by
  unfold zetaPhaseReturnCorrelation
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by
    simp only [zetaPhaseBinomialTest]
    split_ifs <;> positivity

set_option maxRecDepth 4096 in
private theorem unit_cost (k : ℕ) (hk : k ∈ Finset.range 10) :
    zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1) *
      (2 : ℝ) ^ (k + 1) ≤ 1240320 := by
  have hn : ∀ j : Fin 10,
      (∑ i : Fin 11, ∑ l : Fin 11,
        if Nat.dist i.val l.val = j.val + 1 then
          (10 : ℕ).choose i.val * (10 : ℕ).choose l.val else 0) *
            2 ^ (j.val + 1) ≤ 1240320 := by
    decide
  dsimp only [zetaPhaseReturnCorrelation, zetaPhaseBinomialTest]
  exact_mod_cast hn ⟨k, Finset.mem_range.mp hk⟩

private theorem relative_high_cost (k : ℕ) (hk : k ∈ Finset.range 10) :
    zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1) *
      Real.exp ((5 / 4 : ℝ) * (((k + 1 : ℕ) : ℝ) - 4) * Real.log 2) ≤ 77520 := by
  have h := zetaPhaseBinomialTest_ten_cost (σ := 5 / 4) le_rfl k hk
  rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hm := mul_le_mul_of_nonneg_right h
    (Real.exp_pos ((5 / 4 : ℝ) * (((k + 1 : ℕ) : ℝ) - 4) * Real.log 2)).le
  rw [mul_assoc (Real.log 2), ← Real.exp_add,
    show -(5 / 4 : ℝ) * (((k + 1 : ℕ) : ℝ) * Real.log 2) +
        (5 / 4 : ℝ) * (((k + 1 : ℕ) : ℝ) - 4) * Real.log 2 =
      -((5 : ℝ) * Real.log 2) by ring,
    Real.exp_neg, exp_five_log_two] at hm
  apply (mul_le_mul_iff_right₀ (show 0 < Real.log 2 / 2480640 by positivity)).mp
  convert hm using 1 <;> ring

/-- The fourth lag controls every actual prime-power cost across the
whole strip. The dependence on the evaluation point is retained exactly. -/
theorem zetaPhaseBinomialTest_ten_scaled_cost {σ : ℝ}
    (hσ : 1 ≤ σ) (hσle : σ ≤ 5 / 4) (k : ℕ) (hk : k ∈ Finset.range 10) :
    (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
      zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1) ≤
        zetaPhasePrimeWeight σ (2 ^ (k + 1)) := by
  let L := zetaPhaseReturnCorrelation (zetaPhaseBinomialTest 10) (k + 1)
  have hl : L * Real.exp (1 *
      ((((k + 1 : ℕ) : ℝ) - 4) * Real.log 2)) ≤ 77520 := by
    rw [show (1 : ℝ) * ((((k + 1 : ℕ) : ℝ) - 4) * Real.log 2) =
      ((k + 1 : ℕ) : ℝ) * Real.log 2 - (4 : ℝ) * Real.log 2 by ring,
      Real.exp_sub, exp_nat_log_two (k + 1), exp_four_log_two]
    have h := unit_cost k hk
    dsimp only [L]
    norm_num only [pow_succ, pow_zero] at *
    nlinarith only [h]
  have hh : L * Real.exp ((5 / 4 : ℝ) *
      ((((k + 1 : ℕ) : ℝ) - 4) * Real.log 2)) ≤ 77520 := by
    simpa only [mul_assoc] using relative_high_cost k hk
  have hr := lag_cost_between (lag_nonneg (k + 1)) hσ hσle hl hh
  have hm := mul_le_mul_of_nonneg_right hr
    (Real.exp_pos (-(σ * ((k + 1 : ℕ) : ℝ) * Real.log 2))).le
  rw [mul_assoc, ← Real.exp_add,
    show σ * ((((k + 1 : ℕ) : ℝ) - 4) * Real.log 2) +
        -(σ * ((k + 1 : ℕ) : ℝ) * Real.log 2) = -(4 * σ * Real.log 2) by ring] at hm
  have hf := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ Real.log 2 / 77520 by positivity)
  rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  rw [show -σ * (((k + 1 : ℕ) : ℝ) * Real.log 2) =
    -(σ * ((k + 1 : ℕ) : ℝ) * Real.log 2) by ring]
  nlinarith only [hf]

/-- Every frequency's binomial energy survives into the arithmetic
bound at its actual linked phase. This can be stronger at specific heights
than the uniform estimate obtained by keeping only the zero frequency. -/
theorem zetaPhase_binomial_scaled_energy_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (hσle : σ ≤ 5 / 4) (y : ℝ) :
    (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
        ((∑' n, a n * (2 + 2 * Real.cos (ω n * (y * Real.log 2))) ^ 10) -
          184756 * (∑' n, a n)) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have h := zetaPhase_binomial_primePower_energy_le ha hs hP hσ Nat.prime_two 10
    (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520)
    (zetaPhaseBinomialTest_ten_scaled_cost hσ.le hσle) y
  have he : (20 : ℕ).choose 10 = 184756 := by decide
  norm_num only [show 2 * 10 = (20 : ℕ) from rfl, he, Nat.cast_ofNat] at h
  exact h

/-- The scale-dependent reserve applies to every admissible family,
with the same exact zero-frequency source and diagonal mass cost. -/
theorem zetaPhase_binomial_primePower_scaled_floor {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {σ : ℝ} (hσ : 1 < σ) (hσle : σ ≤ 5 / 4) (y : ℝ) :
    (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
        (1048576 * a r - 184756 * (∑' n, a n)) ≤
      ∑' m, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have h := zetaPhase_returnCorrelation_primePower_floor ha hs hP r hr hσ Nat.prime_two
    (zetaPhaseBinomialTest 10)
    (v := Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) (by positivity)
    (zetaPhaseBinomialTest_ten_scaled_cost hσ.le hσle) y
  rw [zetaPhaseBinomialTest_sum, zetaPhaseBinomialTest_sum_sq] at h
  have he : (20 : ℕ).choose 10 = 184756 := by decide
  norm_num only [show 2 * 10 = (20 : ℕ) from rfl, he, Nat.cast_ofNat, pow_succ, pow_zero] at h
  nlinarith only [h]

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The exact optimizer's energy is a finite expression in its nine
proved coefficients, including the zero frequency and all eight modes. -/
theorem phaseContactExact_binomial_energy_eq_finite (θ : ℝ) :
    (∑' n, phaseContactExactFamily n * (2 + 2 * Real.cos ((n : ℝ) * θ)) ^ 10) =
      ∑ i : Fin 9, phaseContactExactCoefficients i *
        (2 + 2 * Real.cos ((phaseContactFrequency i : ℝ) * θ)) ^ 10 :=
  (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
    (fun n ↦ (2 + 2 * Real.cos ((n : ℝ) * θ)) ^ 10)).tsum_eq

/-- The full energy source always dominates the previously certified
uniform source. Its additional phase information cannot weaken that bound. -/
theorem phaseContactExact_binomial_energy_source_lower (θ : ℝ) :
    (46790 : ℝ) ≤
      (∑' n, phaseContactExactFamily n * (2 + 2 * Real.cos ((n : ℝ) * θ)) ^ 10) -
        184756 * (∑' n, phaseContactExactFamily n) := by
  have h := (hasSum_zetaPhase_binomial_energy (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable 10 θ).summable.le_tsum 0
    (fun n _ ↦ mul_nonneg (phaseContactExactFamily_nonneg n)
      (pow_nonneg (by linarith [Real.neg_one_le_cos ((n : ℝ) * θ)]) _))
  norm_num at h
  nlinarith only [h, phaseContactExactFamily_binomial_source_lower]

private theorem scaled_coefficient_lower (σ : ℝ) :
    (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) ≤
      (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) * 46790 := by
  have hb : (16 / 40 : ℝ) ≤ (Real.log 2 / 77520) * 46790 := by
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(4 * σ * Real.log 2))).le
  have he : Real.exp (-4 * (σ - 1) * Real.log 2) =
      Real.exp (-(4 * σ * Real.log 2)) * 16 := by
    rw [show -4 * (σ - 1) * Real.log 2 =
      -(4 * σ * Real.log 2) + (4 : ℝ) * Real.log 2 by ring,
      Real.exp_add, exp_four_log_two]
  rw [he]
  nlinarith only [hm]

/-- The phase-sensitive energy reserve dominates the scale-dependent
uniform reserve at every angle. Both comparisons stay available. -/
theorem phaseContactExact_binomial_energy_reserve_ge_scaled (σ θ : ℝ) :
    (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) ≤
      (Real.log 2 * Real.exp (-(4 * σ * Real.log 2)) / 77520) *
        ((∑' n, phaseContactExactFamily n * (2 + 2 * Real.cos ((n : ℝ) * θ)) ^ 10) -
          184756 * (∑' n, phaseContactExactFamily n)) := by
  exact (scaled_coefficient_lower σ).trans
    (mul_le_mul_of_nonneg_left (phaseContactExact_binomial_energy_source_lower θ)
      (by positivity))

/-- The exact optimizer pays a reserve tending to `1/40` as `σ` tends
to one from above. The real scale is preserved at every height. -/
theorem phaseContactExact_binomial_scaled_arithmetic_floor {σ : ℝ}
    (hσ : 1 < σ) (hσle : σ ≤ 5 / 4) (y : ℝ) :
    (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) ≤
      ∑' m, zetaPhasePrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  exact (phaseContactExact_binomial_energy_reserve_ge_scaled σ (y * Real.log 2)).trans
    (zetaPhase_binomial_scaled_energy_le (ω := fun n ↦ (n : ℝ))
      phaseContactExactFamily_nonneg exact_summable phaseContactExactFamily_kernel_nonneg
      hσ hσle y)

/-- Retaining the scale always recovers the earlier uniform `1/80`
floor; no point in the previously proved strip is lost. -/
theorem phaseContactExact_binomial_scaled_floor_ge_uniform {σ : ℝ}
    (hσ : σ ≤ 5 / 4) :
    (1 / 80 : ℝ) ≤ (1 / 40 : ℝ) * Real.exp (-4 * (σ - 1) * Real.log 2) := by
  have he : -Real.log 2 ≤ -4 * (σ - 1) * Real.log 2 := by
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h := Real.exp_le_exp.mpr he
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- The whole binomial frequency energy enters the actual zero
budget. The ordinate determines its linked prime phases, while the full
multiplicity, source, height sum and pole correction remain present. -/
theorem phaseContactExact_binomial_energy_zero_budget (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) +
      ((1 - rho.1.re) * Real.log 2 / 1240320) *
        Real.exp (-13 * (1 - rho.1.re) * Real.log 2) *
          ((∑' n, phaseContactExactFamily n *
            (2 + 2 * Real.cos ((n : ℝ) * (rho.1.im * Real.log 2))) ^ 10) -
              184756 * (∑' n, phaseContactExactFamily n)) ≤
      448 * (1 - rho.1.re) * (∑' n, phaseContactExactFamily n *
        localZetaLogHeight ((n : ℝ) * rho.1.im)) +
        (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
          (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := zetaPhase_binomial_scaled_energy_le (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable phaseContactExactFamily_kernel_nonneg
    (by linarith : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re))
    (by linarith : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4) rho.1.im
  rw [show -(4 * (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) * Real.log 2) =
    -13 * (1 - rho.1.re) * Real.log 2 - (4 : ℝ) * Real.log 2 by ring,
    Real.exp_sub, exp_four_log_two] at hf
  change _ ≤ ∑' m, zetaPhasePrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
    phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m) at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  nlinarith only [hm, h]

/-- The explicit zero source keeps the ordinate-dependent energy
instead of replacing it by its constant lower bound. -/
theorem phaseContactExact_binomial_energy_zero_source (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    (11 / 625 : ℝ) + ((1 - rho.1.re) * Real.log 2 / 1240320) *
        Real.exp (-13 * (1 - rho.1.re) * Real.log 2) *
          ((∑' n, phaseContactExactFamily n *
            (2 + 2 * Real.cos ((n : ℝ) * (rho.1.im * Real.log 2))) ^ 10) -
              184756 * (∑' n, phaseContactExactFamily n)) ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phaseContactExact_binomial_energy_zero_budget rho hrho
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

/-- A phase-sensitive nonvanishing test for the literal zeta function.
Every phase in its threshold is an explicit function of the tested point;
no arithmetic cancellation hypothesis is assumed. -/
theorem phaseContactExact_binomial_energy_exclusion (s : ℂ) (hs : 15 / 16 ≤ s.re)
    (hy : 1 ≤ |s.im|)
    (hgap : 448 * (1 - s.re) * ((61 / 100 : ℝ) * localZetaLogHeight s.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
      (11 / 625 : ℝ) + ((1 - s.re) * Real.log 2 / 1240320) *
        Real.exp (-13 * (1 - s.re) * Real.log 2) *
          ((∑' n, phaseContactExactFamily n *
            (2 + 2 * Real.cos ((n : ℝ) * (s.im * Real.log 2))) ^ 10) -
              184756 * (∑' n, phaseContactExactFamily n))) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  exact (not_lt_of_ge (phaseContactExact_binomial_energy_zero_source rho hs)) hgap

/-- The literal zero budget retains the larger scale-dependent
reserve, together with multiplicity, all phase heights and the pole term. -/
theorem phaseContactExact_binomial_scaled_zero_budget (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) +
          ((1 - rho.1.re) / 40) * Real.exp (-13 * (1 - rho.1.re) * Real.log 2) ≤
      448 * (1 - rho.1.re) * (∑' n, phaseContactExactFamily n *
        localZetaLogHeight ((n : ℝ) * rho.1.im)) +
        (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
          (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := phaseContactExact_binomial_scaled_arithmetic_floor
    (by linarith : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re))
    (by linarith : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4) rho.1.im
  rw [show -4 * (1 + (13 / 4 : ℝ) * (1 - rho.1.re) - 1) * Real.log 2 =
    -13 * (1 - rho.1.re) * Real.log 2 by ring] at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  nlinarith only [hm, h]

/-- Every zero near the right edge pays `d/40 * exp (-13*d*log 2)`.
The height allowance is unchanged and every arithmetic premise is proved. -/
theorem phaseContactExact_binomial_scaled_zero_source (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    (11 / 625 : ℝ) +
        ((1 - rho.1.re) / 40) * Real.exp (-13 * (1 - rho.1.re) * Real.log 2) ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phaseContactExact_binomial_scaled_zero_budget rho hrho
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

/-- The scale-aware arithmetic reserve gives a stronger explicit
zeta nonvanishing test, with no unproved arithmetic floor assumption. -/
theorem phaseContactExact_binomial_scaled_exclusion (s : ℂ) (hs : 15 / 16 ≤ s.re)
    (hy : 1 ≤ |s.im|)
    (hgap : 448 * (1 - s.re) * ((61 / 100 : ℝ) * localZetaLogHeight s.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
      (11 / 625 : ℝ) + ((1 - s.re) / 40) * Real.exp (-13 * (1 - s.re) * Real.log 2)) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  exact (not_lt_of_ge (phaseContactExact_binomial_scaled_zero_source rho hs)) hgap

end
end RiemannGaussian
