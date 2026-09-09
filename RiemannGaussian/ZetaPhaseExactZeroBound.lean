/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseZeroBudget
import RiemannGaussian.ZetaPhaseExactOptimizer
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual zero exclusion from the exact phase family and its true height cost

The exact optimizer is transported into the literal zeta inequality.
Separating the fixed constant-phase cost from the nonconstant coefficient
mass gives a smaller actual height budget than its original linear cost.
Every coefficient, positivity condition, and convergence hypothesis comes
from the already proved exact family. The remaining pole error and the
selected zero's analytic multiplicity are retained before a uniform margin
is deduced.

This improves the project's unconditional edge exclusion. It does not
close the independent global signed arithmetic bound or prove RH.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

private theorem exact_hasSum_mul (f : ℕ → ℝ) :
    HasSum (fun n ↦ phaseContactExactFamily n * f n)
      (∑ i : Fin 9, phaseContactExactCoefficients i * f (phaseContactFrequency i)) :=
  phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients f

private theorem exact_at_frequency (i : Fin 9) :
    phaseContactExactFamily (phaseContactFrequency i) = phaseContactExactCoefficients i :=
  phaseContactFrequencyFamily_apply phaseContactExactCoefficients i

private theorem exact_coefficient_le (i : Fin 9) :
    phaseContactExactCoefficients i ≤ phaseContactPrimalCenter i + 1 / 10 ^ 15 := by
  linarith [(abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le i)).2]

/-- The exact source efficiency has a proved rational lower bound; its
definition remains the isolated contact root, not a numerical constant. -/
theorem phaseContactExactRoot_source_lower : (11 / 625 : ℝ) ≤ phaseContactExactRoot 8 := by
  have hc : (11 / 625 : ℝ) + 1 / 10 ^ 30 ≤ phaseContactRootCenter 8 := by
    norm_num [phaseContactRootCenter, phaseContactRootCenterQ]
  have hd := (abs_le.mp ((norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) 8).trans
    phaseContactExactRoot_dist_le)).1
  change -(1 / 10 ^ 30 : ℝ) ≤ phaseContactExactRoot 8 - phaseContactRootCenter 8 at hd
  linarith

private theorem exact_zero_coefficient_le : phaseContactExactFamily 0 ≤ (37 / 200 : ℝ) := by
  have h := exact_coefficient_le 0
  have he := exact_at_frequency 0
  norm_num [phaseContactFrequency] at he
  rw [he]
  norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
  linarith

/-- The exact mass governing the growing logarithmic height cost is at
most `61/100`. All eight nonconstant frequencies are included. -/
theorem phaseContactExactFamily_oscillatoryMass_le :
    phaseOscillatoryMass phaseContactExactFamily ≤ (61 / 100 : ℝ) := by
  have he := (exact_hasSum_mul (fun _ ↦ 1)).tsum_eq
  simp only [mul_one] at he
  rw [exact_summable.tsum_eq_zero_add, Fin.sum_univ_succ] at he
  have h0 := exact_at_frequency 0
  norm_num [phaseContactFrequency] at h0
  rw [h0] at he
  have hm : phaseOscillatoryMass phaseContactExactFamily =
      ∑ i : Fin 8, phaseContactExactCoefficients i.succ := by
    unfold phaseOscillatoryMass
    linarith
  rw [hm]
  calc
    _ ≤ ∑ i : Fin 8, (phaseContactPrimalCenter i.succ + 1 / 10 ^ 15) :=
      Finset.sum_le_sum fun i _ ↦ exact_coefficient_le i.succ
    _ ≤ (61 / 100 : ℝ) := by
      norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ, Fin.sum_univ_succ]

private theorem log_le_power_majorant {n a b : ℕ} (hn : 0 < n) (h : n ≤ 2 ^ a * 3 ^ b) :
    Real.log (n : ℝ) ≤ (a : ℝ) * (347 / 500) + (b : ℝ) * (1099 / 1000) := by
  calc
    _ ≤ Real.log ((2 : ℝ) ^ a * 3 ^ b) :=
      Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast h)
    _ = (a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    _ ≤ _ := by
      gcongr
      · linarith [Real.log_two_lt_d9]
      · linarith [Real.log_three_lt_d9]

private def exact_log_ceiling : Fin 9 → ℚ :=
  ![0, 0, 347 / 500, 1099 / 1000, 347 / 250, 1041 / 500,
    2487 / 1000, 347 / 125, 3181 / 1000]

private theorem exact_log_le (i : Fin 9) :
    Real.log (phaseContactFrequency i : ℝ) ≤ (exact_log_ceiling i : ℝ) := by
  fin_cases i <;> norm_num [phaseContactFrequency, exact_log_ceiling]
  · linarith [Real.log_two_lt_d9]
  · linarith [Real.log_three_lt_d9]
  · convert log_le_power_majorant (n := 4) (a := 2) (b := 0) (by decide) (by decide) using 1 <;> norm_num
  · convert log_le_power_majorant (n := 7) (a := 3) (b := 0) (by decide) (by decide) using 1 <;> norm_num
  · convert log_le_power_majorant (n := 10) (a := 2) (b := 1) (by decide) (by decide) using 1 <;> norm_num
  · convert log_le_power_majorant (n := 13) (a := 4) (b := 0) (by decide) (by decide) using 1 <;> norm_num
  · convert log_le_power_majorant (n := 24) (a := 3) (b := 1) (by decide) (by decide) using 1 <;> norm_num

/-- The complete logarithmic frequency overhead of the exact family is
at most `1/4`, despite its separated high frequencies. -/
theorem phaseContactExactFamily_logFrequencyMass_le :
    phaseLogFrequencyMass phaseContactExactFamily ≤ (1 / 4 : ℝ) := by
  have hs := exact_hasSum_mul (fun n ↦ Real.log n)
  have he := hs.tsum_eq
  rw [hs.summable.tsum_eq_zero_add] at he
  simp only [Nat.cast_zero, Real.log_zero, mul_zero, zero_add] at he
  change phaseLogFrequencyMass phaseContactExactFamily = _ at he
  rw [he]
  calc
    _ ≤ ∑ i : Fin 9, phaseContactExactCoefficients i * (exact_log_ceiling i : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (exact_log_le i)
        (phaseContactExactCoefficients_pos i).le
    _ ≤ ∑ i : Fin 9, (phaseContactPrimalCenter i + 1 / 10 ^ 15) * (exact_log_ceiling i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right (exact_coefficient_le i)
      fin_cases i <;> norm_num [exact_log_ceiling]
    _ ≤ (1 / 4 : ℝ) := by
      norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ, exact_log_ceiling,
        Fin.sum_univ_succ]

private theorem log_twentyTwo_le : Real.log 22 ≤ (31 / 10 : ℝ) := by
  have h24 := log_le_power_majorant (n := 24) (a := 3) (b := 1) (by decide) (by decide)
  have hq := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 12)
  have he : Real.log (22 : ℝ) = Real.log 24 + Real.log (11 / 12) := by
    rw [← Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (by norm_num : (11 / 12 : ℝ) ≠ 0)]
    norm_num
  rw [he]
  norm_num at h24 hq
  linarith

/-- The exact family pays at most `61/100` of the growing logarithmic
height plus the fixed allowance `83/100`. This is its actual analytic cost. -/
theorem phaseContactExactFamily_height_le (y : ℝ) :
    (∑' n : ℕ, phaseContactExactFamily n * localZetaLogHeight ((n : ℝ) * y)) ≤
      (61 / 100 : ℝ) * localZetaLogHeight y + 83 / 100 := by
  have h := phase_height_le_split_budget phaseContactExactFamily_nonneg exact_summable
    (exact_hasSum_mul (fun n ↦ Real.log n)).summable y
    (exact_hasSum_mul (fun n ↦ localZetaLogHeight ((n : ℝ) * y))).summable
  have hL : 0 ≤ localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have h0 : 0 ≤ localZetaLogHeight 0 := by linarith [two_lt_localZetaLogHeight 0]
  have hl0 : localZetaLogHeight 0 ≤ (31 / 10 : ℝ) := by
    simpa [localZetaLogHeight] using log_twentyTwo_le
  have hc := mul_le_mul exact_zero_coefficient_le hl0 h0 (by norm_num : (0 : ℝ) ≤ 37 / 200)
  have hm := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le hL
  linarith [phaseContactExactFamily_logFrequencyMass_le]

/-- A uniform lower bound on logarithmic height used only to express
the final exclusion also in the usual reciprocal-logarithm form. -/
theorem three_lt_localZetaLogHeight (y : ℝ) : 3 < localZetaLogHeight y := by
  unfold localZetaLogHeight
  apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
  calc
    Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (11 / 4 : ℝ) ^ 3 := by gcongr; linarith [Real.exp_one_lt_d9]
    _ < |y| + 22 := by nlinarith [abs_nonneg y]

/-- A zero close to the right edge must pay for the exact source, its
excess multiplicity, and the complete signed prime work simultaneously.
The actual height cost and quadratic pole allowance are still uncompressed. -/
theorem phaseContactExact_source_add_primeWork_le (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaPhasePrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
          phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) * (∑' n : ℕ,
        phaseContactExactFamily n * localZetaLogHeight ((n : ℝ) * rho.1.im)) +
      (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
        (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phase_shifted_source_add_primeWork_le phaseContactExactFamily_nonneg
    exact_summable rho (by linarith : 3 / 4 ≤ rho.1.re)
    (by norm_num : (0 : ℝ) < 13 / 4) (by linarith : (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 1 / 4)
    (exact_hasSum_mul (fun n ↦ localZetaLogHeight ((n : ℝ) * rho.1.im))).summable
  have he : phaseShiftSource (phaseContactExactFamily 0)
      (phaseContactExactFamily 1 * (analyticZetaZeroMultiplicity rho : ℝ)) (13 / 4) =
      phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) := by
    rw [← phaseContactExactFamily_source]
    unfold phaseShiftSource phaseContactSource
    ring
  rwa [he] at h

/-- Every literal zero near the right edge obeys the sharpened quadratic
constraint. The coefficient and phase-positivity premises are all discharged
by the exact optimizer, including its separated higher frequencies. -/
theorem phaseContactExact_zero_source_le (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    (11 / 625 : ℝ) ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
      (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  have hd : 0 ≤ 1 - rho.1.re := (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (sub_nonneg.mpr hm)
  have hp : 0 ≤ (1 - rho.1.re) * (∑' m : ℕ,
      zetaPhasePrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) :=
    mul_nonneg hd (tsum_nonneg fun m ↦ mul_nonneg (zetaPhasePrimeWeight_nonneg _ m)
      (phaseContactExactFamily_kernel_nonneg _))
  have hheight := mul_le_mul_of_nonneg_left (phaseContactExactFamily_height_le rho.1.im)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 448) hd)
  have hpole := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  simp only [div_eq_mul_inv] at hpole h ⊢
  nlinarith [phaseContactExactRoot_source_lower]

/-- The exact family imposes an explicit arithmetic constraint on every
finite prime-phase window at a literal zero. The exact source and excess
multiplicity remain in the deficit, so a proved arithmetic lower bound can
be compared directly against it without rebuilding the analytic argument. -/
theorem phaseContactExact_finite_primeWork_le_zero_defect (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) (S : Finset ℕ) :
    (1 - rho.1.re) * (∑ m ∈ S,
      zetaPhasePrimeWeight (1 + (13 / 4 : ℝ) * (1 - rho.1.re)) m *
        phaseContactKernel phaseContactExactFamily (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 - phaseContactExactRoot 8 -
        (4 / 17 : ℝ) * phaseContactExactFamily 1 *
          ((analyticZetaZeroMultiplicity rho : ℝ) - 1) := by
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := zetaPhase_finite_primeWork_le (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable
    (fun t ↦ by simpa only [zetaPhaseKernel_natCast] using phaseContactExactFamily_kernel_nonneg t)
    (show 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re) by linarith) rho.1.im S
  simp only [zetaPhaseKernel_natCast] at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have hheight := mul_le_mul_of_nonneg_left (phaseContactExactFamily_height_le rho.1.im)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 448) hd.le)
  have hpole := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  simp only [div_eq_mul_inv] at hpole h ⊢
  nlinarith

/-- The actual height-dependent margin supplied by the exact family. -/
def phaseContactZeroMargin (y : ℝ) : ℝ :=
  1 / (15600 * localZetaLogHeight y + 21200)

private theorem phaseContactZeroMargin_small (y : ℝ) :
    phaseContactZeroMargin y < (1 / 16 : ℝ) := by
  have hL := three_lt_localZetaLogHeight y
  exact one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) (by linarith)

/-- The sharper height budget excludes every actual nontrivial zero from
the closed right-edge region, uniformly above absolute height one. -/
theorem phaseContact_margin_lt_one_sub_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : phaseContactZeroMargin rho.1.im < 1 - rho.1.re := by
  by_cases hrho : 15 / 16 ≤ rho.1.re
  · let d := 1 - rho.1.re
    let L := localZetaLogHeight rho.1.im
    have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
    have hdsmall : d ≤ 1 / 16 := by dsimp [d]; linarith
    have hL : 3 < L := three_lt_localZetaLogHeight rho.1.im
    have hgap := phaseContactExact_zero_source_le rho hrho
    change (11 / 625 : ℝ) ≤ 448 * d * ((61 / 100 : ℝ) * L + 83 / 100) +
      (793 / 400 : ℝ) * d ^ 2 / rho.1.im ^ 2 at hgap
    have hy2 : 1 ≤ rho.1.im ^ 2 := by nlinarith [sq_abs rho.1.im]
    have hquad : d ^ 2 / rho.1.im ^ 2 ≤ d / 16 := by
      have hdiv : d ^ 2 / rho.1.im ^ 2 ≤ d ^ 2 := div_le_self (sq_nonneg d) hy2
      nlinarith [mul_nonneg hd.le (show 0 ≤ 1 / 16 - d by linarith)]
    have hquad' := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 793 / 400)
    by_contra hn
    have hdm : d ≤ 1 / (15600 * L + 21200) := le_of_not_gt hn
    have hprod := (le_div_iff₀ (show 0 < 15600 * L + 21200 by positivity)).mp hdm
    rw [mul_div_assoc] at hgap
    nlinarith only [hgap, hquad', hprod, hd,
      mul_nonneg hd.le (show 0 ≤ L - 3 by linarith)]
  · exact (phaseContactZeroMargin_small rho.1.im).trans_le (by linarith)

/-- Completion reflection supplies the same strengthened left-edge margin. -/
theorem phaseContact_margin_lt_re (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) : phaseContactZeroMargin rho.1.im < rho.1.re := by
  have h := phaseContact_margin_lt_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_im,
      Complex.one_im, Complex.conj_im, sub_neg_eq_add, zero_add] using hy)
  simpa only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im,
    sub_neg_eq_add, zero_add, sub_sub_cancel] using h

/-- Every actual nontrivial zero above absolute height one lies strictly
inside the strip furnished by the exact family and its true height budget. -/
theorem nontrivialZetaZero_mem_phaseContact_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (phaseContactZeroMargin rho.1.im) (1 - phaseContactZeroMargin rho.1.im) :=
  ⟨phaseContact_margin_lt_re rho hy, by linarith [phaseContact_margin_lt_one_sub_re rho hy]⟩

/-- The literal zeta function is nonzero on the resulting closed
right-edge region, with no assumed arithmetic estimate. -/
theorem riemannZeta_ne_zero_of_phaseContact_margin {s : ℂ} (hy : 1 ≤ |s.im|)
    (hs : 1 - phaseContactZeroMargin s.im ≤ s.re) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith [phaseContactZeroMargin_small s.im]
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  have hgap := phaseContact_margin_lt_one_sub_re rho hy
  change phaseContactZeroMargin s.im < 1 - s.re at hgap
  linarith

/-- A simpler reciprocal-logarithm margin is strictly below the full
height-dependent margin for every height. -/
theorem phaseContact_uniform_margin_lt (y : ℝ) :
    1 / (23000 * localZetaLogHeight y) < phaseContactZeroMargin y := by
  have hL := three_lt_localZetaLogHeight y
  exact one_div_lt_one_div_of_lt (by positivity : 0 < 15600 * localZetaLogHeight y + 21200)
    (by linarith)

/-- The fully discharged reciprocal-logarithm strip improves the former
denominator `27500` to `23000` for all absolute heights at least one. -/
theorem nontrivialZetaZero_mem_phaseContact_reciprocal_log_strip (rho : NontrivialZetaZero)
    (hy : 1 ≤ |rho.1.im|) :
    rho.1.re ∈ Set.Ioo (1 / (23000 * localZetaLogHeight rho.1.im))
      (1 - 1 / (23000 * localZetaLogHeight rho.1.im)) := by
  have h := nontrivialZetaZero_mem_phaseContact_strip rho hy
  have hm := phaseContact_uniform_margin_lt rho.1.im
  exact ⟨hm.trans h.1, by linarith [h.2]⟩

/-- Literal zeta nonvanishing in the simpler uniform reciprocal-log region. -/
theorem riemannZeta_ne_zero_of_phaseContact_reciprocal_log_margin {s : ℂ}
    (hy : 1 ≤ |s.im|) (hs : 1 - 1 / (23000 * localZetaLogHeight s.im) ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_phaseContact_margin hy (by linarith [phaseContact_uniform_margin_lt s.im])

/-- The exact-family margin strictly improves the previous infinite-family
margin at every height, including the fixed and quadratic error allowances. -/
theorem infiniteHeight_margin_lt_phaseContact (y : ℝ) :
    1 / (27500 * localZetaLogHeight y) < phaseContactZeroMargin y := by
  have hL := three_lt_localZetaLogHeight y
  exact one_div_lt_one_div_of_lt (by positivity : 0 < 15600 * localZetaLogHeight y + 21200)
    (by linarith)

end

end RiemannGaussian
