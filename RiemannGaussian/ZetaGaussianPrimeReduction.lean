/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeCorrelation
import RiemannGaussian.ZetaPrimePowerMoments

/-!
# Independent reduction to ordinary Gaussian prime energy

At the current fixed-strip dilation, all proper prime powers and the two
auxiliary prime responses have one summable majorant independent of the
height, frequencies, prime set and dilation. An exact amplitude splitting
keeps the ordinary Gaussian prime phases unchanged. Young's inequality
pays every mixed quadratic term with an explicit tunable allowance.

The actual squared zero-source constraint therefore reduces to ordinary
Gaussian prime energy. With reciprocal-dilation tuning the normalized
additive allowance tends to zero for every moving family of bounded
nonconstant mass. The independent ordinary-prime energy bound and the
RH contradiction remain open; no larger zero-free region follows here.
-/

namespace RiemannGaussian.ZetaGaussianPrimeReduction
noncomputable section
open Complex
open ZetaGaussianScaledBandBudget ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open scoped Classical

/-- The fixed absolute-convergence line controlling the auxiliary responses. -/
def fixedLine : ℝ := 1 + DerivativeOrderComparison.delta 9

/-- The fixed comparison line lies strictly to the right of one. -/
theorem fixedLine_gt_one : 1 < fixedLine := by
  unfold fixedLine
  linarith [DerivativeOrderComparison.delta_pos 9]

/-- The retained ordinary-prime Gaussian amplitude. -/
def primeAmplitude (q : ℝ) (m : ℕ) : ℝ :=
  if m.Prime then ZetaGaussianPhaseArithmetic.amplitude (1 + shift q) (gaussianScale q) m else 0

/-- All other actual positive amplitudes, with the original multipliers. -/
def remainder (q : ℝ) (m : ℕ) : ℝ :=
  (if m.Prime then 0 else ZetaGaussianPhaseArithmetic.amplitude (1 + shift q) (gaussianScale q) m) +
    factor 9 (gaussianScale q) (shift q) * zetaPhasePrimeWeight (rightLine 9 (shift q)) m +
    ZetaSechPrimeBoundary.amplitude (rightLine 9 (shift q)) (verticalScale 9 (shift q)) m /
      (2 * halfWidth 9 (shift q))

/-- The full prime measure splits exactly, without a phase or endpoint change. -/
theorem amplitude_eq (q : ℝ) (m : ℕ) :
    ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) m =
      primeAmplitude q m + remainder q m := by
  unfold ZetaGaussianPrimeBlocks.amplitude primeAmplitude remainder
  split_ifs <;> ring

/-- The retained Gaussian-prime amplitudes are nonnegative. -/
theorem primeAmplitude_nonneg (q : ℝ) (m : ℕ) : 0 ≤ primeAmplitude q m := by
  unfold primeAmplitude
  split_ifs
  · exact ZetaGaussianPhaseArithmetic.amplitude_nonneg _ _ _
  · rfl

/-- Every component of the actual remainder is nonnegative. -/
theorem remainder_nonneg {q : ℝ} (hq : 1 ≤ q) (m : ℕ) : 0 ≤ remainder q m := by
  have hη := halfWidth_pos 9 (shift_bounds hq).1
  have hg : 0 ≤ if m.Prime then 0 else
      ZetaGaussianPhaseArithmetic.amplitude (1 + shift q) (gaussianScale q) m := by
    split_ifs
    · rfl
    · exact ZetaGaussianPhaseArithmetic.amplitude_nonneg _ _ _
  unfold remainder
  exact add_nonneg (add_nonneg hg (mul_nonneg (factor_bounds hq).1
    (zetaPhasePrimeWeight_nonneg _ _)))
      (div_nonneg (ZetaSechPrimeBoundary.amplitude_nonneg _ _ _) (by positivity))

/-- Each fixed nonnegative coefficient has decreasing exponential weight. -/
theorem expWeight_antitone {σ τ : ℝ} (h : σ ≤ τ) (m : ℕ) :
    Real.exp (-τ * Real.log m) ≤ Real.exp (-σ * Real.log m) := by
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right h (Real.log_natCast_nonneg m)]

/-- The right arithmetic line never approaches its fixed comparison line from below. -/
theorem fixedLine_le_rightLine {q : ℝ} (hq : 1 ≤ q) : fixedLine ≤ rightLine 9 (shift q) := by
  unfold fixedLine rightLine
  linarith [(shift_bounds hq).1]

/-- A fixed summable majorant for every separated remainder amplitude. -/
def majorant (m : ℕ) : ℝ :=
  zetaProperPrimePowerCoefficient m * zetaPrimeExpWeight 1 m +
    (1 / 50000 : ℝ) * zetaPhasePrimeWeight fixedLine m +
    94 * ZetaLogPrimeSeries.weight fixedLine m

/-- The same summable majorant works at every dilation and integer. -/
theorem remainder_le_majorant {q : ℝ} (hq : 1 ≤ q) (m : ℕ) :
    remainder q m ≤ majorant m := by
  have hx := (shift_bounds hq).1
  have hB := (gaussianScale_bounds hq).1
  have hη := halfWidth_pos 9 hx
  have hσ := fixedLine_le_rightLine hq
  have he : zetaPhasePrimeWeight (rightLine 9 (shift q)) m ≤ zetaPhasePrimeWeight fixedLine m :=
    mul_le_mul_of_nonneg_left (expWeight_antitone hσ m) ArithmeticFunction.vonMangoldt_nonneg
  have hl : ZetaLogPrimeSeries.weight (rightLine 9 (shift q)) m ≤
      ZetaLogPrimeSeries.weight fixedLine m :=
    mul_le_mul_of_nonneg_left (expWeight_antitone hσ m) (ZetaLogPrimeSeries.coefficient_nonneg m)
  have hb := (ZetaSechPrimeBoundary.amplitude_le
    (rightLine 9 (shift q)) (verticalScale 9 (shift q)) m).trans hl
  have hg : (if m.Prime then 0 else
      ZetaGaussianPhaseArithmetic.amplitude (1 + shift q) (gaussianScale q) m) ≤
        zetaProperPrimePowerCoefficient m * zetaPrimeExpWeight 1 m := by
    by_cases hp : m.Prime
    · simp [hp, zetaProperPrimePowerCoefficient]
    · simp only [hp, if_false, zetaProperPrimePowerCoefficient]
      have hw : GaussianFermiZeroPair.window (gaussianScale q) (Real.log m) ≤ 1 := by
        unfold GaussianFermiZeroPair.window
        exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log m)])
      apply (mul_le_of_le_one_right (zetaPhasePrimeWeight_nonneg (1 + shift q) m) hw).trans
      exact mul_le_mul_of_nonneg_left (expWeight_antitone (by linarith) m)
        ArithmeticFunction.vonMangoldt_nonneg
  have he' := mul_le_mul (factor_bounds hq).2 he (zetaPhasePrimeWeight_nonneg _ _)
    (by norm_num : (0 : ℝ) ≤ 1 / 50000)
  have hb' := mul_le_mul hb (geometry hq).2.2.1
    (by positivity : (0 : ℝ) ≤ 1 / (2 * halfWidth 9 (shift q)))
    (ZetaLogPrimeSeries.weight_nonneg fixedLine m)
  rw [mul_one_div] at hb'
  unfold remainder majorant
  nlinarith only [hg, he', hb']

/-- The uniform majorant has genuine finite total mass. -/
theorem summable_majorant : Summable majorant := by
  exact ((summable_zetaProperPrimePowerExpMass (by norm_num : (1 / 2 : ℝ) < 1)).add
    ((hasSum_zetaPhasePrimeWeight fixedLine_gt_one).summable.mul_left (1 / 50000 : ℝ))).add
      ((ZetaLogPrimeSeries.hasSum_weight fixedLine_gt_one).summable.mul_left 94)

/-- The entire fixed error allowance, independent of height and dilation. -/
def allowance : ℝ := zetaProperPrimePowerExpMass 1 +
  (1 / 50000 : ℝ) * (-logDeriv riemannZeta (fixedLine : ℂ)).re +
  94 * Real.log ‖riemannZeta (fixedLine : ℂ)‖

/-- The displayed fixed allowance is the genuine total mass of the majorant. -/
theorem hasSum_majorant : HasSum majorant allowance := by
  exact ((summable_zetaProperPrimePowerExpMass (by norm_num : (1 / 2 : ℝ) < 1)).hasSum.add
    ((hasSum_zetaPhasePrimeWeight fixedLine_gt_one).mul_left (1 / 50000 : ℝ))).add
      ((ZetaLogPrimeSeries.hasSum_weight fixedLine_gt_one).mul_left 94)

/-- Every part of the majorant is nonnegative. -/
theorem majorant_nonneg (m : ℕ) : 0 ≤ majorant m := by
  unfold majorant
  exact add_nonneg (add_nonneg
    (mul_nonneg (zetaProperPrimePowerCoefficient_nonneg m) (Real.exp_pos _).le)
    (mul_nonneg (by norm_num) (zetaPhasePrimeWeight_nonneg _ _)))
    (mul_nonneg (by norm_num) (ZetaLogPrimeSeries.weight_nonneg _ _))

/-- The actual fixed allowance is nonnegative. -/
theorem allowance_nonneg : 0 ≤ allowance := by
  rw [← hasSum_majorant.tsum_eq]
  exact tsum_nonneg majorant_nonneg

/-- The whole separated remainder is summable at every allowed dilation. -/
theorem summable_remainder {q : ℝ} (hq : 1 ≤ q) : Summable (remainder q) := by
  apply summable_majorant.of_norm_bounded
  intro m
  rw [Real.norm_eq_abs, abs_of_nonneg (remainder_nonneg hq m)]
  exact remainder_le_majorant hq m

/-- All proper powers and both auxiliary responses have bounded total mass. -/
theorem remainder_mass_le {q : ℝ} (hq : 1 ≤ q) : (∑' m, remainder q m) ≤ allowance := by
  rw [← hasSum_majorant.tsum_eq]
  exact (summable_remainder hq).tsum_le_tsum (remainder_le_majorant hq) summable_majorant

/-- The same fixed allowance controls every finite part of the remainder. -/
theorem finite_remainder_mass_le {q : ℝ} (hq : 1 ≤ q) (S : Finset ℕ) :
    (∑ m ∈ S, remainder q m) ≤ allowance := by
  exact ((summable_remainder hq).sum_le_tsum S (fun m _ => remainder_nonneg hq m)).trans
    (remainder_mass_le hq)

/-- Every finite cosine phase sum obeys the same complete error mass. -/
theorem finite_remainder_cosine_le {q : ℝ} (hq : 1 ≤ q) (S : Finset ℕ) (v : ℝ) :
    |∑ m ∈ S, remainder q m * Real.cos (v * Real.log m)| ≤ allowance := by
  calc
    _ ≤ ∑ m ∈ S, |remainder q m * Real.cos (v * Real.log m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, remainder q m := by
      apply Finset.sum_le_sum
      intro m _
      rw [abs_mul, abs_of_nonneg (remainder_nonneg hq m)]
      exact mul_le_of_le_one_right (remainder_nonneg hq m) (Real.abs_cos_le_one _)
    _ ≤ _ := finite_remainder_mass_le hq S

/-- The full real pair energy can be reduced to the ordinary-prime Gaussian
part, with every mixed term paid through an explicit Young allowance. -/
theorem real_energy_le_prime_energy {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {q ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε)
    (t : ℝ) (S : Finset ℕ) :
    ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω
        (ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q)) t S ≤
      (1 + ε) * ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω (primeAmplitude q) t S +
        (1 + 1 / ε) * (∑' n, a n) * allowance ^ 2 := by
  have hf := ZetaGaussianPrimeCorrelation.hasSum_realPrimeEnergy (ω := ω) ha hs
    (ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q)) t S
  have hp := ZetaGaussianPrimeCorrelation.hasSum_realPrimeEnergy (ω := ω) ha hs
    (primeAmplitude q) t S
  have hr := (hp.mul_left (1 + ε)).add (hs.hasSum.mul_left ((1 + 1 / ε) * allowance ^ 2))
  rw [← hf.tsum_eq]
  have he : (1 + ε) * ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω (primeAmplitude q) t S +
        (1 + 1 / ε) * (∑' n, a n) * allowance ^ 2 =
      (1 + ε) * ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω (primeAmplitude q) t S +
        ((1 + 1 / ε) * allowance ^ 2) * (∑' n, a n) := by ring
  rw [he, ← hr.tsum_eq]
  apply hf.summable.tsum_le_tsum _ hr.summable
  intro n
  let g := ∑ m ∈ S, primeAmplitude q m * Real.cos (ω n * (t * Real.log m))
  let r := ∑ m ∈ S, remainder q m * Real.cos (ω n * (t * Real.log m))
  have hsum : (∑ m ∈ S, ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) m *
      Real.cos (ω n * (t * Real.log m))) = g + r := by
    simp only [amplitude_eq, add_mul, Finset.sum_add_distrib, g, r]
  have hrbound : |r| ≤ allowance := by
    simpa only [r, mul_assoc] using finite_remainder_cosine_le hq S (ω n * t)
  have hrsq : r ^ 2 ≤ allowance ^ 2 := by
    have hmul := mul_self_le_mul_self (abs_nonneg r) hrbound
    nlinarith only [hmul, sq_abs r]
  have hy : (g + r) ^ 2 ≤ (1 + ε) * g ^ 2 + (1 + 1 / ε) * allowance ^ 2 := by
    have hi : (ε * g - r) ^ 2 / ε =
        (1 + ε) * g ^ 2 + (1 + 1 / ε) * r ^ 2 - (g + r) ^ 2 := by
      field_simp
      ring
    have hy0 := div_nonneg (sq_nonneg (ε * g - r)) hε.le
    rw [hi] at hy0
    have hm := mul_le_mul_of_nonneg_left hrsq (by positivity : 0 ≤ 1 + 1 / ε)
    linarith only [hy0, hm]
  rw [hsum]
  have h := mul_le_mul_of_nonneg_left hy (ha n)
  dsimp only [g] at h
  nlinarith only [h]

/-- The genuine nonconstant coefficient mass is the full mass minus its zero channel. -/
theorem mass_eq_sum_sub {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) :
    ZetaAngularPhaseAllowance.mass a = (∑' n, a n) - a 0 := by
  have h := (hasSum_ite_eq (0 : ℕ) (a 0)).add
    (ZetaAngularPhaseAllowance.tail_summable ha hs).hasSum
  have hh : HasSum a (a 0 + ZetaAngularPhaseAllowance.mass a) := by
    apply h.congr_fun
    intro n
    by_cases hn : n = 0 <;> simp [ZetaAngularPhaseAllowance.tail, hn]
  have he := hs.hasSum.unique hh
  linarith

/-- Removing the zero frequency from the real energy is an exact identity. -/
theorem real_energy_tail {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω0 : ω 0 = 0) (W : ℕ → ℝ) (t : ℝ) (S : Finset ℕ) :
    ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω W t S - a 0 * (∑ p ∈ S, W p) ^ 2 =
      ZetaGaussianPrimeCorrelation.realPrimeEnergy (ZetaAngularPhaseAllowance.tail a) ω W t S := by
  have ht := ZetaGaussianPrimeCorrelation.hasSum_realPrimeEnergy (ω := ω)
    (ZetaAngularPhaseAllowance.tail_nonneg ha) (ZetaAngularPhaseAllowance.tail_summable ha hs) W t S
  have h := (hasSum_ite_eq (0 : ℕ) (a 0 * (∑ p ∈ S, W p) ^ 2)).add ht
  have hh : HasSum (fun n => a n *
      (∑ p ∈ S, W p * Real.cos (ω n * (t * Real.log p))) ^ 2)
      (a 0 * (∑ p ∈ S, W p) ^ 2 +
        ZetaGaussianPrimeCorrelation.realPrimeEnergy (ZetaAngularPhaseAllowance.tail a) ω W t S) := by
    apply h.congr_fun
    intro n
    by_cases hn : n = 0
    · subst n
      simp [ZetaAngularPhaseAllowance.tail, hω0]
    · simp [ZetaAngularPhaseAllowance.tail, hn]
  have he := (ZetaGaussianPrimeCorrelation.hasSum_realPrimeEnergy (ω := ω) ha hs W t S).unique hh
  linarith

/-- The nonconstant real energy retains only ordinary Gaussian primes on
its main term; the entire remaining quadratic cost is explicit. -/
theorem nonconstant_energy_le_prime {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω0 : ω 0 = 0)
    {q ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (t : ℝ) (S : Finset ℕ) :
    ZetaGaussianPrimeCorrelation.realPrimeEnergy a ω
        (ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q)) t S -
      a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) p) ^ 2 ≤
      (1 + ε) * ZetaGaussianPrimeCorrelation.realPrimeEnergy (ZetaAngularPhaseAllowance.tail a)
        ω (primeAmplitude q) t S +
        (1 + 1 / ε) * ZetaAngularPhaseAllowance.mass a * allowance ^ 2 := by
  rw [real_energy_tail ha hs hω0]
  exact real_energy_le_prime_energy (ZetaAngularPhaseAllowance.tail_nonneg ha)
    (ZetaAngularPhaseAllowance.tail_summable ha hs) hq hε t S

/-- The current scaled shifts satisfy the original zero-budget geometry. -/
theorem shift_le_delta_quarter {q : ℝ} (hq : 1 ≤ q) :
    shift q ≤ DerivativeOrderComparison.delta 9 / 4 := by
  apply (shift_bounds hq).2.trans
  norm_num [GaussianStripProfile.shift, GaussianStripProfile.width,
    DerivativeOrderComparison.delta, DerivativePowerExponents.alpha]

/-- The full squared source constraint now requires only ordinary Gaussian
prime energy, with all auxiliary terms and mixed products independently paid. -/
theorem finite_source_le_prime_energy {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => ZetaAngularPhaseAllowance.tail a n * Real.log (ω n)))
    {q ε M : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (hM : 0 ≤ M)
    (t : ℝ) (Z : Finset NontrivialZetaZero) (hscale : 1 ≤ ZetaNearOneBudgetLimit.scale t)
    (S : Finset ℕ) :
    (max 0 (a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) p) +
        (a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated (gaussianScale q)
          (halfWidth 9 (shift q)) (ZetaNearOneLocalDisc.center (shift q) t) ρ) -
        exactBudget 9 (gaussianScale q) M (shift q) t a ω)) ^ 2 ≤
      (1 + ε) * ZetaAngularPhaseAllowance.mass a *
        ZetaGaussianPrimeCorrelation.realPrimeEnergy (ZetaAngularPhaseAllowance.tail a)
          ω (primeAmplitude q) t S +
      (1 + 1 / ε) * (ZetaAngularPhaseAllowance.mass a) ^ 2 * allowance ^ 2 := by
  have hf := ZetaGaussianPrimeCorrelation.finite_source_correlation_constraint
    ha hs hP hω0 hω1 hω hlog 9 (by norm_num) (gaussianScale_bounds hq).1
    (shift_bounds hq).1 (shift_le_delta_quarter hq) hM t Z hscale S
  rw [← mass_eq_sum_sub ha hs] at hf
  have hr := nonconstant_energy_le_prime ha hs hω0 hq hε t S
  have hm : 0 ≤ ZetaAngularPhaseAllowance.mass a :=
    tsum_nonneg (ZetaAngularPhaseAllowance.tail_nonneg ha)
  have h := mul_le_mul_of_nonneg_left hr hm
  refine hf.trans ?_
  nlinarith only [h]

/-- The full additive energy cost when the Young parameter is reciprocal dilation. -/
def energyAllowance (q m : ℝ) : ℝ := (1 + q) * m ^ 2 * allowance ^ 2

/-- At bounded nonconstant mass, the complete normalized error is at most a fixed reciprocal dilation. -/
theorem normalized_energyAllowance_le {q m A : ℝ} (hq : 1 ≤ q) (hm : 0 ≤ m) (hA : m ≤ A) :
    energyAllowance q m / q ^ 2 ≤ 2 * A ^ 2 * allowance ^ 2 / q := by
  have hq0 : 0 < q := by linarith
  have hs : m ^ 2 ≤ A ^ 2 := by nlinarith only [mul_self_le_mul_self hm hA]
  have hnum : (1 + q) * m ^ 2 * allowance ^ 2 ≤ 2 * q * A ^ 2 * allowance ^ 2 := by
    have h := mul_le_mul (by linarith : 1 + q ≤ 2 * q) hs (sq_nonneg m)
      (by positivity : 0 ≤ 2 * q)
    exact mul_le_mul_of_nonneg_right h (sq_nonneg allowance)
  calc
    _ ≤ (2 * q * A ^ 2 * allowance ^ 2) / q ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg q)
    _ = _ := by field_simp

/-- Every moving family with uniformly bounded nonconstant mass has vanishing
normalized remainder energy, independently of its frequencies and prime sets. -/
theorem tendsto_normalized_energyAllowance (q m : ℕ → ℝ) (hq : ∀ N, 1 ≤ q N)
    (hqt : Filter.Tendsto q Filter.atTop Filter.atTop) (hm : ∀ N, 0 ≤ m N)
    (A : ℝ) (hA : ∀ N, m N ≤ A) :
    Filter.Tendsto (fun N => energyAllowance (q N) (m N) / (q N) ^ 2)
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun N => 2 * A ^ 2 * allowance ^ 2 / q N)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hqt).const_mul (2 * A ^ 2 * allowance ^ 2)
  apply squeeze_zero _ _ hlim
  · intro N
    have hqN := hq N
    exact div_nonneg (by unfold energyAllowance; positivity) (sq_nonneg (q N))
  · intro N
    exact normalized_energyAllowance_le (hq N) (hm N) (hA N)

/-- Reciprocal dilation gives the actual squared zero-source constraint with
the same complete additive allowance whose normalized limit is zero. -/
theorem finite_source_le_prime_energy_scaled {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => ZetaAngularPhaseAllowance.tail a n * Real.log (ω n)))
    {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (t : ℝ) (Z : Finset NontrivialZetaZero) (hscale : 1 ≤ ZetaNearOneBudgetLimit.scale t)
    (S : Finset ℕ) :
    (max 0 (a 0 * (∑ p ∈ S, ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) p) +
        (a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated (gaussianScale q)
          (halfWidth 9 (shift q)) (ZetaNearOneLocalDisc.center (shift q) t) ρ) -
        exactBudget 9 (gaussianScale q) M (shift q) t a ω)) ^ 2 ≤
      (1 + 1 / q) * ZetaAngularPhaseAllowance.mass a *
        ZetaGaussianPrimeCorrelation.realPrimeEnergy (ZetaAngularPhaseAllowance.tail a)
          ω (primeAmplitude q) t S +
      energyAllowance q (ZetaAngularPhaseAllowance.mass a) := by
  have hq0 : 0 < q := by linarith
  have h := finite_source_le_prime_energy ha hs hP hω0 hω1 hω hlog hq
    (by positivity : 0 < 1 / q) hM t Z hscale S
  simpa only [one_div_one_div, energyAllowance] using h

end
end RiemannGaussian.ZetaGaussianPrimeReduction
