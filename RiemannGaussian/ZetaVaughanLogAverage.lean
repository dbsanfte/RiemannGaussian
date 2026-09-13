/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVaughanReduction
import RiemannGaussian.ZetaRoughMoebiusHyperbola
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.Floor

/-!
# Exact logarithmic averaging of the Vaughan hyperbola

The complete two-factor cutoff is averaged before any absolute value is
taken. An arbitrary arithmetic profile first gives an exact signed
convolution identity. The positive-part logarithmic profile then evaluates
the genuine floor-cutoff integral, retaining the prime-power correction.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RiemannGaussian.VaughanLogAverage
noncomputable section
open ZetaVaughanReduction

/-- Pointwise weighting keeps the actual arithmetic function's zero value. -/
def weight (w : ℕ → ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := w n * f n
  map_zero' := by simp

/-- The complete product-minus-factor profile, before divisor summation. -/
def profile (w : ℕ → ℝ) : ArithmeticFunction ℝ :=
  weight w ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt) -
    weight w μ * ArithmeticFunction.vonMangoldt -
      (μ : ArithmeticFunction ℝ) * weight w ArithmeticFunction.vonMangoldt

/-- The Möbius--von Mangoldt convolution is the negative pointwise
Möbius logarithm. This identity uses every prime-power divisor. -/
theorem moebius_mul_vonMangoldt :
    (μ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt =
      -(μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log := by
  have h : (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log * ζ =
      -ArithmeticFunction.vonMangoldt := by
    ext n
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply,
      ArithmeticFunction.neg_apply] using ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  have he := congrArg (fun f : ArithmeticFunction ℝ ↦ f * μ) h
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at he
  linear_combination he

/-- Every arithmetic profile preserves the complete ordered factor pair,
with no regularity, positivity, or coefficient-family restriction. -/
theorem profile_apply (w : ℕ → ℝ) (n : ℕ) :
    profile w n = ∑ ab ∈ n.divisorsAntidiagonal,
      (μ ab.1 : ℝ) * ArithmeticFunction.vonMangoldt ab.2 *
        (w n - w ab.1 - w ab.2) := by
  change (weight w ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt) n -
    (weight w μ * ArithmeticFunction.vonMangoldt) n) -
      ((μ : ArithmeticFunction ℝ) * weight w ArithmeticFunction.vonMangoldt) n = _
  change w n * ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt) n -
    (weight w μ * ArithmeticFunction.vonMangoldt) n -
      ((μ : ArithmeticFunction ℝ) * weight w ArithmeticFunction.vonMangoldt) n = _
  simp only [ArithmeticFunction.mul_apply]
  simp only [weight, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ab _
  ring

/-- Summing the full product profile over divisors collapses it to one
signed divisor sum and its explicit von Mangoldt correction. -/
theorem profile_mul_zeta (w : ℕ → ℝ) :
    profile w * ζ =
      -((weight w μ * ζ).pmul ArithmeticFunction.log) -
        weight w ArithmeticFunction.vonMangoldt := by
  have hlast : (μ : ArithmeticFunction ℝ) * weight w ArithmeticFunction.vonMangoldt * ζ =
      weight w ArithmeticFunction.vonMangoldt := by
    calc
      _ = (μ : ArithmeticFunction ℝ) * ζ * weight w ArithmeticFunction.vonMangoldt := by ring
      _ = _ := by rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  rw [profile, sub_mul, sub_mul, hlast, mul_assoc,
    ArithmeticFunction.vonMangoldt_mul_zeta, moebius_mul_vonMangoldt]
  ext n
  change (weight w (-(μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log) * ζ) n -
    (weight w μ * ArithmeticFunction.log) n - weight w ArithmeticFunction.vonMangoldt n = _
  congr 1
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.neg_apply, ArithmeticFunction.log_apply]
  rw [← Nat.sum_divisorsAntidiagonal (fun a _ ↦ weight w
      (-(μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log) a),
    ← Nat.sum_divisorsAntidiagonal (fun a _ ↦ weight w μ a)]
  rw [ArithmeticFunction.mul_apply, ← Finset.sum_sub_distrib, Finset.sum_mul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ab hab
  obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hab
  have hl : Real.log n = Real.log ab.1 + Real.log ab.2 := by
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  simp only [weight, ArithmeticFunction.coe_mk, ArithmeticFunction.neg_apply,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.log_apply, hl]
  ring

/-- The arbitrary-profile identity at each integer retains all signs and
every product constraint, including the prime-power endpoint. -/
theorem sum_profile_eq (w : ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
      (μ ab.1 : ℝ) * ArithmeticFunction.vonMangoldt ab.2 *
        (w d - w ab.1 - w ab.2)) =
      -Real.log n * (∑ d ∈ n.divisors, (μ d : ℝ) * w d) -
        ArithmeticFunction.vonMangoldt n * w n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) (profile_mul_zeta w)
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simp only [profile_apply] at h
  rw [h]
  change -((weight w μ * ζ).pmul ArithmeticFunction.log n) -
    weight w ArithmeticFunction.vonMangoldt n = _
  simp only [ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [weight, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, mul_comm]
  ring

/-- Both strict cutoffs are kept in the same complete factor pair. -/
theorem bilinear_eq_joint_product (U V n : ℕ) :
    bilinear U V n = ∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
      if U < ab.1 ∧ V < ab.2 then
        (μ ab.1 : ℝ) * ArithmeticFunction.vonMangoldt ab.2 else 0 := by
  rw [bilinear, cofactor, ← mul_assoc, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d _
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro ab _
  change ((μ ab.1 : ℝ) - head U μ ab.1) *
    (ArithmeticFunction.vonMangoldt ab.2 - head V ArithmeticFunction.vonMangoldt ab.2) = _
  by_cases ha : ab.1 ≤ U <;> by_cases hb : ab.2 ≤ V <;>
    simp [head, ha, hb, not_lt.mpr, not_le.mp]

/-- The positive-part logarithmic tail at every actual divisor. -/
def logTail (L : ℝ) (n : ℕ) : ℝ := max 0 (Real.log n - L)

/-- The signed first Riesz mean over the integer's actual divisors. -/
def riesz (L : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (μ d : ℝ) * max 0 (L - Real.log d)

/-- Uniform integration in logarithmic cutoff coordinates. Both floors
belong to the original Vaughan coefficient at every integration point. -/
def logarithmicAverage (L : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Icc 0 L, bilinear ⌊Real.exp t⌋₊ ⌊Real.exp (L - t)⌋₊ n

private theorem cutoff_pair_indicator {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (L c t : ℝ) :
    (if ⌊Real.exp t⌋₊ < a ∧ ⌊Real.exp (L - t)⌋₊ < b then c else 0) =
      (Ioo (L - Real.log b) (Real.log a)).indicator (fun _ ↦ c) t := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [Nat.floor_lt (Real.exp_pos _).le,
    ← Real.lt_log_iff_exp_lt haR, ← Real.lt_log_iff_exp_lt hbR]
  have he : (t < Real.log a ∧ L - t < Real.log b) ↔
      t ∈ Ioo (L - Real.log b) (Real.log a) := by
    simp only [mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [he, indicator_apply]

private theorem integrableOn_cutoff_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (L c : ℝ) :
    IntegrableOn (fun t ↦ if ⌊Real.exp t⌋₊ < a ∧ ⌊Real.exp (L - t)⌋₊ < b then c else 0)
      (Icc 0 L) := by
  simp_rw [cutoff_pair_indicator ha hb]
  exact (integrableOn_const (C := c) (hs := by simp)).indicator measurableSet_Ioo

private theorem clipped_length {L a b : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (min L a - max 0 (L - b)) 0 =
      max 0 (a + b - L) - max 0 (a - L) - max 0 (b - L) := by
  rcases le_total a L with haL | hLa <;> rcases le_total b L with hbL | hLb
  · rw [min_eq_right haL, max_eq_right (sub_nonneg.mpr hbL),
      max_eq_left (sub_nonpos.mpr haL), max_eq_left (sub_nonpos.mpr hbL)]
    rw [max_comm (a - (L - b)) 0, show a - (L - b) = a + b - L by ring]
    simp only [sub_zero]
  · rw [min_eq_right haL, max_eq_left (sub_nonpos.mpr hLb), sub_zero,
      max_eq_left ha, max_eq_right (by linarith : 0 ≤ a + b - L),
      max_eq_left (sub_nonpos.mpr haL), max_eq_right (sub_nonneg.mpr hLb)]
    ring
  · rw [min_eq_left hLa, max_eq_right (sub_nonneg.mpr hbL),
      max_eq_left (by linarith : 0 ≤ L - (L - b)),
      max_eq_right (by linarith : 0 ≤ a + b - L),
      max_eq_right (sub_nonneg.mpr hLa), max_eq_left (sub_nonpos.mpr hbL)]
    ring
  · rw [min_eq_left hLa, max_eq_left (sub_nonpos.mpr hLb), sub_zero,
      max_eq_left hL, max_eq_right (by linarith : 0 ≤ a + b - L),
      max_eq_right (sub_nonneg.mpr hLa), max_eq_right (sub_nonneg.mpr hLb)]
    ring

/-- The exact clipped fibre integral is a product logarithm minus both
factor endpoints. Open and closed integration endpoints are accounted for. -/
theorem integral_cutoff_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    (∫ t in Icc 0 L,
      if ⌊Real.exp t⌋₊ < a ∧ ⌊Real.exp (L - t)⌋₊ < b then c else 0) =
        c * (logTail L (a * b) - logTail L a - logTail L b) := by
  simp_rw [cutoff_pair_indicator ha hb]
  rw [integral_Icc_eq_integral_Ioo, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo, setIntegral_const,
    Real.volume_real_Ioo]
  simp only [smul_eq_mul]
  rw [max_comm (L - Real.log b) 0, min_comm (Real.log a) L,
    clipped_length hL (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b)]
  rw [logTail, logTail, logTail, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr ha.ne') (Nat.cast_ne_zero.mpr hb.ne')]
  ring

/-- The genuine floor-cutoff average is integrable, by its complete
finite decomposition into clipped factor fibres. -/
theorem integrableOn_bilinear (L : ℝ) (n : ℕ) :
    IntegrableOn (fun t ↦ bilinear ⌊Real.exp t⌋₊ ⌊Real.exp (L - t)⌋₊ n) (Icc 0 L) := by
  simp_rw [bilinear_eq_joint_product]
  apply integrable_finsetSum
  intro d _
  apply integrable_finsetSum
  intro ab hab
  obtain ⟨ha, hb⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hab
  exact integrableOn_cutoff_pair (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) _ _

/-- The logarithmic hyperbola average collapses exactly to a single
signed divisor sum. The prime-power endpoint is retained explicitly. -/
theorem logarithmicAverage_eq_tail {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    logarithmicAverage L n =
      -Real.log n * (∑ d ∈ n.divisors, (μ d : ℝ) * logTail L d) -
        ArithmeticFunction.vonMangoldt n * logTail L n := by
  rw [logarithmicAverage]
  simp_rw [bilinear_eq_joint_product]
  rw [integral_finsetSum _ (fun d _ ↦ integrable_finsetSum _ (fun ab hab ↦
    integrableOn_cutoff_pair (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).1)
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).2) _ _))]
  calc
    _ = ∑ d ∈ n.divisors, ∑ ab ∈ d.divisorsAntidiagonal,
        (μ ab.1 : ℝ) * ArithmeticFunction.vonMangoldt ab.2 *
          (logTail L d - logTail L ab.1 - logTail L ab.2) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [integral_finsetSum _ (fun ab hab ↦ integrableOn_cutoff_pair
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).1)
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).2) _ _)]
      apply Finset.sum_congr rfl
      intro ab hab
      rw [integral_cutoff_pair (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).1)
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hab).2) hL,
        (Nat.mem_divisorsAntidiagonal.mp hab).1]
    _ = _ := sum_profile_eq (logTail L) n

/-- The two complementary logarithmic ramps differ by the complete
von Mangoldt term and the exact unit correction. -/
theorem sum_logTail_eq_riesz (L : ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ) * logTail L d) =
      riesz L n - ArithmeticFunction.vonMangoldt n - L * (∑ d ∈ n.divisors, (μ d : ℝ)) := by
  have hr (d : ℕ) : logTail L d = max 0 (L - Real.log d) + Real.log d - L := by
    rcases le_total (Real.log d) L with hd | hd
    · rw [logTail, max_eq_left (sub_nonpos.mpr hd), max_eq_right (sub_nonneg.mpr hd)]
      ring
    · rw [logTail, max_eq_right (sub_nonneg.mpr hd), max_eq_left (sub_nonpos.mpr hd)]
      ring
  have hl : (∑ d ∈ n.divisors, (μ d : ℝ) * Real.log d) =
      -ArithmeticFunction.vonMangoldt n := by
    simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply] using
      ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  simp only [hr, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hl, ← Finset.sum_mul, riesz]
  ring

/-- The complementary Riesz form records exactly the endpoint restored
by completing the divisor sum. It is present on all prime powers. -/
theorem logarithmicAverage_eq_riesz {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    logarithmicAverage L n = -Real.log n * riesz L n +
      ArithmeticFunction.vonMangoldt n * min L (Real.log n) := by
  have hm : (∑ d ∈ n.divisors, (μ d : ℝ)) * Real.log n = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n)
      ArithmeticFunction.coe_moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h
    simp only [ArithmeticFunction.intCoe_apply] at h
    rw [h]
    by_cases hn : n = 1 <;> simp [hn]
  have he : min L (Real.log n) = Real.log n - logTail L n := by
    rcases le_total (Real.log n) L with hn | hn
    · rw [min_eq_right hn, logTail, max_eq_left (sub_nonpos.mpr hn), sub_zero]
    · rw [min_eq_left hn, logTail, max_eq_right (sub_nonneg.mpr hn)]
      ring
  rw [logarithmicAverage_eq_tail hL, sum_logTail_eq_riesz, he]
  linear_combination L * hm

/-- On the squarefree composite support the prime-power correction
vanishes for an arithmetic reason, leaving the exact signed Riesz mean. -/
theorem logarithmicAverage_eq_riesz_of_squarefree_composite {L : ℝ} (hL : 0 ≤ L)
    {n : ℕ} (hn : Squarefree n) (hp : ¬ n.Prime) :
    logarithmicAverage L n = -Real.log n * riesz L n := by
  rw [logarithmicAverage_eq_riesz hL,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h ↦
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, h⟩)), zero_mul, add_zero]

/-- A prime cannot contain both strict Vaughan factors above cutoffs
at least one; the full logarithmic average vanishes on primes. -/
theorem logarithmicAverage_prime {L : ℝ} (hL : 0 ≤ L) {p : ℕ} (hp : p.Prime) :
    logarithmicAverage L p = 0 := by
  rw [logarithmicAverage_eq_tail hL, hp.divisors]
  rw [Finset.sum_pair hp.ne_one.symm]
  simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, logTail, Nat.cast_one,
    Real.log_one, zero_sub, max_eq_left (neg_nonpos.mpr hL),
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, neg_one_mul, zero_add,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

/-- Divisor reflection gives the full Riesz profile its exact Möbius
parity about half the integer's logarithm. No divisor sign is discarded. -/
theorem riesz_reflection (L : ℝ) {n : ℕ} (hn : Squarefree n) (h1 : n ≠ 1)
    (hp : ¬ n.Prime) :
    riesz (Real.log n - L) n = (μ n : ℝ) * riesz L n := by
  have hmu : (∑ d ∈ n.divisors, (μ d : ℝ)) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n)
      ArithmeticFunction.coe_moebius_mul_coe_zeta
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.one_apply, if_neg h1] using h
  have hLambda : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (fun h ↦
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hn, h⟩))
  have ht := sum_logTail_eq_riesz L n
  rw [hmu, hLambda, mul_zero, sub_zero, sub_zero] at ht
  rw [← ht, riesz, ← Nat.sum_div_divisors n
    (fun d ↦ (μ d : ℝ) * max 0 (Real.log n - L - Real.log d)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hmn : (μ (n / d) : ℝ) = (μ n : ℝ) * (μ d : ℝ) := by
    exact_mod_cast RoughMoebiusHyperbola.moebius_cofactor hn hdn
  rw [hmn, Nat.cast_div hdn hd0,
    Real.log_div (Nat.cast_ne_zero.mpr hn.ne_zero) hd0, logTail,
    show Real.log n - L - (Real.log n - Real.log d) = Real.log d - L by ring]
  ring

/-- The original unnormalized floor average inherits the same parity
under `B ↦ n/B`, with both logarithmic interval domains explicit. -/
theorem logarithmicAverage_reflection {L : ℝ} (hL : 0 ≤ L) {n : ℕ}
    (hn : Squarefree n) (h1 : n ≠ 1) (hp : ¬ n.Prime) (hLn : L ≤ Real.log n) :
    logarithmicAverage (Real.log n - L) n = (μ n : ℝ) * logarithmicAverage L n := by
  rw [logarithmicAverage_eq_riesz_of_squarefree_composite (sub_nonneg.mpr hLn) hn hp,
    logarithmicAverage_eq_riesz_of_squarefree_composite hL hn hp, riesz_reflection L hn h1 hp]
  ring

/-- Odd Möbius parity forces exact cancellation at the centre of the
whole logarithmic profile. The centre depends on the integer being tested. -/
theorem riesz_half_log_eq_zero {n : ℕ} (hn : Squarefree n) (h1 : n ≠ 1)
    (hp : ¬ n.Prime) (hmu : μ n = -1) : riesz (Real.log n / 2) n = 0 := by
  have h := riesz_reflection (Real.log n / 2) hn h1 hp
  rw [show Real.log n - Real.log n / 2 = Real.log n / 2 by ring, hmu,
    Int.cast_neg, Int.cast_one, neg_one_mul] at h
  linarith

/-- Below the first possible nonunit divisor, the full Riesz mean is
exactly its unit ramp. This is uniform over all positive integers. -/
theorem riesz_of_le_log_two {L : ℝ} (hL : 0 ≤ L) (hL2 : L ≤ Real.log 2)
    {n : ℕ} (hn : 0 < n) : riesz L n = L := by
  rw [riesz, Finset.sum_eq_single 1]
  · simp [max_eq_right hL]
  · intro d hd hd1
    have hd2 : 2 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
    have hlog : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) (by exact_mod_cast hd2)
    rw [max_eq_left (sub_nonpos.mpr (hL2.trans hlog)), mul_zero]
  · exact fun h ↦ False.elim (h (Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩))

/-- Every odd-parity squarefree composite has two opposite, exactly
evaluated edges in the same Riesz profile. Averaging cannot make all
divisor coefficients one-signed, even before a complex phase is applied. -/
theorem riesz_opposite_edges {L : ℝ} (hL : 0 < L) (hL2 : L ≤ Real.log 2)
    {n : ℕ} (hn : Squarefree n) (h1 : n ≠ 1) (hp : ¬ n.Prime) (hmu : μ n = -1) :
    riesz L n = L ∧ riesz (Real.log n - L) n = -L := by
  have h := riesz_of_le_log_two hL.le hL2 (Nat.pos_of_ne_zero hn.ne_zero)
  refine ⟨h, ?_⟩
  rw [riesz_reflection L hn h1 hp, hmu, Int.cast_neg, Int.cast_one, neg_one_mul, h]

/-- An actual joint floor cell, including its intersection with the
integration interval. No boundary convention is replaced by a sampler. -/
def cell (L : ℝ) (q : ℕ × ℕ) : Set ℝ :=
  Icc 0 L ∩ {t | (⌊Real.exp t⌋₊, ⌊Real.exp (L - t)⌋₊) = q}

/-- All nonempty joint floor cells form a finite set of whole cutoff pairs. -/
def cutoffPairs (L : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊Real.exp L⌋₊ + 1)) ×ˢ
    (Finset.range (⌊Real.exp L⌋₊ + 1))).filter (fun q ↦ (cell L q).Nonempty)

/-- The exact probability weight of a joint floor cell when `L > 0`. -/
def cellWeight (L : ℝ) (q : ℕ × ℕ) : ℝ := volume.real (cell L q) / L

/-- Joint floor cells are measurable, including all of their endpoints. -/
theorem measurableSet_cell (L : ℝ) (q : ℕ × ℕ) : MeasurableSet (cell L q) := by
  apply measurableSet_Icc.inter
  apply measurableSet_eq_fun _ measurable_const
  fun_prop

private theorem cell_subset (L : ℝ) (q : ℕ × ℕ) : cell L q ⊆ Icc 0 L := inter_subset_left

private theorem mem_cutoffPairs {L t : ℝ} (ht : t ∈ Icc 0 L) :
    (⌊Real.exp t⌋₊, ⌊Real.exp (L - t)⌋₊) ∈ cutoffPairs L := by
  simp only [cutoffPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, ?_⟩, ⟨t, ht, rfl⟩⟩
  · exact Nat.lt_succ_of_le (Nat.floor_mono (Real.exp_le_exp.mpr ht.2))
  · exact Nat.lt_succ_of_le (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith [ht.1])))

private theorem integrable_cell_indicator (L : ℝ) (q : ℕ × ℕ) (c : ℝ) :
    Integrable ((cell L q).indicator (fun _ ↦ c)) := by
  exact ((integrableOn_const (C := c) (s := Icc 0 L) (hs := by simp)).mono_set
    (cell_subset L q)).integrable_indicator (measurableSet_cell L q)

/-- Every test of the actual two floors has the exact finite cell
decomposition. This transports the continuous average to whole cutoff pairs. -/
theorem integral_eq_cell_sum (L : ℝ) (f : ℕ → ℕ → ℝ) :
    (∫ t in Icc 0 L, f ⌊Real.exp t⌋₊ ⌊Real.exp (L - t)⌋₊) =
      ∑ q ∈ cutoffPairs L, volume.real (cell L q) * f q.1 q.2 := by
  have he (t : ℝ) (ht : t ∈ Icc 0 L) :
      f ⌊Real.exp t⌋₊ ⌊Real.exp (L - t)⌋₊ =
        ∑ q ∈ cutoffPairs L, (cell L q).indicator (fun _ ↦ f q.1 q.2) t := by
    rw [Finset.sum_eq_single (⌊Real.exp t⌋₊, ⌊Real.exp (L - t)⌋₊)]
    · rw [indicator_of_mem (show t ∈ cell L (⌊Real.exp t⌋₊, ⌊Real.exp (L - t)⌋₊) from ⟨ht, rfl⟩)]
    · intro q _ hq
      exact indicator_of_notMem (fun h ↦ hq h.2.symm) _
    · exact fun h ↦ False.elim (h (mem_cutoffPairs ht))
  rw [setIntegral_congr_fun measurableSet_Icc he,
    integral_finsetSum _ (fun q _ ↦ (integrable_cell_indicator L q _).integrableOn)]
  apply Finset.sum_congr rfl
  intro q _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht ↦
    indicator_of_notMem (fun h ↦ ht ((cell_subset L q) h)) _),
    integral_indicator_const _ (measurableSet_cell L q), smul_eq_mul]

/-- The cell weights are nonnegative at every positive logarithmic length. -/
theorem cellWeight_nonneg {L : ℝ} (hL : 0 < L) (q : ℕ × ℕ) :
    0 ≤ cellWeight L q := div_nonneg (measureReal_nonneg) hL.le

/-- The actual finite cell weights sum to one; normalization is proved
from the entire integration interval, without ignoring its edge cells. -/
theorem sum_cellWeight {L : ℝ} (hL : 0 < L) :
    ∑ q ∈ cutoffPairs L, cellWeight L q = 1 := by
  have h := integral_eq_cell_sum L (fun _ _ ↦ 1)
  simp only [setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le hL.le, sub_zero] at h
  simp only [cellWeight, ← Finset.sum_div, ← h, div_self hL.ne']

/-- The average is the exact convex combination of the original Vaughan
coefficients, with an explicit finite family independent of the integer. -/
theorem logarithmicAverage_div_eq_mixture {L : ℝ} (hL : 0 < L) (n : ℕ) :
    logarithmicAverage L n / L =
      ∑ q ∈ cutoffPairs L, cellWeight L q * bilinear q.1 q.2 n := by
  apply (div_eq_iff hL.ne').mpr
  rw [logarithmicAverage, integral_eq_cell_sum L (fun U V ↦ bilinear U V n), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [cellWeight]
  field_simp

/-- Every nonempty joint floor cell pays the true hyperbolic product
budget. The two factors do not separately spend the same cutoff allowance. -/
theorem cutoffPairs_product_le {L : ℝ} {q : ℕ × ℕ} (hq : q ∈ cutoffPairs L) :
    ((q.1 + 1 : ℕ) : ℝ) * (q.2 + 1) ≤ 2 * (Real.exp L + 1) := by
  obtain ⟨t, ht, he⟩ := (Finset.mem_filter.mp hq).2
  obtain rfl : q = (⌊Real.exp t⌋₊, ⌊Real.exp (L - t)⌋₊) := he.symm
  have ha : (1 : ℝ) ≤ ⌊Real.exp t⌋₊ := by
    exact_mod_cast (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr ht.1)
  have hb : (1 : ℝ) ≤ ⌊Real.exp (L - t)⌋₊ := by
    exact_mod_cast (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr (sub_nonneg.mpr ht.2))
  have hab : (⌊Real.exp t⌋₊ : ℝ) * ⌊Real.exp (L - t)⌋₊ ≤ Real.exp L := by
    calc
      _ ≤ Real.exp t * Real.exp (L - t) := mul_le_mul
        (Nat.floor_le (Real.exp_pos _).le) (Nat.floor_le (Real.exp_pos _).le)
        (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

end
end RiemannGaussian.VaughanLogAverage
