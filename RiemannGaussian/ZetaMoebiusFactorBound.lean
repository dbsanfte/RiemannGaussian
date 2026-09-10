/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFactorResponse
import RiemannGaussian.ZetaEntireMultiplierBound

/-!
# An independent bound for the complete fixed-factor arithmetic response

The actual finite-prefix multipliers have a linear divisor-cutoff budget.
Their fixed-factor cost is explicit, so one Cauchy constant controls every
factor as well as every moment order. No Möbius cancellation estimate is
assumed after the complete-fibre cancellation already proved upstream.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem finite_series_le_card (S : Finset ℕ) (a : ℕ → ℂ)
    {C : ℝ} (hC : ∀ n ∈ S, ‖a n‖ ≤ C) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaFiniteDirichletSeries S a s‖ ≤ (S.card : ℝ) * C := by
  apply (norm_zetaFiniteDirichletSeries_le S a hs).trans
  calc
    _ ≤ ∑ _n ∈ S, C := Finset.sum_le_sum hC
    _ = _ := by simp

private theorem norm_moebius_le_one (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- Both actual prefix polynomials have linear cutoff cost, uniformly
on the closed right half-plane. -/
theorem norm_zetaMoebiusFactorPrefixSeries_le (D P : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMoebiusFactorSlopeSeries D P s‖ ≤ (D : ℝ) * P.divisors.card ∧
      ‖zetaMoebiusFactorInterceptSeries D P s‖ ≤
        (D : ℝ) * ((P.divisors.card : ℝ) * Real.log P) := by
  constructor
  · simpa only [zetaMoebiusFactorSlopeSeries, Nat.card_Icc, Nat.add_sub_cancel] using
      finite_series_le_card (Finset.Icc 1 D) (zetaMoebiusFactorSlope D P)
        (fun d _ ↦ (norm_zetaMoebiusFactorPrefix_le D P d).1) hs
  · simpa only [zetaMoebiusFactorInterceptSeries, Nat.card_Icc, Nat.add_sub_cancel] using
      finite_series_le_card (Finset.Icc 1 D) (zetaMoebiusFactorIntercept D P)
        (fun d _ ↦ (norm_zetaMoebiusFactorPrefix_le D P d).2) hs

/-- The two finite Euler factors have explicit factor-only budgets,
including all prime intersections rather than a fitted finite family. -/
theorem norm_zetaCoprimeEulerFactors_le (P : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaCoprimeEulerFactor P s‖ ≤ P.divisors.card ∧
      ‖zetaCoprimeEulerLogFactor P s‖ ≤ (P.divisors.card : ℝ) * Real.log P := by
  constructor
  · simpa only [zetaCoprimeEulerFactor, mul_one] using
      finite_series_le_card P.divisors (fun d ↦ (μ d : ℂ)) (fun d _ ↦ norm_moebius_le_one d) hs
  · apply finite_series_le_card P.divisors (fun d ↦ (μ d : ℂ) * (Real.log d : ℂ)) _ hs
    intro d hd
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg d)]
    have hdP := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)
    calc
      _ ≤ 1 * Real.log d := mul_le_mul_of_nonneg_right (norm_moebius_le_one d)
        (Real.log_natCast_nonneg d)
      _ ≤ _ := by
        rw [one_mul]
        exact Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors hd) (by exact_mod_cast hdP)

/-- The entire derivative and value multipliers are bounded before
invoking Cauchy's estimate, with costs explicit in the moving factor. -/
theorem norm_zetaMoebiusFactorMultipliers_le (D P : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMoebiusFactorDerivativeMultiplier D P s‖ ≤ (D : ℝ) * (P.divisors.card : ℝ) ^ 2 ∧
      ‖zetaMoebiusFactorValueMultiplier D P s‖ ≤
        2 * (D : ℝ) * (P.divisors.card : ℝ) ^ 2 * Real.log P := by
  obtain ⟨hG, hH⟩ := norm_zetaMoebiusFactorPrefixSeries_le D P hs
  obtain ⟨hE, hL⟩ := norm_zetaCoprimeEulerFactors_le P hs
  have hw := norm_zetaPrimeFeature_le_one hs P
  have hp0 := Real.log_natCast_nonneg P
  constructor
  · rw [zetaMoebiusFactorDerivativeMultiplier, norm_mul, norm_mul]
    have hh := mul_le_mul hG hE (norm_nonneg _) (by positivity)
    exact (mul_le_mul hw hh (by positivity) (by norm_num)).trans_eq (by ring)
  · rw [zetaMoebiusFactorValueMultiplier, norm_mul]
    have hh := (norm_add_le (zetaMoebiusFactorSlopeSeries D P s * zetaCoprimeEulerLogFactor P s)
      (zetaMoebiusFactorInterceptSeries D P s * zetaCoprimeEulerFactor P s)).trans (add_le_add
      (by simpa only [norm_mul] using mul_le_mul hG hL (norm_nonneg _) (by positivity))
      (by simpa only [norm_mul] using mul_le_mul hH hE (norm_nonneg _) (by positivity)))
    exact (mul_le_mul hw hh (norm_nonneg _) (by norm_num)).trans_eq (by ring)

/-- The complete arithmetic cost of the fixed coprime factor. -/
def zetaMoebiusFactorComplexity (P : ℕ) : ℝ :=
  (P.divisors.card : ℝ) ^ 2 * (1 + 2 * Real.log P)

/-- The explicit factor cost is nonnegative at every natural factor. -/
theorem zetaMoebiusFactorComplexity_nonneg (P : ℕ) : 0 ≤ zetaMoebiusFactorComplexity P := by
  have h := Real.log_natCast_nonneg P
  unfold zetaMoebiusFactorComplexity
  positivity

/-- The filtered moments of the actual finite-prefix response. -/
def zetaMoebiusFactorFilter (p : Polynomial ℂ) (D P N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun k ↦ signedTaylorMoment k (zetaMoebiusFactorResponse D P) s) N

/-- One constant controls all cutoffs, factors, moment orders, and
polynomial filters at the chosen ordinate. Every multiplier budget has
been independently discharged for the actual finite prefixes. -/
theorem exists_zetaMoebiusFactorFilter_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D P N : ℕ),
      ‖zetaMoebiusFactorFilter p D P N (3 / 2 + I * y)‖ ≤
        C * D * zetaMoebiusFactorComplexity P * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaEntireMultiplier_filter_bound y hy
  refine ⟨C, hC, ?_⟩
  intro p D P N
  obtain ⟨hf, hg⟩ := differentiable_zetaMoebiusFactorMultipliers D P
  have hlog := Real.log_natCast_nonneg P
  have h := hb _ _ hf hg ((D : ℝ) * (P.divisors.card : ℝ) ^ 2)
    (2 * D * (P.divisors.card : ℝ) ^ 2 * Real.log P) (by positivity) (by positivity)
    (fun s hs ↦ (norm_zetaMoebiusFactorMultipliers_le D P (by linarith)).1)
    (fun s hs ↦ (norm_zetaMoebiusFactorMultipliers_le D P (by linarith)).2) p N
  exact h.trans_eq (by unfold zetaMoebiusFactorComplexity; ring)

/-- The explicit factor cost admits a cubic elementary envelope. -/
theorem zetaMoebiusFactorComplexity_le_cube {P : ℕ} (hP : 1 ≤ P) :
    zetaMoebiusFactorComplexity P ≤ 3 * (P : ℝ) ^ 3 := by
  have hcard : (P.divisors.card : ℝ) ≤ P := by exact_mod_cast Nat.card_divisors_le_self P
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hlog := Real.log_le_self (Nat.cast_nonneg P)
  have hlog0 := Real.log_natCast_nonneg P
  unfold zetaMoebiusFactorComplexity
  calc
    _ ≤ (P : ℝ) ^ 2 * (3 * P) := by gcongr; linarith
    _ = _ := by ring

/-- A growing factor with `P²≤D` has at most a cubic combined cutoff
cost. This bound is uniform over all such factors simultaneously. -/
theorem mul_zetaMoebiusFactorComplexity_le_cube {D P : ℕ} (hP : 1 ≤ P) (hPD : P ^ 2 ≤ D) :
    (D : ℝ) * zetaMoebiusFactorComplexity P ≤ 3 * (D : ℝ) ^ 3 := by
  have hp : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hpd : (P : ℝ) ^ 2 ≤ D := by exact_mod_cast hPD
  have hPD' : (P : ℝ) ≤ D := by nlinarith
  have hc : (P : ℝ) ^ 3 ≤ (D : ℝ) ^ 2 := by
    calc
      _ = (P : ℝ) ^ 2 * P := by ring
      _ ≤ (D : ℝ) * D := mul_le_mul hpd hPD' (by positivity) (by positivity)
      _ = _ := by ring
  have h := mul_le_mul_of_nonneg_left (zetaMoebiusFactorComplexity_le_cube hP) (Nat.cast_nonneg D)
  nlinarith [mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg D)]

/-- The cubic cost still has a strict geometric margin at the actual
cutoff: its exact ratio is the fourth root of the source normalization. -/
theorem zetaMoebiusHeadGrowth_cubic_rate {u : ℝ} (hu : 0 < u) :
    u * zetaMoebiusHeadGrowth u ^ 3 = Real.sqrt (Real.sqrt u) := by
  have hr : Real.sqrt (Real.sqrt u) ≠ 0 := (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu)).ne'
  calc
    _ = (u * zetaMoebiusHeadGrowth u ^ 2) * zetaMoebiusHeadGrowth u := by ring
    _ = Real.sqrt u / Real.sqrt (Real.sqrt u) := by rw [zetaMoebiusHeadGrowth_rate hu]; rfl
    _ = _ := (div_eq_iff hr).mpr (by simpa only [pow_two] using (Real.sq_sqrt (Real.sqrt_nonneg u)).symm)

end
end RiemannGaussian
