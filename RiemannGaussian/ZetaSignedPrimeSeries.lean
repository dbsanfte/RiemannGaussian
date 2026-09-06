import RiemannGaussian.EtaThinStripFactor
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Signed prime positivity for the actual zeta logarithmic derivative

The absolutely convergent von Mangoldt series retains the full complex
phase of each prime-power term. Its real three-height combination is a
nonnegative square, giving signed `3-4-1` positivity before any norm bound.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology LSeries.notation ArithmeticFunction

namespace RiemannGaussian

noncomputable section

/-- Each actual von Mangoldt Dirichlet term retains its exact complex
phase and its positive real amplitude. -/
theorem vonMangoldt_LSeries_term_eq_phase (a y : ℝ) (n : ℕ) :
    LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * y) n =
      ((ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) : ℝ) : ℂ) *
        Complex.exp (-(I * ((y * Real.log n : ℝ) : ℂ))) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log,
      ← Complex.exp_neg]
    have he : -((Real.log (n : ℝ) : ℂ) * ((a : ℂ) + I * y)) =
        ((-a * Real.log (n : ℝ) : ℝ) : ℂ) + -(I * ((y * Real.log (n : ℝ) : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [he, Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring

/-- The real part of the phase-retaining prime-power term is its
positive amplitude times the exact cosine phase. -/
theorem vonMangoldt_LSeries_term_re (a y : ℝ) (n : ℕ) :
    (LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * y) n).re =
      ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) * Real.cos (y * Real.log n) := by
  rw [vonMangoldt_LSeries_term_eq_phase]
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp only [neg_re, neg_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, zero_add, neg_zero, Real.exp_zero, Real.cos_neg]

/-- The actual signed zeta logarithmic derivative is the convergent
von Mangoldt series, before taking a real part or a norm. -/
theorem neg_logDeriv_riemannZeta_eq_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    -logDeriv riemannZeta s =
      ∑' n, LSeries.term (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) s n := by
  simpa only [logDeriv_apply, neg_div, LSeries] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-- Prime-power positivity gives the signed three-height `3-4-1`
inequality for the actual zeta logarithmic derivative on `re s > 1`. -/
theorem neg_logDeriv_riemannZeta_three_height_nonneg {a : ℝ} (ha : 1 < a) (y : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta (a : ℂ)).re +
      4 * (-logDeriv riemannZeta ((a : ℂ) + I * y)).re +
      (-logDeriv riemannZeta ((a : ℂ) + I * ((2 * y : ℝ) : ℂ))).re := by
  let f : ℝ → ℕ → ℂ := fun t ↦ LSeries.term
    (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((a : ℂ) + I * t)
  have hs (t : ℝ) : Summable (f t) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using ha)
  have hsre (t : ℝ) : Summable (fun n ↦ (f t n).re) := Complex.reCLM.summable (hs t)
  have hre (t : ℝ) : (-logDeriv riemannZeta ((a : ℂ) + I * t)).re = ∑' n, (f t n).re := by
    rw [neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using ha), Complex.re_tsum (hs t)]
  have hreal : (-logDeriv riemannZeta (a : ℂ)).re = ∑' n, (f 0 n).re := by
    simpa using hre 0
  rw [hreal, hre y, hre (2 * y), ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((hsre 0).mul_left 3) ((hsre y).mul_left 4),
    ← Summable.tsum_add (((hsre 0).mul_left 3).add ((hsre y).mul_left 4)) (hsre (2 * y))]
  apply tsum_nonneg
  intro n
  dsimp [f]
  have hzero := vonMangoldt_LSeries_term_re a 0 n
  simp only [ofReal_zero, zero_mul, Real.cos_zero, mul_one] at hzero
  rw [hzero, vonMangoldt_LSeries_term_re a y n,
    vonMangoldt_LSeries_term_re a (2 * y) n]
  simp only [mul_assoc (2 : ℝ), Real.cos_two_mul]
  have hnonneg : 0 ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-a * Real.log n) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  nlinarith [mul_nonneg hnonneg (sq_nonneg (1 + Real.cos (y * Real.log n)))]

end

end RiemannGaussian
