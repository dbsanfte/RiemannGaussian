/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompositeProduct

/-!
# The original factorial filter on the completed prime response

The exact finite-band completion passes through every factorial moment of
the original fixed filter. The off-band boundary stays inside the derivatives
and the genuinely integrable paired Fourier expression. No separate bound
or integrability claim for the completed channels is made.
-/

namespace RiemannGaussian.ZetaRieszFilteredCompletion
noncomputable section
open scoped BigOperators
open ZetaRieszPrimeFourier ZetaRieszCompositeProduct

/-- Every signed Taylor coordinate is the literal factorial log weight. -/
theorem signedTaylorMoment_feature (k n : ℕ) (s : ℂ) :
    signedTaylorMoment k (fun z => zetaPrimeFeature z n) s =
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n := by
  have he : (fun z => zetaPrimeFeature z n) =
      (fun z : ℂ => Complex.exp (-(Real.log n : ℂ) * z)) := by
    funext z
    unfold zetaPrimeFeature
    congr 1
    ring
  rw [signedTaylorMoment, he, iteratedDeriv_cexp_const_mul]
  have hsign : (-1 : ℂ) ^ k * (-(Real.log n : ℂ)) ^ k = (Real.log n : ℂ) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  unfold zetaPrimeFeature
  rw [show -(s * (Real.log n : ℂ)) = -(Real.log n : ℂ) * s by ring]
  calc
    _ = ((-1 : ℂ) ^ k * (-(Real.log n : ℂ)) ^ k) / (k.factorial : ℂ) *
      Complex.exp (-(Real.log n : ℂ) * s) := by ring
    _ = _ := by rw [hsign]

/-- Arbitrary complex finite marks commute with all factorial moments. -/
theorem signedTaylorMoment_finite (T : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    signedTaylorMoment k (zetaFiniteDirichletSeries T a) s =
      ∑ n ∈ T, a n * (((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n) := by
  change signedTaylorMoment k (fun z => ∑ n ∈ T, a n * zetaPrimeFeature z n) s = _
  rw [signedTaylorMoment_sum T k _
    (fun n _ => by unfold zetaPrimeFeature; fun_prop)]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [signedTaylorMoment_const_mul, signedTaylorMoment_feature]

/-- The same fixed finite support survives every coordinate of an
arbitrary factorial polynomial filter. -/
theorem finite_filter_eq (T : Finset ℕ) (a : ℕ → ℂ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    zetaMomentSequenceFilter P
      (fun k => signedTaylorMoment k (zetaFiniteDirichletSeries T a) s) N =
        ∑ n ∈ T, a n * zetaPrimeFilterKernel P N s n := by
  simp only [zetaMomentSequenceFilter, Polynomial.sum, signedTaylorMoment_finite,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The completed product keeps the entire omitted band boundary inside
the same analytic function before any high derivative is applied. -/
def completedBand (N : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  compositeResponse (primorial (2 ^ (32 * N))) s xi -
    ∑ n ∈ (((primorial (2 ^ (32 * N))).divisors.erase 1).filter
      (fun n => ¬ n.Prime)).filter (fun n => n ∉ zetaPrimeLogBand N),
      zetaPrimeFeature s n * primeProduct n xi

/-- Product and boundary together equal the original finite band
polynomial as entire functions, not just at the safe center. -/
theorem completedBand_eq_finite (N : ℕ) (xi : ℝ) :
    completedBand N xi = zetaFiniteDirichletSeries
      ((zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime))
      (fun n => primeProduct n xi) := by
  funext s
  unfold completedBand
  rw [← actual_band_symbol_eq_completed_sub_boundary]
  unfold zetaFiniteDirichletSeries
  exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)

/-- The original band support stays fixed through every order of the
factorial filter on the complete product minus its signed boundary. -/
theorem filtered_completedBand_eq (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    zetaMomentSequenceFilter P (fun k => signedTaylorMoment k (completedBand N xi) s) N =
      ∑ n ∈ (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
        primeProduct n xi * zetaPrimeFilterKernel P N s n := by
  rw [completedBand_eq_finite, finite_filter_eq]

/-- One logarithmic mark shifts the factorial moment, with its exact
multiplicity factor. The finite support and complex marks stay unchanged. -/
theorem finite_log_moment (T : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (zetaFiniteDirichletSeries T a) s =
      signedTaylorMoment k (zetaFiniteDirichletSeries T (fun n => (Real.log n : ℂ) * a n)) s := by
  rw [signedTaylorMoment_finite, signedTaylorMoment_finite, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul]
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- The physical logarithmic mark in the actual Riesz coefficient passes
through the completed response with all original factorial shifts explicit. -/
theorem log_filtered_completedBand_eq (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    zetaMomentSequenceFilter P
      (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (completedBand N xi) s) N =
      ∑ n ∈ (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
        ((Real.log n : ℂ) * primeProduct n xi) * zetaPrimeFilterKernel P N s n := by
  rw [completedBand_eq_finite]
  simp_rw [finite_log_moment]
  exact finite_filter_eq _ _ P N s

/-- The original logarithm-marked factorial filter applied jointly to
the completed product and its entire signed band boundary. -/
def filteredCompletedBand (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (completedBand N xi) s) N

/-- Every actual frequency keeps both signs, the original physical length
and all factorial orders of the same fixed band completion. -/
theorem bandPrimePair_eq_filtered_completion (P : Polynomial ℂ) (N : ℕ)
    (s : ℂ) (L xi : ℝ) :
    bandPrimePair (zetaPrimeLogBand N) (fun n => zetaPrimeFilterKernel P N s n) L xi =
      (Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) * filteredCompletedBand P N s xi +
        Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) * filteredCompletedBand P N s (-xi)) /
        ((L : ℂ) * (xi : ℂ) ^ 2) := by
  simp only [filteredCompletedBand, log_filtered_completedBand_eq, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div, bandPrimePair, primePair]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [div_mul_eq_div_div]
  ring

/-- The filtered completed expression has genuine positive-frequency
integrability because its entire original signed band is retained. -/
theorem integrable_filtered_completion (P : Polynomial ℂ) (N : ℕ)
    (s : ℂ) (L : ℝ) :
    MeasureTheory.IntegrableOn (fun xi : ℝ =>
      (Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) * filteredCompletedBand P N s xi +
        Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) * filteredCompletedBand P N s (-xi)) /
        ((L : ℂ) * (xi : ℂ) ^ 2)) (Set.Ioi 0) := by
  simp_rw [← bandPrimePair_eq_filtered_completion]
  exact integrable_bandPrimePair _ _ L

/-- The original carrier is exactly the integrated completed response
after the entire factorial filter; no derivative or integral of an isolated
uncontrolled completion channel is substituted. -/
theorem actual_band_eq_filtered_completion (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi 0,
        (Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) *
            filteredCompletedBand P N (3 / 2 + Complex.I * y) xi +
          Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) *
            filteredCompletedBand P N (3 / 2 + Complex.I * y) (-xi)) /
          ((L : ℂ) * (xi : ℂ) ^ 2) := by
  rw [actual_band_eq_primePair_integral]
  simp_rw [bandPrimePair_eq_filtered_completion]

end
end RiemannGaussian.ZetaRieszFilteredCompletion
