import RiemannGaussian.ZetaReciprocalLowHeight
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The actual reciprocal Dirichlet series on every line to the right of one

The Möbius convolution identifies the genuine reciprocal with its absolutely
convergent series. Its norm has an ordinate-independent finite envelope at
every real abscissa greater than one, including the moving contour abscissa.
The individual complex Dirichlet phases are retained exactly.
-/

open Complex
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The absolute mass of the actual Möbius Dirichlet series at a real abscissa. -/
def moebiusDirichletMass (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (sigma : ℂ) n‖

/-- The actual absolute Dirichlet mass is a convergent sum at every abscissa greater than one. -/
theorem summable_moebiusDirichletMass {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ ↦ ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (sigma : ℂ) n‖) :=
  (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsigma).norm

/-- The positive first Dirichlet term makes the actual absolute mass at least one. -/
theorem one_le_moebiusDirichletMass {sigma : ℝ} (hsigma : 1 < sigma) :
    1 ≤ moebiusDirichletMass sigma := by
  have h := (summable_moebiusDirichletMass hsigma).le_tsum 1 (fun n _ ↦ norm_nonneg _)
  simpa [moebiusDirichletMass, LSeries.term] using h

/-- The genuine reciprocal extension is the full Möbius Dirichlet series in its region of absolute convergence. -/
theorem zetaReciprocalExtension_eq_moebius_LSeries {s : ℂ} (hs : 1 < s.re) :
    zetaReciprocalExtension s = L (fun n : ℕ ↦ ((μ n : ℤ) : ℂ)) s := by
  have hsone : s ≠ 1 := by intro h; simp [h] at hs
  rw [zetaReciprocalExtension_eq_inv hsone]
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  apply mul_left_cancel₀ hz
  rw [mul_inv_cancel₀ hz, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact (ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs).symm

/-- A vertical Dirichlet term keeps constant norm while retaining its complex ordinate phase. -/
theorem norm_moebius_LSeries_term_vertical (sigma t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) ((sigma : ℂ) + (t : ℂ) * I) n‖ =
      ‖LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) (sigma : ℂ) n‖ := by
  simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_self, add_zero]

/-- The full complex phase of each positive-index Möbius Dirichlet term. -/
theorem moebius_LSeries_term_eq_exp (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun m : ℕ ↦ ((μ m : ℤ) : ℂ)) s n =
      ((μ n : ℤ) : ℂ) * Complex.exp (-((Real.log n : ℝ) : ℂ) * s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
    div_eq_mul_inv, ← Complex.exp_neg, ← Complex.ofReal_natCast,
    Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  ring

/-- The actual reciprocal has an ordinate-independent bound throughout each absolutely convergent vertical line. -/
theorem norm_zetaReciprocalExtension_le_moebiusDirichletMass {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    ‖zetaReciprocalExtension ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ moebiusDirichletMass sigma := by
  have hs : 1 < ((sigma : ℂ) + (t : ℂ) * I).re := by simpa using hsigma
  rw [zetaReciprocalExtension_eq_moebius_LSeries hs]
  have hsum := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans_eq
  exact tsum_congr (norm_moebius_LSeries_term_vertical sigma t)

end

end RiemannGaussian
