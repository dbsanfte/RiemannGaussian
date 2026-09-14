/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteSignedFourierHinge
import RiemannGaussian.ZetaSquarefreeSignedTail

/-!
# The original Riesz carrier as an exact coupled Fourier integral

Finite cofactor marks keep the original observation band and factorial
filter. The hinge transform retains both frequencies, its signed first
moment and the ordinary-prime correction. At the literal physical cutoff
it recovers the original negative multiplicity source under a hypothetical
right-half zero. The independent cofinal arithmetic floor remains open.
-/

namespace RiemannGaussian.ZetaRieszFourierCarrier
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ArithmeticFunction.Moebius
open FiniteSignedFourierHinge ZetaSquarefreeRieszCompletion ZetaSquarefreeSignedTail

/-- One exact finite cofactor mark, with all original observation weights,
logarithms and squarefree support retained. The physical cutoff stays fixed. -/
def markWeight (T : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) (d : ℕ) : ℂ :=
  (μ d : ℂ) * (-(1 / (L : ℂ))) *
    ∑ n ∈ T, RoughSquarefreeBare.coefficient ∅ d n * (Real.log n : ℂ) * f n

/-- The ordinary-prime correction of the original composite carrier. -/
def primeCorrection (T : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) : ℂ :=
  ∑ n ∈ T,
    (if n.Prime then ((Real.log n * min L (Real.log n) / L : ℝ) : ℂ) else 0) * f n

/-- Exact Fourier response of the original finite carrier. It keeps the
signed first moment and the ordinary-prime correction alongside the coupled
positive and negative frequencies. -/
def fourierResponse (T : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) (D : ℕ) : ℂ :=
  (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
    ((L - Real.log d : ℝ) : ℂ) * markWeight T f L d) / 2 +
  (1 / (Real.pi : ℂ)) * (∫ xi : ℝ in Ioi 0,
    pairedNumerator ((Finset.Icc 1 D).filter Squarefree) (markWeight T f L)
      (fun d => -Real.log d) (-L) xi / (xi : ℂ) ^ 2) +
  primeCorrection T f L

/-- All marked cofactors of the literal carrier enter one exact integrable
Fourier kernel; the prime correction has not been dropped. -/
theorem original_sum_eq_fourierResponse (T : Finset ℕ) (f : ℕ → ℂ)
    (L : ℝ) (hL0 : 0 < L) {D : ℕ} (hL : L ≤ Real.log (D + 1 : ℕ)) :
    (∑ n ∈ T, SquarefreeVaughanLogSource.coefficient L n * f n) =
      fourierResponse T f L D := by
  rw [sum_original_riesz_eq_mark_sums_add_prime T f L hL0 hL]
  have h := finite_hinge_eq_paired_integral ((Finset.Icc 1 D).filter Squarefree)
    (markWeight T f L) (fun d => -Real.log d) (-L)
  simp only [neg_sub_neg] at h
  unfold fourierResponse primeCorrection
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro d _hd
  unfold markWeight
  push_cast
  ring

/-- The actual polynomial factorial filter and original band are retained
in the exact Fourier identity at every order. Internal moment shifts never
change L or the base band in this theorem. -/
theorem actual_band_eq_fourierResponse (P : Polynomial ℂ) (N : ℕ) (y L : ℝ)
    (hL0 : 0 < L) {D : ℕ} (hL : L ≤ Real.log (D + 1 : ℕ)) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      fourierResponse (zetaPrimeLogBand N)
        (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) L D := by
  exact original_sum_eq_fourierResponse _ _ L hL0 hL

/-- The finite prime-subset tail has an exact two-frequency representation,
retaining every distinct-prime count and the signed first moment. -/
theorem signedSubsetTail_eq_paired_integral {ι : Type*} (Q : Finset ι)
    (a : ι → ℂ) (ell : ι → ℝ) (L : ℝ) :
    signedSubsetTail Q a ell L =
      (∑ S ∈ Q.powerset, (((∑ p ∈ S, ell p) - L : ℝ) : ℂ) * ∏ p ∈ S, (-a p)) / 2 +
      (1 / (Real.pi : ℂ)) * ∫ xi : ℝ in Ioi 0,
        pairedNumerator Q.powerset (fun S => ∏ p ∈ S, (-a p))
          (fun S => ∑ p ∈ S, ell p) L xi / (xi : ℂ) ^ 2 := by
  exact finite_hinge_eq_paired_integral Q.powerset _ _ L

/-- The source's physical divisor cutoff is chosen before any internal
factorial shift. Its logarithm is exactly the original averaging length. -/
def physicalCutoff (u : ℝ) (N : ℕ) : ℕ :=
  (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- The physical divisor cutoff contains every nonzero ramp of the
actual source, without changing its length or integer observation band. -/
theorem length_le_log_physicalCutoff_add_one (u : ℝ) (N : ℕ) :
    SquarefreeVaughanLogSource.length u N ≤ Real.log (physicalCutoff u N + 1 : ℕ) := by
  unfold SquarefreeVaughanLogSource.length physicalCutoff
  push_cast
  apply Real.log_le_log (by positivity)
  linarith

/-- The Fourier response at the literal physical cutoff is exactly the
actual band for every polynomial filter, height and source scale. -/
theorem actual_physical_band_eq_fourierResponse (P : Polynomial ℂ)
    (N : ℕ) (y u : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N)) P N y =
      fourierResponse (zetaPrimeLogBand N)
        (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
        (SquarefreeVaughanLogSource.length u N) (physicalCutoff u N) :=
  actual_band_eq_fourierResponse P N y _ (SquarefreeVaughanLogSource.length_pos u N)
    (length_le_log_physicalCutoff_add_one u N)

/-- Under the original hypothetical right-half zero, the complete Fourier
response has exactly the original negative multiplicity source. This
retains the original filter, first moment and ordinary-prime correction;
it is not an independent lower bound. -/
theorem tendsto_actual_fourierResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      fourierResponse (zetaPrimeLogBand N)
        (fun n => zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
          (3 / 2 + Complex.I * rho.1.im) n)
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
        (physicalCutoff (3 / 2 - rho.1.re) N))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  simpa only [actual_physical_band_eq_fourierResponse] using
    SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho

/-- The exact finite Fourier character is the Euler product over every
prime subset. No prime count, sign or relative frequency is discarded. -/
theorem subset_finiteCharacter_eq_product {ι : Type*} (Q : Finset ι)
    (a : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) :
    finiteCharacter Q.powerset (fun S => ∏ p ∈ S, (-a p))
      (fun S => ∑ p ∈ S, ell p) xi =
      ∏ p ∈ Q, (1 - a p * Complex.exp (Complex.I * xi * ell p)) := by
  unfold finiteCharacter
  rw [← signed_subset_character_product Q a
    (fun p => Complex.exp (Complex.I * xi * ell p))]
  apply Finset.sum_congr rfl
  intro S _hS
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _hp
  push_cast
  ring

end
end RiemannGaussian.ZetaRieszFourierCarrier
