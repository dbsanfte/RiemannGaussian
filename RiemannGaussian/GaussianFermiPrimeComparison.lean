/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiMarginBudget
import RiemannGaussian.ZetaPhaseArithmetic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The ordinary Gaussian prime sum and its bounded Fermi correction

The actual Fermi prime amplitude is the ordinary Gaussian von Mangoldt
amplitude times its logistic factor. Their difference has damping
`3*sigma-1`. Above any fixed `sigma0>2/3`, this entire signed correction
is uniformly bounded by the convergent real logarithmic derivative at
`3*sigma0-1`, independently of the Gaussian width and the ordinate.

This isolates the leading arithmetic term in the Fermi zero budget. The
ordinary Gaussian sum still includes every prime power and its original
cosine phase. A bounded correction is not a bound for that leading sum,
nor for the distinct factorial-moment prime tail in the RH reductio.
-/

namespace RiemannGaussian.GaussianFermiPrimeComparison
noncomputable section
open Complex Filter
open scoped Topology
open EtaGammaSmoothing FermiLaplaceReflection GaussianFermiDerivativeBounds
open GaussianFermiZeroPair GaussianFermiSpectralWeight GaussianFermiPrimeFormula
open GaussianFermiZeroTail GaussianFermiPoleFormula

/-- The ordinary Gaussian-weighted von Mangoldt summand, with both its
real damping and original oscillatory phase explicit. -/
def ordinarySummand (σ B t : ℝ) (n : ℕ) : ℝ :=
  zetaPhasePrimeWeight σ n * window B (Real.log n) * Real.cos (t * Real.log n)

/-- The full ordinary Gaussian von Mangoldt series. -/
def ordinarySum (σ B t : ℝ) : ℝ := ∑' n : ℕ, ordinarySummand σ B t n

/-- The exact difference term has stronger real damping and retains its
Fermi factor, Gaussian scale and cosine phase. -/
def correctionSummand (σ B t : ℝ) (n : ℕ) : ℝ :=
  zetaPhasePrimeWeight (3 * σ - 1) n * window B (Real.log n) *
    fermi (-(2 * σ - 1) * Real.log n) * Real.cos (t * Real.log n)

/-- The complete signed Fermi correction, including every prime power. -/
def correctionSum (σ B t : ℝ) : ℝ := ∑' n : ℕ, correctionSummand σ B t n

/-- The original square-root normalization becomes exactly the ordinary
Dirichlet damping times the Fermi factor. -/
theorem primeSummand_eq_ordinary_mul_fermi (σ B t : ℝ) (n : ℕ) :
    primeSummand (2 * σ - 1) B t n =
      ordinarySummand σ B t n * fermi (-(2 * σ - 1) * Real.log n) := by
  by_cases hn : n = 0
  · simp [hn, primeSummand, ordinarySummand, zetaPhasePrimeWeight]
  · have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hroot : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt n := by
      have he : Real.exp (Real.log (n : ℝ) / 2) * Real.exp (Real.log (n : ℝ) / 2) = n := by
        rw [← Real.exp_add, add_halves, Real.exp_log hnp]
      nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (n : ℝ),
        Real.exp_pos (Real.log (n : ℝ) / 2)]
    have he : Real.exp (-B * Real.log (n : ℝ) ^ 2 - (2 * σ - 1) / 2 * Real.log n) /
        Real.sqrt n = Real.exp (-σ * Real.log n) * window B (Real.log n) := by
      rw [← hroot, ← Real.exp_sub]
      unfold window
      rw [← Real.exp_add]
      congr 1
      ring
    unfold primeSummand signal damped ordinarySummand zetaPhasePrimeWeight
    calc
      _ = ArithmeticFunction.vonMangoldt n *
          (Real.exp (-B * Real.log (n : ℝ) ^ 2 - (2 * σ - 1) / 2 * Real.log n) /
            Real.sqrt n) * fermi (-(2 * σ - 1) * Real.log n) * Real.cos (t * Real.log n) := by ring
      _ = _ := by rw [he]; ring

/-- The signed correction is the literal difference between the two
original prime summands, before any summation or norm is taken. -/
theorem ordinarySummand_eq_prime_add_correction (σ B t : ℝ) (n : ℕ) :
    ordinarySummand σ B t n = primeSummand (2 * σ - 1) B t n + correctionSummand σ B t n := by
  have hw : zetaPhasePrimeWeight (3 * σ - 1) n =
      zetaPhasePrimeWeight σ n * Real.exp (-(2 * σ - 1) * Real.log n) := by
    unfold zetaPhasePrimeWeight
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hp := weight_partition (2 * σ - 1) (fun _ => (1 : ℝ)) (Real.log n)
  simp only [weight, one_mul] at hp
  rw [primeSummand_eq_ordinary_mul_fermi, correctionSummand, hw]
  unfold ordinarySummand
  calc
    _ = (zetaPhasePrimeWeight σ n * window B (Real.log n) * Real.cos (t * Real.log n)) *
        (fermi (-(2 * σ - 1) * Real.log n) +
          Real.exp (-(2 * σ - 1) * Real.log n) * fermi (-(2 * σ - 1) * Real.log n)) := by
      rw [hp, mul_one]
    _ = _ := by ring

/-- A width-independent majorant controls the complete signed
correction term, uniformly in every real ordinate. -/
theorem norm_correctionSummand_le {σ₀ σ B : ℝ} (hσ : σ₀ ≤ σ) (hB : 0 ≤ B)
    (t : ℝ) (n : ℕ) :
    ‖correctionSummand σ B t n‖ ≤ zetaPhasePrimeWeight (3 * σ₀ - 1) n := by
  have hnlog : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  have hw : zetaPhasePrimeWeight (3 * σ - 1) n ≤ zetaPhasePrimeWeight (3 * σ₀ - 1) n := by
    unfold zetaPhasePrimeWeight
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    apply Real.exp_le_exp.mpr
    nlinarith
  have hwindow : window B (Real.log n) ≤ 1 := by
    unfold window
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  have hwpos : 0 ≤ window B (Real.log n) := (Real.exp_pos _).le
  have ha : 0 ≤ zetaPhasePrimeWeight (3 * σ - 1) n * window B (Real.log n) *
      fermi (-(2 * σ - 1) * Real.log n) := by
    exact mul_nonneg (mul_nonneg (zetaPhasePrimeWeight_nonneg _ _) hwpos) (fermi_bounds _).1.le
  rw [correctionSummand, norm_mul, Real.norm_of_nonneg ha]
  calc
    _ ≤ zetaPhasePrimeWeight (3 * σ - 1) n * window B (Real.log n) *
        fermi (-(2 * σ - 1) * Real.log n) := by
      apply mul_le_of_le_one_right ha
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * Real.log n)
    _ ≤ zetaPhasePrimeWeight (3 * σ - 1) n * window B (Real.log n) :=
      mul_le_of_le_one_right (mul_nonneg (zetaPhasePrimeWeight_nonneg _ _) hwpos)
        (fermi_bounds _).2.le
    _ ≤ zetaPhasePrimeWeight (3 * σ - 1) n :=
      mul_le_of_le_one_right (zetaPhasePrimeWeight_nonneg _ _) hwindow
    _ ≤ _ := hw

/-- The correction is genuinely absolutely convergent, also at zero
Gaussian width, throughout every closed half-plane above `2/3`. -/
theorem summable_correctionSummand {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀)
    (hσ : σ₀ ≤ σ) (hB : 0 ≤ B) (t : ℝ) : Summable (correctionSummand σ B t) := by
  exact (hasSum_zetaPhasePrimeWeight (by linarith : 1 < 3 * σ₀ - 1)).summable.of_norm_bounded
    (norm_correctionSummand_le hσ hB t)

/-- The entire correction is bounded by the actual convergent real
logarithmic derivative, with no dependence on width or height. -/
theorem norm_correctionSum_le {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀)
    (hσ : σ₀ ≤ σ) (hB : 0 ≤ B) (t : ℝ) :
    ‖correctionSum σ B t‖ ≤ (-logDeriv riemannZeta ((3 * σ₀ - 1 : ℝ) : ℂ)).re := by
  have hs := hasSum_zetaPhasePrimeWeight (by linarith : 1 < 3 * σ₀ - 1)
  unfold correctionSum
  calc
    _ ≤ ∑' n : ℕ, ‖correctionSummand σ B t n‖ :=
      norm_tsum_le_tsum_norm (summable_correctionSummand hσ₀ hσ hB t).norm
    _ ≤ ∑' n : ℕ, zetaPhasePrimeWeight (3 * σ₀ - 1) n :=
      Summable.tsum_le_tsum (norm_correctionSummand_le hσ hB t)
        (summable_correctionSummand hσ₀ hσ hB t).norm hs.summable
    _ = _ := hs.tsum_eq

/-- The ordinary Gaussian sum has genuine convergence, established from
the proved convergence of the original Fermi sum and its full correction. -/
theorem summable_ordinarySummand {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀)
    (hσ : σ₀ ≤ σ) (hB : 0 < B) (t : ℝ) : Summable (ordinarySummand σ B t) := by
  have hp := summable_primeSummand (by linarith : 0 ≤ 2 * σ - 1) hB t
  exact (hp.add (summable_correctionSummand hσ₀ hσ hB.le t)).congr
    (fun n => (ordinarySummand_eq_prime_add_correction σ B t n).symm)

/-- Exact evaluation of the full signed difference. The two convergent
series and their correction share the same original logarithmic phase. -/
theorem ordinarySum_eq_primeSum_add_correction {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀)
    (hσ : σ₀ ≤ σ) (hB : 0 < B) (t : ℝ) :
    ordinarySum σ B t = primeSum (2 * σ - 1) B t + correctionSum σ B t := by
  unfold ordinarySum
  simp_rw [ordinarySummand_eq_prime_add_correction]
  exact (summable_primeSummand (by linarith : 0 ≤ 2 * σ - 1) hB t).tsum_add
    (summable_correctionSummand hσ₀ hσ hB.le t)

/-- Removing the Fermi factor changes the full signed prime sum by at
most one width- and height-independent constant. -/
theorem norm_ordinarySum_sub_primeSum_le {σ₀ σ B : ℝ} (hσ₀ : 2 / 3 < σ₀)
    (hσ : σ₀ ≤ σ) (hB : 0 < B) (t : ℝ) :
    ‖ordinarySum σ B t - primeSum (2 * σ - 1) B t‖ ≤
      (-logDeriv riemannZeta ((3 * σ₀ - 1 : ℝ) : ℂ)).re := by
  rw [ordinarySum_eq_primeSum_add_correction hσ₀ hσ hB t, add_sub_cancel_left]
  exact norm_correctionSum_le hσ₀ hσ hB.le t

/-- The full actual zero formula may use the ordinary Gaussian prime
sum, with the exact signed correction retained beside it. The preceding
bound controls this complete correction uniformly in width and height. -/
theorem zero_side_eq_poles_digamma_sub_ordinary_add_correction {σ₀ σ b c : ℝ}
    (hσ₀ : 2 / 3 < σ₀) (hσ : σ₀ ≤ σ) (hb : 0 < b) (hc : 0 < c) (t : ℝ) :
    (∑' ρ : NontrivialZetaZero, contribution (b + c) σ t ρ) =
      polePair (b + c) σ t - Real.log Real.pi / 4 +
        digammaAverage (2 * σ - 1) b c t - ordinarySum σ (b + c) t + correctionSum σ (b + c) t := by
  have hzero := zero_side_eq_poles_digamma_sub_prime hb hc (by linarith : 1 / 2 ≤ σ) t
  rw [ordinarySum_eq_primeSum_add_correction hσ₀ hσ (add_pos hb hc) t]
  linarith

end
end RiemannGaussian.GaussianFermiPrimeComparison
