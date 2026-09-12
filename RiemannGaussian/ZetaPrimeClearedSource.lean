/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MeromorphicPolynomialSource
import RiemannGaussian.ZetaPrimeClearedHeat
import RiemannGaussian.ZetaPositiveCompositeResponse
import RiemannGaussian.ZetaMoebiusWronskianMoments

/-!
# The actual ordinary-prime source after polynomial clearing

For every fixed divisor cutoff and finite prime exclusion, the original
ordinary-prime series continues as the negative logarithmic derivative of
zeta minus the analytic proper-prime-power series and the exact finite
excluded head. Its residue at a selected right-half zero is the negative
multiplicity. The actual finite divisor polynomial clears every other pole
and preserves this selected source with a geometric moment error.

The cutoff and exclusions are fixed in the source limit. No uniform claim
for moving cutoffs or joint growing-order Gaussian widths is made here.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter Metric Set Topology
open scoped Classical ArithmeticFunction.Moebius

/-- The full ordinary-prime logarithmic coefficient before the finite head
and prime sieve are removed. -/
def ordinaryPrimeCoefficient (n : ℕ) : ℂ := if n.Prime then (Real.log n : ℂ) else 0

/-- The exact finite set removed from the ordinary-prime series. Composite
indices in this set have zero coefficient. -/
def primeExcludedHead (D : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  zetaFiniteDirichletSeries (Finset.Icc 1 D ∪ S) ordinaryPrimeCoefficient s

/-- The literal prime tail's meromorphic continuation, keeping both its
proper-prime-power subtraction and every finite excluded prime. -/
def primeTailContinuation (D : ℕ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s - (zetaProperPrimePowerSeries s + primeExcludedHead D S s)

/-- The original coefficients equal the full prime coefficient minus the
finite excluded head, before any analytic operation. -/
theorem primeCorrectionCoefficient_eq_full_sub_head {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (n : ℕ) :
    primeCorrectionCoefficient D S n = ordinaryPrimeCoefficient n -
      zetaFiniteCoefficient (Finset.Icc 1 D ∪ S) ordinaryPrimeCoefficient n := by
  rw [primeCorrectionCoefficient_eq_prime_tail hD S hS]
  by_cases hp : n.Prime
  · have hn : 1 ≤ n := hp.one_le
    by_cases hcut : D < n <;> by_cases hnS : n ∈ S <;>
      simp [ordinaryPrimeCoefficient, zetaFiniteCoefficient, Finset.mem_Icc, hp, hcut,
        hnS, hn, Nat.not_le_of_gt, Nat.le_of_not_gt]
  · simp [ordinaryPrimeCoefficient, zetaFiniteCoefficient, hp]

/-- Absolute Euler convergence identifies the complete ordinary-prime
series with its signed logarithmic-derivative continuation. -/
theorem LSeriesHasSum_ordinaryPrime {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum ordinaryPrimeCoefficient s
      (-(logDeriv riemannZeta s + zetaProperPrimePowerSeries s)) := by
  have h := (LSeriesHasSum_zetaMoebiusPrimeDerivative hs).neg
  have he : -(fun n ↦ if n.Prime then zetaMoebiusDerivativeCoefficient n else 0) =
      ordinaryPrimeCoefficient := by
    funext n
    by_cases hp : n.Prime
    · simp [ordinaryPrimeCoefficient, zetaMoebiusDerivativeCoefficient, hp,
        ArithmeticFunction.moebius_apply_prime hp]
    · simp [ordinaryPrimeCoefficient, hp]
  rwa [he] at h

/-- The meromorphic formula is the actual convergent fixed-support prime
series on the whole Euler half-plane. -/
theorem LSeriesHasSum_primeTailContinuation {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (primeCorrectionCoefficient D S) s (primeTailContinuation D S s) := by
  have hzero : 0 ∉ Finset.Icc 1 D ∪ S := by
    simp only [Finset.mem_union, Finset.mem_Icc, not_or]
    exact ⟨by omega, fun h ↦ Nat.not_prime_zero (hS 0 h)⟩
  have h := (LSeriesHasSum_ordinaryPrime hs).sub
    (LSeriesHasSum_zetaFiniteCoefficient (Finset.Icc 1 D ∪ S) ordinaryPrimeCoefficient hzero s)
  have he : ordinaryPrimeCoefficient -
      zetaFiniteCoefficient (Finset.Icc 1 D ∪ S) ordinaryPrimeCoefficient = primeCorrectionCoefficient D S := by
    funext n
    exact (primeCorrectionCoefficient_eq_full_sub_head hD S hS n).symm
  rw [he] at h
  convert! h using 1
  unfold primeTailContinuation primeExcludedHead
  ring

/-- The prime tail and its continuation agree at every Euler point. -/
theorem primeTailContinuation_eq_LSeries {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) {s : ℂ} (hs : 1 < s.re) :
    primeTailContinuation D S s = LSeries (primeCorrectionCoefficient D S) s :=
  (LSeriesHasSum_primeTailContinuation hD S hS hs).LSeries_eq.symm

/-- The complete nonpolar subtraction is analytic throughout the right
half of the zero strip; finite prime exclusions introduce no new poles. -/
theorem analyticAt_primeTailCorrection (D : ℕ) (S : Finset ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (fun z ↦ zetaProperPrimePowerSeries z + primeExcludedHead D S z) s :=
  (analyticAt_zetaProperPrimePowerSeries hs).add
    ((differentiable_zetaFiniteDirichletSeries _ _).analyticAt s)

/-- The actual ordinary-prime tail continues meromorphically throughout
the right half-strip, retaining all zeta poles there. -/
theorem meromorphicAt_primeTailContinuation (D : ℕ) (S : Finset ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    MeromorphicAt (primeTailContinuation D S) s := by
  have hz := meromorphicAt_riemannZeta s
  exact (hz.deriv.div hz).neg.sub (analyticAt_primeTailCorrection D S hs).meromorphicAt

private theorem order_log_zero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta rho.1)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    have hm := analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (show (analyticZetaZeroMultiplicity rho : ℤ) ≠ 0 by omega)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    exact WithTop.coe_ne_top

private theorem order_log_lt_correction (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (-(logDeriv riemannZeta)) rho.1 <
      meromorphicOrderAt (fun z ↦ zetaProperPrimePowerSeries z + primeExcludedHead D S z) rho.1 := by
  rw [← meromorphicOrderAt_neg, order_log_zero]
  apply lt_of_lt_of_le _ (analyticAt_primeTailCorrection D S hrho).meromorphicOrderAt_nonneg
  change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- Removing any fixed finite prime head does not change the selected
zero's simple pole in the ordinary-prime continuation. -/
theorem meromorphicOrderAt_primeTailContinuation (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (primeTailContinuation D S) rho.1 = -1 := by
  change meromorphicOrderAt (-(logDeriv riemannZeta) -
    (fun z ↦ zetaProperPrimePowerSeries z + primeExcludedHead D S z)) rho.1 = _
  rw [sub_eq_add_neg, meromorphicOrderAt_add_eq_left_of_lt
    (analyticAt_primeTailCorrection D S hrho).meromorphicAt.neg (by
      simpa only [← meromorphicOrderAt_neg] using order_log_lt_correction D S rho hrho),
    ← meromorphicOrderAt_neg, order_log_zero]

/-- The selected ordinary-prime residue is exactly the negative analytic
zero multiplicity, including its sign. -/
theorem meromorphicTrailingCoeffAt_primeTailContinuation (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicTrailingCoeffAt (primeTailContinuation D S) rho.1 =
      -(analyticZetaZeroMultiplicity rho : ℂ) := by
  change meromorphicTrailingCoeffAt (-(logDeriv riemannZeta) -
    (fun z ↦ zetaProperPrimePowerSeries z + primeExcludedHead D S z)) rho.1 = _
  rw [(analyticAt_primeTailCorrection D S hrho).meromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt
      (order_log_lt_correction D S rho hrho), meromorphicTrailingCoeffAt_neg]
  have hm : ((analyticZetaZeroMultiplicity rho : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  rw [meromorphicTrailingCoeffAt_logDeriv_of_order (meromorphicAt_riemannZeta rho.1) hm
    (meromorphicOrderAt_riemannZeta_nontrivialZero rho)]
  simp

/-- The continuation is analytic at every Euler center, with zeta
nonvanishing and all series hypotheses discharged. -/
theorem analyticAt_primeTailContinuation (D : ℕ) (S : Finset ℕ) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (primeTailContinuation D S) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact (hz.deriv.div hz (riemannZeta_ne_zero_of_one_lt_re hs)).neg.sub
    (analyticAt_primeTailCorrection D S (by linarith))

/-- The actual prime factorial moment agrees with the derivative of its
polynomially cleared meromorphic continuation at every Euler point. -/
theorem clearedPrimeMoment_eq_continuation (q : Polynomial ℂ) {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    clearedPrimeMoment q D S N s =
      signedTaylorMoment N (fun z ↦ q.eval z * primeTailContinuation D S z) s := by
  apply signedTaylorMoment_congr
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
  rw [primeTailContinuation_eq_LSeries hD S hS hz]

/-- The actual divisor polynomial of the fixed-support prime continuation,
on the existing zero-centered compact domain, excluding the selected zero. -/
def primeTailClearingPolynomial (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero) : Polynomial ℂ :=
  meromorphicPairClearingPolynomial (primeTailContinuation D S) (fun _ ↦ 0)
    (isCompact_closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)) rho.1

/-- Normalization fixes the selected value to one without changing any
pole-clearing root, so the source keeps its literal negative multiplicity. -/
def normalizedPrimeTailClearingPolynomial (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) : Polynomial ℂ :=
  Polynomial.C ((primeTailClearingPolynomial D S rho).eval rho.1)⁻¹ *
    primeTailClearingPolynomial D S rho

/-- The exact finite divisor polynomial never vanishes at its selected zero. -/
theorem primeTailClearingPolynomial_eval_ne_zero (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) : (primeTailClearingPolynomial D S rho).eval rho.1 ≠ 0 :=
  meromorphicPairClearingPolynomial_eval_ne_zero _ _ _ _

/-- The normalized actual clearing polynomial has selected value exactly one. -/
theorem normalizedPrimeTailClearingPolynomial_eval (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) : (normalizedPrimeTailClearingPolynomial D S rho).eval rho.1 = 1 := by
  simp only [normalizedPrimeTailClearingPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  exact inv_mul_cancel₀ (primeTailClearingPolynomial_eval_ne_zero D S rho)

private theorem domain_re_gt_half (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {s : ℂ} (hs : s ∈ closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)) :
    1 / 2 < s.re := by
  have hnorm : ‖s - zetaWronskianMomentCenter rho‖ ≤ zetaWronskianMomentRadius rho := by
    simpa [mem_closedBall, dist_eq_norm] using hs
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (s - zetaWronskianMomentCenter rho)).trans hnorm)).1
  have hc : (zetaWronskianMomentCenter rho).re = 3 / 2 := by simp [zetaWronskianMomentCenter]
  rw [Complex.sub_re, hc] at hre
  have hR := (zetaWronskianMomentRadius_spec rho hrho).2.2
  linarith

/-- With every other pole genuinely cleared, the original fixed-support
prime moment retains the selected source with an independent geometric
error. This estimates the error around the source, not the prime sum itself. -/
theorem exists_normalizedClearedPrimeMoment_source_error {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖(zetaWronskianMomentCenter rho - rho.1) ^ (N + 1) *
        clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N
          (zetaWronskianMomentCenter rho) + (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤
        C * (‖zetaWronskianMomentCenter rho - rho.1‖ / zetaWronskianMomentRadius rho) ^ N := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have heuler : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hf : MeromorphicOn (primeTailContinuation D S)
      (closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)) :=
    fun _ hs ↦ meromorphicAt_primeTailContinuation D S (domain_re_gt_half rho hrho hs)
  have hne : zetaWronskianMomentCenter rho ≠ rho.1 := sub_ne_zero.mp (norm_pos_iff.mp hspec.1)
  obtain ⟨C, hC, hb⟩ := exists_meromorphicClearingPolynomial_source (g := fun _ ↦ 0)
    hf (analyticAt_primeTailContinuation D S heuler) hspec.2.1 hne
    (meromorphicOrderAt_primeTailContinuation D S rho hrho)
  let w := (primeTailClearingPolynomial D S rho).eval rho.1
  have hw : w ≠ 0 := primeTailClearingPolynomial_eval_ne_zero D S rho
  have hwpos : 0 < ‖w⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hw)
  refine ⟨‖w⁻¹‖ * C, mul_pos hwpos hC, fun N ↦ ?_⟩
  have hpol : (fun z ↦ (normalizedPrimeTailClearingPolynomial D S rho).eval z * primeTailContinuation D S z) =
      (fun z ↦ w⁻¹ * ((primeTailClearingPolynomial D S rho).eval z * primeTailContinuation D S z)) := by
    ext z
    simp only [normalizedPrimeTailClearingPolynomial, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, w]
  have he : (zetaWronskianMomentCenter rho - rho.1) ^ (N + 1) *
      clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N
        (zetaWronskianMomentCenter rho) + (analyticZetaZeroMultiplicity rho : ℂ) =
      w⁻¹ * ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 1) *
        signedTaylorMoment N (fun z ↦ (primeTailClearingPolynomial D S rho).eval z *
          primeTailContinuation D S z) (zetaWronskianMomentCenter rho) -
        w * (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
    rw [clearedPrimeMoment_eq_continuation _ hD S hS N heuler, hpol, signedTaylorMoment_const_mul]
    field_simp
    ring
  have hbN := hb N
  rw [meromorphicTrailingCoeffAt_primeTailContinuation D S rho hrho,
    ← meromorphicPairClearingPolynomial_eval] at hbN
  change ‖(zetaWronskianMomentCenter rho - rho.1) ^ (N + 1) *
      signedTaylorMoment N (fun z ↦ (primeTailClearingPolynomial D S rho).eval z *
        primeTailContinuation D S z) (zetaWronskianMomentCenter rho) -
      w * (-(analyticZetaZeroMultiplicity rho : ℂ))‖ ≤ _ at hbN
  rw [he, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hbN (norm_nonneg _)

/-- The actual polynomially cleared prime moment converges to the negative
zero multiplicity for every fixed cutoff and prime exclusion. Its arithmetic
formula is the complete Leibniz sum and its heat is the full Hermite transport. -/
theorem tendsto_normalizedClearedPrimeMoment {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (zetaWronskianMomentCenter rho - rho.1) ^ (N + 1) *
      clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N
        (zetaWronskianMomentCenter rho)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have hR : 0 < zetaWronskianMomentRadius rho := hspec.1.trans hspec.2.1
  obtain ⟨C, _, hb⟩ := exists_normalizedClearedPrimeMoment_source_error hD S hS rho hrho
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (norm_nonneg _) hR.le) ((div_lt_one hR).mpr hspec.2.1)).const_mul C
  have he := squeeze_zero_norm hb (by simpa using ht)
  have h := he.sub_const (analyticZetaZeroMultiplicity rho : ℂ)
  simpa only [add_sub_cancel_right, zero_sub] using h

end
end RiemannGaussian.SquarefreeEulerQuadratic
