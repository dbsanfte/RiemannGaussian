/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeQuadraticMoments

/-!
# Literal arithmetic of the separated prime quadratic

The pure quadratic uses the Dirichlet convolution of von Mangoldt with
itself. Its mixed companion convolves von Mangoldt with the full
prime-divisor weight. Their coefficientwise difference is the already
proved nonnegative composite convolution. All three responses use the
same complex moment kernel, including every derivative of the actual
finite pole weight. Positivity of coefficients is not asserted to
survive that kernel.
-/

open Complex Filter Topology
open scoped Classical LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The complete ordered prime-power pair coefficient. -/
def zetaPrimePairArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt

/-- The prime-power coefficient convolved with both divisor colours. -/
def zetaPrimeMixedProductArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt *
    (ArithmeticFunction.vonMangoldt + zetaMixedPrimeArithmetic)

/-- The exact arithmetic decomposition precedes every filtering or
norm: the mixed coefficient includes the pure pair and the composite arm. -/
theorem zetaPrimeMixedProductArithmetic_eq :
    zetaPrimeMixedProductArithmetic = zetaPrimePairArithmetic + zetaPositiveCompositeArithmetic := by
  rw [zetaPrimeMixedProductArithmetic, mul_add, zetaPrimePairArithmetic,
    zetaPositiveCompositeArithmetic_eq]

/-- Every ordered prime-pair coefficient is nonnegative. -/
theorem zetaPrimePairArithmetic_nonneg (n : ℕ) : 0 ≤ zetaPrimePairArithmetic n := by
  rw [zetaPrimePairArithmetic, ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg (fun _ _ ↦
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)

/-- Before the complex filter, the complete mixed coefficient
dominates the prime pair coefficient at each integer. -/
theorem zetaPrimePairArithmetic_le_mixed (n : ℕ) :
    zetaPrimePairArithmetic n ≤ zetaPrimeMixedProductArithmetic n := by
  rw [zetaPrimeMixedProductArithmetic_eq, ArithmeticFunction.add_apply]
  exact le_add_of_nonneg_right (zetaPositiveCompositeArithmetic_nonneg n)

private theorem prime_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s (-logDeriv riemannZeta s) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  simpa only [logDeriv_apply, neg_div] using h

private theorem convolution_cast (a b : ArithmeticFunction ℝ) :
    (fun n ↦ ((a * b) n : ℂ)) = (fun n ↦ (a n : ℂ)) ⍟ (fun n ↦ (b n : ℂ)) := by
  funext n
  simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    LSeries.convolution_def]

/-- The pure pair series genuinely converges to the square of the
actual zeta logarithmic derivative throughout the Euler half-plane. -/
theorem LSeriesHasSum_zetaPrimePairArithmetic {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (zetaPrimePairArithmetic n : ℂ)) s ((logDeriv riemannZeta s) ^ 2) := by
  rw [zetaPrimePairArithmetic, convolution_cast]
  simpa only [neg_mul_neg, ← pow_two, neg_sq] using (prime_hasSum hs).convolution (prime_hasSum hs)

/-- The whole mixed product is its genuine arithmetic convolution,
with both colours in the second factor. -/
theorem LSeriesHasSum_zetaPrimeMixedProductArithmetic {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (zetaPrimeMixedProductArithmetic n : ℂ)) s
      ((-logDeriv riemannZeta s) * zetaPrimeDivisorResponse s) := by
  rw [zetaPrimeMixedProductArithmetic, convolution_cast]
  exact (prime_hasSum hs).convolution (LSeriesHasSum_zetaPrimeDivisorResponse hs)

/-- The common arithmetic cofactor retains the actual quadratic
pole-clearing weight and the full quartic factor at one. -/
def zetaPrimeQuadraticCofactor (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaPrimeQuadraticWeight rho s * (s - 1) ^ 4

/-- The complete complex arithmetic kernel retains all cofactor
derivatives and the original oscillatory Dirichlet feature. -/
def zetaPrimeQuadraticKernel (rho : NontrivialZetaZero) (N n : ℕ) : ℂ :=
  zetaPrimeFeature (zetaWronskianMomentCenter rho) n *
    ∑ k ∈ Finset.range (N + 1),
      signedTaylorMoment k (zetaPrimeQuadraticCofactor rho) (zetaWronskianMomentCenter rho) *
        ((Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ))

/-- The complete cofactor is entire, including the actual finite
weight that handles all other zeros of arbitrary multiplicity. -/
theorem analyticAt_zetaPrimeQuadraticCofactor (rho : NontrivialZetaZero) (s : ℂ) :
    AnalyticAt ℂ (zetaPrimeQuadraticCofactor rho) s :=
  (analyticAt_zetaPrimeQuadraticWeight rho s).mul ((analyticAt_id.sub analyticAt_const).pow 4)

private theorem weighted_series_moment {c : ℕ → ℂ} (hc0 : c 0 = 0) {V : ℂ → ℂ}
    (hV : ∀ s : ℂ, 1 < s.re → LSeriesHasSum c s (V s)) (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ c n * zetaPrimeQuadraticKernel rho N n)
      (signedTaylorMoment N (fun z ↦ zetaPrimeQuadraticCofactor rho z * V z)
        (zetaWronskianMomentCenter rho)) := by
  have hs : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hb : LSeries.abscissaOfAbsConv c ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact (hV x (by simpa using hx)).LSeriesSummable
  have he : (fun z ↦ zetaPrimeQuadraticCofactor rho z * V z) =ᶠ[𝓝 (zetaWronskianMomentCenter rho)]
      (fun z ↦ zetaPrimeQuadraticCofactor rho z * LSeries c z) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    rw [(hV z hz).LSeries_eq]
  rw [signedTaylorMoment_congr N he]
  simpa only [zetaPrimeQuadraticKernel, mul_assoc] using
    hasSum_signedTaylorMoment_mul_LSeries c hc0 (analyticAt_zetaPrimeQuadraticCofactor rho _)
      (lt_of_le_of_lt hb (by exact_mod_cast hs)) N

/-- The surviving quadratic is a genuine convergent sum over the
literal ordered prime-power pairs with the unchanged complex kernel. -/
theorem hasSum_zetaPrimeQuadraticMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaPrimePairArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)
      (zetaPrimeQuadraticMoment rho N) := by
  have h := weighted_series_moment (by simp) (fun _ hs ↦ LSeriesHasSum_zetaPrimePairArithmetic hs) rho N
  change HasSum _ (signedTaylorMoment N (fun z ↦ zetaPrimeQuadraticWeight rho z *
    zetaPrimeSquareResponse z) (zetaWronskianMomentCenter rho))
  simpa only [zetaPrimeQuadraticMoment, zetaPrimeSquareResponse, zetaPrimeQuadraticCofactor,
    Pi.mul_apply, mul_assoc] using h

/-- The independently bounded mixed moment is its complete
arithmetic convolution, not a replacement by separate factor bounds. -/
theorem hasSum_zetaPrimeMixedProductMoment (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaPrimeMixedProductArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)
      (zetaPrimeMixedProductMoment rho N) := by
  have h := weighted_series_moment (by simp)
    (fun _ hs ↦ LSeriesHasSum_zetaPrimeMixedProductArithmetic hs) rho N
  change HasSum _ (signedTaylorMoment N (fun z ↦ zetaPrimeQuadraticWeight rho z *
    zetaPrimeMixedProductResponse z) (zetaWronskianMomentCenter rho))
  simpa only [zetaPrimeMixedProductMoment, zetaPrimeMixedProductResponse, zetaPrimeQuadraticCofactor,
    Pi.mul_apply, mul_assoc] using h

/-- The exact positive composite arithmetic is the signed difference
of the two complete moments, retaining the common filter unchanged. -/
theorem hasSum_zetaPrimeQuadraticComposite (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)
      (zetaPrimeMixedProductMoment rho N - zetaPrimeQuadraticMoment rho N) := by
  have h := (hasSum_zetaPrimeMixedProductMoment rho N).sub (hasSum_zetaPrimeQuadraticMoment rho N)
  simpa only [zetaPrimeMixedProductArithmetic_eq, ArithmeticFunction.add_apply, Complex.ofReal_add,
    add_mul, add_sub_cancel_left] using h

/-- The literal mixed arithmetic sum has an independent quantitative
sub-source bound, with every coefficient and cross term preserved. -/
theorem exists_zetaPrimeMixedArithmetic_decay_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) *
        (∑' n, (zetaPrimeMixedProductArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)) /
          ((N + 1 : ℕ) : ℂ)‖ ≤ C / ((N + 1 : ℕ) : ℝ) := by
  simpa only [(hasSum_zetaPrimeMixedProductMoment _ _).tsum_eq] using
    exists_zetaPrimeMixedProductMoment_decay_bound rho hrho

/-- Despite coefficientwise domination by the mixed convolution,
the prime-pair sum retains the full selected source through this
complex filter. Raw coefficient positivity does not compare the limits. -/
theorem tendsto_zetaPrimePairArithmetic_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) *
      (∑' n, (zetaPrimePairArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 (zetaPrimeQuadraticSource rho)) := by
  simpa only [(hasSum_zetaPrimeQuadraticMoment _ _).tsum_eq] using
    tendsto_zetaPrimeQuadraticMoment rho hrho

/-- The positive composite sum has the opposite nonzero signed
source after the whole mixed product has been independently bounded. -/
theorem tendsto_zetaPrimeQuadraticComposite_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((zetaWronskianMomentCenter rho - rho.1) ^ (N + 2) *
      (∑' n, (zetaPositiveCompositeArithmetic n : ℂ) * zetaPrimeQuadraticKernel rho N n)) /
        ((N + 1 : ℕ) : ℂ)) atTop (𝓝 (-zetaPrimeQuadraticSource rho)) := by
  simpa only [(hasSum_zetaPrimeQuadraticComposite _ _).tsum_eq, mul_sub, sub_div, zero_sub] using
    (tendsto_zetaPrimeMixedProductMoment rho hrho).sub (tendsto_zetaPrimeQuadraticMoment rho hrho)

end

end RiemannGaussian
