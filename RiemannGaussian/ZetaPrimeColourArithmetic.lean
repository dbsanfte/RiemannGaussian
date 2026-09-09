/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPositiveCompositeMoments

/-!
# The complete prime-power and mixed-prime arithmetic split

The two nonnegative divisor weights have disjoint support. Their actual
zeta functions have opposite zero poles, while their sum contains only
zeta and its derivative, with no reciprocal zeta factor. The positive
composite response is their exact Dirichlet-convolution product. These
identities retain the arithmetic split before any moment estimate.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.zeta LSeries.notation

namespace RiemannGaussian

noncomputable section

/-- The mixed-prime divisor defect vanishes on every prime power. -/
theorem zetaMixedPrimeArithmetic_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    zetaMixedPrimeArithmetic (p ^ k) = 0 := by
  rw [zetaMixedPrimeArithmetic_apply, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hm : p ∈ (p ^ k).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self p hk.ne', pow_ne_zero _ hp.ne_zero⟩
  have he : (∑ d ∈ (p ^ k).divisors, if d.Prime then Real.log d else 0) = Real.log p := by
    rw [Finset.sum_eq_single p]
    · simp [hp]
    · intro d hd hdp
      by_cases hdprime : d.Prime
      · have hdeq : d = p := (Nat.prime_dvd_prime_iff_eq hdprime hp).mp
          (hdprime.dvd_of_dvd_pow (Nat.mem_divisors.mp hd).1)
        exact False.elim (hdp hdeq)
      · simp [hdprime]
    · exact fun h ↦ False.elim (h hm)
  rw [he, sub_self]

/-- The two nonnegative arithmetic weights are pointwise orthogonal:
one lives on prime powers, the other on integers with mixed prime support. -/
theorem vonMangoldt_mul_zetaMixedPrimeArithmetic (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * zetaMixedPrimeArithmetic n = 0 := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    rw [zetaMixedPrimeArithmetic_prime_pow hp hk, mul_zero]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_mul]

/-- The complete positive composite convolution also has no
prime-power support; logarithmic convolution does not recreate that arm. -/
theorem zetaPositiveCompositeArithmetic_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    zetaPositiveCompositeArithmetic (p ^ k) = 0 := by
  rw [zetaPositiveCompositeArithmetic_eq, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro a ha
  have hdvd : a.2 ∣ p ^ k := ⟨a.1, by
    simpa only [mul_comm] using (Nat.mem_divisorsAntidiagonal.mp ha).1.symm⟩
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hj]
  by_cases hj0 : j = 0
  · simp [hj0, zetaMixedPrimeArithmetic_apply]
  · rw [zetaMixedPrimeArithmetic_prime_pow hp (Nat.pos_of_ne_zero hj0), mul_zero]

/-- The complete prime-divisor weight, with both arithmetic colours kept. -/
def zetaPrimeDivisorCoefficient (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n + zetaMixedPrimeArithmetic n

/-- The common weight is the literal sum of logarithms of distinct
prime divisors, before any summatory or asymptotic approximation. -/
theorem zetaPrimeDivisorCoefficient_eq (n : ℕ) :
    zetaPrimeDivisorCoefficient n = ∑ d ∈ n.divisors, if d.Prime then Real.log d else 0 := by
  rw [zetaPrimeDivisorCoefficient, zetaMixedPrimeArithmetic_apply]
  ring

/-- The common divisor weight is nonnegative at every integer. -/
theorem zetaPrimeDivisorCoefficient_nonneg (n : ℕ) : 0 ≤ zetaPrimeDivisorCoefficient n :=
  add_nonneg ArithmeticFunction.vonMangoldt_nonneg (zetaMixedPrimeArithmetic_nonneg n)

/-- Keeping the two colours as a signed difference loses no coefficient
magnitude: disjoint support makes its square equal the complete square. -/
theorem zetaPrimeDivisorColour_sq (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n - zetaMixedPrimeArithmetic n) ^ 2 =
      zetaPrimeDivisorCoefficient n ^ 2 := by
  have h := vonMangoldt_mul_zetaMixedPrimeArithmetic n
  unfold zetaPrimeDivisorCoefficient
  nlinarith

private theorem mixed_convolution :
    (fun n ↦ (zetaMixedPrimeArithmetic n : ℂ)) =
      (fun _ : ℕ ↦ (1 : ℂ)) ⍟ zetaMoebiusCompositeDerivativeCoefficient := by
  calc
    _ = (fun n ↦ (((ζ : ArithmeticFunction ℝ) * zetaMoebiusCompositeArithmetic) n : ℂ)) := by
      rw [zeta_mul_compositeArithmetic]
    _ = (fun n ↦ ((ζ : ArithmeticFunction ℝ) n : ℂ)) ⍟
        (fun n ↦ (zetaMoebiusCompositeArithmetic n : ℂ)) := by
      funext n
      simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        LSeries.convolution_def]
    _ = _ := LSeries.convolution_congr
      (fun {n} hn ↦ by simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn])
      (fun {n} _ ↦ zetaMoebiusCompositeArithmetic_cast n)

/-- The actual mixed-prime zeta response, complementary to the negative
logarithmic derivative and represented by nonnegative coefficients. -/
def zetaMixedPrimeResponse (s : ℂ) : ℂ :=
  logDeriv riemannZeta s - deriv riemannZeta s - riemannZeta s * zetaProperPrimePowerSeries s

/-- The common response has no reciprocal zeta factor. -/
def zetaPrimeDivisorResponse (s : ℂ) : ℂ :=
  -deriv riemannZeta s - riemannZeta s * zetaProperPrimePowerSeries s

/-- The complementary mixed-prime function is its genuine absolutely
convergent arithmetic series in the Euler half-plane. -/
theorem LSeriesHasSum_zetaMixedPrimeResponse {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (zetaMixedPrimeArithmetic n : ℂ)) s (zetaMixedPrimeResponse s) := by
  rw [mixed_convolution]
  have h := (LSeriesHasSum_one hs).convolution (LSeriesHasSum_zetaMoebiusCompositeDerivative hs)
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have he : riemannZeta s * (deriv riemannZeta s / riemannZeta s ^ 2 -
      (logDeriv riemannZeta s + zetaProperPrimePowerSeries s)) = zetaMixedPrimeResponse s := by
    simp only [zetaMixedPrimeResponse, logDeriv_apply]
    field_simp
    ring
  exact he ▸ h

/-- The two signed analytic responses sum exactly to the common
divisor response, even before a zero hypothesis or a norm is applied. -/
theorem zetaPrimeColourResponse_sum (s : ℂ) :
    -logDeriv riemannZeta s + zetaMixedPrimeResponse s = zetaPrimeDivisorResponse s := by
  simp only [zetaMixedPrimeResponse, zetaPrimeDivisorResponse]
  ring

/-- The common response is the genuine series of the full nonnegative
prime-divisor logarithmic weight, with both colours included. -/
theorem LSeriesHasSum_zetaPrimeDivisorResponse {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ (zetaPrimeDivisorCoefficient n : ℂ)) s (zetaPrimeDivisorResponse s) := by
  have hp := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hp
  have h := hp.add (LSeriesHasSum_zetaMixedPrimeResponse hs)
  have he : -deriv riemannZeta s / riemannZeta s + zetaMixedPrimeResponse s =
      zetaPrimeDivisorResponse s := by
    simpa only [logDeriv_apply, neg_div] using zetaPrimeColourResponse_sum s
  rw [he] at h
  change LSeriesHasSum (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) +
    (zetaMixedPrimeArithmetic n : ℂ)) s (zetaPrimeDivisorResponse s) at h
  simpa only [zetaPrimeDivisorCoefficient, Complex.ofReal_add] using h

/-- The common response is analytic throughout the larger half-plane
away from one, including at every hypothetical right-half zero. -/
theorem analyticAt_zetaPrimeDivisorResponse {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ zetaPrimeDivisorResponse s := by
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact hz.deriv.neg.sub (hz.mul (analyticAt_zetaProperPrimePowerSeries hs))

/-- The mixed-prime continuation is genuinely meromorphic where its
common divisor response is analytic, with all zeta zeros retained. -/
theorem meromorphicAt_zetaMixedPrimeResponse {s : ℂ} (hs : 1 / 2 < s.re) :
    MeromorphicAt zetaMixedPrimeResponse s := by
  have hz := meromorphicAt_riemannZeta s
  exact ((hz.deriv.div hz).sub hz.deriv).sub
    (hz.mul (analyticAt_zetaProperPrimePowerSeries hs).meromorphicAt)

private theorem mixed_eq : zetaMixedPrimeResponse = logDeriv riemannZeta + zetaPrimeDivisorResponse := by
  funext s
  simp only [zetaMixedPrimeResponse, zetaPrimeDivisorResponse, Pi.add_apply]
  ring

private theorem order_log_zero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta rho.1)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    have hm := analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (show (analyticZetaZeroMultiplicity rho : ℤ) ≠ 0 by omega)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    exact WithTop.coe_ne_top

private theorem order_log_lt_common (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 < meromorphicOrderAt zetaPrimeDivisorResponse rho.1 := by
  have hs1 : rho.1 ≠ 1 := by
    intro h
    have hr := NontrivialZetaZero.re_lt_one rho
    simp [h] at hr
  rw [order_log_zero]
  apply lt_of_lt_of_le _ (analyticAt_zetaPrimeDivisorResponse hrho hs1).meromorphicOrderAt_nonneg
  change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- The complementary nonnegative mixed-prime series has a simple
pole at every right-half zero, before any filter or phase selection. -/
theorem meromorphicOrderAt_zetaMixedPrimeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) : meromorphicOrderAt zetaMixedPrimeResponse rho.1 = -1 := by
  have hs1 : rho.1 ≠ 1 := by
    intro h
    have hr := NontrivialZetaZero.re_lt_one rho
    simp [h] at hr
  rw [mixed_eq, meromorphicOrderAt_add_eq_left_of_lt
    (analyticAt_zetaPrimeDivisorResponse hrho hs1).meromorphicAt (order_log_lt_common rho hrho),
    order_log_zero]

/-- Its coefficient is exactly the positive multiplicity, opposite
to the negative prime-power response, despite both arithmetic weights
being nonnegative in their half-plane of convergence. -/
theorem meromorphicTrailingCoeffAt_zetaMixedPrimeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicTrailingCoeffAt zetaMixedPrimeResponse rho.1 = (analyticZetaZeroMultiplicity rho : ℂ) := by
  have hs1 : rho.1 ≠ 1 := by
    intro h
    have hr := NontrivialZetaZero.re_lt_one rho
    simp [h] at hr
  have hm : ((analyticZetaZeroMultiplicity rho : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  have hc := (analyticAt_zetaPrimeDivisorResponse hrho hs1).meromorphicAt
  rw [mixed_eq, hc.meromorphicTrailingCoeffAt_add_eq_left_of_lt (order_log_lt_common rho hrho),
    meromorphicTrailingCoeffAt_logDeriv_of_order (meromorphicAt_riemannZeta rho.1) hm
      (meromorphicOrderAt_riemannZeta_nontrivialZero rho)]
  norm_cast

/-- The positive composite response factors as the two complementary
zeta responses. The nonzero denominator hypothesis is kept explicitly. -/
theorem zetaPositiveCompositeResponse_eq_prime_mul_mixed {s : ℂ} (hs : riemannZeta s ≠ 0) :
    zetaPositiveCompositeResponse s = (-logDeriv riemannZeta s) * zetaMixedPrimeResponse s := by
  simp only [zetaPositiveCompositeResponse, zetaMixedPrimeResponse, logDeriv_apply]
  field_simp
  ring

end

end RiemannGaussian
