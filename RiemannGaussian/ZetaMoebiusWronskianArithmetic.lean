/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusWronskian

/-!
# The prime and composite parts of the differential zeta response

The differentiated reciprocal is the actual absolutely convergent
Dirichlet series with coefficients `mu(n) log(n)`. Its prime restriction
continues as `zeta'/zeta` plus the proper-prime-power series, which is
analytic to the right of one half. Coupling both parts to the same
multiplicity cofactor separates their orders at a hypothetical right-half
zero. This is a local structural theorem, not an independent bound for
the remaining composite sum.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The literal logarithmically weighted Möbius coefficient. -/
def zetaMoebiusDerivativeCoefficient (n : ℕ) : ℂ :=
  ((μ n : ℤ) : ℂ) * (Real.log n : ℂ)

/-- The restriction to squarefree composite indices; support is proved
below rather than imposed as an extra analytic assumption. -/
def zetaMoebiusCompositeDerivativeCoefficient (n : ℕ) : ℂ :=
  if n.Prime then 0 else zetaMoebiusDerivativeCoefficient n

/-- The proper-prime-power correction as its actual convergent series
in the half-plane to the right of one half. -/
def zetaProperPrimePowerSeries (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ)) s

/-- Actual absolute convergence permits differentiation of the Möbius
series and identifies its derivative with the reciprocal zeta derivative. -/
theorem LSeriesHasSum_zetaMoebiusDerivative {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum zetaMoebiusDerivativeCoefficient s (deriv riemannZeta s / riemannZeta s ^ 2) := by
  have hab : LSeries.abscissaOfAbsConv (fun n : ℕ ↦ ((μ n : ℤ) : ℂ)) < s.re := by
    rw [ArithmeticFunction.abscissaOfAbsConv_moebius]
    exact_mod_cast hs
  have hc : zetaMoebiusDerivativeCoefficient = LSeries.logMul (fun n : ℕ ↦ ((μ n : ℤ) : ℂ)) := by
    funext n
    simp [zetaMoebiusDerivativeCoefficient, LSeries.logMul, Complex.natCast_log, mul_comm]
  rw [hc, LSeriesHasSum_iff]
  refine ⟨LSeriesSummable_logMul_of_lt_re hab, ?_⟩
  have he : LSeries (fun n : ℕ ↦ ((μ n : ℤ) : ℂ)) =ᶠ[𝓝 s] riemannZeta⁻¹ := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    rw [← zetaReciprocalExtension_eq_moebius_LSeries hz,
      zetaReciprocalExtension_eq_inv (by intro h; simp [h] at hz)]
    rfl
  have hd := he.deriv_eq
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have ha : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs1)
  rw [LSeries_deriv hab, (ha.differentiableAt.hasDerivAt.inv hz).deriv] at hd
  exact neg_injective (by simpa only [neg_div] using hd)

/-- The proper-prime-power correction is analytic throughout the
larger half-plane, independently of the zeta zero hypothesis. -/
theorem analyticAt_zetaProperPrimePowerSeries {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ zetaProperPrimePowerSeries s := by
  apply LSeries_analyticOnNhd
  have hb : LSeries.abscissaOfAbsConv (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ)) ≤
      ((1 / 2 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1 / 2)
    intro y hy
    exact LSeriesSummable_zetaProperPrimePower (by simpa using hy)
  exact lt_of_le_of_lt hb (by exact_mod_cast hs)

/-- The prime restriction is identified coefficient by coefficient,
before summation and without deleting its negative Möbius sign. -/
theorem zetaMoebiusPrimeDerivativeCoefficient_eq (n : ℕ) :
    (if n.Prime then zetaMoebiusDerivativeCoefficient n else 0) =
      (zetaProperPrimePowerCoefficient n : ℂ) - (ArithmeticFunction.vonMangoldt n : ℂ) := by
  by_cases hn : n.Prime
  · simp [hn, zetaMoebiusDerivativeCoefficient, zetaProperPrimePowerCoefficient,
      ArithmeticFunction.moebius_apply_prime hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [hn, zetaProperPrimePowerCoefficient]

/-- The actual prime restriction has the meromorphic continuation
`zeta'/zeta + E`, where `E` is the convergent proper-prime-power series. -/
theorem LSeriesHasSum_zetaMoebiusPrimeDerivative {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ if n.Prime then zetaMoebiusDerivativeCoefficient n else 0) s
      (logDeriv riemannZeta s + zetaProperPrimePowerSeries s) := by
  have hv := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hv
  have he := (LSeriesSummable_zetaProperPrimePower (show 1 / 2 < s.re by linarith)).LSeriesHasSum
  have h := he.sub hv
  have hval : LSeries (fun n ↦ (zetaProperPrimePowerCoefficient n : ℂ)) s -
      (-deriv riemannZeta s / riemannZeta s) =
      logDeriv riemannZeta s + zetaProperPrimePowerSeries s := by
    simp only [logDeriv_apply, zetaProperPrimePowerSeries, neg_div]
    ring
  rw [hval] at h
  apply h.congr_fun
  intro n
  simp only [LSeries.term, zetaMoebiusPrimeDerivativeCoefficient_eq, Pi.sub_apply]

/-- The remaining composite coefficients also form a genuine
absolutely convergent series in the Euler half-plane. -/
theorem LSeriesHasSum_zetaMoebiusCompositeDerivative {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum zetaMoebiusCompositeDerivativeCoefficient s
      (deriv riemannZeta s / riemannZeta s ^ 2 -
        (logDeriv riemannZeta s + zetaProperPrimePowerSeries s)) := by
  apply ((LSeriesHasSum_zetaMoebiusDerivative hs).sub
    (LSeriesHasSum_zetaMoebiusPrimeDerivative hs)).congr_fun
  intro n
  by_cases hn : n.Prime <;> simp [LSeries.term, zetaMoebiusCompositeDerivativeCoefficient, hn]

/-- A nonzero remaining coefficient requires an actual squarefree
composite integer. The unit, primes, and repeated prime factors vanish. -/
theorem zetaMoebiusCompositeDerivativeCoefficient_support {n : ℕ}
    (hn : zetaMoebiusCompositeDerivativeCoefficient n ≠ 0) :
    2 ≤ n ∧ ¬n.Prime ∧ Squarefree n := by
  have hp : ¬n.Prime := by
    intro hp
    simp [zetaMoebiusCompositeDerivativeCoefficient, hp] at hn
  have hn0 : n ≠ 0 := by intro h; simp [h, zetaMoebiusCompositeDerivativeCoefficient,
    zetaMoebiusDerivativeCoefficient] at hn
  have hn1 : n ≠ 1 := by intro h; simp [h, zetaMoebiusCompositeDerivativeCoefficient,
    zetaMoebiusDerivativeCoefficient] at hn
  refine ⟨by omega, hp, ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp ?_⟩
  intro h
  simp [zetaMoebiusCompositeDerivativeCoefficient, zetaMoebiusDerivativeCoefficient, h] at hn

/-- The prime-divisor part multiplied by exactly the same cofactor
as the complete differential response. -/
def zetaMoebiusPrimeWronskian (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaMoebiusWronskianCofactor rho s * (logDeriv riemannZeta s + zetaProperPrimePowerSeries s)

/-- The surviving composite-divisor part, retaining the full complex
difference. Its arithmetic series is established below. -/
def zetaMoebiusCompositeWronskian (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaMoebiusWronskian rho s - zetaMoebiusPrimeWronskian rho s

/-- The full differential response is the literal weighted Möbius
series, with absolute convergence discharged. -/
theorem hasSum_zetaMoebiusWronskian (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusWronskianCofactor rho s *
      LSeries.term zetaMoebiusDerivativeCoefficient s n) (zetaMoebiusWronskian rho s) :=
  (LSeriesHasSum_zetaMoebiusDerivative hs).mul_left _

/-- The prime arm is the actual prime-restricted Möbius series. -/
theorem hasSum_zetaMoebiusPrimeWronskian (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusWronskianCofactor rho s *
      LSeries.term (fun n ↦ if n.Prime then zetaMoebiusDerivativeCoefficient n else 0) s n)
      (zetaMoebiusPrimeWronskian rho s) :=
  (LSeriesHasSum_zetaMoebiusPrimeDerivative hs).mul_left _

/-- The remaining response is a literal series over squarefree
composite Möbius indices, not a newly assumed analytic residual. -/
theorem hasSum_zetaMoebiusCompositeWronskian (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusWronskianCofactor rho s *
      LSeries.term zetaMoebiusCompositeDerivativeCoefficient s n)
      (zetaMoebiusCompositeWronskian rho s) := by
  have h := (LSeriesHasSum_zetaMoebiusCompositeDerivative hs).mul_left
    (zetaMoebiusWronskianCofactor rho s)
  simpa only [mul_sub, zetaMoebiusCompositeWronskian, zetaMoebiusWronskian,
    zetaMoebiusPrimeWronskian] using h

/-- The prime arm equals zeta times the full response plus the same
cofactor times the independently analytic proper-prime-power series. -/
theorem zetaMoebiusPrimeWronskian_eq (rho : NontrivialZetaZero) (s : ℂ) :
    zetaMoebiusPrimeWronskian rho s = riemannZeta s * zetaMoebiusWronskian rho s +
      zetaMoebiusWronskianCofactor rho s * zetaProperPrimePowerSeries s := by
  by_cases hz : riemannZeta s = 0
  · simp [zetaMoebiusPrimeWronskian, zetaMoebiusWronskian, logDeriv_apply, hz]
  · simp only [zetaMoebiusPrimeWronskian, zetaMoebiusWronskian, logDeriv_apply]
    field_simp

/-- The prime response is meromorphic throughout the larger half-plane;
convergence of the proper-prime-power continuation is already proved. -/
theorem meromorphicAt_zetaMoebiusPrimeWronskian (rho : NontrivialZetaZero) {s : ℂ}
    (hs : 1 / 2 < s.re) : MeromorphicAt (zetaMoebiusPrimeWronskian rho) s :=
  (meromorphicAt_zetaMoebiusWronskianCofactor rho s).mul
    (((meromorphicAt_riemannZeta s).deriv.div (meromorphicAt_riemannZeta s)).add
      (analyticAt_zetaProperPrimePowerSeries hs).meromorphicAt)

private theorem order_logDeriv_zero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta rho.1)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    have hm := analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (show (analyticZetaZeroMultiplicity rho : ℤ) ≠ 0 by omega)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    exact WithTop.coe_ne_top

private theorem order_prime_derivative {s : ℂ} (hs : 1 / 2 < s.re)
    (hlog : meromorphicOrderAt (logDeriv riemannZeta) s = -1) :
    meromorphicOrderAt (logDeriv riemannZeta + zetaProperPrimePowerSeries) s = -1 := by
  have he := analyticAt_zetaProperPrimePowerSeries hs
  rw [meromorphicOrderAt_add_eq_left_of_lt he.meromorphicAt, hlog]
  rw [hlog]
  apply lt_of_lt_of_le _ he.meromorphicOrderAt_nonneg
  change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- At the selected right-half zero the prime response has exact order
`m - 2`. Thus it has at most a simple pole, whereas the full response has
a double pole for every multiplicity. -/
theorem meromorphicOrderAt_zetaMoebiusPrimeWronskian (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (zetaMoebiusPrimeWronskian rho) rho.1 =
      ((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) := by
  have he := analyticAt_zetaProperPrimePowerSeries hrho
  have hlog : MeromorphicAt (logDeriv riemannZeta) rho.1 :=
    (meromorphicAt_riemannZeta rho.1).deriv.div (meromorphicAt_riemannZeta rho.1)
  have hsum := order_prime_derivative hrho (order_logDeriv_zero rho)
  change meromorphicOrderAt (zetaMoebiusWronskianCofactor rho *
    (logDeriv riemannZeta + zetaProperPrimePowerSeries)) rho.1 = _
  rw [meromorphicOrderAt_mul (meromorphicAt_zetaMoebiusWronskianCofactor rho rho.1)
      (hlog.add he.meromorphicAt), meromorphicOrderAt_zetaMoebiusWronskianCofactor, hsum]
  change (((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) +
    ((-1 : ℤ) : WithTop ℤ) = (((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add, WithTop.coe_inj]
  ring

private theorem order_full_lt_prime (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (zetaMoebiusWronskian rho) rho.1 <
      meromorphicOrderAt (zetaMoebiusPrimeWronskian rho) rho.1 := by
  rw [meromorphicOrderAt_zetaMoebiusWronskian, meromorphicOrderAt_zetaMoebiusPrimeWronskian rho hrho]
  have hm := analyticZetaZeroMultiplicity_positive rho
  change ((-2 : ℤ) : WithTop ℤ) < (((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) : WithTop ℤ)
  rw [WithTop.coe_lt_coe]
  omega

/-- Removing the actual prime-divisor arm leaves the double pole
unchanged. No independent estimate for the composite sum is assumed. -/
theorem meromorphicOrderAt_zetaMoebiusCompositeWronskian (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (zetaMoebiusCompositeWronskian rho) rho.1 = -2 := by
  change meromorphicOrderAt (zetaMoebiusWronskian rho - zetaMoebiusPrimeWronskian rho) rho.1 = _
  rw [sub_eq_add_neg, meromorphicOrderAt_add_eq_left_of_lt
    (meromorphicAt_zetaMoebiusPrimeWronskian rho hrho).neg,
    meromorphicOrderAt_zetaMoebiusWronskian]
  rw [← meromorphicOrderAt_neg]
  exact order_full_lt_prime rho hrho

/-- The composite series keeps the exact nonzero leading zeta phase
and coefficient, not just the order of its singularity. -/
theorem meromorphicTrailingCoeffAt_zetaMoebiusCompositeWronskian (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicTrailingCoeffAt (zetaMoebiusCompositeWronskian rho) rho.1 =
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 3 * meromorphicTrailingCoeffAt riemannZeta rho.1 := by
  change meromorphicTrailingCoeffAt (zetaMoebiusWronskian rho - zetaMoebiusPrimeWronskian rho) rho.1 = _
  rw [(meromorphicAt_zetaMoebiusPrimeWronskian rho hrho).meromorphicTrailingCoeffAt_sub_eq_left_of_lt
      (order_full_lt_prime rho hrho), meromorphicTrailingCoeffAt_zetaMoebiusWronskian]

/-- The prime arm vanishes at the selected double-pole scale. -/
theorem tendsto_zetaMoebiusPrimeWronskian_mul_sq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * zetaMoebiusPrimeWronskian rho s) (𝓝[≠] rho.1) (𝓝 0) := by
  apply tendsto_zero_of_meromorphicOrderAt_pos
  change 0 < meromorphicOrderAt ((fun s : ℂ ↦ s - rho.1) ^ (2 : ℕ) *
    zetaMoebiusPrimeWronskian rho) rho.1
  rw [meromorphicOrderAt_mul (by fun_prop) (meromorphicAt_zetaMoebiusPrimeWronskian rho hrho),
    meromorphicOrderAt_pow (by fun_prop), meromorphicOrderAt_id_sub_const,
    meromorphicOrderAt_zetaMoebiusPrimeWronskian rho hrho, mul_one]
  change ((0 : ℤ) : WithTop ℤ) < ((2 : ℤ) : WithTop ℤ) +
    (((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add, WithTop.coe_lt_coe]
  have hm := analyticZetaZeroMultiplicity_positive rho
  omega

/-- The literal composite response retains the entire double-pole
source in the punctured limit, with no norm or sign compression. -/
theorem tendsto_zetaMoebiusCompositeWronskian_mul_sq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * zetaMoebiusCompositeWronskian rho s) (𝓝[≠] rho.1)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) ^ 3 *
        meromorphicTrailingCoeffAt riemannZeta rho.1)) := by
  simpa only [← mul_sub, sub_zero, zetaMoebiusCompositeWronskian] using
    (tendsto_zetaMoebiusWronskian_mul_sq rho).sub (tendsto_zetaMoebiusPrimeWronskian_mul_sq rho hrho)

/-- The arithmetic prime arm and zeta times the full response differ
by an actual analytic germ, using the explicitly filled cofactor. -/
theorem zetaMoebiusPrimeWronskian_analytic_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho.1 ∧
      (fun s ↦ zetaMoebiusPrimeWronskian rho s - riemannZeta s * zetaMoebiusWronskian rho s)
        =ᶠ[𝓝[≠] rho.1] g := by
  refine ⟨fun s ↦ zetaMoebiusWronskianCofactorRegular rho s * zetaProperPrimePowerSeries s,
    (analyticAt_zetaMoebiusWronskianCofactorRegular rho).mul
      (analyticAt_zetaProperPrimePowerSeries hrho), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [zetaMoebiusPrimeWronskian_eq, zetaMoebiusWronskianCofactorRegular_eq rho (by simpa using hs)]
  ring

/-- At every other right-half zero the prime arm has exact order
`2k - 3`, hence at most a simple pole. This needs no distance ordering
between zeros. -/
theorem meromorphicOrderAt_zetaMoebiusPrimeWronskian_other_zero (rho tau : NontrivialZetaZero)
    (htau : 1 / 2 < tau.1.re) (hne : tau.1 ≠ rho.1) :
    meromorphicOrderAt (zetaMoebiusPrimeWronskian rho) tau.1 =
      (2 * (analyticZetaZeroMultiplicity tau : ℤ) - 3 : ℤ) := by
  have hz := meromorphicAt_riemannZeta tau.1
  have hlog : MeromorphicAt (logDeriv riemannZeta) tau.1 := hz.deriv.div hz
  change meromorphicOrderAt (zetaMoebiusWronskianCofactor rho *
    (logDeriv riemannZeta + zetaProperPrimePowerSeries)) tau.1 = _
  rw [meromorphicOrderAt_mul (meromorphicAt_zetaMoebiusWronskianCofactor rho tau.1)
      (hlog.add (analyticAt_zetaProperPrimePowerSeries htau).meromorphicAt),
    meromorphicOrderAt_zetaMoebiusWronskianCofactor_of_ne rho hne,
    order_prime_derivative htau (order_logDeriv_zero tau),
    meromorphicOrderAt_deriv_riemannZeta_nontrivialZero]
  change ((2 : ℤ) : WithTop ℤ) * (((analyticZetaZeroMultiplicity tau : ℤ) - 1 : ℤ) : WithTop ℤ) +
    ((-1 : ℤ) : WithTop ℤ) = _
  rw [← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_inj]
  ring

/-- The prime response has a fifth-order pole at one. A global finite
filter must cancel this entire pole, in addition to the simple zero poles. -/
theorem meromorphicOrderAt_zetaMoebiusPrimeWronskian_one (rho : NontrivialZetaZero) :
    meromorphicOrderAt (zetaMoebiusPrimeWronskian rho) 1 = -5 := by
  have hz := meromorphicAt_riemannZeta 1
  have hlog : MeromorphicAt (logDeriv riemannZeta) 1 := hz.deriv.div hz
  have ho : meromorphicOrderAt (logDeriv riemannZeta) 1 = -1 := by
    apply meromorphicOrderAt_logDeriv_eq_neg_one hz
    · rw [meromorphicOrderAt_riemannZeta_one]
      change ((-1 : ℤ) : WithTop ℤ) ≠ ((0 : ℤ) : WithTop ℤ)
      norm_cast
    · rw [meromorphicOrderAt_riemannZeta_one]
      exact WithTop.coe_ne_top
  change meromorphicOrderAt (zetaMoebiusWronskianCofactor rho *
    (logDeriv riemannZeta + zetaProperPrimePowerSeries)) 1 = _
  rw [meromorphicOrderAt_mul (meromorphicAt_zetaMoebiusWronskianCofactor rho 1)
      (hlog.add (analyticAt_zetaProperPrimePowerSeries (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)).meromorphicAt),
    meromorphicOrderAt_zetaMoebiusWronskianCofactor_one,
    order_prime_derivative (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re) ho]
  change ((-4 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) = ((-5 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add]
  rfl

end

end RiemannGaussian
