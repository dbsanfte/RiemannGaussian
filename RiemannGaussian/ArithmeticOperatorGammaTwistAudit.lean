/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorPowerCovariance
import RiemannGaussian.ZetaPrimeLogMoments

/-!
# The Gamma/convolution twist conservation gate

Restoring exact integer factorization after twisting requires the SAME
completely multiplicative phase on the prime-power leg and its cofactor.
Then the full convolution evaluates as a phased logarithm. Analytically
the product is zeta times its negative logarithmic derivative, so the
zero source is annihilated. Twisting only the prime leg retains a source
but leaves the exact cofactor-phase commutator unpaid.

This scopes the no-go to the complete Gamma evaluation, not to a signed
estimate for that unpaid commutator or for distinct prime correlations.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaTwistAudit
noncomputable section
open Complex Filter ArithmeticOperatorKummerCutoff SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Completely multiplicative phase applied to both actual factors. -/
def coupledDivisor (phase : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*phase (n/d)

/-- The prime-leg-only observation that keeps the matched zero pole. -/
def primeLegDivisor (phase : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)*phase d

/-- Exact cofactor-phase discrepancy; no term is estimated or deleted. -/
def twistCommutator (phase : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors,
    (ArithmeticFunction.vonMangoldt d : ℂ)*phase d*(1-phase (n/d))

/-- The finite identity uses literal multiplication and every prime power.
It applies to arbitrary multiplicative phases, including finite characters. -/
theorem coupledDivisor_eq_phased_log (phase : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → phase (a*b) = phase a*phase b)
    {n : ℕ} (hn : 0 < n) :
    coupledDivisor phase n = phase n*(Real.log n : ℂ) := by
  unfold coupledDivisor
  have he (d : ℕ) (hd : d ∈ n.divisors) : phase d*phase (n/d) = phase n := by
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 := Nat.pos_of_dvd_of_pos hdvd hn
    have heq : d*(n/d) = n := Nat.mul_div_cancel' hdvd
    have hq : 0 < n/d := by nlinarith
    rw [← hmul d (n/d) hd0 hq,heq]
  calc
    _ = ∑ d ∈ n.divisors, phase n*(ArithmeticFunction.vonMangoldt d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [mul_assoc,he d hd,mul_comm]
    _ = _ := by rw [← Finset.mul_sum,← Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum]

/-- All row coding, including finite modular or Gaussian row weights,
retains the same exact factorization. The prime phase is not discarded. -/
theorem sum_coupledDivisor_eq (S : Finset ℕ) (row phase : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → phase (a*b) = phase a*phase b)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, row n*coupledDivisor phase n) =
      ∑ n ∈ S, row n*phase n*(Real.log n : ℂ) := by
  exact Finset.sum_congr rfl (fun n hn => by
    rw [coupledDivisor_eq_phased_log phase hmul (hS n hn),mul_assoc])

/-- The exact missing term when only the prime factor is twisted. It is
not a geometric error supplied by the Gamma identity. -/
theorem primeLegDivisor_sub_coupled (phase : ℕ → ℂ) (n : ℕ) :
    primeLegDivisor phase n-coupledDivisor phase n = twistCommutator phase n := by
  unfold primeLegDivisor coupledDivisor twistCommutator
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The actual Archimedean height phase satisfies the required exact
integer multiplicativity on both factors. -/
theorem primePhase_mul (y : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    primePhase y (a*b) = primePhase y a*primePhase y b := by
  unfold primePhase
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'),
    Complex.ofReal_add,mul_add,Complex.exp_add]

/-- Restoring the Gamma evaluation at fixed height couples the cofactor
phase as well; omitting it gives the preceding exact commutator instead. -/
theorem coupledDivisor_primePhase (y : ℝ) {n : ℕ} (hn : 0 < n) :
    coupledDivisor (primePhase y) n = primePhase y n*(Real.log n : ℂ) :=
  coupledDivisor_eq_phased_log _ (fun _ _ ha hb => primePhase_mul y ha hb) hn

/-- On the genuine Euler domain the complete factorized analytic
response is exactly a derivative, not a logarithmic zero pole. -/
theorem coupled_euler_response {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s*LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact mul_div_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re hs)

/-- Exact height transport at each Dirichlet term, including the
zero-index convention. It also transports absolute convergence. -/
theorem term_primePhase (f : ℕ → ℂ) (y : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => f n*primePhase y n) s n = LSeries.term f (s+I*y) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
    simp only [primePhase,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
      ← Complex.natCast_log,div_eq_mul_inv,← Complex.exp_neg]
    rw [mul_assoc,← Complex.exp_add]
    congr 1
    congr 1
    ring

/-- Exact height transport for the ordinary Dirichlet series, with no
change to its coefficients or arithmetic cutoff. -/
theorem LSeries_primePhase (f : ℕ → ℂ) (y : ℝ) (s : ℂ) :
    LSeries (fun n => f n*primePhase y n) s = LSeries f (s+I*y) := by
  unfold LSeries
  exact tsum_congr (term_primePhase f y s)

/-- The preceding identity preserves the genuine domain of absolute
convergence; it is not an assertion of a continued Euler series. -/
theorem LSeriesSummable_primePhase_iff (f : ℕ → ℂ) (y : ℝ) (s : ℂ) :
    LSeriesSummable (fun n => f n*primePhase y n) s ↔ LSeriesSummable f (s+I*y) := by
  unfold LSeriesSummable
  exact summable_congr (term_primePhase f y s)

/-- The exact phased Gamma/divisor coefficients have a genuine
convergent Euler series equal to the shifted zeta derivative. This ties
the finite identity to its source-blind analytic continuation. -/
theorem coupled_series_eq_shifted_derivative {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    LSeries (coupledDivisor (primePhase y)) s = -deriv riemannZeta (s+I*y) := by
  have he : coupledDivisor (primePhase y) =
      fun n : ℕ => (Real.log n : ℂ)*primePhase y n := by
    funext n
    by_cases hn : n = 0
    · simp [coupledDivisor,hn]
    · rw [coupledDivisor_primePhase y (Nat.pos_of_ne_zero hn),mul_comm]
  rw [he,LSeries_primePhase]
  have ht : 1 < (s+I*y).re := by simpa using hs
  have hc : (fun n : ℕ => (Real.log n : ℂ)) =
      LSeries.convolution (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 : ℕ → ℂ) := by
    funext n
    have h := congrFun ArithmeticFunction.convolution_vonMangoldt_const_one n
    simpa only [Complex.natCast_log] using h.symm
  rw [hc,LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt ht)
    (LSeriesSummable_one_iff.mpr ht),LSeries_one_eq_riemannZeta ht,mul_comm]
  exact coupled_euler_response ht

/-- The exact source preflight fails at EVERY actual zero, retaining its
analytic multiplicity: the complete factor kills the logarithmic pole.
The Euler continuation is evaluated locally, not as a divergent series. -/
theorem tendsto_coupled_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*riemannZeta s*(-logDeriv riemannZeta s))
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hz : Tendsto riemannZeta (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [rho.2.1] using
      (analyticAt_riemannZeta_nontrivialZero rho).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hl := AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have ht := hz.mul hl.neg
  convert ht using 1
  · funext s
    ring
  · simp

end
end RiemannGaussian.ArithmeticOperatorGammaTwistAudit
