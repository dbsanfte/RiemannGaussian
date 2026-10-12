/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Complete Gamma rows with arbitrary fixed modular codes

Additive residue codes need not be multiplicative. Applied to the TOTAL
integer label, they still preserve the exact complete Gamma divisor row.
Its genuine Euler continuation is a derivative of the periodic L-function,
analytic at every off-line zero coordinate. Every fixed finite height/code
family is therefore source-blind, including nonprincipal additive codes.

This freezes complete fixed-periodic Gamma evaluation only. Prime-leg-only
coding leaves an exact unpaid cofactor-phase commutator. Moving moduli,
incomplete correlated masks and that commutator are not estimated here.
-/

namespace RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
noncomputable section
open Complex Filter Topology
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Classical

/-- Periodic code of the WHOLE integer, with the cofactor phase retained. -/
def wholeRow {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ d∈n.divisors,(ArithmeticFunction.vonMangoldt d : ℂ)*
    Phi (d*(n/d) : ℕ)*primePhase y d*primePhase y (n/d)

/-- Only the prime leg is phased in this different, source-bearing row. -/
def primeRow {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ d∈n.divisors,(ArithmeticFunction.vonMangoldt d : ℂ)*
    Phi (d*(n/d) : ℕ)*primePhase y d

/-- Exact remaining correction; no CRT or physical boundary is norm-paid. -/
def correction {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ d∈n.divisors,(ArithmeticFunction.vonMangoldt d : ℂ)*
    Phi (d*(n/d) : ℕ)*primePhase y d*(1-primePhase y (n/d))

/-- The arbitrary-weight identity keeps all literal prime-power fibers.
Only the ACTUAL Mangoldt specialization evaluates to the Gamma logarithm. -/
theorem arbitrary_row_join {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ)
    (w : ℕ → ℂ) {n : ℕ} (hn : 0<n) :
    (∑ d∈n.divisors,w d*Phi (d*(n/d) : ℕ)*primePhase y d*primePhase y (n/d)) =
      Phi n*primePhase y n*(∑ d∈n.divisors,w d) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_dvd_of_pos hdiv hn
  have he := Nat.mul_div_cancel' hdiv
  have hco : 0<n/d := by nlinarith
  rw [he,mul_assoc (w d*Phi n),←primePhase_mul y hdpos hco,he]
  ring

/-- Complete actual Gamma data survive EVERY residue code, including
nonmultiplicative additive characters, with the full height phase. -/
theorem wholeRow_eq_log {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) :
    wholeRow Phi y n=Phi n*primePhase y n*(Real.log n : ℂ) := by
  by_cases hn : n=0
  · simp [wholeRow,hn]
  · rw [wholeRow,arbitrary_row_join Phi y _ (Nat.pos_of_ne_zero hn),
      ←Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum]

/-- Exact physical cutoff and arbitrary outer test remain unchanged. -/
theorem finite_wholeRow_join {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ)
    (S : Finset ℕ) (test : ℕ → ℂ) :
    (∑ n∈S,test n*wholeRow Phi y n)=
      ∑ n∈S,test n*Phi n*primePhase y n*(Real.log n : ℂ) := by
  simp_rw [wholeRow_eq_log]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Removing the cofactor phase is an exact UNPAID commutator. -/
theorem primeRow_sub_wholeRow {q : ℕ} (Phi : ZMod q → ℂ) (y : ℝ) (n : ℕ) :
    primeRow Phi y n-wholeRow Phi y n=correction Phi y n := by
  rw [primeRow,wholeRow,correction,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Periodic coding does not remove the old prime-only discrepancy. -/
theorem correction_eq_old_commutator {q : ℕ} (Phi : ZMod q → ℂ)
    (y : ℝ) (n : ℕ) :
    correction Phi y n=Phi n*twistCommutator (primePhase y) n := by
  rw [correction,twistCommutator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  ring

/-- Meromorphic continuation of the COMPLETE row, not a convergent
prime series asserted outside its Euler domain. -/
def response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (y : ℝ) (s : ℂ) : ℂ :=
  -deriv (ZMod.LFunction Phi) (s+Complex.I*y)

/-- An arbitrary fixed periodic coefficient has no singularity except
possibly at one. This includes every additive or Ramanujan residue code. -/
theorem analyticAt_periodicL {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    {s : ℂ} (hs : s≠1) : AnalyticAt ℂ (ZMod.LFunction Phi) s := by
  have hd : DifferentiableOn ℂ (ZMod.LFunction Phi) ({(1 : ℂ)}ᶜ) := by
    intro z hz
    exact (ZMod.differentiableAt_LFunction Phi z (Or.inl hz)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

theorem analyticAt_response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (y : ℝ)
    {s : ℂ} (hs : s+Complex.I*y≠1) : AnalyticAt ℂ (response Phi y) s := by
  exact AnalyticAt.comp (g := fun z => -deriv (ZMod.LFunction Phi) z)
    (f := fun z : ℂ => z+Complex.I*y)
    (analyticAt_periodicL Phi hs).deriv.neg (analyticAt_id.add analyticAt_const)

/-- Exact Euler-half-plane response, with every proper power and the
original prime/cofactor phases retained. No common-L-zero premise occurs. -/
theorem euler_response {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (y : ℝ)
    {s : ℂ} (hs : 1<s.re) : LSeries (wholeRow Phi y) s=response Phi y s := by
  have he : wholeRow Phi y=(fun n : ℕ =>
      (Phi n*(Real.log n : ℂ))*primePhase y n) := by
    funext n
    rw [wholeRow_eq_log]
    ring
  rw [he,LSeries_primePhase]
  have ht : 1<(s+Complex.I*y).re := by simpa using hs
  let c : ℕ → ℂ := fun n => Phi n
  have hb : LSeries.abscissaOfAbsConv c≤1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact ZMod.LSeriesSummable_of_one_lt_re Phi (by simpa using hx)
  have hbc : LSeries.abscissaOfAbsConv c<(s+Complex.I*y).re :=
    lt_of_le_of_lt hb (by exact_mod_cast ht)
  have hg : ZMod.LFunction Phi =ᶠ[𝓝 (s+Complex.I*y)] LSeries c := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds ht] with z hz
    exact ZMod.LFunction_eq_LSeries Phi hz
  have hlog : (fun n : ℕ => Phi n*(Real.log n : ℂ))=LSeries.logMul c := by
    funext n
    simp only [LSeries.logMul,←Complex.natCast_log,c]
    ring
  rw [hlog,response,hg.deriv_eq,LSeries_deriv hbc,neg_neg]

/-- Every complete fixed-periodic Gamma row has ZERO matched residue at
every actual nontrivial zero, not just a synthetic source or simple zero. -/
theorem actual_zero_source_vanishes {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (y : ℝ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-(rho.1-Complex.I*y))*response Phi y s)
      (𝓝[≠] (rho.1-Complex.I*y)) (𝓝 0) := by
  have hs : rho.1-Complex.I*y+Complex.I*y≠1 := by
    simpa using rho.2.2.2
  have hr : Tendsto (response Phi y) (𝓝[≠] (rho.1-Complex.I*y))
      (𝓝 (response Phi y (rho.1-Complex.I*y))) :=
    (analyticAt_response Phi y hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun s : ℂ => s-(rho.1-Complex.I*y))
      (𝓝[≠] (rho.1-Complex.I*y)) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-(rho.1-Complex.I*y))
      (𝓝[≠] (rho.1-Complex.I*y)) (𝓝 ((rho.1-Complex.I*y)-(rho.1-Complex.I*y))) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [zero_mul] using hz.mul hr

/-- A genuinely zero-mean residue code removes the density pole too.
It does not preserve an off-line source hidden in a logarithmic quotient. -/
theorem density_source_vanishes {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ)
    (hPhi : ∑ a : ZMod q,Phi a=0) :
    Tendsto (fun s : ℂ => (s-1)*response Phi 0 s) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
  have hA : AnalyticAt ℂ (response Phi 0) 1 := by
    have he : response Phi 0= -deriv (ZMod.LFunction Phi) := by
      funext s
      simp [response]
    rw [he]
    exact ((ZMod.differentiable_LFunction_of_sum_zero hPhi).analyticAt 1).deriv.neg
  have hs : Tendsto (fun s : ℂ => s-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun s : ℂ => s-1)
      (𝓝[≠] (1 : ℂ)) (𝓝 ((1 : ℂ)-1)) from
        (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [zero_mul] using hs.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- All fixed finite analytic codes remain source-blind at an actual
zero coordinate. Singular/growing transform-level coefficients are excluded. -/
theorem finite_analytic_codes_source_vanishes {ι : Type*} {q : ℕ} [NeZero q]
    (S : Finset ι) (Phi : ι → ZMod q → ℂ) (y : ℝ) (rho : NontrivialZetaZero)
    (a : ι → ℂ → ℂ)
    (ha : ∀ i∈S,AnalyticAt ℂ (a i) (rho.1-Complex.I*y)) :
    Tendsto (fun s : ℂ => (s-(rho.1-Complex.I*y))*
      ∑ i∈S,a i s*response (Phi i) y s)
      (𝓝[≠] (rho.1-Complex.I*y)) (𝓝 0) := by
  have hsum := tendsto_finsetSum S (fun i hi =>
    ((ha i hi).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (actual_zero_source_vanishes (Phi i) y rho))
  simp only [mul_zero,Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end
end RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
