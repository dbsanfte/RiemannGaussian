/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Finite complete-Gamma convolution hierarchies are source-blind

All ordinary multiplicative fibers and finite cutoff endpoints are kept.
Every Gamma-compatible leg includes its cofactor phase. Any fixed finite
convolution hierarchy then has an analytic continuation which is a product
of shifted zeta DERIVATIVES, not logarithmic derivatives. Thus no finite
hierarchy or finite code of these hierarchies has a zero residue on the
open critical strip. This does not cover an inverse-zeta factor, prime-only
commutator, pointwise product, or additive successor correlation.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorCommutatorAudit ArithmeticOperatorDilationAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- A finite convolution word, retaining every divisor fiber. Its
empty word is the literal unit label, not an omitted endpoint. -/
def word (f : ℝ → ℕ → ℂ) : List ℝ → ℕ → ℂ
  | [] => LSeries.delta
  | y::ys => divisorConvolution (f y) (word f ys)

/-- The actual Gamma-compatible hierarchy; every leg keeps all powers. -/
def gammaWord (ys : List ℝ) : ℕ → ℂ := word (fun y => coupledDivisor (primePhase y)) ys

/-- A finite local continuation, with no logarithmic pole inserted. -/
def response : List ℝ → ℂ → ℂ
  | [] => fun _ => 1
  | y::ys => fun s => -deriv riemannZeta (s+I*y)*response ys s

/-- The hierarchy's cutoff recursion is an exact integer identity for
arbitrary arrays. No prime or asymptotic premise pays a quotient fiber. -/
theorem word_cutoff_cons (f : ℝ → ℕ → ℂ) (y : ℝ) (ys : List ℝ) (X : ℕ) :
    prefixSum (word f (y::ys)) X =
      ∑ d ∈ Finset.Icc 1 X, f y d*prefixSum (word f ys) (X/d) := by
  exact cutoffConvolution_eq_quotient (f y) (word f ys) X

private theorem word_cons_eq_convolution (f : ℝ → ℕ → ℂ) (y : ℝ) (ys : List ℝ) :
    word f (y::ys) = LSeries.convolution (f y) (word f ys) := by
  funext n
  simp only [word, divisorConvolution, LSeries.convolution_def]

private theorem gamma_leg_summable (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (coupledDivisor (primePhase y)) s := by
  have he : coupledDivisor (primePhase y) =
      fun n : ℕ => (Real.log n : ℂ)*primePhase y n := by
    funext n
    by_cases hn : n = 0
    · simp [hn, coupledDivisor]
    · rw [coupledDivisor_primePhase y (Nat.pos_of_ne_zero hn), mul_comm]
  rw [he, LSeriesSummable_primePhase_iff]
  have ht : 1 < (s+I*y).re := by simpa using hs
  have hc : (fun n : ℕ => (Real.log n : ℂ)) =
      LSeries.convolution (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 : ℕ → ℂ) := by
    funext n
    have h := congrFun ArithmeticFunction.convolution_vonMangoldt_const_one n
    simpa only [Complex.natCast_log] using h.symm
  rw [hc]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt ht).convolution
    (LSeriesSummable_one_iff.mpr ht)

/-- Every finite Gamma word has a genuinely absolutely convergent
Euler series on `Re(s)>1`. No continuation is called an Euler sum. -/
theorem gammaWord_summable (ys : List ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (gammaWord ys) s := by
  induction ys with
  | nil =>
    change Summable (LSeries.term LSeries.delta s)
    have he : LSeries.term LSeries.delta s = fun n : ℕ => if n = 1 then (1 : ℂ) else 0 :=
      funext (LSeries.term_delta s)
    rw [he]
    exact (hasSum_ite_eq 1 (1 : ℂ)).summable
  | cons y ys ih =>
    unfold gammaWord
    rw [word_cons_eq_convolution]
    exact (gamma_leg_summable y hs).convolution ih

/-- Genuine series identity for an arbitrary finite number of legs at
arbitrary fixed heights. Every cofactor phase is indispensable. -/
theorem gammaWord_euler_response (ys : List ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (gammaWord ys) s = response ys s := by
  induction ys with
  | nil => simp [gammaWord, word, response, LSeries_delta]
  | cons y ys ih =>
    change LSeries (word (fun y => coupledDivisor (primePhase y)) (y::ys)) s = _
    rw [word_cons_eq_convolution]
    change LSeries (LSeries.convolution (coupledDivisor (primePhase y)) (gammaWord ys)) s = _
    rw [
      LSeries_convolution' (gamma_leg_summable y hs) (gammaWord_summable ys hs),
      coupled_series_eq_shifted_derivative hs y]
    rw [ih]
    rfl

/-- The whole completed hierarchy is analytic at every point whose real
part is not one. Products cannot recreate a selected zero's log pole. -/
theorem response_analyticAt (ys : List ℝ) {s : ℂ} (hs : s.re ≠ 1) :
    AnalyticAt ℂ (response ys) s := by
  induction ys with
  | nil => exact analyticAt_const
  | cons y ys ih =>
    have hz : s+I*y ≠ 1 := by
      intro hh
      apply hs
      have he := congrArg Complex.re hh
      simpa using he
    have ha : AnalyticAt ℂ riemannZeta (s+I*y) := analyticOn_riemannZeta _ hz
    have hc : AnalyticAt ℂ (fun z : ℂ => z+I*y) s := analyticAt_id.add analyticAt_const
    have hh : AnalyticAt ℂ (fun z : ℂ => -deriv riemannZeta (z+I*y)) s :=
      AnalyticAt.comp (g := fun z => -deriv riemannZeta z)
        (f := fun z => z+I*y) (x := s) ha.deriv.neg hc
    exact hh.mul ih

/-- No fixed finite completed hierarchy has a matched zero residue,
with no exposure, simplicity, or multiplicity assumption. -/
theorem tendsto_response_zero_source (ys : List ℝ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*response ys s) (𝓝[≠] rho.1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1)
      (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have ha := response_analyticAt ys (ne_of_lt (NontrivialZetaZero.re_lt_one rho))
  simpa only [zero_mul] using ht.mul (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- A fixed finite linear code of completed hierarchies cannot repair
their zero blindness. Arbitrary literal coefficient masks are not included. -/
theorem tendsto_finite_hierarchy_zero_source {ι : Type*} (S : Finset ι)
    (ys : ι → List ℝ) (coeff : ι → ℂ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*(∑ i ∈ S, coeff i*response (ys i) s))
      (𝓝[≠] rho.1) (𝓝 0) := by
  have ht := tendsto_finsetSum S (fun i _ =>
    (tendsto_response_zero_source (ys i) rho).const_mul (coeff i))
  simp only [mul_zero, Finset.sum_const_zero] at ht
  convert ht using 1
  funext s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The same no-go permits analytic transform-level coefficients,
including regular finite dilation factors. A coefficient singular at
the selected zero, or an arithmetic mask on the original labels, is
separate input and is not silently treated as one of these factors. -/
theorem tendsto_analytic_hierarchy_zero_source {ι : Type*} (S : Finset ι)
    (ys : ι → List ℝ) (coeff : ι → ℂ → ℂ) (rho : NontrivialZetaZero)
    (hcoeff : ∀ i ∈ S, AnalyticAt ℂ (coeff i) rho.1) :
    Tendsto (fun s : ℂ => (s-rho.1)*(∑ i ∈ S, coeff i s*response (ys i) s))
      (𝓝[≠] rho.1) (𝓝 0) := by
  have ht := tendsto_finsetSum S (fun i hi =>
    ((hcoeff i hi).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_response_zero_source (ys i) rho))
  simp only [mul_zero, Finset.sum_const_zero] at ht
  convert ht using 1
  funext s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end
end RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit
