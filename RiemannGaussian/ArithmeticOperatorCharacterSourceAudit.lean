/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Nonprincipal modular codes: which actual divisor supplies the source?

The complete finite character code is joined with all actual Mangoldt
powers and the original height phase. Its genuine Euler continuation is
a finite sum of logarithmic derivatives of the corresponding L-functions.
If those L-functions are nonzero at the selected zeta zero, the centered
code has zero matched residue. Any nonzero residue after deleting the
principal character therefore requires a common NONPRINCIPAL L-zero.

No absence or existence of such common zeros is assumed or proved.
In particular this is not unconditional decay of all nonprincipal codes.
It isolates the extra spectral information required for their source gate.
-/

namespace RiemannGaussian.ArithmeticOperatorCharacterSourceAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Finite modular code, including every residue of every prime power. -/
def code {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (n : ℕ) : ℂ :=
  ∑ χ ∈ S, coeff χ*χ n

/-- Complete phased actual-prime coefficients of the finite code. -/
def coefficient {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n*code S coeff n

/-- The exact analytic response on the Euler half-plane, with no norm
or independent character allowance introduced. -/
def response {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (s : ℂ) : ℂ :=
  ∑ χ ∈ S, coeff χ*(-logDeriv (DirichletCharacter.LFunction χ) s)

/-- Ordinary finite residue density cancels exactly for a nonprincipal
character code. This does not assume a prime-distribution estimate. -/
theorem residue_density_eq_zero {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hprincipal : ∀ χ ∈ S, χ ≠ 1) :
    (∑ a : ZMod q, ∑ χ ∈ S, coeff χ*χ a) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro χ hχ
  rw [← Finset.mul_sum, χ.sum_eq_zero_of_ne_one (hprincipal χ hχ), mul_zero]

/-- Finite integer bookkeeping holds for arbitrary row/column measures.
The actual-prime specialization is not silently used for other measures. -/
theorem finite_code_join {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (X : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, w n*code S coeff n) =
      ∑ χ ∈ S, coeff χ*(∑ n ∈ Finset.Icc 1 X, w n*χ n) := by
  unfold code
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Literal coefficients and their complete Dirichlet series agree on
the genuine domain of absolute convergence. The continuation elsewhere
is not called a convergent Euler sum. -/
theorem euler_response {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coefficient S coeff y) s = response S coeff (s+I*y) := by
  have ht : 1 < (s+I*y).re := by simpa using hs
  have he : coefficient S coeff y =
      fun n : ℕ => ((∑ χ ∈ S, coeff χ*(χ n*(ArithmeticFunction.vonMangoldt n : ℂ))))*
        primePhase y n := by
    funext n
    unfold coefficient code
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he, LSeries_primePhase]
  have hfun : (fun n : ℕ => ∑ χ ∈ S,
      coeff χ*(χ n*(ArithmeticFunction.vonMangoldt n : ℂ))) =
      ∑ χ ∈ S, coeff χ •
        ((fun n : ℕ => χ n)*(fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [hfun]
  rw [LSeries_sum (fun χ _ => (χ.LSeriesSummable_twist_vonMangoldt ht).smul (coeff χ))]
  unfold response
  apply Finset.sum_congr rfl
  intro χ _
  rw [LSeries_smul, χ.LSeries_twist_vonMangoldt_eq ht,
    ← χ.deriv_LFunction_eq_deriv_LSeries ht, ← χ.LFunction_eq_LSeries ht]
  simp only [logDeriv_apply, neg_div]

/-- Deleting the principal character does not create a new automatic
zeta-zero source. When every retained nonprincipal L-function is regular
and nonzero there, the exact code continuation has zero matched residue. -/
theorem tendsto_source_zero_of_no_common_zero {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hprincipal : ∀ χ ∈ S, χ ≠ 1) (rho : ℂ)
    (hregular : ∀ χ ∈ S, DirichletCharacter.LFunction χ rho ≠ 0) :
    Tendsto (fun s : ℂ => (s-rho)*response S coeff s) (𝓝[≠] rho) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-rho) (𝓝[≠] rho) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho) (𝓝[≠] rho) (𝓝 (rho-rho)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hl (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) :
      ContinuousAt (fun s => -logDeriv (DirichletCharacter.LFunction χ) s) rho := by
    have ha := (DirichletCharacter.differentiable_LFunction (hprincipal χ hχ)).analyticAt rho
    exact (ha.deriv.continuousAt.div ha.continuousAt (hregular χ hχ)).neg
  have hsum := tendsto_finsetSum S (fun χ hχ =>
    (ht.mul ((hl χ hχ).tendsto.mono_left nhdsWithin_le_nhds)).const_mul (coeff χ))
  simp only [zero_mul, mul_zero, Finset.sum_const_zero] at hsum
  convert hsum using 1
  funext s
  unfold response
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A nonzero matched response in a principal-deleted code at an actual
zeta zero FORCES an additional common nonprincipal L-zero. This exact
spectral requirement is kept explicit; no common-zero conjecture is used. -/
theorem source_forces_common_nonprincipal_zero {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hprincipal : ∀ χ ∈ S, χ ≠ 1) (rho : NontrivialZetaZero) {v : ℂ} (hv : v ≠ 0)
    (hsource : Tendsto (fun s : ℂ => (s-rho.1)*response S coeff s)
      (𝓝[≠] rho.1) (𝓝 v)) :
    ∃ χ ∈ S, χ ≠ 1 ∧ DirichletCharacter.LFunction χ rho.1 = 0 := by
  classical
  by_contra h
  have hr : ∀ χ ∈ S, DirichletCharacter.LFunction χ rho.1 ≠ 0 := by
    intro χ hχ hzero
    exact h ⟨χ,hχ,hprincipal χ hχ,hzero⟩
  exact hv (tendsto_nhds_unique hsource
    (tendsto_source_zero_of_no_common_zero S coeff hprincipal rho.1 hr))

/-- Density-pole separation is genuine and unconditional. It does not
provide the separate common-zero source required by a zeta detector. -/
theorem tendsto_density_pole_zero {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hprincipal : ∀ χ ∈ S, χ ≠ 1) :
    Tendsto (fun s : ℂ => (s-1)*response S coeff s) (𝓝[≠] 1) (𝓝 0) :=
  tendsto_source_zero_of_no_common_zero S coeff hprincipal 1
    (fun χ hχ => χ.LFunction_apply_one_ne_zero (hprincipal χ hχ))

end
end RiemannGaussian.ArithmeticOperatorCharacterSourceAudit
