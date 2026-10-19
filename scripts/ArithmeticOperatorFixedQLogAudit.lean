/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Analytic-germ obstruction for fixed-q ordinary logarithmic norms

An analytic germ sampled at q^n, 0<q<1, is either eventually zero or,
after retaining its finite vanishing order and constant, its logarithm
has a geometrically small residual. Every polynomially weighted absolute
residual is summable. The quadratic-height version keeps the actual
height term before centering.

The hypotheses are explicit. The general Gaussian-binomial determinant
normal form and its q-product identification are paper-level in the
companion audit; this file does not declare that bridge as an axiom.
No physical prime-power phase, moving-size determinant or RH bound follows.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace OpenAIReview.FixedQLog

/-- The complete logarithmic residual, with its linear order and constant retained. -/
def residual (f : ℝ → ℝ) (q : ℝ) (e : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  Real.log (f (q^n))-((e : ℝ)*(n : ℝ)*Real.log q+Real.log c)

/-- A nonzero analytic germ gives an eventually nonzero sampled sequence and a
geometric residual even when the germ vanishes at the origin. -/
theorem analytic_log_residual {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, f x=0) :
    ∃ (e : ℕ) (c : ℝ), c≠0 ∧
      (∀ᶠ n : ℕ in atTop, f (q^n)≠0) ∧
      residual f q e c =O[atTop] (fun n => q^n) := by
  obtain ⟨e,g,hg,hg0,hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hq : Tendsto (fun n : ℕ => q^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  refine ⟨e,g 0,hg0,?_,?_⟩
  · filter_upwards [hq.eventually hfg,hq.eventually (hg.continuousAt.eventually_ne hg0)] with n hn hgn
    simp only [sub_zero,smul_eq_mul] at hn
    rw [hn]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq0.ne')) hgn
  · have hbig := (hg.differentiableAt.log hg0).isBigO_sub.comp_tendsto hq
    have heq : residual f q e (g 0) =ᶠ[atTop]
        (fun n => Real.log (g (q^n))-Real.log (g 0)) := by
      filter_upwards [hq.eventually hfg,hq.eventually (hg.continuousAt.eventually_ne hg0)] with n hn hgn
      simp only [sub_zero,smul_eq_mul] at hn
      unfold residual
      rw [hn,Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hq0.ne')) hgn,
        Real.log_pow,Real.log_pow]
      ring
    simpa only [sub_zero,Function.comp_def] using heq.isBigO.trans hbig

/-- A locally zero germ produces an actually zero tail, so it cannot be used
as an eventually nonzero integer norm witness. -/
theorem zero_germ_zero_tail {q : ℝ} (hq0 : 0≤q) (hq1 : q<1)
    {f : ℝ → ℝ} (hf : ∀ᶠ x in 𝓝 0, f x=0) :
    ∀ᶠ n : ℕ in atTop, f (q^n)=0 :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually hf

/-- Every polynomial absolute moment of a geometrically bounded residual is finite. -/
theorem summable_polynomial_residual {q : ℝ} (hq0 : 0≤q) (hq1 : q<1)
    {r : ℕ → ℝ} (hr : r =O[atTop] (fun n => q^n)) (k : ℕ) :
    Summable (fun n : ℕ => ‖(n : ℝ)^k*r n‖) := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ)^k) atTop).mul hr
  exact summable_of_isBigO_nat
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1))
    h.norm_norm

/-- A fixed positive-base quadratic height is paid exactly, leaving the same
geometric residual and every finite polynomial absolute moment. -/
theorem quadratic_height_log_residual {b : ℝ} (hb : 1<b) (A : ℕ)
    {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hne : ¬ ∀ᶠ x in 𝓝 0, f x=0) :
    ∃ (e : ℕ) (c : ℝ), c≠0 ∧
      (fun n : ℕ => Real.log (b^(A*n*n)*f ((b⁻¹)^n))-
        (((A : ℝ)*(n : ℝ)^2-(e : ℝ)*(n : ℝ))*Real.log b+Real.log c))
          =O[atTop] (fun n => (b⁻¹)^n) := by
  have hb0 : 0<b := lt_trans zero_lt_one hb
  have hq0 : 0<b⁻¹ := inv_pos.mpr hb0
  have hq1 : b⁻¹<1 := (inv_lt_one₀ hb0).mpr hb
  obtain ⟨e,c,hc,hfn,hr⟩ := analytic_log_residual hq0 hq1 hf hne
  refine ⟨e,c,hc,?_⟩
  have heq : (fun n : ℕ => Real.log (b^(A*n*n)*f ((b⁻¹)^n))-
        (((A : ℝ)*(n : ℝ)^2-(e : ℝ)*(n : ℝ))*Real.log b+Real.log c))
      =ᶠ[atTop] residual f (b⁻¹) e c := by
    filter_upwards [hfn] with n hn
    rw [Real.log_mul (pow_ne_zero _ hb0.ne') hn,Real.log_pow]
    simp only [Nat.cast_mul,residual,Real.log_inv]
    ring
  exact heq.isBigO.trans hr

end OpenAIReview.FixedQLog

#lint+ in OpenAIReview.FixedQLog

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty fixed-q logarithm audit."
  logInfo m!"Fixed-q log audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-fixed-qdet-source-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-fixed-qdet-source-gate/axioms.json"
    (Json.mkObj [("scope",toJson "analytic normal-form hypothesis explicit; general actual q-determinant bridge remains paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
