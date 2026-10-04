/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedGamma
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
Optional rate regression for a proposed Selberg/PNT transfer.

These are exact tests of a synthetic radial error, not estimates of any
prime sum. They introduce no project carrier and do not prove the floor.
The full factorial integral is retained; no fixed saddle is substituted.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory Set
namespace RiemannGaussian.ZetaRieszSelbergSpectralRateRegression

/-- Exact rate of an exponentially damped error in the radial factorial
test. The error estimate for ordinary primes is NOT an input or conclusion. -/
theorem normalized_factorial_error (u delta : ℝ) (N : ℕ)
    (hd : 0 < 1/2+delta) :
    (u : ℂ)^(N+1) * (∫ t : ℝ in Ioi 0,
      (t : ℂ)^N/(N.factorial : ℂ)*
        Complex.exp (-((1/2+delta : ℝ) : ℂ)*t)) =
      ((u/(1/2+delta) : ℝ) : ℂ)^(N+1) := by
  rw [(ZetaRieszSelectedGamma.complex_factorial_laplace
    (z := ((1/2+delta : ℝ) : ℂ)) (by simpa using hd) N).2,
    ←mul_pow,Complex.ofReal_div,div_eq_mul_inv]
  simp only [div_eq_mul_inv]

/-- Qualitative decay of the critical synthetic error is genuine. -/
theorem critical_error_tendsto :
    Tendsto (fun t : ℝ => Real.exp (-((1/20000 : ℝ)*t))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<1/20000))

/-- Despite that qualitative decay, its normalized factorial integral
has mass one at EVERY order. This is a transfer countertest only. -/
theorem critical_normalized_error (N : ℕ) :
    (((10001/20000 : ℝ) : ℂ)^(N+1) * (∫ t : ℝ in Ioi 0,
      (t : ℂ)^N/(N.factorial : ℂ)*
        Complex.exp (-((1/2+1/20000 : ℝ) : ℂ)*t))) = 1 := by
  rw [normalized_factorial_error (10001/20000) (1/20000) N (by norm_num)]
  norm_num

/-- A stronger exponential error WOULD have a strict rate. No theorem
about actual primes establishes this hypothetical error in this checker. -/
theorem stronger_error_rate (N : ℕ) :
    (((10001/20000 : ℝ) : ℂ)^(N+1) * (∫ t : ℝ in Ioi 0,
      (t : ℂ)^N/(N.factorial : ℂ)*
        Complex.exp (-((1/2+1/10000 : ℝ) : ℂ)*t))) =
      ((10001/10002 : ℝ) : ℂ)^(N+1) := by
  rw [normalized_factorial_error (10001/20000) (1/10000) N (by norm_num)]
  norm_num

end RiemannGaussian.ZetaRieszSelbergSpectralRateRegression

#lint+ in RiemannGaussian.ZetaRieszSelbergSpectralRateRegression

open Lean Elab Command
run_cmd do
  let names := #[
    `RiemannGaussian.ZetaRieszSelbergSpectralRateRegression.normalized_factorial_error,
    `RiemannGaussian.ZetaRieszSelbergSpectralRateRegression.critical_error_tendsto,
    `RiemannGaussian.ZetaRieszSelbergSpectralRateRegression.critical_normalized_error,
    `RiemannGaussian.ZetaRieszSelbergSpectralRateRegression.stronger_error_rate]
  let env ← getEnv
  let mut report : Array Json := #[]
  for name in names do
    unless (env.find? name).isSome do throwError "Missing rate regression: {name}"
    let dependencies ← Lean.collectAxioms name
    for ax in dependencies do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {name}: {ax}"
    report := report.push (Json.mkObj [("theorem",toJson name.toString),
      ("axioms",toJson (dependencies.map Name.toString))])
  IO.FS.writeFile ".lake/riesz-selberg-spectral-rate/axioms.json"
    (Json.mkObj [("syntheticRateRegressionsOnly",toJson true),
      ("ordinaryPrimeEstimateProved",toJson false),
      ("onlyStandardAxioms",toJson true),("theorems",Json.arr report)]).pretty
  logInfo m!"Checked four synthetic rate regressions; no ordinary-prime estimate."
