/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import LeanCert.Engine.IntervalEvalDyadic
import Mathlib.Data.List.Forall2

/-!
# Checked interval programs with shared intermediate values

Each instruction is evaluated by LeanCert's checked dyadic evaluator and
prepends its result to the environment. Sharing intermediate quantities
avoids repeated evaluation of the same denominator and derivative. Failure
of a domain check propagates; it never supplies an enclosure.
-/

namespace RiemannGaussian.CertifiedIntervalProgram
open LeanCert.Core LeanCert.Engine

/-- Interval environment with a mathematically valid zero default. -/
def intervalEnv (xs : List IntervalDyadic) : IntervalDyadicEnv :=
  fun i => xs[i]?.getD default

/-- Real counterpart of the interval environment. -/
noncomputable def realEnv (xs : List ℝ) : ℕ → ℝ := fun i => xs[i]?.getD 0

/-- Execute a sequence of checked instructions, preserving each result. -/
def run (cfg : DyadicConfig) : List Expr → List IntervalDyadic →
    EvalResult (List IntervalDyadic)
  | [], xs => .ok xs
  | e :: es, xs =>
    match evalIntervalDyadicChecked e (intervalEnv xs) cfg with
    | .error err => .error err
    | .ok y => run cfg es (y :: xs)

/-- Exact real semantics of the same sequence. -/
noncomputable def runReal : List Expr → List ℝ → List ℝ
  | [], xs => xs
  | e :: es, xs => runReal es (Expr.eval (realEnv xs) e :: xs)

/-- Pointwise list containment supplies the evaluator environment. -/
theorem envMem_of_forall₂ {xs : List ℝ} {ys : List IntervalDyadic}
    (h : List.Forall₂ (fun x I => x ∈ I) xs ys) :
    envMemDyadic (realEnv xs) (intervalEnv ys) := by
  intro i
  induction h generalizing i with
  | nil =>
    simp [realEnv, intervalEnv, Membership.mem,
      default, IntervalDyadic.singleton, LeanCert.Core.Dyadic.zero,
      LeanCert.Core.Dyadic.toRat]
  | cons ha hab ih =>
    cases i with
    | zero => simpa only [realEnv, intervalEnv, List.getElem?_cons_zero,
        Option.getD_some] using ha
    | succ i => simpa only [realEnv, intervalEnv, List.getElem?_cons_succ] using ih i

/-- Every successful instruction sequence encloses its exact real
semantics. This theorem checks every reciprocal's domain along the way. -/
theorem run_sound (cfg : DyadicConfig) (hprec : cfg.precision ≤ 0)
    (es : List Expr) {xs : List ℝ} {ys zs : List IntervalDyadic}
    (hxy : List.Forall₂ (fun x I => x ∈ I) xs ys)
    (h : run cfg es ys = .ok zs) :
    List.Forall₂ (fun x I => x ∈ I) (runReal es xs) zs := by
  induction es generalizing xs ys with
  | nil =>
    simp only [run, Except.ok.injEq] at h
    subst zs
    exact hxy
  | cons e es ih =>
    cases hy : evalIntervalDyadicChecked e (intervalEnv ys) cfg with
    | error err => simp [run, hy] at h
    | ok y =>
      have he := evalIntervalDyadicChecked_correct e (realEnv xs) (intervalEnv ys)
        (envMem_of_forall₂ hxy) cfg hprec y hy
      exact ih (List.Forall₂.cons he hxy) (by simpa [run, hy] using h)

end RiemannGaussian.CertifiedIntervalProgram
