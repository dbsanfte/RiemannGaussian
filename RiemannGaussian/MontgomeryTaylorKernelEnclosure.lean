/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedIntervalProgram
import RiemannGaussian.MontgomeryTaylorKernelDerivatives

/-!
# A shared interval program for the kernel and its derivatives

Sine and cosine enter as certified intervals. All subsequent instructions
are rational operations, and the common reciprocal denominator is evaluated
once. The exact semantics recover the previously proved derivative formulas.
-/

namespace RiemannGaussian.MontgomeryTaylorKernelEnclosure
open LeanCert.Core LeanCert.Engine
open CertifiedIntervalProgram MontgomeryTaylorNumericalKernel

local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul

private def denInstruction : Expr :=
  Expr.const 2 *ₑ (Expr.var 1).pow 2 *ₑ (Expr.var 0).pow 2 -ₑ Expr.const 1

private def kernelInstruction : Expr :=
  (Expr.const 2 *ₑ Expr.var 3 *ₑ Expr.var 6 *ₑ Expr.var 2 *ₑ Expr.var 4 -ₑ Expr.var 5) *ₑ
    Expr.var 0

private def derivativeInstruction : Expr :=
  ((Expr.const 2 *ₑ Expr.var 4 *ₑ Expr.var 7 *ₑ
      (Expr.var 5 +ₑ Expr.var 4 *ₑ Expr.var 3 *ₑ Expr.var 6) +ₑ
        Expr.var 4 *ₑ Expr.var 5) -ₑ
      Expr.var 0 *ₑ (Expr.const 4 *ₑ (Expr.var 4).pow 2 *ₑ Expr.var 3)) *ₑ Expr.var 1

private def secondDerivativeInstruction : Expr :=
  (((Expr.var 5).pow 2 *ₑ (Expr.const 4 *ₑ Expr.var 8 +ₑ Expr.const 1) *ₑ Expr.var 7 -ₑ
      Expr.const 2 *ₑ (Expr.var 5).pow 3 *ₑ Expr.var 8 *ₑ Expr.var 4 *ₑ Expr.var 6) -ₑ
    Expr.const 2 *ₑ Expr.var 0 *ₑ (Expr.const 4 *ₑ (Expr.var 5).pow 2 *ₑ Expr.var 4) -ₑ
    Expr.var 1 *ₑ (Expr.const 4 *ₑ (Expr.var 5).pow 2)) *ₑ Expr.var 2

/-- Initial inputs are `[x, pi, sin(pi*x), cos(pi*x), etaRat]`.
The first three final outputs are the curvature, slope, and squared kernel. -/
def program : List Expr :=
  [denInstruction, .inv (.var 0), kernelInstruction, derivativeInstruction,
    secondDerivativeInstruction, (Expr.var 2).pow 2,
    Expr.const 2 *ₑ Expr.var 3 *ₑ Expr.var 2,
    Expr.const 2 *ₑ (Expr.var 3).pow 2 +ₑ Expr.const 2 *ₑ Expr.var 4 *ₑ Expr.var 2]

/-- Exact real inputs supplied to the interval program. -/
noncomputable def inputs (x : ℝ) : List ℝ :=
  [x, Real.pi, Real.sin (Real.pi * x), Real.cos (Real.pi * x), (etaRat : ℝ)]

/-- The instruction indices and formulas agree with the actual analytic
model, including both derivatives and the common denominator. -/
theorem program_semantics (x : ℝ) :
    runReal program (inputs x) =
      [squaredDD x, squaredD x, kernel x ^ 2, kernelDD x, kernelD x, kernel x,
        (denominator x)⁻¹, denominator x, x, Real.pi,
        Real.sin (Real.pi * x), Real.cos (Real.pi * x), (etaRat : ℝ)] := by
  simp only [program, runReal, inputs, denInstruction, kernelInstruction,
    derivativeInstruction, secondDerivativeInstruction, Expr.eval, Expr.sub,
    Expr.pow, realEnv, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Rat.cast_ofNat, Rat.cast_one, mul_one]
  simp only [squaredDD, squaredD, kernelDD, kernelD, kernel, numeratorDD,
    numeratorD, denominator, div_eq_mul_inv, pow_succ, pow_zero, one_mul,
    sub_eq_add_neg, mul_assoc]

/-- A successful checked run encloses all three analytic quantities for
every real input represented by the input intervals. -/
theorem enclosures {cfg : DyadicConfig} (hprec : cfg.precision ≤ 0)
    {x : ℝ} {ys zs : List IntervalDyadic}
    (hxy : List.Forall₂ (fun v I => v ∈ I) (inputs x) ys)
    (h : run cfg program ys = .ok zs) :
    squaredDD x ∈ intervalEnv zs 0 ∧ squaredD x ∈ intervalEnv zs 1 ∧
      kernel x ^ 2 ∈ intervalEnv zs 2 := by
  have hall := run_sound cfg hprec program hxy h
  rw [program_semantics] at hall
  have he := envMem_of_forall₂ hall
  exact ⟨he 0, he 1, he 2⟩

end RiemannGaussian.MontgomeryTaylorKernelEnclosure
