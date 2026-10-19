/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# The ordinary-density balance in simultaneous Frobenius extraction

For a finite group of conjugates and a fixed visible coordinate set, join
ALL coordinate incidences before averaging over Frobenius classes. The
uniform coefficient is exactly (visible coordinates / group order) times
the total degree. If an independent interpolation theorem has this same
dimension ratio as its Archimedean slope, the uniform main terms coincide.
No interpolation, prime equidistribution, determinant bound, or zeta-source
bridge is assumed to have been proved by this finite calculation.

The four-class specialization gives the exact three quadratic-character
terms left after subtracting the ACTUAL uncoloured arithmetic row. Smooth
density subtraction is different: it leaves that row's arithmetic error.
All identities allow arbitrary complex weights, including prime-power
phases. They are a scoped obstruction to an automatic density surplus,
not an independent RH estimate or a no-go for all determinant methods.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RiemannGaussian.ArithmeticOperatorFrobeniusBalanceAudit

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Main degree extracted by a class whose action is left multiplication. -/
def degreeOverlap (V : Finset G) (degree : G → ℂ) (g : G) : ℂ :=
  ∑ h ∈ V, if g * h ∈ V then degree h else 0

/-- Each coordinate is visible under exactly `V.card` group translates. -/
theorem sum_translate_indicator (V : Finset G) (h : G) (w : ℂ) :
    (∑ g : G, if g * h ∈ V then w else 0) = (V.card : ℂ) * w := by
  calc
    _ = ∑ g : G, if g ∈ V then w else 0 :=
      Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Exact incidence double count; no distribution of actual primes enters. -/
theorem sum_degreeOverlap (V : Finset G) (degree : G → ℂ) :
    (∑ g : G, degreeOverlap V degree g) =
      (V.card : ℂ) * ∑ h ∈ V, degree h := by
  unfold degreeOverlap
  rw [Finset.sum_comm]
  simp_rw [sum_translate_indicator]
  rw [Finset.mul_sum]

/-- The uniform Frobenius main coefficient is the geometric dimension ratio. -/
theorem uniform_average (V : Finset G) (degree : G → ℂ) :
    (∑ g : G, degreeOverlap V degree g) / Fintype.card G =
      ((V.card : ℂ) / Fintype.card G) * ∑ h ∈ V, degree h := by
  rw [sum_degreeOverlap]
  ring

/-- This is conditional only on the displayed slope equality, NOT a new
interpolation theorem for arbitrary visible subsets. -/
theorem uniform_sub_height_eq_zero (V : Finset G) (degree : G → ℂ)
    (slope : ℂ) (hslope : slope = (V.card : ℂ) / Fintype.card G) :
    (∑ g : G, degreeOverlap V degree g) / Fintype.card G -
      slope * ∑ h ∈ V, degree h = 0 := by
  rw [uniform_average, hslope, sub_self]

/-- The sign of one quadratic conjugation. -/
def quadraticSign (flip : Bool) : ℂ := if flip then -1 else 1

/-- Visible coordinates are `1, sigma, sigma*tau`; the missing one is `tau`.
Arguments record whether the two independent square roots change sign. -/
def biquadraticWeight (a b c : ℂ) (flipA flipB : Bool) : ℂ :=
  if flipA then (if flipB then a + c else a + b)
  else (if flipB then b + c else a + b + c)

/-- All four classes, including the class omitted by single-coordinate
extraction, decompose into the trivial and three nontrivial characters. -/
theorem biquadraticWeight_eq_characters (a b c : ℂ) (flipA flipB : Bool) :
    biquadraticWeight a b c flipA flipB =
      3 / 4 * (a + b + c) + (-a + b + c) / 4 * quadraticSign flipA +
      (a + b - c) / 4 * quadraticSign flipB +
      (a - b + c) / 4 * (quadraticSign flipA * quadraticSign flipB) := by
  cases flipA <;> cases flipB <;>
    simp [biquadraticWeight, quadraticSign] <;> ring

/-- The all-class main coefficient equals the paper's rank-four / three-
coordinate Archimedean ratio exactly, before any conductor or rounding cost. -/
theorem biquadratic_uniform_balance (a b c : ℂ) :
    (biquadraticWeight a b c false false + biquadraticWeight a b c true false +
      biquadraticWeight a b c false true + biquadraticWeight a b c true true) / 4 =
      3 / 4 * (a + b + c) := by
  simp [biquadraticWeight]
  ring

/-- Exact centering by the full arithmetic row removes only the trivial
character term. No absolute values or phases have been discarded. -/
theorem centered_packet_eq_characters {ι : Type*} (I : Finset ι)
    (weight : ι → ℂ) (flipA flipB : ι → Bool) (a b c : ℂ) :
    (∑ i ∈ I, weight i * biquadraticWeight a b c (flipA i) (flipB i)) -
        (3 / 4 * (a + b + c)) * ∑ i ∈ I, weight i =
      ((-a + b + c) / 4) * ∑ i ∈ I, weight i * quadraticSign (flipA i) +
      ((a + b - c) / 4) * ∑ i ∈ I, weight i * quadraticSign (flipB i) +
      ((a - b + c) / 4) *
        ∑ i ∈ I, weight i * (quadraticSign (flipA i) * quadraticSign (flipB i)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [biquadraticWeight_eq_characters]
  ring

/-- Subtracting a smooth density instead leaves the actual uncoloured error.
This is the exact term that cannot be silently called a paid pole. -/
theorem smooth_centering_ledger {ι : Type*} (I : Finset ι)
    (weight : ι → ℂ) (flipA flipB : ι → Bool) (a b c density : ℂ) :
    (∑ i ∈ I, weight i * biquadraticWeight a b c (flipA i) (flipB i)) -
        (3 / 4 * (a + b + c)) * density =
      ((∑ i ∈ I, weight i * biquadraticWeight a b c (flipA i) (flipB i)) -
        (3 / 4 * (a + b + c)) * ∑ i ∈ I, weight i) +
      (3 / 4 * (a + b + c)) * ((∑ i ∈ I, weight i) - density) := by
  ring

end RiemannGaussian.ArithmeticOperatorFrobeniusBalanceAudit

#lint+ in RiemannGaussian.ArithmeticOperatorFrobeniusBalanceAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty Frobenius balance audit."
  logInfo m!"Frobenius balance audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/siegel-paper-review/formal-balance"
  IO.FS.writeFile ".lake/siegel-paper-review/formal-balance/axioms.json"
    (Json.mkObj [("scope", toJson "finite all-class degree incidence and exact arithmetic/smooth centering; no interpolation, prime estimate or zero source"),
      ("onlyStandardAxioms", toJson true), ("namespaceLinters", toJson (15 : Nat)),
      ("allLocalDeclarationsByModuleProvenance", toJson true),
      ("declarations", toJson declarations),
      ("theoremsIncludingGeneratedHelpers", toJson theorems),
      ("declarationAxioms", Json.arr reports)]).pretty
