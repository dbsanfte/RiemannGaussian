/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.CalibrationCancellation
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Changing the calibration character at a fixed physical modulus

This is different from averaging residue-unit translates. The character itself
may vary, while the two coprime Eisenstein moduli, frequency and arbitrary
physical function stay fixed. Native CRT gives an exact rank-one factorization.
After dividing by the actual nonzero calibration factor every character gives
the same Fourier coefficient. A zero-sum combination removes that coefficient,
including any source it carries. No claim about separately projected theta
pieces, changing moduli, or a bound for the common coefficient is made.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.CalibrationFamily
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT OAI.CubicEisenstein
  OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge OAI.CompletedGauss
  OAI.SevenEighths.ProbePhysical
  OAI.SevenEighths.CenteredMomentCommonSupport OAI.SevenEighths.CenteredMomentFourier
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Literal finite CRT transform, with arbitrary physical weights and all zeros. -/
def mixed (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [Fintype (Residue (a*b))] (χ : MulChar (Residue a) ℂ)
    (F : Residue b → ℂ) (h : Residue (a*b)) : ℂ :=
  ∑ x : Residue (a*b),
    χ (frequencyReduction a (a*b) (dvd_mul_right a b) x) *
      F (frequencyReduction b (a*b) (dvd_mul_left b a) x) *
      quotientTrace (a*b) (mul_ne_zero ha hb) (h*x)

/-- The actual character and Gauss normalization, at this same frequency. -/
def factor (a b : O) (ha : a ≠ 0) (χ : MulChar (Residue a) ℂ)
    (h : Residue (a*b)) : ℂ :=
  χ (Ideal.Quotient.mk _ b) *
    residueGauss a ha χ (frequencyReduction a (a*b) (dvd_mul_right a b) h)

/-- The unchanged physical Fourier coefficient after CRT. -/
def bare (a b : O) (hb : b ≠ 0) [Fintype (Residue b)]
    (F : Residue b → ℂ) (h : Residue (a*b)) : ℂ :=
  ∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
    quotientTrace b hb
      (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)

/-- No assumption on the physical weight; no squarefree or source approximation. -/
theorem mixed_eq (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : MulChar (Residue a) ℂ) (F : Residue b → ℂ) (h : Residue (a*b)) :
    mixed a b ha hb χ F h = factor a b ha χ h * bare a b hb F h :=
  coprime_mixed_fourier a b ha hb hcop χ F h

/-- Frequency support is retained: a vanishing calibration factor kills the raw row. -/
theorem mixed_eq_zero_of_factor_zero (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : MulChar (Residue a) ℂ) (F : Residue b → ℂ) (h : Residue (a*b))
    (hzero : factor a b ha χ h = 0) : mixed a b ha hb χ F h = 0 := by
  rw [mixed_eq a b ha hb hcop, hzero, zero_mul]

/-- All calibrated character choices have the same normalized physical image. -/
theorem normalized_eq (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : MulChar (Residue a) ℂ) (F : Residue b → ℂ) (h : Residue (a*b))
    (hne : factor a b ha χ h ≠ 0) :
    mixed a b ha hb χ F h / factor a b ha χ h = bare a b hb F h := by
  rw [mixed_eq a b ha hb hcop]
  exact mul_div_cancel_left₀ _ hne

/-- The raw family is rank one, even at excluded frequencies. -/
theorem raw_family_eq {ι : Type*} (I : Finset ι) (w : ι → ℂ)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : ι → MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a*b)) :
    (∑ i ∈ I, w i * mixed a b ha hb (χ i) F h) =
      (∑ i ∈ I, w i * factor a b ha (χ i) h) * bare a b hb F h := by
  simp_rw [mixed_eq a b ha hb hcop, ← mul_assoc]
  exact (Finset.sum_mul _ _ _).symm

/-- A fixed-modulus normalized code is only its coefficient sum times the old row. -/
theorem normalized_family_eq {ι : Type*} (I : Finset ι) (w : ι → ℂ)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : ι → MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a*b)) (hne : ∀ i ∈ I, factor a b ha (χ i) h ≠ 0) :
    (∑ i ∈ I, w i * (mixed a b ha hb (χ i) F h / factor a b ha (χ i) h)) =
      (∑ i ∈ I, w i) * bare a b hb F h := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalized_eq a b ha hb hcop (χ i) F h (hne i hi)]

/-- An annihilating normalized code also deletes any nonzero common source. -/
theorem normalized_family_zero_iff {ι : Type*} (I : Finset ι) (w : ι → ℂ)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a*b))]
    (χ : ι → MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a*b)) (hne : ∀ i ∈ I, factor a b ha (χ i) h ≠ 0)
    (hsource : bare a b hb F h ≠ 0) :
    (∑ i ∈ I, w i * (mixed a b ha hb (χ i) F h / factor a b ha (χ i) h)) = 0 ↔
      (∑ i ∈ I, w i) = 0 := by
  rw [normalized_family_eq I w a b ha hb hcop χ F h hne]
  exact mul_eq_zero.trans (or_iff_left hsource)

/-- Native calibration compensation has this same bare-image interpretation. -/
theorem native_compensated_eq (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (A s : O)
    (hA : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {A}))
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s
        (supportedElement_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator) : ℂ)*C.tau*C.residueMonoid s*
          star (C.residueMonoid H)) * (C.Xi A)⁻¹ =
      bareCongruenceCoefficient A s
        (supportedElement_ne_zero A hA) H :=
  calibration_coefficient_cancel S hS A s hA hs hcop H hH

end OpenAIReview.CalibrationFamily

#lint+ in OpenAIReview.CalibrationFamily

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty calibration-family audit."
  logInfo m!"Calibration-family audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-calibration-family-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-calibration-family-gate/axioms.json"
    (Json.mkObj [("scope",toJson "fixed coprime Eisenstein moduli; arbitrary physical weights; exact raw and normalized character-family collapse; no separate theta projection or arithmetic bound"),
      ("namespaceLinters",toJson (15:Nat)),("allLocalModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
