/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
import OAI.NumberTheory.DirichletL.Detector.SourceCoefficient
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual calibrated Gauss-row averaging conserves every fixed frequency

The finite family consists of actual Eisenstein multipliers fixing calibration,
coprime to the physical modulus, with the stated ACTUAL character ratio.
For minus-one sextic cosets this ratio is subset parity, including physical
prime powers and cube rows. General CRT existence is not asserted here.
The sign-corrected average equals the literal physicalQuotient pointwise.
Thus its Fourier coefficient is unchanged at every fixed H, including u*a^6.
This does not assert that the global sixth-power frequency set is unit invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.GaugeAverage
open OAI OAI.ActualEisensteinCubic OAI.CubicEisenstein OAI.ConcreteTraceCRT
  OAI.CanonicalRowCompletion OAI.SevenEighths.ProbePhysical
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The literal actual physical quotient has the actual unit-character ratio. -/
theorem physicalQuotient_scale (C : CalibrationData) (A s : O)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s)
    (x : O ⧸ Ideal.span {(C.generator*A)*s}) :
    physicalQuotient C A s (supportedElement_ne_zero s hs)
        (Ideal.Quotient.mk _ b*x) =
      (C.residueMonoid b * idealRowHom b (Ideal.span {A}) *
        (idealRowHom b (Ideal.span {s}))⁻¹) *
          physicalQuotient C A s (supportedElement_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul,physicalQuotient_mk,physicalQuotient_mk]
  unfold calibratedNumerator
  rw [map_mul,idealRowHom_argument_mul,show -(b*m)=b*(-m) by ring,
    sexticGauss_unit_scale s hs b (-m) hcop]
  ring

/-- A finite average of ACTUAL common multipliers, retaining every quotient zero. -/
def rawAverage (C : CalibrationData) (A s : O) (hs : s≠0) (B : Finset O)
    (x : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  (B.card : ℂ)⁻¹ * ∑ b ∈ B, physicalQuotient C A s hs (Ideal.Quotient.mk _ b*x)

/-- Common minus-one cosets have an exact parity eigenvalue, not damping. -/
theorem rawAverage_eq (C : CalibrationData) (A s : O)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (B : Finset O) (hB : B.Nonempty) (r : ℕ)
    (hcop : ∀ b∈B, IsCoprime b s)
    (hcal : ∀ b∈B, C.residueMonoid b=1)
    (hphase : ∀ b∈B, idealRowHom b (Ideal.span {A}) *
      (idealRowHom b (Ideal.span {s}))⁻¹ = (-1 : ℂ)^r)
    (x : O ⧸ Ideal.span {(C.generator*A)*s}) :
    rawAverage C A s (supportedElement_ne_zero s hs) B x =
      (-1 : ℂ)^r * physicalQuotient C A s (supportedElement_ne_zero s hs) x := by
  have hn : (B.card : ℂ)≠0 := by exact_mod_cast hB.card_pos.ne'
  unfold rawAverage
  have he : (∑ b ∈ B, physicalQuotient C A s (supportedElement_ne_zero s hs)
      (Ideal.Quotient.mk _ b*x)) =
      (B.card : ℂ) * ((-1 : ℂ)^r * physicalQuotient C A s (supportedElement_ne_zero s hs) x) := by
    calc
      _ = ∑ _b ∈ B, (-1 : ℂ)^r * physicalQuotient C A s (supportedElement_ne_zero s hs) x := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [physicalQuotient_scale C A s hs b (hcop b hb),hcal b hb,one_mul,hphase b hb]
      _ = _ := by simp
  rw [he,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

/-- Averaging has norm-one action on the actual physical row at every point. -/
theorem rawAverage_norm (C : CalibrationData) (A s : O)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (B : Finset O) (hB : B.Nonempty) (r : ℕ)
    (hcop : ∀ b∈B, IsCoprime b s)
    (hcal : ∀ b∈B, C.residueMonoid b=1)
    (hphase : ∀ b∈B, idealRowHom b (Ideal.span {A}) *
      (idealRowHom b (Ideal.span {s}))⁻¹ = (-1 : ℂ)^r)
    (x : O ⧸ Ideal.span {(C.generator*A)*s}) :
    ‖rawAverage C A s (supportedElement_ne_zero s hs) B x‖ =
      ‖physicalQuotient C A s (supportedElement_ne_zero s hs) x‖ := by
  rw [rawAverage_eq C A s hs B hB r hcop hcal hphase x,norm_mul]
  simp

/-- Compensation keeps the original prescribed row, not a changed detector. -/
def correctedAverage (C : CalibrationData) (A s : O) (hs : s≠0)
    (B : Finset O) (r : ℕ) (x : O ⧸ Ideal.span {(C.generator*A)*s}) : ℂ :=
  (-1 : ℂ)^r * rawAverage C A s hs B x

/-- Every entry of the original actual calibrated Gauss row is conserved. -/
theorem correctedAverage_eq (C : CalibrationData) (A s : O)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (B : Finset O) (hB : B.Nonempty) (r : ℕ)
    (hcop : ∀ b∈B, IsCoprime b s)
    (hcal : ∀ b∈B, C.residueMonoid b=1)
    (hphase : ∀ b∈B, idealRowHom b (Ideal.span {A}) *
      (idealRowHom b (Ideal.span {s}))⁻¹ = (-1 : ℂ)^r)
    (x : O ⧸ Ideal.span {(C.generator*A)*s}) :
    correctedAverage C A s (supportedElement_ne_zero s hs) B r x =
      physicalQuotient C A s (supportedElement_ne_zero s hs) x := by
  unfold correctedAverage
  rw [rawAverage_eq C A s hs B hB r hcop hcal hphase x,← mul_assoc,← pow_add]
  simp [← two_mul r,pow_mul]

/-- The actual finite Fourier transform of the sign-corrected averaged row. -/
def averagedFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0)
    (B : Finset O) (r : ℕ) (H : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {(C.generator*A)*s},
    correctedAverage C A s hs B r x *
      quotientTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
        (Ideal.Quotient.mk _ H*x)

/-- Conservation is at each FIXED actual H, not a global sixth-power reindexing. -/
theorem averagedFourier_eq (C : CalibrationData) (A s : O) (hA : A≠0)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (B : Finset O) (hB : B.Nonempty) (r : ℕ)
    (hcop : ∀ b∈B, IsCoprime b s)
    (hcal : ∀ b∈B, C.residueMonoid b=1)
    (hphase : ∀ b∈B, idealRowHom b (Ideal.span {A}) *
      (idealRowHom b (Ideal.span {s}))⁻¹ = (-1 : ℂ)^r) (H : O) :
    averagedFourier C A s hA (supportedElement_ne_zero s hs) B r H =
      actualPhysicalFourier C A s hA (supportedElement_ne_zero s hs) H := by
  unfold averagedFourier actualPhysicalFourier
  apply tsum_congr
  intro x
  rw [correctedAverage_eq C A s hs B hB r hcop hcal hphase x]
  rfl

/-- Literal native congruence coefficient at every calibrated source frequency. -/
theorem averagedFourier_source_frequency (C : CalibrationData) (A s : O) (hA : A≠0)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (B : Finset O) (hB : B.Nonempty) (r : ℕ)
    (hcop : ∀ b∈B, IsCoprime b s)
    (hcal : ∀ b∈B, C.residueMonoid b=1)
    (hphase : ∀ b∈B, idealRowHom b (Ideal.span {A}) *
      (idealRowHom b (Ideal.span {s}))⁻¹ = (-1 : ℂ)^r) (u a : O) :
    averagedFourier C A s hA (supportedElement_ne_zero s hs) B r (u*a^6) =
      (Ideal.absNorm (Ideal.span {s}) : ℂ) * actualCongruenceCoefficient C A s hA (u*a^6) := by
  rw [averagedFourier_eq C A s hA hs B hB r hcop hcal hphase,
    actualPhysicalFourier_eq]

end OpenAIReview.GaugeAverage

#lint+ in OpenAIReview.GaugeAverage

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty gauge-average audit."
  logInfo m!"Gauge-average audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-gauge-average-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-gauge-average-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual calibrated physical quotient finite average and every fixed actual Fourier/source-frequency coefficient; actual unit-family hypotheses explicit; no CRT existence/global source/estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
