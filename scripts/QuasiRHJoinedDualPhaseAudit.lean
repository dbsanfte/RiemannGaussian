/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
import OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native Gauss cancellation in an independent physical/spectral dual pair

The actual corrected spectral coefficient times its normalized sextic Gauss
root is exactly the spectral ideal's Mobius sign. Multiplication by the
physical Gauss and its conjugate cancels the physical root WITHOUT adding
a physical Mobius sign. The displayed dual product is the sign-adjusted CRT
root; identifying it with a complete primitive Fourier transform additionally
uses the coprime CRT formula. This leaf does not assert a Poisson estimate,
physical source coverage, nonsquarefree-physical extension or covariance saving.
Every literal frequency and native character zero is retained in the final identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.QuasiRHJoinedDualPhaseAudit
open OAI ActualEisensteinCubic CompletedGauss FiniteGaussPhase QuadraticGaussRay
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

/-- Actual squarefree coefficient with its literal modulus-four correction. -/
def correctedNativeCoefficient (n : O) : ℂ :=
  squarefreeGaussCoefficient (Ideal.span {n}) *
    star (fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4:O)}) n))

/-- The native corrected spectral Gauss product leaves exactly mu(I),
with the actual integer ideal and original additive convention. -/
theorem correctedCoefficient_mul_gauss
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1) :
    correctedNativeCoefficient (∏ i, p i)*
      canonicalProductGauss p hp hcop hgood (fun _ => 1) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) := by
  have hc := canonicalProductCoefficient_mul_gauss_one p hp hcop hgood hchar hprimary
  have hg : canonicalProductG p hp hcop hgood *
      star (canonicalProductG p hp hcop hgood)=1 := by
    rw [← starRingEnd_apply,Complex.mul_conj',
      norm_canonicalProductG p hp hcop hgood hchar hprimary]
    norm_num
  unfold correctedNativeCoefficient
  rw [squarefreeGaussCoefficient_eq_canonicalProductCoefficient p hp hcop hgood hprimary,
    ← canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  calc
    _ = (canonicalProductCoefficient p hp hcop hgood*
        canonicalProductGauss p hp hcop hgood (fun _ => 1))*
          star (canonicalProductG p hp hcop hgood) := by ring
    _ = _ := by rw [hc,mul_assoc,hg,mul_one]

/-- The physical Gauss phase cancels its dual conjugate. There is no mu(A).
`phase` keeps the complete fixed-ray/reciprocity CRT multiplier explicit. -/
theorem joined_signAdjusted_crt_phase
    {α ι : Type*} [Fintype α] [Fintype ι]
    (a : α → O) (ha : ∀ j, a j ≠ 0) [∀ j, (Ideal.span {a j}).IsMaximal]
    (acop : Pairwise (Function.onFun IsCoprime (fun j => Ideal.span {a j})))
    (agood : ∀ j, lambda ∉ Ideal.span {a j})
    (achar : ∀ j, ringChar (O ⧸ Ideal.span {a j}) ≠ 2)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (phase : ℂ) :
    canonicalProductGauss a ha acop agood (fun _ => 1)*
      correctedNativeCoefficient (∏ i, p i)*
      (canonicalProductGauss p hp hcop hgood (fun _ => 1)*
        star (canonicalProductGauss a ha acop agood (fun _ => 1))*phase) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)*phase := by
  have hA : canonicalProductGauss a ha acop agood (fun _ => 1)*
      star (canonicalProductGauss a ha acop agood (fun _ => 1))=1 := by
    rw [← starRingEnd_apply,Complex.mul_conj',
      norm_canonicalProductGauss a ha acop agood achar (fun _ => 1)
        (by intro; decide) (by intro; decide)]
    norm_num
  calc
    _ = (correctedNativeCoefficient (∏ i, p i)*
        canonicalProductGauss p hp hcop hgood (fun _ => 1))*
        (canonicalProductGauss a ha acop agood (fun _ => 1)*
          star (canonicalProductGauss a ha acop agood (fun _ => 1)))*phase := by ring
    _ = _ := by rw [correctedCoefficient_mul_gauss p hp hcop hgood hchar hprimary,hA,mul_one]

/-- The literal native dual characters survive at every frequency, including
zero, nonunits and principal sixth-power frequencies. No shifted support is deleted. -/
theorem joined_frequency_phase
    {α ι : Type*} [Fintype α] [Fintype ι]
    (a : α → O) (ha : ∀ j, a j ≠ 0) [∀ j, (Ideal.span {a j}).IsMaximal]
    (acop : Pairwise (Function.onFun IsCoprime (fun j => Ideal.span {a j})))
    (agood : ∀ j, lambda ∉ Ideal.span {a j})
    (achar : ∀ j, ringChar (O ⧸ Ideal.span {a j}) ≠ 2)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (phase : ℂ) (h : O) :
    (canonicalProductGauss a ha acop agood (fun _ => 1)*
      correctedNativeCoefficient (∏ i, p i)*
      (canonicalProductGauss p hp hcop hgood (fun _ => 1)*
        star (canonicalProductGauss a ha acop agood (fun _ => 1))*phase))*
      star (idealRowHom h (Ideal.span {∏ i, p i}))*
        idealRowHom h (Ideal.span {∏ j, a j}) =
    ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)*phase)*
      star (idealRowHom h (Ideal.span {∏ i, p i}))*
        idealRowHom h (Ideal.span {∏ j, a j}) := by
  rw [joined_signAdjusted_crt_phase a ha acop agood achar p hp hcop hgood hchar hprimary]

/-- The literal native reciprocity factor for the two primary products. -/
def nativeReciprocityFactor (A I : O) : ℂ :=
  idealRowHom A (Ideal.span {I})*star (idealRowHom I (Ideal.span {A}))

/-- The frequency identity with the actual native CRT reciprocity factor.
The primitive-Fourier interpretation is restricted to coprime A,I; the finite
phase equality itself retains all zeros even without that restriction. -/
theorem native_joined_frequency_phase
    {α ι : Type*} [Fintype α] [Fintype ι]
    (a : α → O) (ha : ∀ j, a j ≠ 0) [∀ j, (Ideal.span {a j}).IsMaximal]
    (acop : Pairwise (Function.onFun IsCoprime (fun j => Ideal.span {a j})))
    (agood : ∀ j, lambda ∉ Ideal.span {a j})
    (achar : ∀ j, ringChar (O ⧸ Ideal.span {a j}) ≠ 2)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1) (h : O) :
    (canonicalProductGauss a ha acop agood (fun _ => 1)*
      correctedNativeCoefficient (∏ i, p i)*
      (canonicalProductGauss p hp hcop hgood (fun _ => 1)*
        star (canonicalProductGauss a ha acop agood (fun _ => 1))*
        nativeReciprocityFactor (∏ j, a j) (∏ i, p i)))*
      star (idealRowHom h (Ideal.span {∏ i, p i}))*
        idealRowHom h (Ideal.span {∏ j, a j}) =
    ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ)*
      nativeReciprocityFactor (∏ j, a j) (∏ i, p i))*
      star (idealRowHom h (Ideal.span {∏ i, p i}))*
        idealRowHom h (Ideal.span {∏ j, a j}) :=
  joined_frequency_phase a ha acop agood achar p hp hcop hgood hchar hprimary _ h

end RiemannGaussian.QuasiRHJoinedDualPhaseAudit

#lint+ in RiemannGaussian.QuasiRHJoinedDualPhaseAudit

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
  logInfo m!"Native joined dual phase: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-joint-covariance-probe/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
