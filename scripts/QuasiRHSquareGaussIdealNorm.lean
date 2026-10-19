/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHAllSquarePartition
import scripts.QuasiRHSquareGaussNorm
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! General supported divisor families and actual normalized square Gauss bounds.
Zero root exponents remain in the common physical prime family. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace OpenAIReview.SquareGaussIdealNorm
open OAI UniqueFactorizationMonoid
open OpenAIReview.AllSquarePartition
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisor_support_subset {C T : Id} (hC : C ≠ 0) (hT : T ≠ 0) (hd : T ∣ C) :
    support T ⊆ support C := by
  have hm := (dvd_iff_normalizedFactors_le_normalizedFactors hT hC).mp hd
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hm (Multiset.mem_toFinset.mp hP))

/-- Every divisor uses the physical prime family, including its zero exponents. -/
lemma primaryGenerator_divisor_family {C T : Id} (hC : C ≠ 0) (hT : T ≠ 0) (hd : T ∣ C) :
    CompletedGauss.primaryGenerator T =
      ∏ P : PrimeOf C, primeElement C P ^ val T P := by
  have hh : (∏ P ∈ support C, CompletedGauss.primaryPrime P ^ val T P) =
      ∏ P ∈ support T, CompletedGauss.primaryPrime P ^ val T P := by
    symm
    apply Finset.prod_subset (divisor_support_subset hC hT hd)
    intro P _ hp
    rw [val_zero_of_not_mem hp,pow_zero]
  rw [primaryGenerator_product hT, ← hh]
  exact (Finset.prod_coe_sort (support C)
    (fun P : Id => CompletedGauss.primaryPrime P ^ val T P)).symm

/-- Supported physical ideals supply every nonzero divisor hypothesis. -/
lemma supported_divisor_primaryGenerator_family {C T : Id}
    (hC : CanonicalQuadraticSieve.Supported C) (hd : T ∣ C) :
    CompletedGauss.primaryGenerator T =
      ∏ P : PrimeOf C, primeElement C P ^ val T P :=
  primaryGenerator_divisor_family hC.1 (supported_of_dvd hC hd).1 hd

/-- Uniform actual square-baseline bound for ANY divisor of the physical ideal.
The divisor need not be its canonical root part. -/
theorem gaussRow_divisor_square_norm {C T : Id}
    (hC : CanonicalQuadraticSieve.Supported C) (hd : T ∣ C)
    (ζ : O) (hζ : IsUnit ζ) :
    ‖SevenEighths.CenteredMomentGaussEnergy.gaussRow (CompletedGauss.primaryGenerator C)
      ((CanonicalQuadraticSieve.supported_span_primaryGenerator_iff C).mpr hC)
      (-ζ * (CompletedGauss.primaryGenerator T)^2)‖ ≤ (Ideal.absNorm T : ℝ) := by
  have hT := supported_of_dvd hC hd
  have hcgen := primaryGenerator_family hC.1
  have htgen := primaryGenerator_divisor_family hC.1 hT.1 hd
  have hh := OpenAIReview.SquareGaussNorm.prime_product_square_norm
    (Finset.univ : Finset (PrimeOf C)) (primeElement C)
    (primeElement_prime hC) (primeElement_supported hC) (primeElement_coprime hC)
    (fun P => val C P) (fun P => val T P) (-ζ) (by
      intro P _
      exact fun hp => (primeElement_prime hC P).not_isUnit (isUnit_of_dvd_unit hp hζ.neg))
  simp only [← hcgen, ← htgen] at hh
  simpa only [SevenEighths.ProbePhysical.elementNorm,
    (CompletedGauss.primaryGenerator_spec T
      (CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero T hT)).1] using hh

end OpenAIReview.SquareGaussIdealNorm
#lint+ in OpenAIReview.SquareGaussIdealNorm

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    details := details.push (Json.mkObj [("declaration", toJson n.toString),
      ("isTheorem", toJson ci.isTheorem), ("axioms", toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty actual ideal Gauss norm audit."
  logInfo m!"Actual divisor square Gauss norm: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-square-gauss-ideal-norm"
  IO.FS.writeFile ".lake/arithmetic-operator-square-gauss-ideal-norm/axioms.json"
    (Json.mkObj [("scope", toJson "actual normalized Gauss square bound for any divisor of a supported physical ideal; no source/energy estimate"),
      ("namespaceLinters", toJson (15 : Nat)), ("onlyStandardAxioms", toJson true),
      ("allLocalModuleProvenance", toJson true), ("declarations", toJson declarations),
      ("theoremsIncludingHelpers", toJson theorems), ("details", Json.arr details)]).pretty
