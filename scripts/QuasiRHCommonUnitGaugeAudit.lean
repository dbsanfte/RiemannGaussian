/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# A common ACTUAL residue-unit gauge of native numerator columns

The residue units must satisfy the stated actual canonical sextic values.
They are not freely supplied complex phases. Native character columns on the
common product residue algebra retain all nonunit zeros. Their unweighted Gram
is invariant under the actual squarefree Mobius diagonal. Weighted profiles
must co-transform, and the actual physical Gauss row acquires its own phase.
CRT existence, alpha invariance, source continuation and savings are not asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.CommonUnitGauge
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.CanonicalRowCompletion
  OAI.SevenEighths.ProbePhysical OAI.ConcretePrimeRowBridge
local notation "O" => OAI.ActualEisensteinCubic.O

section Pool
variable {n : ℕ} (P : Fin n → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

/-- Finite actual prime residue fields. -/
local instance residueFintype (i : Fin n) : Fintype (O ⧸ P i) := Fintype.ofFinite _

/-- The actual common CRT target ring, not a ring of invented phases. -/
abbrev Residues := (i : Fin n) → O ⧸ P i

/-- Actual numerator character column attached to a squarefree prime subset. -/
def column (S : Finset (Fin n)) (x : Residues P) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hg i) (x i)

/-- Literal native ideal represented by the subset. -/
def subsetIdeal (S : Finset (Fin n)) : Ideal O := ∏ i ∈ S, P i

/-- Its actual rational Mobius sign. -/
def subsetMu (S : Finset (Fin n)) : ℂ :=
  (UniqueFactorizationMonoid.moebius (subsetIdeal P S) : ℂ)

/-- Pullback of the CRT column is the imported actual idealRowHom. -/
theorem column_pullback (S : Finset (Fin n)) (m : O) :
    column P hg S (fun i => Ideal.Quotient.mk (P i) m) = idealRowHom m (subsetIdeal P S) := by
  unfold column subsetIdeal
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact (idealRowHom_prime m (P i) (hg i)).symm

/-- Actual residue-unit multiplication is one common permutation of all columns. -/
def dilate (a : (i : Fin n) → (O ⧸ P i)ˣ) : Equiv.Perm (Residues P) :=
  Equiv.piCongrRight (fun i => (a i).mulLeft)

/-- An actual common residue unit with sextic value minus one supplies the subset parity. -/
theorem column_dilate (a : (i : Fin n) → (O ⧸ P i)ˣ)
    (ha : ∀ i, canonicalSextic (P i) (hg i) (a i) = -1)
    (S : Finset (Fin n)) (x : Residues P) :
    column P hg S (dilate P a x) = (-1 : ℂ)^S.card * column P hg S x := by
  change (∏ i ∈ S, canonicalSextic (P i) (hg i) ((a i : O ⧸ P i) * x i)) =
    (-1 : ℂ)^S.card * ∏ i ∈ S, canonicalSextic (P i) (hg i) (x i)
  simp_rw [map_mul, ha]
  rw [Finset.prod_mul_distrib]
  simp

include P in
/-- Distinct actual prime ideals identify subset parity with their native Mobius. -/
theorem subsetMu_eq (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (S : Finset (Fin n)) : subsetMu P S = (-1 : ℂ)^S.card := by
  exact prime_product_moebius P hprime hinj S

/-- The sign is not an arbitrary supplied diagonal: it is the actual supported ideal's Mobius. -/
theorem column_dilate_native (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (a : (i : Fin n) → (O ⧸ P i)ˣ)
    (ha : ∀ i, canonicalSextic (P i) (hg i) (a i) = -1)
    (S : Finset (Fin n)) (x : Residues P) :
    column P hg S (dilate P a x) = subsetMu P S * column P hg S x := by
  rw [subsetMu_eq P hprime hinj]
  exact column_dilate P hg a ha S x

/-- Literal finite numerator-column Gram, with all zero entries retained. -/
def weightedGram (w : Residues P → ℂ) (S T : Finset (Fin n)) : ℂ :=
  ∑ x, w x * column P hg S x * star (column P hg T x)

/-- The actual common permutation also transports the finite profile. -/
theorem weightedGram_covariance (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (a : (i : Fin n) → (O ⧸ P i)ˣ)
    (ha : ∀ i, canonicalSextic (P i) (hg i) (a i) = -1)
    (w : Residues P → ℂ) (S T : Finset (Fin n)) :
    weightedGram P hg w S T = subsetMu P S * star (subsetMu P T) *
      weightedGram P hg (fun x => w (dilate P a x)) S T := by
  have he := Equiv.sum_comp (dilate P a)
    (fun x => w x * column P hg S x * star (column P hg T x))
  unfold weightedGram
  rw [← he]
  simp_rw [column_dilate_native P hg hprime hinj a ha, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Complete-period Gram is invariant under this ACTUAL Mobius gauge. -/
theorem uniformGram_mu_invariant (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (a : (i : Fin n) → (O ⧸ P i)ˣ)
    (ha : ∀ i, canonicalSextic (P i) (hg i) (a i) = -1)
    (S T : Finset (Fin n)) :
    weightedGram P hg (fun _ => 1) S T = subsetMu P S * star (subsetMu P T) *
      weightedGram P hg (fun _ => 1) S T := by
  exact weightedGram_covariance P hg hprime hinj a ha (fun _ => 1) S T

end Pool

/-- The whole physical/numerator join has its own physical Gauss co-transform.
The multiplier is literal, including calibration, not a deleted physical sign. -/
theorem actual_join_unit_scale (C : CalibrationData) (A s : O)
    (hs : OAI.CanonicalQuadraticSieve.Supported (Ideal.span {s}))
    (b m : O) (hcop : IsCoprime b s) :
    calibratedNumerator C A (b*m) *
      sexticGauss s (supportedElement_ne_zero s hs) (-(b*m)) =
      C.residueMonoid b * idealRowHom b (Ideal.span {A}) *
        (idealRowHom b (Ideal.span {s}))⁻¹ *
        (calibratedNumerator C A m * sexticGauss s (supportedElement_ne_zero s hs) (-m)) := by
  unfold calibratedNumerator
  rw [map_mul, idealRowHom_argument_mul, show -(b*m)=b*(-m) by ring,
    sexticGauss_unit_scale s hs b (-m) hcop]
  ring

end OpenAIReview.CommonUnitGauge

#lint+ in OpenAIReview.CommonUnitGauge

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
  unless declarations > 0 do throwError "Empty common-unit gauge audit."
  logInfo m!"Common-unit gauge audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-whole-gauss-orthogonality-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-whole-gauss-orthogonality-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual canonical-sextic common residue-unit conditional Gram gauge and actual physical calibrated co-transform; no CRT existence/source/saving"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
