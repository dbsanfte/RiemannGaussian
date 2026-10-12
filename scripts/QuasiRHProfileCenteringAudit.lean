/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Source gate for finite smooth-profile comparisons

At fixed geometry, character, correction and prime-slot multiplier, centering
the double-principal Mellin mass kills the actual detector source identically.
This is a scoped no-go, not an estimate of the complete low physical probe.
Allowing different arithmetic slot multipliers leaves their signed difference
unpaid; the last identity records exactly where a useful comparison must act.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.ProfileCentering
open OAI OAI.SevenEighths OAI.SevenEighths.PrincipalMellinResidues
open HeckeFamily ProbePhysical ProbeEuler ProbeFiniteProductBounds

variable {ι : Type*}

/-- The entire dependence of the double-principal source on the smooth profiles. -/
def profileMass (W0 W1 : SchwartzMap ℝ ℂ) : ℂ :=
  mellin W1 1 * mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)

/-- The actual common reciprocal-L kernel, with every Gaussian and scale factor retained. -/
def commonSource (X Z : ℝ) (eta : HeckeFamily.Character) (s : ℂ)
    (H B : ℂ → ℂ → ℂ) : ℂ :=
  (X:ℂ)^(1/3:ℂ) * (Z:ℂ)^(s-5/6) * Complex.exp ((s-5/6)^2) /
    LFunction eta s * H 1 (1/6) * B 1 (1/6)

theorem source_eq_mass (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : HeckeFamily.Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    sourceMultiplier W0 W1 X Y Z eta s H B 1 (1/6) =
      profileMass W0 W1 * commonSource X Z eta s H B := by
  unfold sourceMultiplier profileMass commonSource
  rw [show (1/2:ℂ)-1/6=1/3 by norm_num,
    show s+(1/6:ℂ)-1=s-5/6 by ring]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  ring

/-- Any number of profiles still shares just one arithmetic source kernel. -/
theorem finite_source_factorization (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : HeckeFamily.Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    (∑ i ∈ I, c i * sourceMultiplier (W0 i) (W1 i) X Y Z eta s H B 1 (1/6)) =
      (∑ i ∈ I, c i * profileMass (W0 i) (W1 i)) * commonSource X Z eta s H B := by
  simp_rw [source_eq_mass, ← mul_assoc]
  rw [Finset.sum_mul]

/-- Centering this scalar cancels ALL reciprocal-L sources, not just a density mode. -/
theorem centered_source_zero (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (hc : ∑ i ∈ I, c i * profileMass (W0 i) (W1 i) = 0)
    (X Y Z : ℝ) (eta : HeckeFamily.Character) (s : ℂ)
    (H B : ℂ → ℂ → ℂ) :
    (∑ i ∈ I, c i * sourceMultiplier (W0 i) (W1 i) X Y Z eta s H B 1 (1/6)) = 0 := by
  rw [finite_source_factorization, hc, zero_mul]

/-- The exact double residue, with the actual fixed Hecke residue and multiplicity two. -/
theorem finite_double_residue_factorization (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M]
    (X Y Z : ℝ) (eta : HeckeFamily.Character) (s : ℂ)
    (H B : ℂ → ℂ → ℂ) :
    (∑ i ∈ I, c i * (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier (W0 i) (W1 i) X Y Z eta s H B 1 (1/6))) =
      (∑ i ∈ I, c i * profileMass (W0 i) (W1 i)) *
        (fixedPrincipalResidue M ^ 2 / 6 * commonSource X Z eta s H B) := by
  simp_rw [source_eq_mass]
  calc
    _ = ∑ i ∈ I, (c i * profileMass (W0 i) (W1 i)) *
      (fixedPrincipalResidue M ^ 2 / 6 * commonSource X Z eta s H B) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem centered_double_residue_zero (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (hc : ∑ i ∈ I, c i * profileMass (W0 i) (W1 i) = 0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ)
    (eta : HeckeFamily.Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) :
    (∑ i ∈ I, c i * (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier (W0 i) (W1 i) X Y Z eta s H B 1 (1/6))) = 0 := by
  rw [finite_double_residue_factorization, hc, zero_mul]

theorem finite_normalizer_factorization (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M] :
    (∑ i ∈ I, c i * sourceResidueConstant (W0 i) (W1 i) M) =
      (∑ i ∈ I, c i * profileMass (W0 i) (W1 i)) * fixedPrincipalResidue M ^ 2 / 6 := by
  simp only [sourceResidueConstant, profileMass]
  simp_rw [mul_div_assoc, ← mul_assoc]
  rw [← Finset.sum_mul]

/-- No interchange of integrals is needed: the joined integrand is already identically zero. -/
theorem centered_source_integral_zero (I : Finset ι) (c : ι → ℂ)
    (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (hc : ∑ i ∈ I, c i * profileMass (W0 i) (W1 i) = 0)
    (X Y Z a : ℝ) (eta : HeckeFamily.Character)
    (H B : ℂ → ℂ → ℂ → ℂ) :
    ProbePhysical.verticalIntegral a (fun s =>
      ∑ i ∈ I, c i * sourceMultiplier (W0 i) (W1 i) X Y Z eta s
        (H s) (B s) 1 (1/6)) = 0 := by
  have hz : (fun s => ∑ i ∈ I, c i * sourceMultiplier (W0 i) (W1 i) X Y Z eta s
      (H s) (B s) 1 (1/6)) = fun _ => 0 := by
    funext s
    exact centered_source_zero I c W0 W1 hc X Y Z eta s (H s) (B s)
  rw [hz]
  simp [ProbePhysical.verticalIntegral]

/-- The conclusion applies to the literal prime-slot pools used by the imported detector. -/
theorem actual_pool_centered_source_zero {K : ℕ}
    (I : Finset ι) (c : ι → ℂ) (W0 W1 : ι → SchwartzMap ℝ ℂ)
    (hc : ∑ i ∈ I, c i * profileMass (W0 i) (W1 i) = 0)
    (eta : HeckeFamily.Character) (S : Finset (Ideal HeckeFamily.O))
    (hS : ProbePhysical.SourceExclusions S)
    (T : Fin K → Finset PrimeIdeal) (b : Fin K → PrimeIdeal → ℂ)
    (X Y Z : ℝ) (s : ℂ) :
    (∑ i ∈ I, c i * sourceMultiplier (W0 i) (W1 i) X Y Z
      (eta.excludePrimes S hS.prime) s
      (ProbePhysical.globalClosedCorrection eta S s)
      (ProbeFiniteProductBounds.slotMultiplier eta Finset.univ T b s) 1 (1/6)) = 0 := by
  exact centered_source_zero I c W0 W1 hc X Y Z _ s _ _

/-- Two-profile scalar centering is exact for every source location. -/
theorem two_profile_source_zero (V0 V1 W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (eta : HeckeFamily.Character) (s : ℂ)
    (H B : ℂ → ℂ → ℂ) :
    profileMass W0 W1 * sourceMultiplier V0 V1 X Y Z eta s H B 1 (1/6) -
      profileMass V0 V1 * sourceMultiplier W0 W1 X Y Z eta s H B 1 (1/6) = 0 := by
  rw [source_eq_mass, source_eq_mass]
  ring

/-- Nonidentical arithmetic multipliers are deliberately NOT covered by the no-go. -/
theorem two_profile_arithmetic_difference (V0 V1 W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (eta : HeckeFamily.Character) (s : ℂ)
    (H B0 B1 : ℂ → ℂ → ℂ) :
    profileMass W0 W1 * sourceMultiplier V0 V1 X Y Z eta s H B0 1 (1/6) -
      profileMass V0 V1 * sourceMultiplier W0 W1 X Y Z eta s H B1 1 (1/6) =
        profileMass V0 V1 * profileMass W0 W1 *
          commonSource X Z eta s H (fun w z => B0 w z - B1 w z) := by
  rw [source_eq_mass, source_eq_mass]
  unfold commonSource
  ring

end OpenAIReview.ProfileCentering

#lint+ in OpenAIReview.ProfileCentering

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    unless (n.toString.splitOn "OpenAIReview.ProfileCentering").length > 1 do continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty profile-centering audit."
  logInfo m!"Profile-centering audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/quasi-rh-profile-centering"
  IO.FS.writeFile ".lake/quasi-rh-profile-centering/axioms.json"
    (Json.mkObj [("scope",toJson "finite profile centering at fixed arithmetic source kernel"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
