/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native four-field moments with an independent positive auxiliary gap

The final imported contradiction wrapper ties `Delta` to `beta - 7/8`.
The actual terminal moment producer only needs its capacity inequality.
This leaf retains the actual fine slots, source data, calibration, all four
moment fields and moving height, and removes that unnecessary wrapper tie.
It is not a bound on the physical probe/theta term or a zero-free theorem.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace OpenAIReview.MomentBelowBoundary
open OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification Parameters
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

/-- The literal terminal certificate only requires the true capacity condition. -/
theorem certified_bands_of_capacity {Delta : ℝ} (D : HighData Delta)
    (F : SourceData D) (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hcapacity : 2 * HeckeZeroSupremum.beta - 1 ≤ kappaPlain D)
    (radial : ℝ) (hradial : 0 < radial) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) radial 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D)) := by
  have hp := fixed_parameters D
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) radial 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hradial
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · exact hbeta
  · exact hcapacity

/-- Below the imported boundary, every native positive-gap datum has enough capacity. -/
theorem native_capacity_below_boundary {Delta : ℝ} (D : HighData Delta)
    (hbeta : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    2 * HeckeZeroSupremum.beta - 1 ≤ kappaPlain D := by
  have hp := (fixed_parameters D).2.2.2.2.1
  linarith

/-- All four actual source moment fields survive with the same fine-slot requirement. -/
theorem source_moments_below_boundary {Delta : ℝ} (hDelta : 0 < Delta)
    (D : HighData Delta) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh Delta D.t / 200)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hupper : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ eta : Character, ∃ C : ℝ, 0 < C ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts eta Z tau (C * (1 + Z^(2*tau))^J) (Z^(2*tau)) := by
  obtain ⟨hpositive, hzero⟩ := plain_inputs F
    (certified_bands_of_capacity D F hbeta (native_capacity_below_boundary D hupper))
  exact source_moments F counts (detectorMesh Delta D.t)
    (detectorMesh_pos hDelta D.t_pos) hfine hpositive hzero

/-- A fixed small height exponent absorbs the polynomial height cost in the native data. -/
theorem chosen_height_below_boundary {Delta : ℝ} (hDelta : 0 < Delta)
    (D : HighData Delta) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t)
    (hfine : ∀ j, D.ell j ≤ detectorMesh Delta D.t / 200)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hupper : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ tau : ℝ, 0 < tau ∧ tau < (1/200 : ℝ)/2 ∧
      4*tau < (1/200)*D.cost ∧ tau < D.t ∧ 2*tau ≤ D.t ∧
      tau*(2+4*D.eps) < D.t ∧
      ∀ eta : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts eta Z tau (C*Z^D.t) (Z^(2*tau)) := by
  obtain ⟨J, hJ, hsource⟩ :=
    source_moments_below_boundary hDelta D F counts hfine hbeta hupper
  exact chosen_data_height D F counts J hJ hsource

/-- Fine source data and their full moment input exist for every independent positive gap. -/
theorem exists_native_moments_below_boundary (Delta : ℝ) (hDelta : 0 < Delta)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hupper : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ D : HighData Delta, ∃ F : SourceData D,
      ∃ counts : CountParameters F.modulus ⊤ D.t,
        (∀ j, D.ell j ≤ detectorMesh Delta D.t / 200) ∧
        ∃ tau : ℝ, 0 < tau ∧ tau < (1/200 : ℝ)/2 ∧
          4*tau < (1/200)*D.cost ∧ tau < D.t ∧ 2*tau ≤ D.t ∧
          tau*(2+4*D.eps) < D.t ∧
          ∀ eta : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
            SourceMomentBound F counts eta Z tau (C*Z^D.t) (Z^(2*tau)) := by
  obtain ⟨D, hfine⟩ := exists_high_data_fine Delta hDelta (detectorMesh Delta)
    (fun t ht => detectorMesh_pos hDelta ht)
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  exact ⟨D, F, counts, hfine,
    chosen_height_below_boundary hDelta D F counts hfine hbeta hupper⟩

end OpenAIReview.MomentBelowBoundary
#lint+ in OpenAIReview.MomentBelowBoundary

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
  unless declarations > 0 do throwError "Empty native moment audit."
  logInfo m!"Native moment audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-moment-below-boundary-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-moment-below-boundary-gate/axioms.json"
    (Json.mkObj [("scope", toJson "actual four-field source moments and moving height with independent positive gap; not physical theta payment or zero exclusion"),
      ("declarations", toJson declarations), ("theoremsIncludingHelpers", toJson theorems),
      ("namespaceLinters", toJson (15 : Nat)), ("allLocalModuleProvenance", toJson true),
      ("onlyStandardAxioms", toJson true), ("details", Json.arr reports)]).pretty
