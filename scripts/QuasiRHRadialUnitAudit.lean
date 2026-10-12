/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHCalibratedMatchingAudit
import OAI.NumberTheory.DirichletL.Hecke.UnitRows
import Lean.Util.CollectAxioms

/-!
# Exact unit selection on the actual calibrated radial row

All ordinary cofactor elements, their prime powers, the calibration, the
sextic cofactor row and the complete complex radial window are retained.
Unit-forbidden annuli vanish exactly.  The finite six-unit projector is an
identity on the original matching row, not a source or signed growth bound
for the surviving neutral class.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.RadialUnit
open OAI OAI.CanonicalRowCompletion OAI.ConcretePrimeRowBridge
open OAI.CompletedGauss OAI.ConcreteTraceCRT
open OAI.CubicEisenstein hiding O
open OAI.SevenEighths.ProbePhysical OAI.CanonicalQuadraticSieve
open OpenAIReview.CalibratedMatching
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The native Eisenstein unit type contains exactly six elements. -/
local instance radialUnits : Fintype Oˣ :=
  @Fintype.ofFinite _ OAI.PrimaryIdealUnitReindex.finite_units

theorem elementNorm_unit (u : Oˣ) : elementNorm (u : O) = 1 := by
  unfold elementNorm
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
  simp

theorem elementNorm_unit_mul (u : Oˣ) (m : O) :
    elementNorm ((u : O)*m) = elementNorm m := by
  rw [elementNorm_mul, elementNorm_unit, one_mul]

/-- Unit neutrality concerns the actual calibration and the actual cofactor ideal. -/
def UnitNeutral (C : CalibrationData) (B : Ideal O) : Prop :=
  ∀ u : Oˣ, cofactorCharacter C B (u : O) = 1

/-- The exact native annulus is an eigenvector for each of the six unit actions. -/
theorem cofactorAnnulus_unit_eq (C : CalibrationData) (B : Ideal O)
    (W : ℝ → ℂ) (Q : ℝ) (u : Oˣ) :
    cofactorAnnulus C B W Q =
      cofactorCharacter C B (u : O)*cofactorAnnulus C B W Q := by
  change (∑' m : O, cofactorCharacter C B m*W (elementNorm m/Q)) = _
  calc
    _ = ∑' m : O, cofactorCharacter C B ((u : O)*m)*
        W (elementNorm ((u : O)*m)/Q) :=
      (u.mulLeft.tsum_eq (fun m : O => cofactorCharacter C B m*W (elementNorm m/Q))).symm
    _ = _ := by
      simp only [cofactorCharacter_mul, elementNorm_unit_mul, mul_assoc, tsum_mul_left]
      rfl

theorem cofactorAnnulus_eq_zero_of_unit (C : CalibrationData) (B : Ideal O)
    (W : ℝ → ℂ) (Q : ℝ) (u : Oˣ)
    (hu : cofactorCharacter C B (u : O) ≠ 1) :
    cofactorAnnulus C B W Q = 0 := by
  have he := cofactorAnnulus_unit_eq C B W Q u
  have hz : (1-cofactorCharacter C B (u : O))*cofactorAnnulus C B W Q = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hu.symm)

theorem cofactorAnnulus_ne_zero_implies_neutral (C : CalibrationData)
    (B : Ideal O) (W : ℝ → ℂ) (Q : ℝ)
    (hne : cofactorAnnulus C B W Q ≠ 0) : UnitNeutral C B := by
  intro u
  by_contra hu
  exact hne (cofactorAnnulus_eq_zero_of_unit C B W Q u hu)

/-- The puncture ideal is invariant under multiplication by every unit. -/
theorem puncturedAnnulus_unit_eq (C : CalibrationData) (B : Ideal O) (p : O)
    (W : ℝ → ℂ) (Q : ℝ) (u : Oˣ) :
    puncturedAnnulus C B p W Q =
      cofactorCharacter C B (u : O)*puncturedAnnulus C B p W Q := by
  let f : O → ℂ := fun m => if m∈(Ideal.span {p} : Ideal O) then 0 else
    cofactorCharacter C B m*W (elementNorm m/Q)
  change (∑' m : O, f m) = cofactorCharacter C B (u : O)*(∑' m : O, f m)
  calc
    _ = ∑' m : O, f ((u : O)*m) := (u.mulLeft.tsum_eq f).symm
    _ = ∑' m : O, cofactorCharacter C B (u : O)*f m := by
      apply tsum_congr
      intro m
      simp only [f, Ideal.unit_mul_mem_iff_mem _ u.isUnit,
        cofactorCharacter_mul, elementNorm_unit_mul]
      split_ifs <;> simp [mul_assoc]
    _ = _ := tsum_mul_left

theorem puncturedAnnulus_eq_zero_of_unit (C : CalibrationData) (B : Ideal O)
    (p : O) (W : ℝ → ℂ) (Q : ℝ) (u : Oˣ)
    (hu : cofactorCharacter C B (u : O) ≠ 1) :
    puncturedAnnulus C B p W Q = 0 := by
  have he := puncturedAnnulus_unit_eq C B p W Q u
  have hz : (1-cofactorCharacter C B (u : O))*puncturedAnnulus C B p W Q = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hu.symm)

/-- Six-unit projector; its scalar depends on the literal calibration and cofactor. -/
def unitProjector (C : CalibrationData) (B : Ideal O) : ℂ :=
  (1/6 : ℂ)*∑ u : Oˣ, cofactorCharacter C B (u : O)

theorem unit_card : Fintype.card Oˣ = 6 := by
  simpa only [Nat.card_eq_fintype_card] using OAI.PrimaryIdealUnitReindex.card_units_eq_six

theorem unitProjector_mul_annulus (C : CalibrationData) (B : Ideal O)
    (W : ℝ → ℂ) (Q : ℝ) :
    unitProjector C B*cofactorAnnulus C B W Q = cofactorAnnulus C B W Q := by
  unfold unitProjector
  rw [mul_assoc, Finset.sum_mul]
  simp only [←cofactorAnnulus_unit_eq C B W Q, Finset.sum_const,
    Finset.card_univ, unit_card, nsmul_eq_mul]
  ring

theorem unitProjector_mul_puncture (C : CalibrationData) (B : Ideal O) (p : O)
    (W : ℝ → ℂ) (Q : ℝ) :
    unitProjector C B*puncturedAnnulus C B p W Q = puncturedAnnulus C B p W Q := by
  unfold unitProjector
  rw [mul_assoc, Finset.sum_mul]
  simp only [←puncturedAnnulus_unit_eq C B p W Q, Finset.sum_const,
    Finset.card_univ, unit_card, nsmul_eq_mul]
  ring

theorem unitProjector_eq_one_of_neutral (C : CalibrationData) (B : Ideal O)
    (hn : UnitNeutral C B) : unitProjector C B = 1 := by
  unfold unitProjector
  simp only [show ∀ u : Oˣ, cofactorCharacter C B (u : O)=1 from hn,
    Finset.sum_const, Finset.card_univ, unit_card, nsmul_eq_mul]
  norm_num

theorem unitProjector_eq_zero_of_unit (C : CalibrationData) (B : Ideal O) (u : Oˣ)
    (hu : cofactorCharacter C B (u : O) ≠ 1) : unitProjector C B = 0 := by
  let f : Oˣ → ℂ := fun v => cofactorCharacter C B (v : O)
  have he : (∑ v : Oˣ, f v) = cofactorCharacter C B (u : O)*(∑ v : Oˣ, f v) := by
    calc
      _ = ∑ v : Oˣ, f (u*v) := (Equiv.sum_comp (Equiv.mulLeft u) f).symm
      _ = _ := by simp only [f, Units.val_mul, cofactorCharacter_mul, Finset.mul_sum]
  have hz : (1-cofactorCharacter C B (u : O))*(∑ v : Oˣ, f v) = 0 := by
    linear_combination he
  have hf := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hu.symm)
  unfold unitProjector
  change (1/6 : ℂ)*(∑ v : Oˣ, f v) = 0
  rw [hf, mul_zero]

theorem unitProjector_eq_indicator (C : CalibrationData) (B : Ideal O) :
    unitProjector C B = if UnitNeutral C B then 1 else 0 := by
  by_cases hn : UnitNeutral C B
  · rw [ite_eq_left hn, unitProjector_eq_one_of_neutral C B hn]
  · rw [ite_eq_right hn]
    have hx : ∃ u : Oˣ, cofactorCharacter C B (u : O) ≠ 1 := by
      simpa only [UnitNeutral, not_forall] using hn
    obtain ⟨u,hu⟩ := hx
    exact unitProjector_eq_zero_of_unit C B u hu

/-- Native good-ideal normalization exposes the exact surviving unit constraint. -/
theorem cofactorCharacter_unit_supported (C : CalibrationData) (B : Ideal O)
    (hB : Supported B) (u : Oˣ) :
    cofactorCharacter C B (u : O) = C.residueMonoid (u : O)*
      eisEmbedding ((u : O)^((Ideal.absNorm B-1)/6)) := by
  unfold cofactorCharacter
  rw [OAI.CanonicalUnitEuler.idealRowHom_unit_norm u B hB.1
    (supported_factors_good B hB)]

theorem unitNeutral_supported_iff (C : CalibrationData) (B : Ideal O)
    (hB : Supported B) :
    UnitNeutral C B ↔ ∀ u : Oˣ, C.residueMonoid (u : O)*
      eisEmbedding ((u : O)^((Ideal.absNorm B-1)/6)) = 1 := by
  simp only [UnitNeutral, cofactorCharacter_unit_supported C B hB]

/-- The permitted native unit sector depends on the cofactor norm only modulo 36. -/
theorem cofactorCharacter_unit_eq_of_norm_mod_thirty_six (C : CalibrationData)
    (B D : Ideal O) (hB : Supported B) (hD : Supported D)
    (hmod : Ideal.absNorm B%36=Ideal.absNorm D%36) (u : Oˣ) :
    cofactorCharacter C B (u : O) = cofactorCharacter C D (u : O) := by
  unfold cofactorCharacter
  rw [OAI.CanonicalUnitEuler.idealRowHom_unit_eq_of_norm_mod_thirty_six u B D
    hB.1 hD.1 (supported_factors_good B hB) (supported_factors_good D hD) hmod]

theorem unitNeutral_iff_of_norm_mod_thirty_six (C : CalibrationData)
    (B D : Ideal O) (hB : Supported B) (hD : Supported D)
    (hmod : Ideal.absNorm B%36=Ideal.absNorm D%36) :
    UnitNeutral C B ↔ UnitNeutral C D := by
  simp only [UnitNeutral, cofactorCharacter_unit_eq_of_norm_mod_thirty_six C B D hB hD hmod]

/-- On the surviving class the six-unit projection is exactly the original annulus. -/
theorem neutral_projection_preserves_annulus (C : CalibrationData) (B : Ideal O)
    (hn : UnitNeutral C B) (W : ℝ → ℂ) (Q : ℝ) :
    unitProjector C B*cofactorAnnulus C B W Q = cofactorAnnulus C B W Q := by
  rw [unitProjector_eq_one_of_neutral C B hn, one_mul]

/-- The actual matching Gauss coefficient is preserved under the finite unit projector. -/
theorem calibrated_matching_unit_projector (C : CalibrationData) (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda∉Ideal.span {p}) (t : ℕ) (B : Ideal O) (A : O)
    (hA : (Ideal.span {A} : Ideal O)=(Ideal.span {p})^(6*t+1)*B)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (Q : ℝ) (hQ : 0<Q) :
    (∑' m : O, calibratedNumerator C A m*sexticGauss p hp (-m)*
      W (elementNorm m/Q)) =
      (actualSextic (Ideal.span {p}) hg (-1)*
        gaussSum (actualSextic (Ideal.span {p}) hg) (quotientTrace p hp))*
        (unitProjector C B*puncturedAnnulus C B p W Q) := by
  rw [unitProjector_mul_puncture, calibrated_matching_annulus_eq C p hp hg t B A hA
    W hW Q hQ, puncturedAnnulus_eq C B p hp W hW Q hQ]

/-- Nonneutral native radial matching rows vanish, with their Gauss constant retained. -/
theorem calibrated_matching_eq_zero_of_unit (C : CalibrationData) (p : O) (hp : p≠0)
    [(Ideal.span {p} : Ideal O).IsMaximal] [Fintype (O ⧸ Ideal.span {p})]
    (hg : goodLambda∉Ideal.span {p}) (t : ℕ) (B : Ideal O) (A : O)
    (hA : (Ideal.span {A} : Ideal O)=(Ideal.span {p})^(6*t+1)*B)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (Q : ℝ) (hQ : 0<Q)
    (u : Oˣ) (hu : cofactorCharacter C B (u : O)≠1) :
    (∑' m : O, calibratedNumerator C A m*sexticGauss p hp (-m)*
      W (elementNorm m/Q)) = 0 := by
  rw [calibrated_matching_unit_projector C p hp hg t B A hA W hW Q hQ,
    unitProjector_eq_zero_of_unit C B u hu, zero_mul, mul_zero]

end OpenAIReview.RadialUnit

#lint+ in OpenAIReview.RadialUnit

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
  unless declarations>0 do throwError "Empty radial-unit audit."
  logInfo m!"Radial-unit audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-radial-unit"
  IO.FS.writeFile ".lake/arithmetic-operator-radial-unit/axioms.json"
    (Json.mkObj [("scope",toJson "exact actual calibrated annulus/puncture unit selection; surviving neutral class unchanged; no source or signed growth estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
