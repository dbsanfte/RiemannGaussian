/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.CubicSieve.Gauss
import OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles
import OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native cubic orientation and the surviving sextic twist

The native trace character has the additional denominator `sqrt(-3)`.
Changing it to the ordinary trace character produces a fixed ramified
cubic ray factor, not complex conjugation. The native numerator character
also has a genuine quadratic component. No estimate from the cubic
first-moment paper is imported by these exact finite identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.CubicOrientation
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss
  OAI.ConcreteTraceCRT OAI.CubicJacobiGlobal
  OAI.SevenEighths.CubicSieve OAI.CanonicalRowCompletion
open OAI.CanonicalQuadraticSieve (Supported)
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The paper's ordinary trace character, defined on the actual quotient. -/
def paperTrace (n : O) (hn : n ≠ 0) : AddChar (O ⧸ Ideal.span {n}) ℂ :=
  (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn).mulShift
    (Ideal.Quotient.mk _ traceLambda)

/-- This is exactly `e(Tr(x/n))`, with no conjugation or omitted unit. -/
theorem paperTrace_mk (n : O) (hn : n ≠ 0) (x : O) :
    paperTrace n hn (Ideal.Quotient.mk _ x) =
      ShortDraftTrace.breveE (eisEmbedding x / eisEmbedding n) := by
  rw [paperTrace, AddChar.mulShift_apply, ← map_mul]
  rw [eisTraceModChar, IdealGaussCRT.traceModChar_mk, map_mul, eisEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero]

/-- The trace-changing element is invertible on every native primary quotient. -/
theorem traceLambda_quotient_isUnit (I : Ideal O)
    (hI : primaryGenerator I ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {primaryGenerator I}) traceLambda) := by
  apply (CubicEisenstein.isUnit_quotient_span_iff _ _).mpr
  have hcop : IsCoprime lambda (primaryGenerator I) :=
    CubicEisenstein.coprime_of_dvd_sub_one _ _ ((dvd_pow_self lambda (by decide : 2 ≠ 0)).trans
      (primaryGenerator_spec I hI).2)
  rw [traceLambda_eq_unit_mul_lambda]
  exact (isCoprime_mul_unit_left_right neg_omega_isUnit _ _).mpr hcop.symm

/-- The paper's normalized cubic Gauss sum on the same primary generator. -/
def paperGauss (I : Ideal O) (hI : Admissible I) : ℂ := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  exact gaussSum (principalCubicCharacter I hI)
    (paperTrace (primaryGenerator I) hI.2) /
      (‖eisEmbedding (primaryGenerator I)‖ : ℂ)

/-- Exact orientation bridge: native `gaussTwo` is a ray times paper `G`. -/
theorem gaussTwo_eq_ray_mul_paper (I : Ideal O) (hI : Admissible I) :
    gaussTwo I hI.2 =
      eisEmbedding (symbol traceLambda (primaryGenerator I)) * paperGauss I hI := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let u := (traceLambda_quotient_isUnit I hI.2).unit
  have h := gaussSum_mulShift (principalCubicCharacter I hI)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      (primaryGenerator I) hI.2) u
  rw [IsUnit.unit_spec, principalCubicCharacter_mk] at h
  rw [gaussTwo_eq_gaussSum I hI]
  change _ = _ * (_ / _)
  rw [← h]
  change (eisEmbedding (idealSymbol I traceLambda) * _) / _ = _
  have hs : idealSymbol I traceLambda = symbol traceLambda (primaryGenerator I) := by
    unfold symbol
    rw [(primaryGenerator_spec I hI.2).1]
  rw [hs]
  unfold paperTrace
  ring

/-- The fixed ray is explicitly the native modulus-nine supplementary character. -/
theorem gaussTwo_eq_linearRay_mul_paper (I : Ideal O) (hI : Admissible I) :
    gaussTwo I hI.2 =
      eisEmbedding (CubicRamified.linearRay 0 (-1) (primaryGenerator I)) *
        paperGauss I hI := by
  rw [gaussTwo_eq_ray_mul_paper,
    CubicRamified.symbol_traceLambda_eq_linearRay _ (primaryGenerator_spec I hI.2).2]

/-- Bare native coefficient: fixed angular minus one, fixed ray, and positive cubic G. -/
theorem squarefreeGaussCoefficient_eq_paper (I : Ideal O) (hI : Admissible I) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
        eisEmbedding (CubicRamified.linearRay 0 (-1) (primaryGenerator I)) *
          paperGauss I hI := by
  rw [squarefreeGaussCoefficient_eq I hI.1 hI.2,
    gaussTwo_eq_linearRay_mul_paper I hI]
  ring

/-- The sextic numerator factor has an exact quadratic-times-cubic split.
Nonunit values are retained on both sides. -/
theorem idealRowHom_quadratic_cubic (m : O) (I : Ideal O)
    (hI : Supported I) :
    idealRowHom m I = idealRowHom m I ^ 3 *
      (eisEmbedding (idealSymbol I m)) ^ 2 := by
  rw [← idealRowHom_square]
  have h6 := idealRowHom_sixth_mask m I hI
  rw [idealRowHom_argument_pow m 6 I hI] at h6
  by_cases hc : IsCoprime I (Ideal.span {m})
  · rw [ite_eq_left hc] at h6
    calc
      _ = idealRowHom m I ^ 6 * idealRowHom m I := by rw [h6, one_mul]
      _ = _ := by ring
  · rw [ite_eq_right hc] at h6
    have hz : idealRowHom m I = 0 := eq_zero_of_pow_eq_zero h6
    simp only [hz, zero_pow (by decide : (3:ℕ) ≠ 0), zero_pow (by decide : (2:ℕ) ≠ 0),
      mul_zero]

/-- The native complete cofactor column expressed in the paper's orientation.
The uncancelled quadratic factor depends on both the numerator and the ideal. -/
theorem twisted_squarefreeGaussCoefficient_eq_paper (m : O) (I : Ideal O)
    (hI : Admissible I) (hs : Supported I) :
    squarefreeGaussCoefficient I * idealRowHom m I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
        eisEmbedding (CubicRamified.linearRay 0 (-1) (primaryGenerator I)) *
          paperGauss I hI * idealRowHom m I ^ 3 *
            (eisEmbedding (idealSymbol I m)) ^ 2 := by
  rw [squarefreeGaussCoefficient_eq_paper I hI]
  nth_rw 1 [idealRowHom_quadratic_cubic m I hs]
  ring

/-- At a genuine prime, the remaining cubic component is exactly the
opposite cubic character, suitable for an additive-numerator twist. -/
theorem prime_sextic_split (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (m : O) :
    idealRowHom m P =
      QuadraticAllOddCRT.character P (Ideal.Quotient.mk P m) *
        ((canonicalSextic P hg ^ 2) (Ideal.Quotient.mk P m)) ^ 2 := by
  rw [idealRowHom_prime _ _ hg]
  have h3 := congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ (Ideal.Quotient.mk P m))
    (actualSextic_cube_quadratic P hg)
  rw [MulChar.pow_apply' _ (by decide : (3:ℕ) ≠ 0)] at h3
  rw [← h3, MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
  have h6 := canonicalSextic_sixth_power_mask P hg m
  simp only [map_pow] at h6
  by_cases hm : m ∈ P
  · rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm]
    simp only [MulChar.map_zero, zero_pow (by decide : (3:ℕ) ≠ 0),
      zero_pow (by decide : (2:ℕ) ≠ 0), mul_zero]
  · rw [ite_eq_right hm] at h6
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P m)) ^ 6 *
          actualSextic P hg (Ideal.Quotient.mk P m) := by rw [h6, one_mul]
      _ = _ := by ring

/-- The additional sextic row cannot be any power of the cubic row at an
actual odd-characteristic good prime. Fixed angular/ray constants do not
change this statement after evaluation at numerator one. -/
theorem actualSextic_ne_cubic_power (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r : ℕ) :
    actualSextic P hg ≠ (canonicalSextic P hg ^ 2) ^ r := by
  intro h
  have h3 := congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ ^ 3) h
  have hr : ((canonicalSextic P hg ^ 2) ^ r) ^ 3 = 1 := by
    calc
      _ = (canonicalSextic P hg ^ 6) ^ r := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = 1 := by rw [canonicalSextic_pow_six, one_pow]
  rw [hr] at h3
  exact canonicalSextic_pow_ne_one P hg hc (by decide : (3:ℕ) ≠ 0)
    (by decide : (3:ℕ) < 6) h3

/-- Even an arbitrary constant on the cofactor column cannot absorb its
sextic numerator character into a cubic power on all integer numerators. -/
theorem no_scalar_cubic_representation (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r : ℕ) (c : ℂ) :
    ¬ ∀ m : O, idealRowHom m P =
      c * ((canonicalSextic P hg ^ 2) ^ r) (Ideal.Quotient.mk P m) := by
  intro h
  have h1 := h 1
  rw [idealRowHom_prime _ _ hg] at h1
  simp only [map_one, mul_one] at h1
  apply actualSextic_ne_cubic_power P hg hc r
  apply DFunLike.ext
  intro x
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← idealRowHom_prime _ _ hg, h m, ← h1, one_mul]

/-- Exact finite additive-numerator form of the twist. The quadratic
character remains outside the cubic Gauss sum, including at nonunits. -/
theorem prime_twisted_gauss_eq_quadratic (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2)
    [Fintype (O ⧸ P)] (ψ : AddChar (O ⧸ P) ℂ) (m : O) :
    idealRowHom m P * gaussSum (canonicalSextic P hg ^ 2) ψ =
      QuadraticAllOddCRT.character P (Ideal.Quotient.mk P m) *
        gaussSum (canonicalSextic P hg ^ 2)
          (ψ.mulShift (Ideal.Quotient.mk P m)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  have hn : canonicalSextic P hg ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hg hc (by decide : (2:ℕ) ≠ 0)
      (by decide : (2:ℕ) < 6)
  have hi : (canonicalSextic P hg ^ 2)⁻¹ = canonicalSextic P hg ^ 4 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 2 + 4 = 6 by decide, canonicalSextic_pow_six]
  rw [ShortDraftLocal.gaussSum_mulShift_any _ _ hn, hi,
    MulChar.pow_apply' _ (by decide : (4:ℕ) ≠ 0),
    prime_sextic_split P hg m, MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
  ring

end OpenAIReview.CubicOrientation

#lint+ in OpenAIReview.CubicOrientation

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
  unless declarations > 0 do throwError "Empty cubic-orientation audit."
  logInfo m!"Cubic orientation audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-cubic-native-bridge"
  IO.FS.writeFile ".lake/arithmetic-operator-cubic-native-bridge/axioms.json"
    (Json.mkObj [("scope",toJson "exact actual squarefree cubic orientation and surviving quadratic numerator twist; no source or arithmetic estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
