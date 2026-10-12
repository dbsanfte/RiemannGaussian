/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.EulerCoordinates
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import Lean.Util.CollectAxioms

/-!
# The actual angular-six channel is not a finite ray character

For any two finite ray characters, a primary Eisenstein element congruent
to one modulo both periods separates the actual angular coefficient from
the second character. This blocks direct substitution of the imported
finite-character theorem for the angular correction. It does not rule out
an independent analytic continuation or zero-order theorem for that channel.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.AngularPeriod
open OAI OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.ProbeEuler OAI.EisensteinEmbedding
local notation "O" => OAI.ActualEisensteinCubic.O

/-- An exact polynomial calculation in the actual Eisenstein embedding. -/
theorem sixth_power_polynomial (b : ℝ) :
    (1 + (b : ℂ) * omega3)^6 =
      ((1 - 15*b^2 + 20*b^3 - 6*b^5 + b^6 : ℝ) : ℂ) +
      ((3*b*(1-b)*(1+b)*(2-b)*(1-2*b) : ℝ) : ℂ)*omega3 := by
  push_cast
  linear_combination
    ((b:ℂ)^6*(omega3^4-omega3^3+omega3-1) +
      6*(b:ℂ)^5*(omega3^3-omega3^2+1) +
      15*(b:ℂ)^4*(omega3^2-omega3) +
      20*(b:ℂ)^3*(omega3-1) + 15*(b:ℂ)^2) * omega3_sq

/-- In this primary progression the sixth power is never real. -/
theorem sixth_power_im_ne_zero {b : ℝ} (hb : 3 ≤ b) :
    ((1 + (b : ℂ) * omega3)^6).im ≠ 0 := by
  rw [sixth_power_polynomial]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, add_zero, zero_add]
  apply mul_ne_zero _ omega3_im_ne_zero
  have h0 : b ≠ 0 := by linarith
  have h1 : 1-b ≠ 0 := by linarith
  have h2 : 1+b ≠ 0 := by linarith
  have h3 : 2-b ≠ 0 := by linarith
  have h4 : 1-2*b ≠ 0 := by linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) h0) h1) h2) h3) h4

/-- The separating element is one in both finite ray quotients. -/
def separatingElement (eta psi : HeckeFamily.Character) : O :=
  1 + (3*eta.period*psi.period : ℕ)*HeckeFamily.omega

theorem separatingElement_eta (eta psi : HeckeFamily.Character) :
    elementCoeff eta (separatingElement eta psi) = 1 := by
  have h : separatingElement eta psi =
      1 + (eta.period : O) * ((3*psi.period : ℕ)*HeckeFamily.omega) := by
    simp only [separatingElement, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [h, elementCoeff_add_period_mul, elementCoeff_one]

theorem separatingElement_psi (eta psi : HeckeFamily.Character) :
    elementCoeff psi (separatingElement eta psi) = 1 := by
  have h : separatingElement eta psi =
      1 + (psi.period : O) * ((3*eta.period : ℕ)*HeckeFamily.omega) := by
    simp only [separatingElement, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [h, elementCoeff_add_period_mul, elementCoeff_one]

theorem separatingElement_embedding (eta psi : HeckeFamily.Character) :
    ConcreteTraceCRT.eisEmbedding (separatingElement eta psi) =
      1 + ((3*eta.period*psi.period : ℕ) : ℂ)*omega3 := by
  change ConcreteTraceCRT.eisEmbedding
    (ActualEisensteinCoordinates.eval 1 (3*eta.period*psi.period)) = _
  rw [ActualEisensteinCubic.eisEmbedding_eval]
  norm_cast

theorem separatingElement_period_ge_three (eta psi : HeckeFamily.Character) :
    (3 : ℝ) ≤ (3*eta.period*psi.period : ℕ) := by
  have h1 : 1 ≤ eta.period := eta.period_pos
  have h2 : 1 ≤ psi.period := psi.period_pos
  exact_mod_cast (show 3 ≤ 3*eta.period*psi.period from by nlinarith)

theorem separatingElement_ne_zero (eta psi : HeckeFamily.Character) :
    separatingElement eta psi ≠ 0 := by
  intro h
  have hi := sixth_power_im_ne_zero (separatingElement_period_ge_three eta psi)
  norm_cast at hi
  rw [← separatingElement_embedding, h, map_zero, zero_pow (by decide)] at hi
  exact hi rfl

theorem separatingElement_primary (eta psi : HeckeFamily.Character) :
    ActualEisensteinCubic.lambda^2 ∣ separatingElement eta psi - 1 := by
  apply ActualEisensteinCubic.lambda_sq_dvd_three.trans
  refine ⟨(eta.period : O)*(psi.period : O)*HeckeFamily.omega, ?_⟩
  simp only [separatingElement, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- A nonreal sixth power cannot have trivial angular-six coefficient. -/
theorem angular_six_ne_one {z : ℂ} (hi : (z^6).im ≠ 0) :
    star (z / (‖z‖ : ℂ)) ^ 6 ≠ 1 := by
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hi
  have hn : (‖z‖ : ℂ)^6 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  intro h
  have hd : z^6 / (‖z‖ : ℂ)^6 = 1 := by
    simpa [star_pow, star_div, div_pow] using congrArg star h
  have he := (div_eq_one_iff_eq hn).mp hd
  have him := congrArg Complex.im he
  simp only [← Complex.ofReal_pow, Complex.ofReal_im] at him
  exact hi him

theorem separatingElement_angular_ne_one (eta psi : HeckeFamily.Character) :
    actualAPhase eta (separatingElement eta psi) ≠ 1 := by
  rw [actualAPhase, separatingElement_eta, one_pow, mul_one,
    FiniteGaussPhase.angularFactor]
  apply angular_six_ne_one
  rw [separatingElement_embedding]
  exact_mod_cast sixth_power_im_ne_zero (separatingElement_period_ge_three eta psi)

/-- Every finite ray character is separated by a primary native element. -/
theorem exists_primary_separating_element (eta psi : HeckeFamily.Character) :
    ∃ z : O, z ≠ 0 ∧ ActualEisensteinCubic.lambda^2 ∣ z-1 ∧
      actualAPhase eta z ≠ elementCoeff psi z := by
  refine ⟨separatingElement eta psi, separatingElement_ne_zero eta psi,
    separatingElement_primary eta psi, ?_⟩
  rw [separatingElement_psi]
  exact separatingElement_angular_ne_one eta psi

/-- In particular, the actual extracted ideal channel cannot be a finite
ray character, even on nonzero primary principal ideals. -/
theorem actual_angular_channel_not_finite_ray (eta : HeckeFamily.Character) :
    ¬ ∃ psi : HeckeFamily.Character, ∀ I : Ideal O, I ≠ 0 →
      actualAPhase eta (CompletedGauss.primaryGenerator I) = idealCoeff psi I := by
  rintro ⟨psi, h⟩
  obtain ⟨z, hz, hp, hne⟩ := exists_primary_separating_element eta psi
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have he := h (Ideal.span {z}) hI
  rw [CompletedGauss.primaryGenerator_span z hz hp, idealCoeff_span psi hz] at he
  exact hne he

/-- Enlarging a character's recorded period changes none of its values. -/
def enlargedPeriod (psi : HeckeFamily.Character) (n : ℕ) (hn : 0 < n) :
    HeckeFamily.Character where
  modulus := psi.modulus
  modulus_ne_bot := psi.modulus_ne_bot
  residue := psi.residue
  unit_trivial := psi.unit_trivial
  period := psi.period*n
  period_pos := Nat.mul_pos psi.period_pos hn
  period_mem := by
    rw [Nat.cast_mul]
    exact psi.modulus.mul_mem_right _ psi.period_mem

/-- A finite excluded modulus cannot account for the coefficient mismatch:
the separating element can also be chosen congruent to one modulo it. -/
theorem exists_separating_element_modulo (eta psi : HeckeFamily.Character)
    (M : Ideal O) (hM : M ≠ 0) :
    ∃ z : O, z ≠ 0 ∧ ActualEisensteinCubic.lambda^2 ∣ z-1 ∧
      z-1 ∈ M ∧ actualAPhase eta z ≠ elementCoeff psi z := by
  have hn : 0 < Ideal.absNorm M := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact hM
  let proxy := enlargedPeriod psi (Ideal.absNorm M) hn
  let z := separatingElement eta proxy
  refine ⟨z, separatingElement_ne_zero eta proxy,
    separatingElement_primary eta proxy, ?_, ?_⟩
  · have he : z-1 = (Ideal.absNorm M : O)*
        (3*(eta.period : O)*(psi.period : O)*HeckeFamily.omega) := by
      simp only [z, proxy, separatingElement, enlargedPeriod, Nat.cast_mul,
        Nat.cast_ofNat]
      ring
    rw [he]
    exact M.mul_mem_right _ (Ideal.absNorm_mem M)
  · have hcoef : elementCoeff psi z = elementCoeff proxy z := rfl
    rw [hcoef, separatingElement_psi]
    exact separatingElement_angular_ne_one eta proxy

/-- Direct finite-ray substitution also fails after restricting to
elements congruent to one modulo any nonzero excluded modulus. -/
theorem actual_angular_channel_not_finite_ray_on_congruence
    (eta : HeckeFamily.Character) (M : Ideal O) (hM : M ≠ 0) :
    ¬ ∃ psi : HeckeFamily.Character, ∀ z : O,
      z ≠ 0 → ActualEisensteinCubic.lambda^2 ∣ z-1 → z-1 ∈ M →
      actualAPhase eta z = elementCoeff psi z := by
  rintro ⟨psi, h⟩
  obtain ⟨z, hz, hp, hm, hne⟩ := exists_separating_element_modulo eta psi M hM
  exact hne (h z hz hp hm)

/-- The same witness lies outside every excluded prime dividing `M`. -/
theorem exists_coprime_primary_separating_ideal
    (eta psi : HeckeFamily.Character) (M : Ideal O) (hM : M ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ IsCoprime I M ∧
      actualAPhase eta (CompletedGauss.primaryGenerator I) ≠ idealCoeff psi I := by
  obtain ⟨z, hz, hp, hm, hne⟩ := exists_separating_element_modulo eta psi M hM
  refine ⟨Ideal.span {z}, Ideal.span_singleton_eq_bot.not.mpr hz, ?_, ?_⟩
  · apply Ideal.isCoprime_iff_exists.mpr
    refine ⟨z, Ideal.subset_span (by simp), 1-z, ?_, by ring⟩
    convert M.neg_mem hm using 1
    ring
  · rw [CompletedGauss.primaryGenerator_span z hz hp, idealCoeff_span psi hz]
    exact hne

/-- Removing any fixed nonzero bad-prime modulus does not permit direct
finite-ray coefficient substitution. -/
theorem actual_angular_channel_not_finite_ray_outside_modulus
    (eta : HeckeFamily.Character) (M : Ideal O) (hM : M ≠ 0) :
    ¬ ∃ psi : HeckeFamily.Character, ∀ I : Ideal O,
      I ≠ 0 → IsCoprime I M →
      actualAPhase eta (CompletedGauss.primaryGenerator I) = idealCoeff psi I := by
  rintro ⟨psi, h⟩
  obtain ⟨I, hI, hm, hne⟩ := exists_coprime_primary_separating_ideal eta psi M hM
  exact hne (h I hI hm)

end OpenAIReview.AngularPeriod

#lint+ in OpenAIReview.AngularPeriod

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
  unless declarations>0 do throwError "Empty angular-period audit."
  logInfo m!"Angular-period audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-angular-period"
  IO.FS.writeFile ".lake/arithmetic-operator-angular-period/axioms.json"
    (Json.mkObj [("scope",toJson "actual angular-six character cannot equal any finite ray character; no general angular continuation obstruction or RH estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
