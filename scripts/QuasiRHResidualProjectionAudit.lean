/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Native principal and sextic additive profiles are different

On the actual Eisenstein prime quotient the principal unit profile has
nonzero mass at zero, while the actual canonical nontrivial sextic character
has zero mass there. Thus the complete profiles cannot be identified.
This finite mismatch does not assert an automorphic trace formula, residual
projection identity, source transfer, or bound for the native covariance.
-/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators Classical

namespace OpenAIReview.ResidualProjection
open OAI ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
/-- The actual maximal Eisenstein ideal has its native quotient field. -/
noncomputable local instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P
/-- The actual prime quotient is finite, as required for literal unit sums. -/
noncomputable local instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

/-- The principal additive profile on the actual quotient unit group. -/
def principalProfile (P : Ideal O) [P.IsMaximal]
    (ψ : AddChar (O ⧸ P) ℂ) (n : O ⧸ P) : ℂ :=
  ∑ u : (O ⧸ P)ˣ, ψ (n*(u : O ⧸ P))

/-- The genuinely sextic profile, retaining the canonical character weight. -/
def sexticProfile (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (ψ : AddChar (O ⧸ P) ℂ) (n : O ⧸ P) : ℂ :=
  ∑ u : (O ⧸ P)ˣ, canonicalSextic P hg (u : O ⧸ P)*ψ (n*(u : O ⧸ P))

private theorem sum_zero_add_units {F : Type*} [Field F] [Fintype F]
    (f : F → ℂ) : (∑ x : F, f x)=f 0+∑ u : Fˣ, f (u : F) := by
  calc
    _ = f 0+∑ x ∈ (Finset.univ : Finset F).erase 0, f x := by
      simpa only [add_comm] using
        (Finset.sum_erase_add (Finset.univ : Finset F) f (Finset.mem_univ (0:F))).symm
    _ = f 0+∑ x : {x : F // x≠0}, f x := by
      congr 1
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := by
      congr 1
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x≠0})
        (fun u : Fˣ => f (u : F)) (fun x : {x : F // x≠0} => f x) ?_).symm
      intro u
      rfl

/-- Zero frequency retains every actual unit in the principal profile. -/
theorem principalProfile_zero (P : Ideal O) [P.IsMaximal]
    (ψ : AddChar (O ⧸ P) ℂ) :
    principalProfile P ψ 0=(Fintype.card (O ⧸ P)ˣ : ℂ) := by
  simp [principalProfile]

/-- The actual canonical sextic character has no zero-frequency unit mass. -/
theorem sexticProfile_zero (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (hchar : ringChar (O ⧸ P)≠2) (ψ : AddChar (O ⧸ P) ℂ) :
    sexticProfile P hg ψ 0=0 := by
  have hn : canonicalSextic P hg≠1 := by
    simpa using canonicalSextic_pow_ne_one P hg hchar (j:=1) (by decide) (by decide)
  have hs := sum_zero_add_units (canonicalSextic P hg)
  have hz := MulChar.sum_eq_zero_of_ne_one hn
  simp only [MulChar.map_zero,zero_add] at hs
  simp only [sexticProfile,zero_mul,AddChar.map_zero_eq_one,mul_one]
  exact hs.symm.trans hz

/-- Principal zero mass cannot be replaced by the nontrivial sextic zero mass. -/
theorem zero_profiles_ne (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (hchar : ringChar (O ⧸ P)≠2) (ψ : AddChar (O ⧸ P) ℂ) :
    principalProfile P ψ 0≠sexticProfile P hg ψ 0 := by
  rw [principalProfile_zero,sexticProfile_zero P hg hchar]
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (O ⧸ P)ˣ≠0)

/-- Hence the full actual numerator profiles are unequal, independently of
the choice of the additive character or any Fourier normalization. -/
theorem native_profiles_ne (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (hchar : ringChar (O ⧸ P)≠2) (ψ : AddChar (O ⧸ P) ℂ) :
    principalProfile P ψ≠sexticProfile P hg ψ := by
  intro h
  exact zero_profiles_ne P hg hchar ψ (congrFun h 0)

end OpenAIReview.ResidualProjection

#lint+ in OpenAIReview.ResidualProjection

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut details : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    details := details.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty native residual projection audit."
  logInfo m!"Native profile audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-residual-projection-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-residual-projection-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual canonical Eisenstein character profiles; no analytic spectral projection or source theorem"),
      ("namespaceLinters",toJson (15:Nat)),("onlyStandardAxioms",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr details)]).pretty
