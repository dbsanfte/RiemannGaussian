/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.QuasiRHMatchingDensityAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual principal local source outside the matching physical divisor block

The left side is the imported literal unrestricted `sourcePrincipalSeries` minus
the literal restricted `matchingSeries` from the previous strict leaf. The exact
remainder retains every physical power in its free zero-index tail. A second
literal sum imposes physical coprimality with the completed spectral ideal. No global
Euler product, pole/source comparison or truncated-period estimate is asserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option quotPrecheck false
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.NonmatchingSource
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
  OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeEuler
  OAI.SevenEighths.CubicSieve OAI.SevenEighths.ProbeRow
  OpenAIReview.MatchingDensity
local notation "O" => OAI.ActualEisensteinCubic.O

/-- The literal physical local sum with no physical prime at positive completed order. -/
def disjointInner (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (x w z : ℂ) (e r : ℕ) : ℂ :=
  if e+3*(2*r)=0 then
    ∑' k : ℕ, ∑' m : ℕ,
      sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e (2*r) k m
  else ∑' m : ℕ,
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e (2*r) 0 m

/-- Literal principal local sum for physical ideal coprime to the completed spectral ideal. -/
def disjointSeries (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' r : ℕ, disjointInner η p hp hg x w z e.val r

section Prime
variable (η : OAI.SevenEighths.HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (x w z : ℂ)
local notation "q" => (Ideal.absNorm (Ideal.span {p}) : ℂ)
local notation "X" => q^(-x)
local notation "W" => q^(-w)
local notation "V" => coordV (Ideal.absNorm (Ideal.span {p})) z
local notation "R" => matchingRatio η p x z

include hc in
/-- The full literal source sum minus the matching literal sum retains exactly the extra-physical tails. -/
theorem full_sub_matching (hV : ‖V‖ < 1) (hR : ‖R‖ < 1) (hW : ‖W‖ < 1) :
    sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z -
      matchingSeries η p hp hg x w z = W/(1-W)+W*R/(1-R) := by
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hrcoord : ‖coordR (Ideal.absNorm (Ideal.span {p}))
      ((actualACube η p)^2) x z‖ < 1 := by
    have he := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}) : ℝ) hq
      (actualACube η p) x z
    simpa only [← he, Complex.ofReal_natCast, matchingRatio] using hR
  have hwcoord : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖ < 1 := by
    simpa only [coordW, one_mul, Complex.ofReal_natCast] using hW
  rw [sourcePrincipalSeries_eq p hp hg hc _ _ x w z hV hrcoord hwcoord]
  unfold principalFullSeries
  rw [principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV (by
      simpa only [matchingRatio, Complex.ofReal_natCast] using hR),
    matchingSeries_eq η p hp hg hc x w z hV hR]
  unfold markedFactor
  simp only [matchingRatio, Complex.ofReal_natCast] at hR ⊢
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  have hr := one_sub_ne_zero_of_norm_lt_one _ hR
  field_simp [hv, hw, hr]
  ring

include hc in
/-- After the exact nonsquarefree zero-index tail is deleted, the remaining local extra tail starts at W. -/
theorem full_sub_repeated_tail_sub_matching
    (hV : ‖V‖ < 1) (hR : ‖R‖ < 1) (hW : ‖W‖ < 1) :
    (sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z -
      W^2/(1-W)) - matchingSeries η p hp hg x w z = W+W*R/(1-R) := by
  have he := full_sub_matching η p hp hg hc x w z hV hR hW
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  calc
    _ = (sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z -
        matchingSeries η p hp hg x w z)-W^2/(1-W) := by ring
    _ = _ := by
      rw [he]
      field_simp [hw]
      ring

/-- The disjoint zero completed block retains every physical prime power. -/
theorem disjointInner_zero (hV : ‖V‖ < 1) (hW : ‖W‖ < 1) :
    disjointInner η p hp hg x w z 0 0 = 1/(1-V)+W/(1-W) := by
  unfold disjointInner
  simp only [Nat.mul_zero, Nat.zero_add, ite_true]
  simp_rw [sourcePrincipalTerm_zero]
  exact zeroIndexSeries_eq p hp _ _ _ hW hV

include hc in
/-- A positive even cube order in the disjoint population permits only physical exponent zero. -/
theorem disjointInner_even (hV : ‖V‖ < 1) (r : ℕ) :
    disjointInner η p hp hg x w z 0 (r+1) =
      R^r*(R*(1-q⁻¹)/(1-V)) := by
  unfold disjointInner
  rw [ite_eq_right (by omega)]
  simpa only [matchingInner, Nat.zero_add, Finset.sum_range_one] using
    matchingInner_even η p hp hg hc x w z hV r

include hc in
/-- The exact native disjoint squarefree block has no physical exponent one. -/
theorem disjointInner_squarefree (r : ℕ) :
    disjointInner η p hp hg x w z 1 r = R^r*(-targetMonoid η p*X) := by
  unfold disjointInner
  rw [ite_eq_right (by omega)]
  have he : (∑' m : ℕ, sourcePrincipalTerm p hp hg (targetMonoid η p)
      (actualACube η p) x w z 1 (2*r) 0 m) =
      ∑' m : ℕ, principalMarkedTerm p hp hg (targetMonoid η p) (actualACube η p)
        X W V 1 (2*r) 0 m := by
    apply tsum_congr
    intro m
    exact sourcePrincipalTerm_pos p hp hg _ _ x w z 1 (2*r) 0 m (by omega)
  rw [he, (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq]
  rfl

include hc in
/-- The literal coprime physical population retains its full physical density tail. -/
theorem disjointSeries_eq (hV : ‖V‖ < 1) (hR : ‖R‖ < 1) (hW : ‖W‖ < 1) :
    disjointSeries η p hp hg x w z =
      (1-q⁻¹*R-targetMonoid η p*X*(1-V))/((1-V)*(1-R))+W/(1-W) := by
  have h0tail : HasSum (fun r : ℕ => disjointInner η p hp hg x w z 0 (r+1))
      ((R*(1-q⁻¹)/(1-V))/(1-R)) := by
    simpa only [disjointInner_even η p hp hg hc x w z hV, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (R*(1-q⁻¹)/(1-V))
  have h0 := HasSum.sum_range_add
    (f:=fun r : ℕ => disjointInner η p hp hg x w z 0 r) (k:=1) h0tail
  have h1 : HasSum (fun r : ℕ => disjointInner η p hp hg x w z 1 r)
      ((-targetMonoid η p*X)/(1-R)) := by
    simpa only [disjointInner_squarefree η p hp hg hc x w z, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (-targetMonoid η p*X)
  unfold disjointSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0.tsum_eq, h1.tsum_eq]
  simp only [Finset.sum_range_one, disjointInner_zero η p hp hg x w z hV hW]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hr := one_sub_ne_zero_of_norm_lt_one _ hR
  field_simp [hv, hr]
  ring

end Prime
end OpenAIReview.NonmatchingSource

#lint+ in OpenAIReview.NonmatchingSource

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
  unless declarations > 0 do throwError "Empty nonmatching-source audit."
  logInfo m!"Nonmatching-source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-period-source"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-period-source/axioms.json"
    (Json.mkObj [("scope",toJson "literal native full-minus-matching and physical-coprime local source sums, repeated-power tail subtraction; no global pole or period transfer"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
