/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal matching physical-divisor principal local sum

The physical local exponent is restricted to `k ≤ e`, with `e ∈ {0,1}` the
squarefree spectral exponent, and the cube order is even. The exact native
`sourcePrincipalTerm` sum has no physical density denominator `1-q^(-w)`.
Global Euler products, normal convergence, contours and other source channels
are outside this local leaf.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
set_option quotPrecheck false
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.MatchingDensity
open OAI OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
  OAI.SevenEighths.ProbePhysical OAI.SevenEighths.ProbeEuler
  OAI.SevenEighths.CubicSieve OAI.SevenEighths.ProbeRow
local notation "O" => OAI.ActualEisensteinCubic.O

/-- Literal native local frequency sum with physical exponent at most the squarefree exponent. -/
def matchingInner (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (x w z : ℂ) (e r : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (e+1), ∑' m : ℕ,
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p)
      x w z e (2*r) k m

/-- The literal restricted native local sum over both squarefree and all even cube orders. -/
def matchingSeries (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' r : ℕ, matchingInner η p hp hg x w z e.val r

/-- Actual geometric ratio in the native local-series coordinates. -/
def matchingRatio (η : OAI.SevenEighths.HeckeFamily.Character) (p : O)
    (x z : ℂ) : ℂ :=
  evenRatio (Ideal.absNorm (Ideal.span {p}) : ℂ) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}) : ℂ)^(-x))
    (coordV (Ideal.absNorm (Ideal.span {p})) z)

section Prime
variable (η : OAI.SevenEighths.HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (x w z : ℂ)
local notation "q" => (Ideal.absNorm (Ideal.span {p}) : ℂ)
local notation "X" => q^(-x)
local notation "W" => q^(-w)
local notation "V" => coordV (Ideal.absNorm (Ideal.span {p})) z
local notation "R" => matchingRatio η p x z
local notation "δ" => targetMonoid η p * X

private theorem positive_msum (e r k : ℕ) (ht : e+3*(2*r) ≠ 0) :
    (∑' m : ℕ, sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p)
      x w z e (2*r) k m) =
    ∑' m : ℕ, principalMarkedTerm p hp hg (targetMonoid η p) (actualACube η p)
      X W V e (2*r) k m := by
  apply tsum_congr
  intro m
  exact sourcePrincipalTerm_pos p hp hg _ _ x w z e (2*r) k m ht

/-- The matching zero block retains only the sixth-frequency density. -/
theorem matchingInner_zero (hV : ‖V‖ < 1) :
    matchingInner η p hp hg x w z 0 0 = 1/(1-V) := by
  unfold matchingInner
  simp only [Nat.zero_add, Nat.mul_zero, Finset.sum_range_one]
  simp_rw [sourcePrincipalTerm_zero]
  exact (zeroIndex_inner_zero p _ _ _ hV).tsum_eq

include hc in
/-- At positive even cube order, exponent zero permits only physical exponent zero. -/
theorem matchingInner_even (hV : ‖V‖ < 1) (r : ℕ) :
    matchingInner η p hp hg x w z 0 (r+1) = R^r *
      (R*(1-q⁻¹)/(1-V)) := by
  unfold matchingInner
  simp only [Nat.zero_add, Finset.sum_range_one]
  rw [positive_msum η p hp hg x w z 0 (r+1) 0 (by omega)]
  rw [show 2*(r+1)=2*r+2 by omega]
  rw [(even_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  unfold matchingRatio
  ring

include hc in
/-- At squarefree exponent one, both allowed physical exponents retain their actual Gauss terms. -/
theorem matchingInner_squarefree (hV : ‖V‖ < 1) (r : ℕ) :
    matchingInner η p hp hg x w z 1 r = R^r *
      (-δ-δ*(q-1)*W*V/(1-V)) := by
  unfold matchingInner
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [positive_msum η p hp hg x w z 1 r 0 (by omega),
    positive_msum η p hp hg x w z 1 r 1 (by omega),
    (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq,
    (squarefree_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  unfold matchingRatio
  ring

include hc in
/-- Exact sum over all even cube orders, before any global Euler or contour argument. -/
theorem matchingSeries_eq (hV : ‖V‖ < 1) (hR : ‖R‖ < 1) :
    matchingSeries η p hp hg x w z =
      (1-q⁻¹*R-δ*(1-V+(q-1)*W*V))/((1-V)*(1-R)) := by
  have h0tail : HasSum (fun r : ℕ => matchingInner η p hp hg x w z 0 (r+1))
      ((R*(1-q⁻¹)/(1-V))/(1-R)) := by
    simpa only [matchingInner_even η p hp hg hc x w z hV, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (R*(1-q⁻¹)/(1-V))
  have h0 := HasSum.sum_range_add
    (f:=fun r : ℕ => matchingInner η p hp hg x w z 0 r) (k:=1) h0tail
  have h1 : HasSum (fun r : ℕ => matchingInner η p hp hg x w z 1 r)
      ((-δ-δ*(q-1)*W*V/(1-V))/(1-R)) := by
    simpa only [matchingInner_squarefree η p hp hg hc x w z hV, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (-δ-δ*(q-1)*W*V/(1-V))
  unfold matchingSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0.tsum_eq, h1.tsum_eq]
  simp only [Finset.sum_range_one, matchingInner_zero η p hp hg x w z hV]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hr := one_sub_ne_zero_of_norm_lt_one _ hR
  field_simp [hv, hr]
  ring

include hc in
/-- The actual matching block cancels its two remaining geometric denominators exactly. -/
theorem matchingSeries_density_identity (hV : ‖V‖ < 1) (hR : ‖R‖ < 1) :
    (1-V)*(1-R)*matchingSeries η p hp hg x w z =
      1-q⁻¹*R-δ*(1-V+(q-1)*W*V) := by
  rw [matchingSeries_eq η p hp hg hc x w z hV hR]
  exact mul_div_cancel₀ _ (mul_ne_zero
    (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hR))

include hc in
/-- The same reciprocal target factor remains, with no physical density denominator. -/
theorem matchingSeries_target_factor (hV : ‖V‖ < 1) (hR : ‖R‖ < 1)
    (hδ : 1-δ ≠ 0) :
    matchingSeries η p hp hg x w z = (1-δ)/(1-V) *
      (1+(R*(1-q⁻¹-δ)+δ*V*(1-(q-1)*W))/((1-R)*(1-δ))) := by
  rw [matchingSeries_eq η p hp hg hc x w z hV hR]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hr := one_sub_ne_zero_of_norm_lt_one _ hR
  field_simp [hv, hr, hδ]
  ring

end Prime
end OpenAIReview.MatchingDensity

#lint+ in OpenAIReview.MatchingDensity

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
  unless declarations > 0 do throwError "Empty matching-density audit."
  logInfo m!"Matching-density audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-joint-gauss-correlation"
  IO.FS.writeFile ".lake/arithmetic-operator-joint-gauss-correlation/matching-density-axioms.json"
    (Json.mkObj [("scope",toJson "literal native sourcePrincipalTerm sum restricted k<=e, e<=1, even cube orders; no global source or contour theorem"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
