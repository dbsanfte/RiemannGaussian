/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.GramPrimaryLattice
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual primitive bottom rows and native finite-section support

Right multiplication is an exact bijection of primitive Eisenstein rows.
The literal native primaryCoefficient is preserved when the first column
is congruent to the identity modulo its ACTUAL fixed modulus. Zero first
coordinates have zero coefficient on both sides. The full sextic symbol
row law and Eisenstein/Fourier normalization are paper-level, not assumed
or proved by this finite support leaf.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option warningAsError true
noncomputable section
open scoped Classical MatrixGroups

namespace OpenAIReview.NativeSectionLift
open OAI ActualEisensteinCubic CanonicalQuadraticSieve
open SevenEighths.ProbePhysical SevenEighths.ProbeGramCommon
local notation "O" => ActualEisensteinCubic.O

/-- Literal multiplication of a primitive bottom row by an actual determinant-one matrix. -/
def rowTransform (g : SL(2,O)) (v : O×O) : O×O :=
  (v.1*g 0 0+v.2*g 1 0,v.1*g 0 1+v.2*g 1 1)

/-- No squarefree or unit hypothesis on either row coordinate is needed. -/
theorem primitive_row_preserved (g : SL(2,O)) (v : O×O)
    (hv : IsCoprime v.1 v.2) : IsCoprime (rowTransform g v).1 (rowTransform g v).2 := by
  obtain ⟨r,s,h⟩ := hv
  refine ⟨r*g 1 1-s*g 0 1,s*g 0 0-r*g 1 0,?_⟩
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  change (r*g 1 1-s*g 0 1)*(v.1*g 0 0+v.2*g 1 0)+
    (s*g 0 0-r*g 1 0)*(v.1*g 0 1+v.2*g 1 1)=1
  calc
    _=(r*v.1+s*v.2)*(g 0 0*g 1 1-g 0 1*g 1 0) := by ring
    _=1 := by rw [h,hd,one_mul]

/-- Right row multiplication has the literal matrix multiplication order. -/
theorem row_transform_mul (g k : SL(2,O)) (v : O×O) :
    rowTransform (g*k) v=rowTransform k (rowTransform g v) := by
  apply Prod.ext <;>
    simp only [rowTransform,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- The identity matrix preserves every row, including the two zero-coordinate cases. -/
theorem row_transform_one (v : O×O) : rowTransform 1 v=v := by
  simp [rowTransform,Matrix.SpecialLinearGroup.coe_one]

/-- Primitive rows, including rows with c=0 or d=0, are permuted exactly. -/
def primitiveRowEquiv (g : SL(2,O)) :
    {v : O×O // IsCoprime v.1 v.2} ≃ {v : O×O // IsCoprime v.1 v.2} where
  toFun v := ⟨rowTransform g v.val,primitive_row_preserved g v.val v.property⟩
  invFun v := ⟨rowTransform g⁻¹ v.val,primitive_row_preserved g⁻¹ v.val v.property⟩
  left_inv v := by
    apply Subtype.ext
    change rowTransform g⁻¹ (rowTransform g v.val)=v.val
    rw [←row_transform_mul,mul_inv_cancel,row_transform_one]
  right_inv v := by
    apply Subtype.ext
    change rowTransform g (rowTransform g⁻¹ v.val)=v.val
    rw [←row_transform_mul,inv_mul_cancel,row_transform_one]

/-- The actual finite primary coefficient, not a supplied row phase, is preserved. -/
theorem actual_coefficient_row_transform (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (σ : RayFourExpansion.RayRing)
    (g : SL(2,O)) (v : O×O)
    (hA : g 0 0-1∈jointFixedModulus S hS)
    (hC : g 1 0∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ (rowTransform g v).1=primaryCoefficient S hS σ v.1 := by
  apply primaryCoefficient_periodic
  have hm := (jointFixedModulus S hS).add_mem
    ((jointFixedModulus S hS).mul_mem_left v.1 hA)
    ((jointFixedModulus S hS).mul_mem_left v.2 hC)
  convert hm using 1
  simp only [rowTransform]
  ring

/-- Literal native calibration/primary support kills the omitted zero first coordinate. -/
theorem actual_coefficient_zero (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayFourExpansion.RayRing) :
    primaryCoefficient S hS σ 0=0 := by
  by_contra h
  have hs := (primaryCoefficient_nonzero_supported S hS hbad σ 0 h).1
  exact hs.1 (by simp)

/-- A transformed zero first coordinate cannot create a missing nonzero summand. -/
theorem transformed_zero_has_zero_coefficient (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayFourExpansion.RayRing) (g : SL(2,O)) (v : O×O)
    (hA : g 0 0-1∈jointFixedModulus S hS)
    (hC : g 1 0∈jointFixedModulus S hS) (hz : (rowTransform g v).1=0) :
    primaryCoefficient S hS σ v.1=0 := by
  rw [←actual_coefficient_row_transform S hS σ g v hA hC,hz]
  exact actual_coefficient_zero S hS hbad σ

/-- An original zero first coordinate remains zero in the ACTUAL weighted row sum. -/
theorem original_zero_has_zero_coefficient (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayFourExpansion.RayRing) (g : SL(2,O)) (v : O×O)
    (hA : g 0 0-1∈jointFixedModulus S hS)
    (hC : g 1 0∈jointFixedModulus S hS) (hz : v.1=0) :
    primaryCoefficient S hS σ (rowTransform g v).1=0 := by
  rw [actual_coefficient_row_transform S hS σ g v hA hC,hz]
  exact actual_coefficient_zero S hS hbad σ

end OpenAIReview.NativeSectionLift

#lint+ in OpenAIReview.NativeSectionLift

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
  unless declarations>0 do throwError "Empty native section lift audit."
  logInfo m!"Native section lift audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-native-section-lift-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-native-section-lift-gate/axioms.json"
    (Json.mkObj [("scope",toJson "actual primitive Eisenstein row bijection and literal native primaryCoefficient periodicity/zero-row support. Full sextic symbol row law, automorphy, unfolding and source remain paper-level"),
      ("namespaceLinters",toJson (15:Nat)),("allLocalDeclarationsByModuleProvenance",toJson true),
      ("onlyStandardAxioms",toJson true),("declarations",toJson declarations),
      ("theoremsIncludingGeneratedHelpers",toJson theorems),("declarationAxioms",Json.arr reports)]).pretty
