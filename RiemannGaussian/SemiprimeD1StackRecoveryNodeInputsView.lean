/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsInventory
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Exact140-word call boundaries: unchanged old112 bank and only two acquired array outputs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsView
open SemiprimeD1StackRecoveryNodeInputs SemiprimeD1StackRecoveryNodeInputsInventory
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- All28 fresh words are EMPTY before the inverse and powers actually execute. -/
def empty (old : A.Stack→List Bool) : Stack→List Bool := bank old (fun _=>[]) (fun _=>[])
/-- The real inverse changes only its actual new chronological output word. -/
def afterInverse (old : A.Stack→List Bool) (inv : List Bool) : Stack→List Bool :=
  Function.update (empty old) inverseOutput inv
/-- All140 final fields: EVERY112 original affine/Grid word plus only two new actual complete arrays. -/
def result (old : A.Stack→List Bool) (inv pow : List Bool) : Stack→List Bool :=
  Function.update (afterInverse old inv) powersOutput pow
/-- Actual inverse output is outside the ENTIRE real powers role image. -/
theorem powers_not_inverseOutput (k : P.Stack) : powers k≠inverseOutput := by
  change powers k≠inverseWork 11
  rcases k with k|k
  · simp [powers,inverseWork,affine]
  · cases k <;> simp [powers,inverseWork,powersWork,affine]
/-- No original112 physical word is an inverse output address. -/
theorem affine_not_inverseOutput (k : A.Stack) : affine k≠inverseOutput := by
  change affine k≠inverseWork 11
  simp [affine,inverseWork]
/-- No original112 physical word is a powers output address. -/
theorem affine_not_powersOutput (k : A.Stack) : affine k≠powersOutput := by
  change affine k≠powersWork 7
  simp [affine,powersWork]
/-- Every actual old112 cache word survives BOTH entire real calls. -/
theorem old_retained (old : A.Stack→List Bool) (inv pow : List Bool) (k : A.Stack) :
    result old inv pow (affine k)=old k := by
  rw [result,Function.update_of_ne (affine_not_powersOutput k),afterInverse,
    Function.update_of_ne (affine_not_inverseOutput k)]
  rfl
/-- Direct physical input projection of the complete inverse source; no copied/prepared answer fields are supplied. -/
theorem inverse_initial (old : A.Stack→List Bool) (den q width : List Bool)
    (hr : ∀k,old (A.rational k)=if k=SemiprimeD1StackRationalOperation.aux .template then width else [])
    (hd : old (A.aux .array)=den) (hq : old (A.aux .retainedQ)=q) :
    Link.DataRel inverse (empty old) (I.input den q width) (empty old) := by
  constructor
  · intro k
    rcases k with k|k
    · exact hr k
    · rcases k with ⟨r,bit⟩|k
      · rfl
      · cases k <;> first | exact hd | exact hq | rfl
  · intro k _;rfl
/-- The complete powers source sees the actually retained Grid argument/q/W through direct aliases after inverse completion. -/
theorem powers_initial (old : A.Stack→List Bool) (inv signed den q width : List Bool)
    (hr : ∀k,old (A.rational k)=if k=SemiprimeD1StackRationalOperation.aux .template then width else [])
    (hs : old (A.grid (Q.reg .argument false))=signed)
    (hd : old (A.grid (Q.reg .argument true))=den) (hq : old (A.aux .retainedQ)=q) :
    Link.DataRel powers (afterInverse old inv) (P.input signed den q width) (afterInverse old inv) := by
  constructor
  · intro k
    rw [afterInverse,Function.update_of_ne (powers_not_inverseOutput k)]
    rcases k with k|k
    · exact hr k
    · cases k <;> first | exact hs | exact hd | exact hq | rfl
  · intro k _;rfl
end RiemannGaussian.SemiprimeD1StackRecoveryNodeInputsView
