/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionBounds
import RiemannGaussian.SemiprimeD1StackExprPowerBounds
import RiemannGaussian.SemiprimeD1StackJetPoint
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeMacroEntryBitCheck
/-! # Original-binary acquisition of all four root/normalization source codes
Exponents are acquired from actual modulus-WORD and exponent-cache lengths.
No modulus VALUE, exponent answer, expression or source code is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackRootSources
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1BinaryPublicAcquisition (Stack Label program input initial digitStack fermatStack)
end P
namespace Pow
export SemiprimeD1StackExprPower (Stack Label program store initial)
end Pow
/-- Eight physical syntax/marker/copy roles; no unbounded control payload. -/
inductive Aux where
  | base | markers | count | scratch | root | normal | forwardRoot | forwardNormal
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.base,.markers,.count,.scratch,.root,.normal,.forwardRoot,.forwardNormal]
  (by intro k;cases k <;> simp)
/-- Entire original acquired public bank and eight actual construction stacks. -/
abbrev Stack := P.Stack⊕Aux
/-- Actual acquired modulus WORD, whose length is n+1, NOT modulus value. -/
def modulusKey : P.Stack := P.fermatStack (.inr false)
/-- Actual acquired transform-exponent marker cache, length depth+1. -/
def exponentKey : P.Stack := P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .exponent)
/-- Three physically executed preserving copy sites. -/
def copyStack (site : Fin 3) (k : Fin 3) : Stack :=
  if k=0 then .inl (if site=2 then exponentKey else modulusKey)
  else if k=1 then .inr (if site=2 then .count else .markers) else .inr .scratch
/-- Both exact power constructors share empty work but have distinct output codes. -/
def powerStack (normal : Bool) (k : Fin 5) : Stack :=
  if k=0 then .inr .base else if k=1 then .inr .markers else if k=2 then .inr .count
  else if k=3 then .inr .scratch else .inr (if normal then .normal else .root)
/-- Fixed literal byte strings; these are constant instruction-table data only. -/
def literalCode (kind : Fin 5) : List Bool :=
  if kind=0 ∨ kind=2 then SemiprimeD1StackExprCodec.encode (.literal [false,false,true]) []
  else if kind=1 then SemiprimeD1StackExprCodec.encode (.literal [false,true]) []
  else if kind=3 then SemiprimeD1StackExprCodec.encode (.literal [true]) []
  else [true,false,false,false,false]
/-- Static output role for each fixed literal constructor. -/
def literalStack (kind : Fin 5) : Stack :=
  .inr (if kind=0 ∨ kind=1 then .base else if kind=2 then .forwardRoot else if kind=3 then .forwardNormal else .normal)
/-- All finite source-construction and actual component locations. -/
inductive Label where
  | start | copyRoot | dropRoot1 | dropRoot2 | powerRoot | clearRootMarkers | clearRootBase
  | copyNormal | dropNormal | copyExponent | cancel | cancelMarker | powerNormal | clearNormalMarkers | clearNormalBase
  | seed (kind : Fin 5) (position : Fin 10) | done
  | preprocess (pc : P.Label) | copy (site : Fin 3) (pc : Fin 9) | power (normal : Bool) (pc : Pow.Label)
  deriving DecidableEq,Fintype
/-- Next literal/control site, fixed before original N. -/
def afterSeed (kind : Fin 5) : Label :=
  if kind=0 then .powerRoot else if kind=1 then .powerNormal else if kind=2 then .seed 3 0
  else if kind=3 then .done else .seed 2 0
/-- ONE fixed instruction table. Lists in literalCode are static finite literals;
operand words, marker lengths and source syntax never occur in finite control. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.preprocess (SemiprimeD1BinaryPublicAcquisition.mainLabel .start)) .copyRoot
  | .copyRoot=>.call (.copy 0 0) .dropRoot1
  | .dropRoot1=>.base (.pop (.inr .markers) .dropRoot2 .dropRoot2 .dropRoot2)
  | .dropRoot2=>.base (.pop (.inr .markers) (.seed 0 0) (.seed 0 0) (.seed 0 0))
  | .powerRoot=>.call (.power false .start) .clearRootMarkers
  | .clearRootMarkers=>.base (.pop (.inr .markers) .clearRootBase .clearRootMarkers .clearRootMarkers)
  | .clearRootBase=>.base (.pop (.inr .base) .copyNormal .clearRootBase .clearRootBase)
  | .copyNormal=>.call (.copy 1 0) .dropNormal
  | .dropNormal=>.base (.pop (.inr .markers) .copyExponent .copyExponent .copyExponent)
  | .copyExponent=>.call (.copy 2 0) .cancel
  | .cancel=>.base (.pop (.inr .count) (.seed 1 0) .cancelMarker .cancelMarker)
  | .cancelMarker=>.base (.pop (.inr .markers) .cancel .cancel .cancel)
  | .powerNormal=>.call (.power true .start) .clearNormalMarkers
  | .clearNormalMarkers=>.base (.pop (.inr .markers) .clearNormalBase .clearNormalMarkers .clearNormalMarkers)
  | .clearNormalBase=>.base (.pop (.inr .base) (.seed 4 0) .clearNormalBase .clearNormalBase)
  | .seed kind pos=>if pos.val<(literalCode kind).length then
      .base (.push (literalStack kind) ((literalCode kind).reverse[pos.val]?.getD false)
        (.seed kind ⟨min (pos.val+1) 9,by omega⟩))
    else .base (.jump (afterSeed kind))
  | .done=>.base .halt
  | .preprocess pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.preprocess (P.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .power normal pc=>SemiprimeD1StackValidationLink.instruction (powerStack normal) (Label.power normal) (Pow.program pc)
/-- Physical auxiliary payload view. -/
def aux (base markers count scratch root normal forwardRoot forwardNormal : List Bool) : Aux→List Bool
  | .base=>base | .markers=>markers | .count=>count | .scratch=>scratch | .root=>root | .normal=>normal
  | .forwardRoot=>forwardRoot | .forwardNormal=>forwardNormal
/-- Full literal payload, not an executing source-code supplier. -/
def store (cache : P.Stack→List Bool) (base markers count scratch root normal forwardRoot forwardNormal : List Bool) : Stack→List Bool :=
  Sum.elim cache (aux base markers count scratch root normal forwardRoot forwardNormal)
/-- Original BINARY N is the ONLY initial physical data. -/
def input (bits : List Bool) : Stack→List Bool := store (P.input bits) [] [] [] [] [] [] [] []
/-- Actual original-input source entry. -/
def initial (bits : List Bool) : C.State Stack Label := ⟨some .start,none,none,input bits,[]⟩
/-- Every preserving copy has separate actual data roles. -/
theorem copy_injective (site : Fin 3) : Function.Injective (copyStack site) := by
  fin_cases site <;> decide
/-- All five roles of each actual power constructor are distinct. -/
theorem power_injective (normal : Bool) : Function.Injective (powerStack normal) := by cases normal <;> decide
/-- Actual fixed finite source producer. Root output is designated; all four codes are retained. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (.inl (P.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))) (.inr .root) .start program
/-- Every data and return alphabet is finite before original N. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- Finite control has no decoded N/exponent/list or expression payload. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Exact fixed data-role count. -/
theorem stack_card : Fintype.card Stack=36 := by decide
end RiemannGaussian.SemiprimeD1StackRootSources
