/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridView
/-! # Exact original-grid output bank and physical rational/slope codecs
These are proof-side boundary specifications for the already literal source,
not supplied geometry, multiplicity, rational output or operation-stream inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridEncoding
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
/-- Actual original grid size, used only in semantic statements and own resource bounds. -/
def gridSize (a:Nat) :Nat:=2^(a+1)
/-- Exact legacy register-word specification; inactive work registers are actually empty. -/
def registerWord (a t:Nat) (old:SemiprimeD1RecoveryGridBits.Report) :Reg→Option SemiprimeRationalBits.RationalWord
  | .two=>some SemiprimeD1RecoveryGridBits.twoWord
  | .center=>some old.center | .alpha=>some old.alpha
  | .node=>some (SemiprimeD1RecoveryGridBits.index a t).word
  | .gridNum=>some old.grid.numerator | .gridDen=>some old.grid.denominator
  | .scalar=>some old.scalar | .argument=>some old.argument | _=>none
/-- Every actual stopped register word, including all16 physically cleared transient words. -/
def registerBank (a t:Nat) (old:SemiprimeD1RecoveryGridBits.Report) (k:Reg×Bool) :List Bool:=
  match registerWord a t old k.1 with
  | none=>[] | some word=>if k.2 then word.denominator else signed word
/-- Exact complete source stop retains originals, actual h, actual a+2 template and all original grid rational bytes. -/
def resultWords (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :Words:=
  let old:=SemiprimeD1RecoveryGridBits.acquire width a M u t
  {originals (List.replicate a true) (List.replicate M true) (List.replicate u true) tword width with division:=SemiprimeD1StackUnaryDivmod.contents [] [] [] [] (List.replicate (SemiprimeD1TaperedLoss.height M u) true) [], registers:=registerBank a t.val old, auxiliary:=Function.update (Function.update (originalAux (List.replicate a true) (List.replicate M true) (List.replicate u true) tword) .indexTemplate (List.replicate (a+2) false)) .slopes (slopeTape old.grid.slopes)}
/-- All104 literal output words are specified, including every empty shadow and every physically cleared helper. -/
def result (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :Stack→List Bool:=bank (resultWords a M u t tword width)
/-- Whole true halt has both flags and actual internal returns clear. -/
def done (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :C.State Stack Label:=⟨none,none,none,result a M u t tword width,[]⟩
/-- Proof-side interpretation of two actual rational words; every sign and high-zero byte is retained. -/
def outputWord (data:Stack→List Bool) (r:Reg) :SemiprimeRationalBits.RationalWord:=
  ⟨⟨(data (reg r false)).head?.getD false,(data (reg r false)).tail⟩,data (reg r true)⟩
/-- Exact original grid numerator word, including legacy width and sign. -/
theorem numerator_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .gridNum=(SemiprimeD1RecoveryGridBits.acquire width a M u t).grid.numerator:=rfl
/-- Exact original grid denominator word, including legacy width and sign. -/
theorem denominator_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .gridDen=(SemiprimeD1RecoveryGridBits.acquire width a M u t).grid.denominator:=rfl
/-- Exact original Ezero normalized and fitted byte word. -/
theorem scalar_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .scalar=(SemiprimeD1RecoveryGridBits.acquire width a M u t).scalar:=rfl
/-- Exact original local argument normalized and fitted byte word. -/
theorem argument_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .argument=(SemiprimeD1RecoveryGridBits.acquire width a M u t).argument:=rfl
/-- Exact original centre word includes the literal oneWord a0 case, even W0. -/
theorem center_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .center=(SemiprimeD1RecoveryGridBits.acquire width a M u t).center:=rfl
/-- Exact original alpha byte word is distinct from the independent true geometric binary alpha. -/
theorem alpha_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    outputWord (result a M u t tword width) .alpha=(SemiprimeD1RecoveryGridBits.acquire width a M u t).alpha:=rfl
/-- Every repeated slope word appears in original forward q order, with no occurrence discarded. -/
theorem slopes_original (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    result a M u t tword width (aux .slopes)=slopeTape (SemiprimeD1RecoveryGridBits.acquire width a M u t).grid.slopes:=rfl
/-- Original metadata/index words and actual W are retained literally at the whole-grid boundary. -/
theorem originals_retained (a M u:Nat) (t:Fin (gridSize a)) (tword width:List Bool) :
    result a M u t tword width (aux .originalA)=List.replicate a true ∧
    result a M u t tword width (aux .originalM)=List.replicate M true ∧
    result a M u t tword width (aux .originalU)=List.replicate u true ∧
    result a M u t tword width (aux .originalT)=tword ∧ result a M u t tword width template=width:=⟨rfl,rfl,rfl,rfl,rfl⟩
/-- All true grid and width values are explicitly paid by actual materialized dimensions and metadata. -/
def resource (a M u:Nat) (tword width:List Bool) :Nat:=a+M+u+tword.length+width.length+gridSize a+1
end RiemannGaussian.SemiprimeD1StackRecoveryGridEncoding
