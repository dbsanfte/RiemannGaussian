/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedRootMetadataOriginal
import RiemannGaussian.SemiprimeD1StackRadixDigitExecution
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual packed count/sum acquisition from N and its acquired scalar
Only binary N and the actual contraction scalar occupy the two input words.
The real metadata source acquires the digit width from N. Two actual radix
sources obtain compact low/high blocks. The original-N-only counter caller
must still supply its actually acquired scalar; no scalar acquisition is
asserted here. No count, sum, factor, decoded width or digit answer is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadout
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackPackedRootMetadata (Stack Label program input boot aux)
end M
namespace D
export SemiprimeD1StackRadixDigit (Stack Label program store)
end D
/-- Exactly three additional retained scalar/count/sum words. -/
inductive Aux where | scalar | count | sum deriving DecidableEq,Repr
/-- Literal enumeration before every original input and scalar. -/
instance auxFintype : Fintype Aux := Fintype.ofList [.scalar,.count,.sum] (by intro k;cases k <;> simp)
/-- All22 words include every retained metadata and all six radix-source roles. -/
abbrev Stack := M.Stack⊕(D.Stack⊕Aux)
/-- Entire real metadata-source allocation is retained. -/
def metadata (k : M.Stack) : Stack := .inl k
/-- Entire actual radix-digit source allocation. -/
def digit (k : D.Stack) : Stack := .inr (.inl k)
/-- Actual retained scalar and newly computed moment words. -/
def aux (k : Aux) : Stack := .inr (.inr k)
/-- Original binary N input role. -/
def originalInput : Stack := metadata (M.boot .input)
/-- Actual acquired scalar role, not an input moment/factor oracle. -/
def scalarInput : Stack := aux .scalar
/-- Six literal preserving-copy routes: width/value/output for each of two digits. -/
inductive Copy where | width (high : Bool) | scalar (high : Bool) | output (high : Bool)
  deriving DecidableEq,Repr,Fintype
/-- Every copy restores the same genuinely empty metadata scratch. -/
def copyStack (site : Copy) (k : Fin 3) : Stack :=
  if k=0 then match site with
    | .width _ => metadata (M.boot .width)
    | .scalar _ => scalarInput
    | .output _ => digit .output
  else if k=1 then match site with
    | .width _ => digit .width
    | .scalar _ => digit .input
    | .output high => aux (if high then .sum else .count)
  else metadata (M.aux .copyScratch)
/-- Finite block selectors only; no width, offset, value or clock enters control. -/
inductive Control where
  | start | copyWidth (high : Bool) | copyScalar (high : Bool) | seedIndex
  | acquire (high : Bool) | copyOutput (high : Bool) | clearOutput (high : Bool) | done
  deriving DecidableEq,Repr,Fintype
/-- Complete fixed finite control and included real-source labels. -/
abbrev Label := Control⊕(M.Label⊕(D.Label⊕(Copy×Fin 9)))
/-- Fixed enclosing program stage. -/
def ctl : Control→Label := Sum.inl
/-- Actual metadata-source inclusion. -/
def metadataLabel (pc : M.Label) : Label := .inr (.inl pc)
/-- Actual six-word radix-source inclusion. -/
def digitLabel (pc : D.Label) : Label := .inr (.inr (.inl pc))
/-- Actual preserving-copy inclusion. -/
def copyLabel (site : Copy) (pc : Fin 9) : Label := .inr (.inr (.inr (site,pc)))
/-- Literal next source after copying the current scalar. -/
def afterScalar (high : Bool) : Label := if high then ctl .seedIndex else ctl (.acquire false)
/-- Literal next moment/finish after physically draining a real digit output. -/
def afterClear (high : Bool) : Label := if high then ctl .done else ctl (.copyWidth true)
/-- Fixed actual N-width source, two radix acquisitions and all six paid copies. -/
def program : Label→C.Instruction Stack Label
  | .inl .start => .call (metadataLabel (.local .start)) (ctl (.copyWidth false))
  | .inl (.copyWidth high) => .call (copyLabel (.width high) 0) (ctl (.copyScalar high))
  | .inl (.copyScalar high) => .call (copyLabel (.scalar high) 0) (afterScalar high)
  | .inl .seedIndex => .base (.push (digit .index) true (ctl (.acquire true)))
  | .inl (.acquire high) => .call (digitLabel .start) (ctl (.copyOutput high))
  | .inl (.copyOutput high) => .call (copyLabel (.output high) 0) (ctl (.clearOutput high))
  | .inl (.clearOutput high) => .base (.pop (digit .output) (afterClear high) (ctl (.clearOutput high)) (ctl (.clearOutput high)))
  | .inl .done => .base .halt
  | .inr (.inl pc) => SemiprimeD1StackValidationLink.instruction metadata metadataLabel (M.program pc)
  | .inr (.inr (.inl pc)) => SemiprimeD1StackValidationLink.instruction digit digitLabel (D.program pc)
  | .inr (.inr (.inr (site,pc))) =>
    SemiprimeD1StackMultiplierLink.instruction (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
/-- Exact complete three-bank payload, without discarded shadows or helpers. -/
def bank (m : M.Stack→List Bool) (d : D.Stack→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  Sum.elim m (Sum.elim d u)
/-- Actual additional three-word payload. -/
def words (scalar count sum : List Bool) : Aux→List Bool
  | .scalar => scalar | .count => count | .sum => sum
/-- Precisely N and the acquired scalar are initially physically populated. -/
def input (bits scalar : List Bool) : Stack→List Bool := bank (M.input bits) (fun _ => []) (words scalar [] [])
/-- Genuine two-word prepared front door, before real width acquisition. -/
def initial (bits scalar : List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits scalar,[]⟩
/-- Fixed finite machine; its prepared entry contains the separately acquired scalar word. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .sum) (ctl .start) program
/-- Every retained, private and output data word is counted. -/
theorem stack_card : Fintype.card Stack=22 := by decide
/-- Entire real metadata bank has no aliases. -/
theorem metadata_injective : Function.Injective metadata := Sum.inl_injective
/-- All six actual radix operands are distinct. -/
theorem digit_injective : Function.Injective digit := by intro a b h;exact Sum.inl_injective (Sum.inr_injective h)
/-- Each real preserving copy has three physically distinct roles. -/
theorem copy_injective (site : Copy) : Function.Injective (copyStack site) := by cases site <;> rename_i high <;> cases high <;> decide
/-- All physical data and saved-return alphabets are fixed finite before N. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Internal state contains only finite flags and literal block/source labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPackedMomentReadout
