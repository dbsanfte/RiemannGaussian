/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputBounds
import RiemannGaussian.SemiprimeD1StackWordBlockBounds
import RiemannGaussian.SemiprimeD1StackUnaryProductRaw

/-! # Physical marked first-input coefficient acquisition
The only inputs are original binary N, the original assignment, the actual
unary descriptor index and the actual side singleton. The literal checker
executes first. A marked successful row then reacquires its word and its
radix-position shift from the retained physical inputs and paid caches.
All coefficient arithmetic remains binary; only bounded offsets are unary.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInput
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace P
export SemiprimeD1StackPublicInput (Stack Label program initial assignment index output modulusKey)
end P
namespace B
export SemiprimeD1StackWordBlock (Label program)
end B
namespace F
export SemiprimeD1StackWordFit (Label program)
end F
namespace U
export SemiprimeD1StackUnaryProduct (Stack Label code entry)
end U
/-- Five private Boolean words; no derived number is an input cell. -/
inductive Aux where
  | side | widthTemplate | shifted | copyScratch | output
  deriving DecidableEq, Repr
/-- Complete literal private inventory, independent of the original input. -/
instance : Fintype Aux := Fintype.ofList
  [.side,.widthTemplate,.shifted,.copyScratch,.output] (by intro k; cases k <;> simp)
/-- All checker caches, five extractor allocations, four product roles and
five private words; the unused extractor-template shadow remains counted. -/
abbrev Stack := P.Stack ⊕ (Fin 5 ⊕ (U.Stack ⊕ Aux))
/-- Whole original checker bank retained by direct inclusion. -/
def checker : P.Stack → Stack := Sum.inl
/-- Allocated extractor role, including its unused template shadow. -/
def word : Fin 5 → Stack := fun k => .inr (.inl k)
/-- Actual offset-product roles. -/
def product : U.Stack → Stack := fun k => .inr (.inr (.inl k))
/-- Private physical word. -/
def aux : Aux → Stack := fun k => .inr (.inr (.inr k))
/-- Paid ell marker cache of the actual checker acquisition. -/
def ell : Stack := checker (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))
/-- Paid TRUE radix marker cache; this is not the signal-word width. -/
def radix : Stack := checker (.inl (.inl SemiprimeD1StackPublicInputWidth.radixKey))
/-- Real word extraction directly shares the paid signal-width template. -/
def blockStack (k : Fin 5) : Stack :=
  if k=1 then checker (.inl P.modulusKey) else word k
/-- The real fitter reuses only the extractor's empty counter and scratch. -/
def fitStack (k : Fin 5) : Stack :=
  if k=0 then aux .shifted else if k=1 then aux .widthTemplate
  else if k=4 then aux .output else word k
/-- Six static preserving-copy sources; no runtime role selector exists. -/
def copySource (kind : Fin 6) : Stack :=
  if kind=0 then checker P.assignment else if kind=1 then checker P.index
  else if kind=2 then radix else if kind=4 then word 4 else ell
/-- Each destination is an actual empty or explicitly retained word. -/
def copyTarget (kind : Fin 6) : Stack :=
  if kind=0 then word 0 else if kind=1 then product .multiplier
  else if kind=2 then product .multiplicand else if kind=3 then product .product
  else if kind=4 then aux .shifted else aux .widthTemplate
/-- Literal three-role preserving-copy wiring. -/
def copyStack (kind : Fin 6) (k : Fin 3) : Stack :=
  if k=0 then copySource kind else if k=1 then copyTarget kind else aux .copyScratch
/-- Finite local stages contain no decoded operand, width or offset. -/
inductive Control where
  | start | checked | side | zero | one | raw | extract | index | radix | multiply
  | offset | digit | shift | shiftZero | low | setOne | widthA | widthB | fit
  | clearRaw | clearWord | clearRadix | done | bad
  deriving DecidableEq, Repr
/-- Explicit complete local control inventory. -/
instance : Fintype Control := Fintype.ofList
  [.start,.checked,.side,.zero,.one,.raw,.extract,.index,.radix,.multiply,
   .offset,.digit,.shift,.shiftZero,.low,.setOne,.widthA,.widthB,.fit,
   .clearRaw,.clearWord,.clearRadix,.done,.bad] (by intro k; cases k <;> simp)
/-- Every included label is static before N and the actual assignment. -/
abbrev Label := Control ⊕ (P.Label ⊕ (B.Label ⊕ (U.Label ⊕ (F.Label ⊕ (Fin 6 × Fin 9)))))
/-- Literal local stage inclusion. -/
def ctl : Control → Label := Sum.inl
/-- Literal whole-checker label inclusion. -/
def checkerLabel : P.Label → Label := fun k => .inr (.inl k)
/-- Literal extractor label inclusion. -/
def blockLabel : B.Label → Label := fun k => .inr (.inr (.inl k))
/-- Literal unary-product label inclusion. -/
def productLabel : U.Label → Label := fun k => .inr (.inr (.inr (.inl k)))
/-- Literal final-fitting label inclusion. -/
def fitLabel : F.Label → Label := fun k => .inr (.inr (.inr (.inr (.inl k))))
/-- Literal preserving-copy label inclusion. -/
def copyLabel (kind : Fin 6) (k : Fin 9) : Label :=
  .inr (.inr (.inr (.inr (.inr (kind,k)))))
/-- One closed finite Boolean-stack instruction table. In particular, no
native digit extraction, multiplication, shift, fit or coefficient opcode occurs. -/
def program : Label → C.Instruction Stack Label
  | .inl .start => .call (checkerLabel .start) (ctl .checked)
  | .inl .checked => .base (.peek (checker P.output) (ctl .bad) (ctl .zero) (ctl .side))
  | .inl .side => .base (.peek (aux .side) (ctl .bad) (ctl .raw) (ctl .one))
  | .inl .zero => .base (.jump (ctl .widthA))
  | .inl .one => .base (.push (aux .shifted) true (ctl .widthA))
  | .inl .raw => .call (copyLabel 0 0) (ctl .extract)
  | .inl .extract => .call (blockLabel .start) (ctl .index)
  | .inl .index => .call (copyLabel 1 0) (ctl .radix)
  | .inl .radix => .call (copyLabel 2 0) (ctl .multiply)
  | .inl .multiply => .call (productLabel U.entry) (ctl .offset)
  | .inl .offset => .call (copyLabel 3 0) (ctl .digit)
  | .inl .digit => .call (copyLabel 4 0) (ctl .shift)
  | .inl .shift => .base (.pop (product .product) (ctl .low) (ctl .shiftZero) (ctl .shiftZero))
  | .inl .shiftZero => .base (.push (aux .shifted) false (ctl .shift))
  | .inl .low => .base (.pop (aux .shifted) (ctl .bad) (ctl .setOne) (ctl .bad))
  | .inl .setOne => .base (.push (aux .shifted) true (ctl .widthA))
  | .inl .widthA => .call (copyLabel 5 0) (ctl .widthB)
  | .inl .widthB => .call (copyLabel 5 0) (ctl .fit)
  | .inl .fit => .call (fitLabel .start) (ctl .clearRaw)
  | .inl .clearRaw => .base (.pop (word 0) (ctl .clearWord) (ctl .clearRaw) (ctl .clearRaw))
  | .inl .clearWord => .base (.pop (word 4) (ctl .clearRadix) (ctl .clearWord) (ctl .clearWord))
  | .inl .clearRadix => .base (.pop (product .multiplicand) (ctl .done) (ctl .clearRadix) (ctl .clearRadix))
  | .inl .done | .inl .bad => .base .halt
  | .inr (.inl k) => SemiprimeD1StackValidationLink.instruction checker checkerLabel (P.program k)
  | .inr (.inr (.inl k)) => SemiprimeD1StackValidationLink.instruction blockStack blockLabel (B.program k)
  | .inr (.inr (.inr (.inl k))) => SemiprimeD1StackMultiplierLink.instruction product productLabel (U.code k)
  | .inr (.inr (.inr (.inr (.inl k)))) => SemiprimeD1StackValidationLink.instruction fitStack fitLabel (F.program k)
  | .inr (.inr (.inr (.inr (.inr (kind,k))))) =>
      SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (copyLabel kind) (SemiprimeD1StackCopy.code k)
/-- Initial private bank contains only the physical descriptor-side singleton. -/
def privateInput (side : List Bool) : Fin 5 ⊕ (U.Stack ⊕ Aux) → List Bool
  | .inr (.inr .side) => side
  | _ => []
/-- Exactly four source words; every coefficient, metadata and work output is empty. -/
def initial (bits raw indexWord side : List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,
    Sum.elim (P.initial bits raw indexWord).data (privateInput side),[]⟩
/-- Every real block operand is distinct despite the direct template alias. -/
theorem block_injective : Function.Injective blockStack := by decide
/-- The five real fitter operands remain distinct. -/
theorem fit_injective : Function.Injective fitStack := by decide
/-- Each preserving-copy call has three genuinely distinct physical roles. -/
theorem copy_injective (kind : Fin 6) : Function.Injective (copyStack kind) := by
  fin_cases kind <;> decide
/-- Fixed genuine bit machine; descriptor acquisition remains caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine
  (checker (.inl SemiprimeD1StackPublicInputWidth.original)) (aux .output) (ctl .start) program
/-- Every allocated role, including the unused template shadow, is counted. -/
theorem stack_card : Fintype.card Stack=66 := by decide
/-- No unbounded metadata, coefficient or evaluator enters transient control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite
  (checker (.inl SemiprimeD1StackPublicInputWidth.original)) (aux .output) (ctl .start) program
/-- All physical data and return alphabets are finite before the input. -/
theorem all_alphabets_finite : ∀ k, Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite
  (checker (.inl SemiprimeD1StackPublicInputWidth.original)) (aux .output) (ctl .start) program
end RiemannGaussian.SemiprimeD1StackMarkedPublicInput
