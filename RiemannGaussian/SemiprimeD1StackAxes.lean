/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformBounds
import RiemannGaussian.SemiprimeD1StackValidationLink

/-! # Fixed original-input axes/depth program
The original exponent is copied and consumed in physical pairs. Actual copy
and move loops double both axes; an odd marker doubles only the second axis.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxes
namespace Meta
export SemiprimeD1StackTransform (Stack Label program input initial)
end Meta
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace LinkB
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end LinkB
namespace LinkC
export SemiprimeD1StackValidationLink (instruction Rel run_rel)
end LinkC
/-- Fixed original metadata plus first-axis, second-axis and depth outputs. -/
abbrev Stack := Meta.Stack⊕Fin 3
/-- Fixed local finite control, including three literal doubling continuations. -/
inductive Local where
  | start | ready | initQ | copyE | first | second | copyDepth | popDepth | halt
  | copyAxis (mode:Fin 3) | moveAxis (mode:Fin 3) | pushAxis (mode:Fin 3)
  deriving DecidableEq,Repr
/-- Exhaustive static local instruction labels. -/
instance : Fintype Local where
  elems:={.start,.ready,.initQ,.copyE,.first,.second,.copyDepth,.popDepth,.halt}∪
    Finset.univ.image Local.copyAxis∪Finset.univ.image Local.moveAxis∪Finset.univ.image Local.pushAxis
  complete:=by intro k;cases k <;> simp
/-- Metadata plus four real Copy inclusions; none depends on the input. -/
abbrev Label := Local⊕(Meta.Label⊕(Fin 4×Fin 9))
/-- Metadata label inclusion. -/
def metaLabel (pc:Meta.Label) : Label := .inr (.inl pc)
/-- Actual copy source: E, P, Q, E. -/
def copyInput (mode:Fin 4) : Stack :=
  if mode=1 then .inr 0 else if mode=2 then .inr 1 else .inl .exponent
/-- Actual copy destination: exponent work, move work, move work, depth. -/
def copyOutput (mode:Fin 4) : Stack :=
  if mode=0 then .inl .squareWork else if mode=3 then .inr 2 else .inl .thresholdWork
/-- Real three-role Copy operand map. -/
def copyStack (mode:Fin 4) (k:Fin 3) : Stack :=
  if k=0 then copyInput mode else if k=1 then copyOutput mode else .inl .temporary
/-- Static Copy labels. -/
def copyLabel (mode:Fin 4) (pc:Fin 9) : Label := .inr (.inr (mode,pc))
/-- First doubling selects P; both other continuations select Q. -/
def axis (mode:Fin 3) : Stack := if mode=0 then .inr 0 else .inr 1
/-- Actual real Copy operand for a doubling. -/
def axisCopy (mode:Fin 3) : Fin 4 := if mode=0 then 1 else 2
/-- Static successor after each physical doubling. -/
def afterAxis (mode:Fin 3) : Label :=
  if mode=0 then .inl (.copyAxis 1) else if mode=1 then .inl .first else .inl .copyDepth
/-- ONE fixed literal program; no power/division or desired-axis instruction. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => LinkC.instruction Sum.inl metaLabel (Meta.program pc)
  | .inr (.inr (mode,pc)) => LinkB.instruction (copyStack mode) (copyLabel mode) (SemiprimeD1StackCopy.code pc)
  | .inl .start => .call (metaLabel (.inl .start)) (.inl .ready)
  | .inl .ready => .base (.push (.inr 0) true (.inl .initQ))
  | .inl .initQ => .base (.push (.inr 1) true (.inl .copyE))
  | .inl .copyE => .call (copyLabel 0 0) (.inl .first)
  | .inl .first => .base (.pop (.inl .squareWork) (.inl .copyDepth) (.inl .second) (.inl .second))
  | .inl .second => .base (.pop (.inl .squareWork) (.inl (.copyAxis 2)) (.inl (.copyAxis 0)) (.inl (.copyAxis 0)))
  | .inl (.copyAxis mode) => .call (copyLabel (axisCopy mode) 0) (.inl (.moveAxis mode))
  | .inl (.moveAxis mode) => .base (.pop (.inl .thresholdWork) (afterAxis mode) (.inl (.pushAxis mode)) (.inl (.pushAxis mode)))
  | .inl (.pushAxis mode) => .base (.push (axis mode) true (.inl (.moveAxis mode)))
  | .inl .copyDepth => .call (copyLabel 3 0) (.inl .popDepth)
  | .inl .popDepth => .base (.pop (.inr 2) (.inl .halt) (.inl .halt) (.inl .halt))
  | .inl .halt => .base .halt
/-- Fixed finite machine before every input. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl .input) (.inr 2) (.inl .start) program
/-- The only initial data are original binary N. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (Meta.input bits) (fun _=>[])
/-- Actual unprepared start. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,input bits,[]⟩
/-- Every Copy uses disjoint input/output/scratch roles. -/
theorem copyStack_injective (mode:Fin 4) : Function.Injective (copyStack mode) := by fin_cases mode <;> decide
/-- Fourteen fixed Boolean data stacks. -/
theorem stack_card : Fintype.card Stack=14 := by decide
/-- One hundred fifty-three fixed labels, including all nested procedures. -/
theorem label_card : Fintype.card Label=153 := by decide
/-- Every alphabet is finite, including the actual return tags. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inl .input) (.inr 2) (.inl .start) program
end RiemannGaussian.SemiprimeD1StackAxes
