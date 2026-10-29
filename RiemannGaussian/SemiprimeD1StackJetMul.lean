/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetPointBounds
import RiemannGaussian.SemiprimeD1StackFrame
/-! # Fixed physical dense-jet multiplication caller
A physical rank copy drives the descending output-index loop. Each coefficient
executes the literal closed routed point program. Real framing prepends the
acquired binary coefficient; the temporary word is then physically cleared.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackJetMul
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace P
export SemiprimeD1StackJetPoint (Stack Label program aux)
end P

/-- The fifty-three real point registers plus output and frame scratch. -/
abbrev Stack := P.Stack ⊕ Bool
/-- Literal dense-vector output register. -/
def output : Stack := .inr false
/-- Literal frame scratch register. -/
def scratch : Stack := .inr true
/-- The physical output-index counter is the point program's retained target. -/
def counter : Stack := .inl (P.aux .target)
/-- The real point output is consumed by framing and cleanup. -/
def coefficient : Stack := .inl (P.aux .acc)
/-- Real outer rank-copy inclusion. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inl (P.aux .rank) else if k=1 then counter else .inl (P.aux .copyWork)
/-- Real binary coefficient framing, preserving the coefficient for explicit cleanup. -/
def frameStack (k : Fin 3) : Stack :=
  if k=0 then coefficient else if k=1 then output else scratch

/-- Fixed finite outer loop and literal component-program labels. -/
inductive Label where
  | start | copyRank | loop | callPoint | callFrame | cons | clear | done
  | copy (pc : Fin 9)
  | point (pc : P.Label)
  | frame (pc : Fin 11)
  deriving DecidableEq,Fintype

/-- Actual dense-jet multiplication, with no coefficient/route/count callback. -/
def program : Label → C.Instruction Stack Label
  | .start => .base (.push output false .copyRank)
  | .copyRank => .call (.copy 0) .loop
  | .loop => .base (.pop counter .done .callPoint .callPoint)
  | .callPoint => .call (.point .start) .callFrame
  | .callFrame => .call (.frame 0) .cons
  | .cons => .base (.push output true .clear)
  | .clear => .base (.pop coefficient .loop .clear .clear)
  | .done => .base .halt
  | .copy pc => SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .point pc => SemiprimeD1StackValidationLink.instruction Sum.inl Label.point (P.program pc)
  | .frame pc => SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)

/-- The literal cache/work state has no prepared target or coefficient answer. -/
def inputData (a b axes width rank : List Bool) : Stack → List Bool
  | .inl k => SemiprimeD1StackJetPoint.inputData a b axes width rank [] k
  | .inr _ => []
/-- Actual entry with cleared flags, return frames and all work/output stacks. -/
def initial (a b axes width rank : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,inputData a b axes width rank,[]⟩
/-- Actual fixed compiled finite-stack machine. Context acquisition is a caller stage. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inl (P.aux .a)) output Label.start program

/-- Rank-copy operands have distinct physical addresses. -/
theorem copyStack_injective : Function.Injective copyStack := by decide
/-- Framing operands have distinct physical addresses. -/
theorem frameStack_injective : Function.Injective frameStack := by decide

end RiemannGaussian.SemiprimeD1StackJetMul
