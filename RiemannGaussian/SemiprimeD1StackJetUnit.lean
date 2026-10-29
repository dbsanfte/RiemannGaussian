/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContextBounds
import RiemannGaussian.SemiprimeD1StackJetAddExecution
/-! # Literal physical dense-jet unit acquisition
Six literal bit pushes prepare raw scalar-one and zero vectors. The actual dense
adder canonicalizes them at the physically cached rank/precision; no unit vector
or coefficient answer is an input. Context caches come from the actual supplier.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
namespace RiemannGaussian.SemiprimeD1StackJetUnit
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace A
export SemiprimeD1StackJetAdd (Stack Label program store)
end A
/-- The literal dense-adder register bank is reused directly. -/
abbrev Stack := A.Stack
/-- Physically retained precision markers. -/
def widthCache : Stack := .inl (.inr false)
/-- Physically retained rank markers. -/
def rankCache : Stack := .inr .rank
/-- Real dense-unit output tape. -/
def output : Stack := .inr .output

/-- Literal seed/call/halt labels, before all context inputs. -/
inductive Label where
  | seed0 | seed1 | seed2 | seed3 | seed4 | seed5 | callAdd | done
  | add (pc : A.Label)
  deriving DecidableEq,Fintype

/-- Fixed literal seeding and actual dense modular addition. -/
def program : Label → C.Instruction Stack Label
  | .seed0 => .base (.push (.inr .leftTape) false .seed1)
  | .seed1 => .base (.push (.inr .leftTape) false .seed2)
  | .seed2 => .base (.push (.inr .leftTape) true .seed3)
  | .seed3 => .base (.push (.inr .leftTape) true .seed4)
  | .seed4 => .base (.push (.inr .leftTape) true .seed5)
  | .seed5 => .base (.push (.inr .rightTape) false .callAdd)
  | .callAdd => .call (.add .start) .done
  | .done => .base .halt
  | .add pc => SemiprimeD1StackValidationLink.instruction id Label.add (A.program pc)

/-- Declarative cache/vector state, with every unlisted work register empty. -/
def bank (width rank a b out : List Bool) : Stack → List Bool :=
  A.store [] [] [] [] width [] a b rank [] [] out [] [] []
/-- Actual entry has only physical context caches, not a unit/zero vector answer. -/
def initial (width rank : List Bool) : C.State Stack Label :=
  ⟨some .seed0,none,none,bank width rank [] [] [],[]⟩
/-- Actual fixed finite-stack unit-vector supplier. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine widthCache output Label.seed0 program

end RiemannGaussian.SemiprimeD1StackJetUnit
