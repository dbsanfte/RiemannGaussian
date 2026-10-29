/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryBootstrap
import RiemannGaussian.SemiprimeD1StackProcedureFragments

/-! # Original-input physical transform/radix acquisition
The original binary input is retained by the actual included bootstrap. Only
its small unary WIDTH is scaled/compared. R and its square are doubled and
quadrupled by literal marker writes; no native logarithm, power or division is
executed. The actual radix is acquired by consuming four R markers per output.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransform
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end Link
namespace Boot
export SemiprimeD1BinaryBootstrap (Stack Label code state done seenOne)
end Boot

/-- Eleven fixed Boolean data stacks; N remains on input in binary. -/
inductive Stack where
  | input | width | nonzero | threshold | radius | square | exponent
  | squareWork | thresholdWork | temporary | radix
  deriving DecidableEq,Repr
/-- Fixed literal stack catalogue. -/
instance : Fintype Stack where
  elems:={.input,.width,.nonzero,.threshold,.radius,.square,.exponent,
    .squareWork,.thresholdWork,.temporary,.radix}
  complete:=by intro k;cases k <;> simp

/-- Fixed local control for comparison, scaling and four-marker radix extraction. -/
inductive Local where
  | start | initSquare | copySquare | copyThreshold | compareThreshold | compareSquare
  | clearSuccess | clearFailure | radiusPop | radiusPush1 | radiusPush2
  | radiusRestore | radiusRestorePush | squarePop | squarePush1 | squarePush2
  | squarePush3 | squarePush4 | squareRestore | squareRestorePush | incExponent
  | radixStart | radixPop0 | radixPop1 | radixPop2 | radixPop3 | radixPush | halt
  deriving DecidableEq,Repr
/-- Fixed finite local instruction catalogue. -/
instance : Fintype Local where
  elems:={.start,.initSquare,.copySquare,.copyThreshold,.compareThreshold,.compareSquare,
    .clearSuccess,.clearFailure,.radiusPop,.radiusPush1,.radiusPush2,.radiusRestore,.radiusRestorePush,
    .squarePop,.squarePush1,.squarePush2,.squarePush3,.squarePush4,.squareRestore,.squareRestorePush,
    .incExponent,.radixStart,.radixPop0,.radixPop1,.radixPop2,.radixPop3,.radixPush,.halt}
  complete:=by intro k;cases k <;> simp

/-- All labels are fixed: local code, sixteen literal copies, bootstrap and four Copy instances. -/
abbrev Label := Local⊕(Fin 17⊕(Boot.Label⊕(Fin 4×Fin 9)))

/-- Fixed bootstrap operand inclusion. -/
def bootStack : Boot.Stack→Stack
  | .input => .input
  | .reverse => .temporary
  | .width => .width
  | .nonzero => .nonzero
/-- Fixed bootstrap code inclusion. -/
def bootLabel (pc:Boot.Label) : Label := .inr (.inr (.inl pc))
/-- Fixed sixteen-copy setup label, never an input-dependent loop counter in control. -/
def setupLabel (pc:Fin 17) : Label := .inr (.inl pc)
/-- Fixed Copy source operand. -/
def copyInput (mode:Fin 4) : Stack :=
  if mode=0 then .width else if mode=1 then .square else if mode=2 then .threshold else .radius
/-- Fixed Copy destination operand. -/
def copyOutput (mode:Fin 4) : Stack :=
  if mode=0 then .threshold else if mode=2 then .thresholdWork else .squareWork
/-- Literal three-stack Copy inclusion. -/
def copyStack (mode:Fin 4) (k:Fin 3) : Stack :=
  if k=0 then copyInput mode else if k=1 then copyOutput mode else .temporary
/-- Fixed Copy instruction inclusion. -/
def copyLabel (mode:Fin 4) (pc:Fin 9) : Label := .inr (.inr (.inr (mode,pc)))

/-- Complete actual instruction table; all tests inspect physical stack tops or fixed labels. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inr (.inl pc)) => Link.instruction bootStack bootLabel (Boot.code pc)
  | .inr (.inr (.inr (mode,pc))) =>
      Link.instruction (copyStack mode) (copyLabel mode) (SemiprimeD1StackCopy.code pc)
  | .inr (.inl index) =>
      if h:index.val<16 then
        .call (copyLabel 0 0) (setupLabel ⟨index.val+1,by omega⟩)
      else .base (.push .radius true (.inl .initSquare))
  | .inl .start => .call (bootLabel (.scan,false)) (setupLabel 0)
  | .inl .initSquare => .base (.push .square true (.inl .copySquare))
  | .inl .copySquare => .call (copyLabel 1 0) (.inl .copyThreshold)
  | .inl .copyThreshold => .call (copyLabel 2 0) (.inl .compareThreshold)
  | .inl .compareThreshold => .base (.pop .thresholdWork (.inl .clearSuccess) (.inl .compareSquare) (.inl .compareSquare))
  | .inl .compareSquare => .base (.pop .squareWork (.inl .clearFailure) (.inl .compareThreshold) (.inl .compareThreshold))
  | .inl .clearSuccess => .base (.pop .squareWork (.inl .radixStart) (.inl .clearSuccess) (.inl .clearSuccess))
  | .inl .clearFailure => .base (.pop .thresholdWork (.inl .radiusPop) (.inl .clearFailure) (.inl .clearFailure))
  | .inl .radiusPop => .base (.pop .radius (.inl .radiusRestore) (.inl .radiusPush1) (.inl .radiusPush1))
  | .inl .radiusPush1 => .base (.push .temporary true (.inl .radiusPush2))
  | .inl .radiusPush2 => .base (.push .temporary true (.inl .radiusPop))
  | .inl .radiusRestore => .base (.pop .temporary (.inl .squarePop) (.inl .radiusRestorePush) (.inl .radiusRestorePush))
  | .inl .radiusRestorePush => .base (.push .radius true (.inl .radiusRestore))
  | .inl .squarePop => .base (.pop .square (.inl .squareRestore) (.inl .squarePush1) (.inl .squarePush1))
  | .inl .squarePush1 => .base (.push .temporary true (.inl .squarePush2))
  | .inl .squarePush2 => .base (.push .temporary true (.inl .squarePush3))
  | .inl .squarePush3 => .base (.push .temporary true (.inl .squarePush4))
  | .inl .squarePush4 => .base (.push .temporary true (.inl .squarePop))
  | .inl .squareRestore => .base (.pop .temporary (.inl .incExponent) (.inl .squareRestorePush) (.inl .squareRestorePush))
  | .inl .squareRestorePush => .base (.push .square true (.inl .squareRestore))
  | .inl .incExponent => .base (.push .exponent true (.inl .copySquare))
  | .inl .radixStart => .call (copyLabel 3 0) (.inl .radixPop0)
  | .inl .radixPop0 => .base (.pop .squareWork (.inl .halt) (.inl .radixPop1) (.inl .radixPop1))
  | .inl .radixPop1 => .base (.pop .squareWork (.inl .halt) (.inl .radixPop2) (.inl .radixPop2))
  | .inl .radixPop2 => .base (.pop .squareWork (.inl .halt) (.inl .radixPop3) (.inl .radixPop3))
  | .inl .radixPop3 => .base (.pop .squareWork (.inl .halt) (.inl .radixPush) (.inl .radixPush))
  | .inl .radixPush => .base (.push .radix true (.inl .radixPop0))
  | .inl .halt => .base .halt

/-- One fixed actual finite machine whose ONLY initial input is binary N. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.input Stack.radix (.inl .start) program

/-- Actual original-input initial data; no dimension/counter answer is supplied. -/
def input (bits:List Bool) : Stack→List Bool
  | .input => bits
  | _ => []
/-- Actual start before executing the bootstrap call. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,input bits,[]⟩

/-- Bootstrap uses four distinct actual stack operands. -/
theorem bootStack_injective : Function.Injective bootStack := by decide
/-- Every Copy instance has three distinct actual operands. -/
theorem copyStack_injective (mode:Fin 4) : Function.Injective (copyStack mode) := by
  fin_cases mode <;> decide
/-- The fixed program has eleven Boolean data-stack names. -/
theorem stack_card : Fintype.card Stack=11 := by decide
/-- Every local/setup/component label totals 99 before every input. -/
theorem label_card : Fintype.card Label=99 := by decide
/-- Every data/return alphabet is finite, not merely the input alphabet. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.input Stack.radix (.inl .start) program
end RiemannGaussian.SemiprimeD1StackTransform
