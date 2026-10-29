/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprLiteralBounds
import RiemannGaussian.SemiprimeD1StackResidueAddBounds
import RiemannGaussian.SemiprimeD1StackResidueSubBounds
import RiemannGaussian.SemiprimeD1StackResidueMulBounds
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackRecursiveCallTrace
/-! # Closed physical prefix arithmetic expression evaluator
Only physical code/cache/operand words enter the program. Recursive evaluation
uses real finite-label call/return frames, framed saved values, and the literal
complete Add/Sub/Mul procedures. No Expr/Nat/List/function is stored in control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExpr
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Lit
export SemiprimeD1StackExprLiteral (Stack Label program inputCode output ctl input)
end Lit
namespace Add
export SemiprimeD1StackResidueAdd (Stack Label program modulus output input initial)
end Add
namespace Sub
export SemiprimeD1StackResidueSub (Stack Label program modulus output input initial)
end Sub
namespace Mul
export SemiprimeD1StackResidueMul (Stack Label program modulus output input initial)
end Mul
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field

/-- Only three fixed operator cases are carried by continuation labels. -/
inductive Op | add | sub | mul deriving DecidableEq,Repr,Inhabited
instance : Fintype Op where
  elems := {.add,.sub,.mul}
  complete := by intro op;cases op <;> simp
/-- Shared physical roles and disjoint complete private component banks. -/
inductive Stack where
  | code | modulus | saved | result | left | right | flag | scratch
  | literal (k : Lit.Stack) | addition (k : Add.Stack)
  | subtraction (k : Sub.Stack) | multiplication (k : Mul.Stack)
  deriving DecidableEq,Fintype
/-- Fixed real recursive and component locations, independent of syntax size. -/
inductive Label where
  | start | eval | secondLow | secondHigh | literalCall | returnPC | done | bad
  | begin (op : Op) | saveLeft (op : Op) | clearLeft (op : Op)
  | rightEval (op : Op) | copyRight (op : Op) | clearRight (op : Op)
  | readLeft (op : Op) | checkLeft (op : Op) | applyOp (op : Op)
  | literal (pc : Lit.Label) | addition (pc : Add.Label)
  | subtraction (pc : Sub.Label) | multiplication (pc : Mul.Label)
  | frame (pc : Fin 11) | copy (pc : Fin 9) | field (pc : Field.Label)
  deriving DecidableEq,Fintype

/-- Literal input/cache/output share the actual caller's roles, not copies or getters. -/
def literalStack (k : Lit.Stack) : Stack :=
  if k=Lit.inputCode then .code else
  if k=.inl SemiprimeD1StackExprLiteral.Fit.template then .modulus else
  if k=Lit.output then .result else .literal k
/-- The real first addition operand. -/
def addLeft : Add.Stack := .inl .left
/-- The real second addition operand. -/
def addRight : Add.Stack := .inl .right
/-- Actual addition wiring with all other roles private. -/
def addStack (k : Add.Stack) : Stack :=
  if k=addLeft then .left else if k=addRight then .right else
  if k=Add.modulus then .modulus else if k=Add.output then .result else .addition k
/-- The real first subtraction operand. -/
def subLeft : Sub.Stack := .inl .left
/-- The real second subtraction operand. -/
def subRight : Sub.Stack := .inr (.inl .right)
/-- Actual subtraction wiring; both internal modulus copies remain real operations. -/
def subStack (k : Sub.Stack) : Stack :=
  if k=subLeft then .left else if k=subRight then .right else
  if k=Sub.modulus then .modulus else if k=Sub.output then .result else .subtraction k
/-- The real first multiplication operand. -/
def mulLeft : Mul.Stack := .inl SemiprimeD1StackResidueMul.M.input
/-- The real second multiplication operand. -/
def mulRight : Mul.Stack := .inl SemiprimeD1StackResidueMul.M.factor
/-- Actual multiplication wiring, including its real restoring divider. -/
def mulStack (k : Mul.Stack) : Stack :=
  if k=mulLeft then .left else if k=mulRight then .right else
  if k=Mul.modulus then .modulus else if k=Mul.output then .result else .multiplication k
/-- Actual left-result frame append into the physical saved-value stack. -/
def frameStack (k : Fin 3) : Stack := if k=0 then .result else if k=1 then .saved else .scratch
/-- Actual right-result copy into its arithmetic operand slot. -/
def copyStack (k : Fin 3) : Stack := if k=0 then .result else if k=1 then .right else .scratch
/-- Actual saved-left field parser, with a physically produced validity bit. -/
def fieldStack : Field.Stack→Stack
  | .inl .input=>.saved | .inl .scratch=>.scratch | .inl .output=>.left | .inr _=>.flag

/-- ONE closed instruction table. Recursive calls really target this same .eval. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call .eval .done
  | .eval=>.base (.pop .code .bad .secondLow .secondHigh)
  | .secondLow=>.base (.pop .code .bad .literalCall (.begin .add))
  | .secondHigh=>.base (.pop .code .bad (.begin .sub) (.begin .mul))
  | .literalCall=>.call (.literal (Lit.ctl .fieldCall)) .returnPC
  | .begin op=>.call .eval (.saveLeft op)
  | .saveLeft op=>.call (.frame 0) (.clearLeft op)
  | .clearLeft op=>.base (.pop .result (.rightEval op) (.clearLeft op) (.clearLeft op))
  | .rightEval op=>.call .eval (.copyRight op)
  | .copyRight op=>.call (.copy 0) (.clearRight op)
  | .clearRight op=>.base (.pop .result (.readLeft op) (.clearRight op) (.clearRight op))
  | .readLeft op=>.call (.field (Field.active .tagPop (none,false))) (.checkLeft op)
  | .checkLeft op=>.base (.pop .flag .bad .bad (.applyOp op))
  | .applyOp .add=>.call (.addition .start) .returnPC
  | .applyOp .sub=>.call (.subtraction .start) .returnPC
  | .applyOp .mul=>.call (.multiplication .start) .returnPC
  | .returnPC=>.ret
  | .done | .bad=>.base .halt
  | .literal pc=>SemiprimeD1StackValidationLink.instruction literalStack Label.literal (Lit.program pc)
  | .addition pc=>SemiprimeD1StackValidationLink.instruction addStack Label.addition (Add.program pc)
  | .subtraction pc=>SemiprimeD1StackValidationLink.instruction subStack Label.subtraction (Sub.program pc)
  | .multiplication pc=>SemiprimeD1StackValidationLink.instruction mulStack Label.multiplication (Mul.program pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)

/-- Exact shared-payload view; all actual private component stacks are empty. -/
def bank (code cached saved result left right flag scratch : List Bool) : Stack→List Bool
  | .code=>code | .modulus=>cached | .saved=>saved | .result=>result
  | .left=>left | .right=>right | .flag=>flag | .scratch=>scratch | _=>[]
/-- Prepared physical syntax/cache data, without a decoded expression argument. -/
def input (code cached : List Bool) : Stack→List Bool := bank code cached [] [] [] [] [] []
/-- Closed actual entry for physical code and cached modulus alone. -/
def initial (code cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,input code cached,[]⟩
/-- Actual finite machine; supplying the encoded syntax/cache is caller work. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.code Stack.result .start program
/-- Every stack alphabet, including real return tags, is genuinely finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.code Stack.result Label.start program
/-- No input-sized syntax, natural or closure occurs in internal machine control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.code Stack.result Label.start program
/-- The literal data-stack inventory is fixed before all expressions and moduli. -/
theorem stack_card : Fintype.card Stack=75 := by decide
end RiemannGaussian.SemiprimeD1StackExpr
