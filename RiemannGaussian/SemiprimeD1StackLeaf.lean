/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexProductExecution
import RiemannGaussian.SemiprimeD1StackAssignmentEnumerationBounds
/-! # Fixed physical original-header eager leaf contraction
The literal procedure acquires rank and precision, acquires the assignment width
from its binary word, materializes its actual assignment catalogue, and parses
that catalogue. Every assignment executes the actual parsed vertex product and
actual dense addition. No leaf, assignment, tensor entry or coefficient callback
occurs in the executed instruction table.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeaf
namespace P
export SemiprimeD1StackVertexProduct (Stack Label program main contextStack axes rank width product aux)
end P
namespace A
export SemiprimeD1StackJetAdd (Stack Label program Aux)
end A
namespace E
export SemiprimeD1StackAssignmentLoop (Stack Label code control)
end E
namespace U
export SemiprimeD1StackAdder (Stack)
export SemiprimeD1StackUnaryCounter (Label code)
end U
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F

/-- Literal outer-loop data roles; each is an actual Boolean stack. -/
inductive Aux where
  | widthBits | catalogue | sum | sumResult | valid | fieldScratch | copyWork
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList
  [.widthBits,.catalogue,.sum,.sumResult,.valid,.fieldScratch,.copyWork]
  (by intro k; cases k <;> simp)

/-- Fixed component banks, independent of every numeric input. -/
abbrev Stack := P.Stack ⊕ (A.Stack ⊕ (E.Stack ⊕ (U.Stack ⊕ Aux)))
/-- Physical embedding of the whole literal product procedure. -/
def productStack : P.Stack→Stack := Sum.inl
/-- Unaliased dense-sum work bank. -/
def addWork (k : A.Stack) : Stack := .inr (.inl k)
/-- Unaliased assignment-enumeration work bank. -/
def enumerationWork (k : E.Stack) : Stack := .inr (.inr (.inl k))
/-- Actual binary-to-unary assignment-width work bank. -/
def unaryStack (k : U.Stack) : Stack := .inr (.inr (.inr (.inl k)))
/-- Literal caller storage. -/
def aux (k : Aux) : Stack := .inr (.inr (.inr (.inr k)))
/-- Original encoded axes, retained by the actual context and product calls. -/
def axes : Stack := productStack P.axes
/-- Original binary precision, retained by the actual context acquisition. -/
def precisionBits : Stack := productStack (P.aux .precisionBits)
/-- Original literal vertex-record tape, retained by every product call. -/
def vertices : Stack := productStack (P.aux .verticesCache)
/-- Current actual assignment field, cleared between catalogue records. -/
def assignment : Stack := productStack (P.aux .assignment)
/-- Physical context acquisition shares the product's actual rank/precision caches. -/
def contextStack (k : SemiprimeD1StackJetContext.Stack) : Stack := productStack (P.contextStack k)
/-- Actual dense-adder operands are the product and reached sum buffers. -/
def addStack (k : A.Stack) : Stack :=
  if k=SemiprimeD1StackJetUnit.widthCache then productStack P.width
  else if k=SemiprimeD1StackJetUnit.rankCache then productStack P.rank
  else if k=.inr .leftTape then productStack P.product
  else if k=.inr .rightTape then aux .sum
  else if k=.inr .output then aux .sumResult else addWork k
/-- The real enumeration output is the catalogue consumed by the outer loop. -/
def enumerationStack : E.Stack→Stack
  | .output => aux .catalogue
  | k => enumerationWork k
/-- Real parser reads the acquired catalogue directly into the product assignment. -/
def fieldStack : F.Stack→Stack
  | .inl .input => aux .catalogue
  | .inl .scratch => aux .fieldScratch
  | .inl .output => assignment
  | .inr _ => aux .valid
/-- Two literal physical copies: binary width to its acquisition procedure, and
actual newly computed sum to the next reached accumulator. -/
def copyStack (sum : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if sum then aux .sumResult else aux .widthBits)
  else if k=1 then (if sum then aux .sum else unaryStack .left)
  else aux .copyWork

/-- Finite caller labels and literal included procedures. -/
inductive Label where
  | start | widthCopy | widthUnary | makeZero | pushZero | initializeSum
  | enumerate | catalogueTag | parse | parsed | callProduct | callAdd
  | copySum | clearSumResult | clearAssignment | done | abort
  | context (pc : SemiprimeD1StackJetContext.Label)
  | unary (pc : U.Label)
  | enumeration (pc : E.Label)
  | product (pc : P.Label)
  | add (pc : A.Label)
  | field (pc : F.Label)
  | copy (sum : Bool) (pc : Fin 9)
  deriving DecidableEq,Fintype

/-- Actual closed leaf program. Every variable-sized loop is driven by physical
input/counter/field bytes and actual included calls with real return frames. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label
  | .start => .call (.context .start) .widthCopy
  | .widthCopy => .call (.copy false 0) .widthUnary
  | .widthUnary => .call (.unary .reverse) .makeZero
  | .makeZero => .base (.pop (unaryStack .output) .initializeSum .pushZero .pushZero)
  | .pushZero => .base (.push (enumerationWork .word) false .makeZero)
  | .initializeSum => .base (.push (aux .sum) false .enumerate)
  | .enumerate => .call (.enumeration (E.control .bodyCall)) .catalogueTag
  | .catalogueTag => .base (.pop (aux .catalogue) .done .done .parse)
  | .parse => .call (.field (F.active .tagPop (none,false))) .parsed
  | .parsed => .base (.pop (aux .valid) .abort .abort .callProduct)
  | .callProduct => .call (.product .prepared) .callAdd
  | .callAdd => .call (.add .start) .copySum
  | .copySum => .call (.copy true 0) .clearSumResult
  | .clearSumResult => .base (.pop (aux .sumResult) .clearAssignment .clearSumResult .clearSumResult)
  | .clearAssignment => .base (.pop assignment .catalogueTag .clearAssignment .clearAssignment)
  | .done | .abort => .base .halt
  | .context pc => SemiprimeD1StackValidationLink.instruction contextStack Label.context (SemiprimeD1StackJetContext.program pc)
  | .unary pc => SemiprimeD1StackMultiplierLink.instruction unaryStack Label.unary (U.code pc)
  | .enumeration pc => SemiprimeD1StackValidationLink.instruction enumerationStack Label.enumeration (E.code pc)
  | .product pc => SemiprimeD1StackValidationLink.instruction productStack Label.product (P.program pc)
  | .add pc => SemiprimeD1StackValidationLink.instruction addStack Label.add (A.program pc)
  | .field pc => SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .copy sum pc => SemiprimeD1StackMultiplierLink.instruction (copyStack sum) (Label.copy sum)
      (SemiprimeD1StackCopy.code pc)

/-- Original headers and literal records are the only initially live data. -/
def inputData (axisTape pBits widthBits vertexTape : List Bool) : Stack→List Bool :=
  Function.update (Function.update (Function.update (Function.update (fun _=>[]) axes axisTape)
    precisionBits pBits) (aux .widthBits) widthBits) vertices vertexTape
/-- Closed physical start has no supplied assignment, rank, tensor entry or sum. -/
def initial (axisTape pBits widthBits vertexTape : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  ⟨some .start,none,none,inputData axisTape pBits widthBits vertexTape,[]⟩
/-- Fixed finite-stack leaf machine; its entire output is the canonical sum vector. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine vertices (aux .sum) Label.start program

/-- Context components retain distinct actual registers. -/
theorem contextStack_injective : Function.Injective contextStack := by decide
/-- Actual sum operands/cache/work registers are distinct. -/
theorem addStack_injective : Function.Injective addStack := by decide
/-- Enumeration bank has no physical aliases. -/
theorem enumerationStack_injective : Function.Injective enumerationStack := by decide
/-- Catalogue field parser has distinct input/work/output/flag registers. -/
theorem fieldStack_injective : Function.Injective fieldStack := by decide
/-- Both copy inclusions have distinct source/target/work registers. -/
theorem copyStack_injective (sum : Bool) : Function.Injective (copyStack sum) := by cases sum <;> decide

end RiemannGaussian.SemiprimeD1StackLeaf
