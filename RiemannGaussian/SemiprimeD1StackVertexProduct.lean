/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetUnitBounds
import RiemannGaussian.SemiprimeD1StackVertexReadBounds
/-! # Fixed parsed-vertex physical product caller
Context rank/precision are acquired from the actual original headers. The vertex
loop parses original port/table fields, calls physical gather/tree lookup, and
feeds its encoded vector directly to the closed physical dense multiplier.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeD1StackVertexProduct
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace M
export SemiprimeD1StackJetMul (Stack Label program output)
end M
namespace X
export SemiprimeD1StackJetContext (Stack Label program axesCache precisionBits rankCache widthCache)
end X
namespace U
export SemiprimeD1StackJetUnit (Stack Label program widthCache rankCache output)
end U
namespace V
export SemiprimeD1StackVertexRead (Stack Label code control)
end V
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F

/-- Original input caches and literal parsing/copy work. -/
inductive Aux where
  | verticesCache | verticesReader | assignment | precisionBits | ports | table
  | fieldScratch | fieldValid | copyWork
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList
  [.verticesCache,.verticesReader,.assignment,.precisionBits,.ports,.table,.fieldScratch,.fieldValid,.copyWork]
  (by intro k; cases k <;> simp)

/-- One fixed finite Boolean register bank, including all literal callee work. -/
abbrev Stack := M.Stack ⊕ ((X.Stack ⊕ U.Stack) ⊕ (V.Stack ⊕ (F.Stack ⊕ Aux)))
/-- Actual multiplier data address. -/
def main (k : M.Stack) : Stack := .inl k
/-- Actual dedicated context work address. -/
def contextWork (k : X.Stack) : Stack := .inr (.inl (.inl k))
/-- Actual dedicated unit work address. -/
def unitWork (k : U.Stack) : Stack := .inr (.inl (.inr k))
/-- Actual dedicated vertex-reader work address. -/
def vertexWork (k : V.Stack) : Stack := .inr (.inr (.inl k))
/-- Actual caller cache/work address. -/
def aux (k : Aux) : Stack := .inr (.inr (.inr (.inr k)))
/-- First encoded-vector operand of the literal multiplier. -/
def left : Stack := main (.inl (SemiprimeD1StackJetPoint.aux .a))
/-- Current encoded product, retained as the second literal multiplier operand. -/
def product : Stack := main (.inl (SemiprimeD1StackJetPoint.aux .b))
/-- Shared original axis tape. -/
def axes : Stack := main (.inl (SemiprimeD1StackJetPoint.aux .axes))
/-- Shared physically acquired rank cache. -/
def rank : Stack := main (.inl (SemiprimeD1StackJetPoint.aux .rank))
/-- Shared physically acquired precision markers. -/
def width : Stack := main (.inl SemiprimeD1StackJetPoint.precision)
/-- Actual newly acquired product tape. -/
def result : Stack := main M.output

/-- Actual context outputs ARE the later arithmetic caches; no native projection
or recoding of the computed rank/precision is executed. -/
def contextStack (k : X.Stack) : Stack :=
  if k=X.axesCache then axes else if k=X.rankCache then rank else if k=X.widthCache then width
  else if k=X.precisionBits then aux .precisionBits else contextWork k

/-- Literal unit construction uses the same empty operands and actual caches. -/
def unitStack (k : U.Stack) : Stack :=
  if k=U.widthCache then width else if k=U.rankCache then rank else if k=U.output then result
  else if k=Sum.inr SemiprimeD1StackJetAdd.Aux.leftTape then left
  else if k=Sum.inr SemiprimeD1StackJetAdd.Aux.rightTape then product else unitWork k

/-- Real table read writes its encoded vector DIRECTLY into the multiplier operand. -/
def vertexStack : V.Stack → Stack
  | .ports => aux .ports
  | .assignment => aux .assignment
  | .tableTape => aux .table
  | .output => left
  | k => vertexWork k

/-- Both original vertex fields are physically parsed from the same input stream. -/
def fieldStack (table : Bool) : F.Stack → Stack
  | .inl .input => aux .verticesReader
  | .inl .scratch => aux .fieldScratch
  | .inl .output => aux (if table then .table else .ports)
  | .inr _ => aux .fieldValid

/-- Literal original-record and current-result copies, both actually executed. -/
def copyStack (vertices : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if vertices then aux .verticesCache else result)
  else if k=1 then (if vertices then aux .verticesReader else product) else aux .copyWork

/-- Fixed caller and included-program labels, independent of context and network size. -/
inductive Label where
  | start | prepared | unitDone | clearUnitOut | copyVertices | vertexTag | readPorts | portsDone
  | readTable | tableDone | callVertex | callMul | clearA | clearB | copyProduct | clearOutput | done | abort
  | context (pc : X.Label)
  | unit (pc : U.Label)
  | vertex (pc : V.Label)
  | multiply (pc : M.Label)
  | field (table : Bool) (pc : F.Label)
  | copy (vertices : Bool) (pc : Fin 9)
  deriving DecidableEq,Fintype

/-- Actual context acquisition and parsed-vertex product. The prepared label is
an internal entry for an assignment caller that ALREADY executed this context
supplier; the top-level start always acquires its own original context caches. -/
def program : Label → C.Instruction Stack Label
  | .start => .call (.context .start) .prepared
  | .prepared => .call (.unit .seed0) .unitDone
  | .unitDone => .call (.copy false 0) .clearUnitOut
  | .clearUnitOut => .base (.pop result .copyVertices .clearUnitOut .clearUnitOut)
  | .copyVertices => .call (.copy true 0) .vertexTag
  | .vertexTag => .base (.pop (aux .verticesReader) .done .done .readPorts)
  | .readPorts => .call (.field false (F.active .tagPop (none,false))) .portsDone
  | .portsDone => .base (.pop (aux .fieldValid) .abort .abort .readTable)
  | .readTable => .call (.field true (F.active .tagPop (none,false))) .tableDone
  | .tableDone => .base (.pop (aux .fieldValid) .abort .abort .callVertex)
  | .callVertex => .call (.vertex (V.control .start)) .callMul
  | .callMul => .call (.multiply .start) .clearA
  | .clearA => .base (.pop left .clearB .clearA .clearA)
  | .clearB => .base (.pop product .copyProduct .clearB .clearB)
  | .copyProduct => .call (.copy false 0) .clearOutput
  | .clearOutput => .base (.pop result .vertexTag .clearOutput .clearOutput)
  | .done | .abort => .base .halt
  | .context pc => SemiprimeD1StackValidationLink.instruction contextStack Label.context (X.program pc)
  | .unit pc => SemiprimeD1StackValidationLink.instruction unitStack Label.unit (U.program pc)
  | .vertex pc => SemiprimeD1StackValidationLink.instruction vertexStack Label.vertex (V.code pc)
  | .multiply pc => SemiprimeD1StackValidationLink.instruction main Label.multiply (M.program pc)
  | .field table pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack table) (Label.field table) (F.code pc)
  | .copy vertices pc => SemiprimeD1StackMultiplierLink.instruction (copyStack vertices) (Label.copy vertices)
      (SemiprimeD1StackCopy.code pc)

/-- Input representation only, never an executed vertex/entry getter.
Each original field is physically parsed by the literal program above. -/
def records : List SemiprimeD1LeafCounter.Vertex → List Bool
  | [] => [false]
  | v::vs => true::SemiprimeSourceHistogramKeyBits.frame
      (SemiprimeD1StackVertexReadExecution.portTape v.ports)
      (SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1TensorTapeCodec.tape v.table) (records vs))

/-- Literal original physical headers, vertex records and assignment, no rank,
precision-count, selected entry, product or leaf answer prepared. -/
def inputData (axisTape precisionBits vertexTape assignment : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update (fun _=>[]) axes axisTape)
    (aux .precisionBits) precisionBits) (aux .verticesCache) vertexTape) (aux .assignment) assignment
/-- Actual start has cleared flags/frames and all work/arithmetic operands empty. -/
def initial (axisTape precisionBits vertexTape assignment : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,inputData axisTape precisionBits vertexTape assignment,[]⟩
/-- Actual fixed finite-stack original-header vertex-product machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (aux .verticesCache) product Label.start program

/-- Context-cache/output aliases preserve distinct physical component registers. -/
theorem contextStack_injective : Function.Injective contextStack := by decide
/-- Unit-cache/output aliases preserve distinct physical component registers. -/
theorem unitStack_injective : Function.Injective unitStack := by decide
/-- The literal vertex-read operands have disjoint physical registers. -/
theorem vertexStack_injective : Function.Injective vertexStack := by decide
/-- Both physical field parsers have distinct registers. -/
theorem fieldStack_injective (table : Bool) : Function.Injective (fieldStack table) := by cases table <;> decide
/-- Both physical copies have distinct source/target/work registers. -/
theorem copyStack_injective (vertices : Bool) : Function.Injective (copyStack vertices) := by cases vertices <;> decide

end RiemannGaussian.SemiprimeD1StackVertexProduct
