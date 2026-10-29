/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueBounds
import RiemannGaussian.SemiprimeD1StackUnaryProduct
import RiemannGaussian.SemiprimeD1StackUnarySumLessBytecode

/-! # Physical original-vertex arity from the actual cached counters
This internal procedure reads a physically parsed tag/index and shared source
metadata. The original-N port caller will acquire all of these inputs itself.
No native graph arity, comparison verdict or product answer is executed.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArity
namespace B
export SemiprimeD1StackBytecode (Instruction State execute step run)
end B
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackMultiplierLink (instruction DataRel data_unique Rel run_rel)
end Link
namespace Product
export SemiprimeD1StackUnaryProduct (Stack Label code entry contents product_run)
end Product
namespace Compare
export SemiprimeD1StackUnarySumLess (Stack contents)
export SemiprimeD1StackUnarySumLessBytecode (Label code entry compare_run)
end Compare
/-- Six actual readonly words; the index is the input constructor's second coordinate. -/
inductive Source where
  | tag | index | radiusSucc | firstAxis | secondAxis | digits
  deriving DecidableEq,Repr
instance : Fintype Source where
  elems:={.tag,.index,.radiusSucc,.firstAxis,.secondAxis,.digits}
  complete:=by intro k;cases k <;> simp
/-- Nine actual arity/copy/product/comparison work stacks. -/
inductive Aux where
  | arity | tagReader | copyScratch | multiplier | mulScratch
  | compareLeft | compareRight | compareLimit | compareResult
  deriving DecidableEq,Repr
instance : Fintype Aux where
  elems:={.arity,.tagReader,.copyScratch,.multiplier,.mulScratch,.compareLeft,.compareRight,.compareLimit,.compareResult}
  complete:=by intro k;cases k <;> simp
/-- All fifteen physical data stacks have Boolean alphabets. -/
abbrev Stack := Source⊕Aux
instance : DecidableEq Stack := inferInstanceAs (DecidableEq (Source⊕Aux))
instance : Fintype Stack := inferInstanceAs (Fintype (Source⊕Aux))
/-- Static source-cache inclusion. -/
def source (key:Source) : Stack := .inl key
/-- Static work/result inclusion. -/
def aux (key:Aux) : Stack := .inr key
/-- The six actual source-preserving copy operations. -/
inductive CopyKind | tag | radius | first | second | index | digits
  deriving DecidableEq
instance : Fintype CopyKind where
  elems:={.tag,.radius,.first,.second,.index,.digits}
  complete:=by intro k;cases k <;> simp
/-- Literal fixed finite arity control. -/
inductive Control where
  | main | decode (count:Fin 18) | invalidClear
  | inputRadius | inputIndex | inputDigits | compare | verdict | inputFlag
  | oneRadius | twoRadius (stage:Fin 2) | threeRadius (stage:Fin 3)
  | multiplyFirst (stage:Fin 2) | multiplySecond (stage:Fin 2)
  | product | literal (remaining:Fin 3) | halt
  deriving DecidableEq,Fintype
/-- Product/compare finite locations are fixed, not indexed by their operand values.
They require only Fintype, never label equality or Repr. -/
abbrev Label := Control⊕((CopyKind×Fin 9)⊕(Product.Label⊕Compare.Label))
instance : Fintype Label := inferInstanceAs (Fintype (Control⊕((CopyKind×Fin 9)⊕(Product.Label⊕Compare.Label))))
/-- Actual readonly copy supplier for each static case. -/
def copySource : CopyKind→Source
  | .tag => .tag
  | .radius => .radiusSucc
  | .first => .firstAxis
  | .second => .secondAxis
  | .index => .index
  | .digits => .digits
/-- Actual destination for each static copy. -/
def copyTarget : CopyKind→Aux
  | .tag => .tagReader
  | .radius => .arity
  | .first | .second => .multiplier
  | .index => .compareRight
  | .digits => .compareLimit
/-- Literal three-stack Copy inclusion. -/
def copyStack (kind:CopyKind) (k:Fin 3) : Stack :=
  if k=0 then source (copySource kind) else if k=1 then aux (copyTarget kind) else aux .copyScratch
/-- Static included copy labels. -/
def copyLabel (kind:CopyKind) (pc:Fin 9) : Label := .inr (.inl (kind,pc))
/-- Multiplicand aliases the actual readonly R+1 source, not an advised product. -/
def productStack : Product.Stack→Stack
  | .multiplier => aux .multiplier
  | .multiplicand => source .radiusSucc
  | .scratch => aux .mulScratch
  | .product => aux .arity
/-- Static included product labels. -/
def productLabel (pc:Product.Label) : Label := .inr (.inr (.inl pc))
/-- Actual compare operands: zero+copied index versus copied digit count. -/
def compareStack : Compare.Stack→Stack
  | .left => aux .compareLeft
  | .right => aux .compareRight
  | .limit => aux .compareLimit
  | .valid => aux .compareResult
/-- Static included compare labels. -/
def compareLabel (pc:Compare.Label) : Label := .inr (.inr (.inr pc))
/-- Only a static finite tag position chooses a literal original arity recipe. -/
def recipe (count:Fin 18) : Label :=
  if count.val=0 then .inl .inputRadius
  else if count.val=1 then .inl (.multiplySecond 0)
  else if count.val=2 then .inl (.twoRadius 0)
  else if count.val=3 then .inl (.multiplyFirst 0)
  else if count.val=4 then .inl (.threeRadius 0)
  else if count.val=5 then .inl .oneRadius
  else if count.val=6 then .inl (.threeRadius 0)
  else if count.val=7 then .inl .oneRadius
  else if count.val=8 then .inl (.literal 2)
  else if count.val=9 then .inl (.literal 0)
  else .inl (.literal 1)
/-- One fixed finite arity program; every multiply/compare/copy is an actual real call. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl (kind,pc)) => Link.instruction (copyStack kind) (copyLabel kind) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inl pc)) => Link.instruction productStack productLabel (Product.code pc)
  | .inr (.inr (.inr pc)) => Link.instruction compareStack compareLabel (Compare.code pc)
  | .inl .main => .call (copyLabel .tag 0) (.inl (.decode 0))
  | .inl (.decode count) =>
      let next:Label:=if h:count.val<17 then .inl (.decode ⟨count.val+1,by omega⟩) else .inl .invalidClear
      .base (.pop (aux .tagReader) (recipe count) next next)
  | .inl .invalidClear => .base (.pop (aux .tagReader) (.inl .halt) (.inl .invalidClear) (.inl .invalidClear))
  | .inl .inputRadius => .call (copyLabel .radius 0) (.inl .inputIndex)
  | .inl .inputIndex => .call (copyLabel .index 0) (.inl .inputDigits)
  | .inl .inputDigits => .call (copyLabel .digits 0) (.inl .compare)
  | .inl .compare => .call (compareLabel Compare.entry) (.inl .verdict)
  | .inl .verdict => .base (.pop (aux .compareResult) (.inl .halt) (.inl .halt) (.inl .inputFlag))
  | .inl .inputFlag => .base (.push (aux .arity) true (.inl .halt))
  | .inl .oneRadius => .call (copyLabel .radius 0) (.inl .halt)
  | .inl (.twoRadius stage) => .call (copyLabel .radius 0)
      (if stage.val=0 then .inl (.twoRadius 1) else .inl .halt)
  | .inl (.threeRadius stage) => .call (copyLabel .radius 0)
      (if h:stage.val<2 then .inl (.threeRadius ⟨stage.val+1,by omega⟩) else .inl .halt)
  | .inl (.multiplyFirst stage) => .call (copyLabel .first 0)
      (if stage.val=0 then .inl (.multiplyFirst 1) else .inl .product)
  | .inl (.multiplySecond stage) => .call (copyLabel .second 0)
      (if stage.val=0 then .inl (.multiplySecond 1) else .inl .product)
  | .inl .product => .call (productLabel Product.entry) (.inl .halt)
  | .inl (.literal count) => .base (.push (aux .arity) true
      (if count.val=0 then .inl .halt else .inl (.literal ⟨count.val-1,by omega⟩)))
  | .inl .halt => .base .halt
/-- Fixed internal finite machine for physical shared-metadata arity construction.
The public port caller supplies these words by its own original-N acquisition. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (source .tag) (aux .arity) (.inl .main) program
/-- Literal source/working data, used only to describe actual configurations. -/
def data (header:Source→List Bool) (work:Aux→List Bool) : Stack→List Bool := Sum.elim header work
/-- Every alphabet, including every product/compare/call location, is finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (source .tag) (aux .arity) (.inl .main) program
/-- Fifteen actual Boolean data roles, independent of graph dimensions. -/
theorem stack_card : Fintype.card Stack=15 := by decide
end RiemannGaussian.SemiprimeD1StackVertexArity
