/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackAssignmentBody
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1WeightedTuples
/-! # Real feasible-only weighted-tuple recursion with physical activation records
This prepared entry takes an actual framed positive-weight tape and the actual
unary precision WIDTH. It copies WIDTH and physically removes one marker for
its budget. Every child has a real return frame and five saved Boolean words.
Only successful repeated subtraction creates another child. Catalogue/packet
acquisition is a separate frontend, never an evaluator hidden in this control.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedMode
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
/-- Seventeen fixed Boolean words; activation records and outputs are ordinary tape data. -/
inductive Stack where
  | catalogue | width | weights | budget | path | weight | exponent | frames | tuple | pathReader
  | fieldScratch | valid | copyScratch | frameScratch | subTodo | history | output
  deriving DecidableEq,Repr
instance :Fintype Stack where
  elems:={.catalogue,.width,.weights,.budget,.path,.weight,.exponent,.frames,.tuple,.pathReader,
    .fieldScratch,.valid,.copyScratch,.frameScratch,.subTodo,.history,.output}
  complete:=by intro k;cases k <;> simp
/-- Four actual preserving-copy sites, each independent of all numerical values. -/
inductive Copy where | catalogue | width | path | weight deriving DecidableEq,Repr
instance :Fintype Copy where
  elems:={.catalogue,.width,.path,.weight}
  complete:=by intro k;cases k <;> simp
/-- Five literal saved activation fields, in their physical restore order. -/
def saved : Fin 5→Stack :=![.weight,.weights,.budget,.exponent,.path]
/-- Nine actual mutable words are physically drained before every recursive return. -/
def cleared : Fin 9→Stack :=![.weights,.budget,.path,.weight,.exponent,.subTodo,.tuple,.pathReader,.valid]
/-- Seven fixed parser sites: one weight, one leaf-path field and five restored activation fields. -/
inductive Parse where | weight | path | restore (part:Fin 5) deriving DecidableEq,Repr,Fintype
/-- Three fixed frame sites: activation save, recursive path push and leaf tuple reversal. -/
inductive Frame where | save (part:Fin 5) | path | tuple deriving DecidableEq,Repr,Fintype
/-- Fixed finite locations; recursion depth, weights, budgets and exponents never enter labels. -/
inductive Control where
  | start | widthCopy | budgetPred | pathSeed | root | finishSeed | reverse | done | abort
  | visit | weightRead | weightValid | weightPositive | save (part:Fin 5)
  | pathFrame | pathTag | clearWeight | clearExponent | child | afterChild
  | restore (part:Fin 5) | restoreValid (part:Fin 5)
  | copyWeight | subtract | budgetPop | increment | failure
  | tupleSeed | copyPath | tupleNext | tupleRead | tupleValid | tupleFrame | tupleTag | tupleClear | emit
  | cleanup (part:Fin 9) | returning
  deriving DecidableEq,Repr,Fintype
/-- Real primitive and recursive return-label alphabets are fixed before every input. -/
abbrev Label :=Control⊕((Copy×Fin 9)⊕((Parse×Field.Label)⊕((Frame×Fin 11)⊕(Body.Label⊕Fin 4))))
/-- Actual included copy labels. -/
def copyLabel (site:Copy) (pc:Fin 9) : Label :=.inr (.inl (site,pc))
/-- Actual included field-parser labels. -/
def parseLabel (site:Parse) (pc:Field.Label) : Label :=.inr (.inr (.inl (site,pc)))
/-- Actual included preserving frame labels. -/
def frameLabel (site:Frame) (pc:Fin 11) : Label :=.inr (.inr (.inr (.inl (site,pc))))
/-- Actual tuple logger labels. -/
def bodyLabel (pc:Body.Label) : Label :=.inr (.inr (.inr (.inr (.inl pc))))
/-- Actual final whole-history reversal labels. -/
def reverseLabel (pc:Fin 4) : Label :=.inr (.inr (.inr (.inr (.inr pc))))
/-- Real copy source and initially empty target; the scratch is always counted. -/
def copyStack (site:Copy) (k:Fin 3) : Stack :=
  if k=0 then match site with | .catalogue=>.catalogue | .width=>.width | .path=>.path | .weight=>.weight
  else if k=1 then match site with | .catalogue=>.weights | .width=>.budget | .path=>.pathReader | .weight=>.subTodo
  else .copyScratch
/-- Each field comes from the physical weight suffix, copied path, or actual activation stack. -/
def parseStack (site:Parse) : Field.Stack→Stack
  | .inl .input=>match site with | .weight=>.weights | .path=>.pathReader | .restore _=>.frames
  | .inl .output=>match site with | .weight | .path=>.weight | .restore i=>saved i
  | .inl .scratch=>.fieldScratch
  | .inr _=>.valid
/-- Actual activation/path/tuple framing uses one separate restoring scratch word. -/
def frameStack (site:Frame) (k:Fin 3) : Stack :=
  if k=0 then match site with | .save i=>saved i | .path=>.exponent | .tuple=>.weight
  else if k=1 then match site with | .save _=>.frames | .path=>.path | .tuple=>.tuple
  else .frameScratch
/-- Every emitted tuple is restored and copied into the same chronological reverse log. -/
def bodyStack : Body.Stack→Stack | .word=>.tuple | .scratch=>.copyScratch | .history=>.history
/-- One final real reversal writes the physical output, seeded with its false terminator. -/
def reverseStack (k:Fin 2) : Stack :=if k=0 then .history else .output
local notation "ctl" => (Sum.inl : Control→Label)
/-- The next literal save field; fields are pushed last-first and restored first-last. -/
def saveNext (i:Fin 5) : Label :=if h:0 < i.val then ctl (.save ⟨i.val-1,by omega⟩) else ctl .pathFrame
/-- The next literal restore field, followed by the feasible-branch subtraction test. -/
def restoreNext (i:Fin 5) : Label :=if h:i.val<4 then ctl (.restore ⟨i.val+1,by omega⟩) else ctl .copyWeight
/-- The next physical cleanup word, with actual return after all nine words are empty. -/
def cleanupNext (i:Fin 9) : Label :=if h:i.val<8 then ctl (.cleanup ⟨i.val+1,by omega⟩) else ctl .returning
/-- One fixed finite controller: actual positive-weight traversal, feasible children only and real recursion. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.call (copyLabel .catalogue 0) (ctl .widthCopy)
  | .inl .widthCopy=>.call (copyLabel .width 0) (ctl .budgetPred)
  | .inl .budgetPred=>.base (.pop .budget (ctl .pathSeed) (ctl .pathSeed) (ctl .pathSeed))
  | .inl .pathSeed=>.base (.push .path false (ctl .root))
  | .inl .root=>.call (ctl .visit) (ctl .finishSeed)
  | .inl .finishSeed=>.base (.push .output false (ctl .reverse))
  | .inl .reverse=>.call (reverseLabel 0) (ctl .done)
  | .inl .done|.inl .abort=>.base .halt
  | .inl .visit=>.base (.pop .weights (ctl .abort) (ctl .tupleSeed) (ctl .weightRead))
  | .inl .weightRead=>.call (parseLabel .weight (Field.active .tagPop (none,false))) (ctl .weightValid)
  | .inl .weightValid=>.base (.pop .valid (ctl .abort) (ctl .abort) (ctl .weightPositive))
  | .inl .weightPositive=>.base (.peek .weight (ctl .abort) (ctl (.save 4)) (ctl (.save 4)))
  | .inl (.save i)=>.call (frameLabel (.save i) 0) (saveNext i)
  | .inl .pathFrame=>.call (frameLabel .path 0) (ctl .pathTag)
  | .inl .pathTag=>.base (.push .path true (ctl .clearWeight))
  | .inl .clearWeight=>.base (.pop .weight (ctl .clearExponent) (ctl .clearWeight) (ctl .clearWeight))
  | .inl .clearExponent=>.base (.pop .exponent (ctl .child) (ctl .clearExponent) (ctl .clearExponent))
  | .inl .child=>.call (ctl .visit) (ctl .afterChild)
  | .inl .afterChild=>.base (.jump (ctl (.restore 0)))
  | .inl (.restore i)=>.call (parseLabel (.restore i) (Field.active .tagPop (none,false))) (ctl (.restoreValid i))
  | .inl (.restoreValid i)=>.base (.pop .valid (ctl .abort) (ctl .abort) (restoreNext i))
  | .inl .copyWeight=>.call (copyLabel .weight 0) (ctl .subtract)
  | .inl .subtract=>.base (.pop .subTodo (ctl .increment) (ctl .budgetPop) (ctl .budgetPop))
  | .inl .budgetPop=>.base (.pop .budget (ctl .failure) (ctl .subtract) (ctl .subtract))
  | .inl .increment=>.base (.push .exponent true (ctl (.save 4)))
  | .inl .failure=>.base (.pop .subTodo (ctl (.cleanup 0)) (ctl .failure) (ctl .failure))
  | .inl .tupleSeed=>.base (.push .tuple false (ctl .copyPath))
  | .inl .copyPath=>.call (copyLabel .path 0) (ctl .tupleNext)
  | .inl .tupleNext=>.base (.pop .pathReader (ctl .abort) (ctl .emit) (ctl .tupleRead))
  | .inl .tupleRead=>.call (parseLabel .path (Field.active .tagPop (none,false))) (ctl .tupleValid)
  | .inl .tupleValid=>.base (.pop .valid (ctl .abort) (ctl .abort) (ctl .tupleFrame))
  | .inl .tupleFrame=>.call (frameLabel .tuple 0) (ctl .tupleTag)
  | .inl .tupleTag=>.base (.push .tuple true (ctl .tupleClear))
  | .inl .tupleClear=>.base (.pop .weight (ctl .tupleNext) (ctl .tupleClear) (ctl .tupleClear))
  | .inl .emit=>.call (bodyLabel Body.entry) (ctl (.cleanup 0))
  | .inl (.cleanup i)=>.base (.pop (cleared i) (cleanupNext i) (ctl (.cleanup i)) (ctl (.cleanup i)))
  | .inl .returning=>.ret
  | .inr (.inl (site,pc))=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inl (site,pc)))=>SemiprimeD1StackMultiplierLink.instruction (parseStack site) (parseLabel site) (Field.code pc)
  | .inr (.inr (.inr (.inl (site,pc))))=>SemiprimeD1StackMultiplierLink.instruction (frameStack site) (frameLabel site) (SemiprimeD1StackFrame.code pc)
  | .inr (.inr (.inr (.inr (.inl pc))))=>SemiprimeD1StackMultiplierLink.instruction bodyStack bodyLabel (Body.code pc)
  | .inr (.inr (.inr (.inr (.inr pc))))=>SemiprimeD1StackMultiplierLink.instruction reverseStack reverseLabel (SemiprimeD1StackReverseWord.code pc)
/-- Prepared input has only actual catalogue bytes and actual unary precision WIDTH. -/
def input (catalogue width:List Bool) : Stack→List Bool
  | .catalogue=>catalogue | .width=>width | _=>[]
/-- Actual two-operand prepared front door; no feasible tuple/count/answer is supplied. -/
def initial (catalogue width:List Bool) : C.State Stack Label :=⟨some (ctl .start),none,none,input catalogue width,[]⟩
/-- One genuine finite machine; explicit prepared inputs are accounted separately. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine Stack.width Stack.output (ctl .start) program
/-- All actual data roles are counted. -/
theorem stack_card :Fintype.card Stack=17:=by decide
/-- Actual copy operands are pairwise distinct. -/
theorem copy_injective (site:Copy) :Function.Injective (copyStack site):=by cases site <;> decide
/-- Actual parser operands are pairwise distinct. -/
theorem parse_injective (site:Parse) :Function.Injective (parseStack site):=by
  cases site with
  | weight|path=>decide
  | restore i=>fin_cases i <;> decide
/-- Actual frame operands are pairwise distinct. -/
theorem frame_injective (site:Frame) :Function.Injective (frameStack site):=by
  cases site with
  | path|tuple=>decide
  | save i=>fin_cases i <;> decide
/-- Actual logger operands are pairwise distinct. -/
theorem body_injective :Function.Injective bodyStack:=by decide
/-- Actual final reversal operands are distinct. -/
theorem reverse_injective :Function.Injective reverseStack:=by decide
/-- No infinite numerical or callback alphabet enters internal control. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data/real-return alphabet is fixed finite before all inputs. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackWeightedMode
