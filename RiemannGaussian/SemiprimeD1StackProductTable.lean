/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicProductFinite
import RiemannGaussian.SemiprimeD1StackReverseWord
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Concrete original-N product truth-table tape acquisition
One fixed finite program acquires its own arity, traverses assignments false
first, executes the actual public product checker at each leaf, writes literal
root coefficient vectors, and physically clears every checker role for reuse.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTable
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1StackPublicProduct (Stack Label program original assignment output modulusKey)
end P
/-- Private retained N, unary depth, reverse prefix, real copy workspace and tape. -/
inductive Aux where
  | source | depth | prefix | work | scratch | reversed | output
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.source,.depth,.prefix,.work,.scratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- All83 Boolean data roles, including every reused actual checker role. -/
abbrev Stack := P.Stack⊕Aux
/-- Complete static public-acquisition role list; no input-sized index is used. -/
def publicRoles : List SemiprimeD1BinaryPublicAcquisition.Stack :=
  let metaStack:=SemiprimeD1BinaryDigitAcquisition.metaStack
  let bankStack:=SemiprimeD1BinaryDigitAcquisition.bankStack
  let digitRoles : List SemiprimeD1BinaryDigitAcquisition.Stack :=
    (([.input,.width,.nonzero,.threshold,.radius,.square,.exponent,.squareWork,.thresholdWork,.temporary,.radix]:
      List SemiprimeD1StackTransform.Stack).map metaStack)++
    (([.input,.width,.counter,.scratch,.temporary,.dummyLeft,.dummyRight,.output]:
      List SemiprimeD1StackDigitBlock.Stack).map (fun k=>bankStack (.inl k)))++
    [bankStack (.inr 0),bankStack (.inr 1),bankStack (.inr 2),SemiprimeD1BinaryDigitAcquisition.copyTemporary]
  digitRoles.map SemiprimeD1BinaryPublicAcquisition.digitStack++
    [SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr false),SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true),
      SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 0),SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 1),
      SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 2)]
/-- Complete static private checker role list, including unused modulus shadows. -/
def productRoles : List SemiprimeD1StackProductCheck.Stack :=
  let a : List SemiprimeD1StackAdder.Stack := [.left,.right,.scratch,.output]
  let d : List SemiprimeD1StackDivider.Stack := a.map Sum.inl ++
    ([.input,.divisor,.digits,.remainder,.quotient,.copyScratch,.template]:List SemiprimeD1StackDivider.Aux).map Sum.inr
  let b : List SemiprimeD1StackResidueMul.M.Stack := a.map Sum.inl ++
    (List.finRange 3).map (fun k=>.inr (.inl k)) ++ [.inr (.inr false),.inr (.inr true)]
  let m : List SemiprimeD1StackResidueMul.Stack := b.map Sum.inl ++ d.map (fun k=>.inr (.inl k)) ++ [.inr (.inr false),.inr (.inr true)]
  let w : List SemiprimeD1StackWordVector.Stack := (List.finRange 5).map Sum.inl ++ (List.finRange 5).map Sum.inr
  let g : List SemiprimeD1StackVectorCanonical.Stack := [.cache,.modulus,.reader,.word,.scratch,.valid,.difference,.copiedModulus,.lessFlag,.output]
  w.map Sum.inl ++ g.map (fun k=>.inr (.inl k)) ++ m.map (fun k=>.inr (.inr (.inl k))) ++
    a.map (fun k=>.inr (.inr (.inr (.inl k)))) ++ (List.finRange 2).map (fun k=>.inr (.inr (.inr (.inr k))))
/-- Fixed complete cleanup inventory, computed before every original input. -/
def checkerRoles : List P.Stack := publicRoles.map Sum.inl++productRoles.map Sum.inr
/-- The static cleanup table has exactly all76 slots. -/
theorem checkerRoles_length : checkerRoles.length=76 := by decide
/-- One literal cleanup role; its index is fixed finite control, not an address
or a source-list getter on the input data. -/
def clearRole (pos : Fin 76) : Stack := .inl ((checkerRoles[pos.val]?).getD P.original)
/-- The three actual restoring-copy sites. -/
inductive CopyKind where | source | arity | prefix
  deriving DecidableEq,Repr
instance : Fintype CopyKind := Fintype.ofList [.source,.arity,.prefix] (by intro k;cases k <;> simp)
/-- Literal source/destination/scratch wiring for preserving physical copies. -/
def copyStack (kind : CopyKind) (k : Fin 3) : Stack :=
  if k=0 then match kind with
    | .source=>.inr .source
    | .arity=>.inl (.inl P.modulusKey)
    | .prefix=>.inr .prefix
  else if k=1 then match kind with
    | .source=>.inl P.original
    | .arity=>.inr .work
    | .prefix=>.inr .work
  else .inr .scratch
/-- The two real consuming reversals: current prefix and completed tape. -/
inductive ReverseKind where | prefix | table
  deriving DecidableEq,Repr
instance : Fintype ReverseKind := Fintype.ofList [.prefix,.table] (by intro k;cases k <;> simp)
/-- Literal reversal roles, with the original prefix kept by the preceding copy. -/
def reverseStack (kind : ReverseKind) (k : Fin 2) : Stack :=
  if k=0 then match kind with | .prefix=>.inr .work | .table=>.inr .reversed
  else match kind with | .prefix=>.inl P.assignment | .table=>.inr .output
/-- Entire fixed DFS/checker/cleanup control, independent of N and table depth. -/
inductive Label where
  | start | bootstrap | arityCopy (pass : Fin 3) | arityScan (pass : Fin 3) | arityPush (pass : Fin 3)
  | bootstrapClear | build | visit | fork | low | afterLow | high | afterHigh | restore | returnDone
  | leaf | reversePrefix | copySource | check | verdict | zero (position : Fin 4) | one (position : Fin 6)
  | leafClear | leafCleanup | leafReturn | clear (position : Fin 76) | clearDone | finish | done | bad
  | acquisition (pc : SemiprimeD1BinaryPublicAcquisition.Label)
  | checker (pc : P.Label) | copy (kind : CopyKind) (pc : Fin 9) | reverse (kind : ReverseKind) (pc : Fin 4)
  deriving Fintype
/-- Following static cleanup role, fixed before every table and assignment. -/
def clearNext (pos : Fin 76) : Label :=
  if h : pos.val<75 then .clear ⟨pos.val+1,by omega⟩ else .clearDone
/-- Literal zero/one leaf-code bits: false tree tag, one coefficient vector. -/
def zeroBits : Fin 4→Bool := fun k=>[false,true,false,false][k.val]!
/-- Literal accepted root coefficient code; no modular/table evaluator is called. -/
def oneBits : Fin 6→Bool := fun k=>[false,true,true,true,false,false][k.val]!
/-- Entire closed finite source program: only Boolean stacks and real returns. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.copy .source 0) .bootstrap
  | .bootstrap=>.call (.acquisition (SemiprimeD1BinaryPublicAcquisition.mainLabel .start)) (.arityCopy 0)
  | .arityCopy pass=>.call (.copy .arity 0) (.arityScan pass)
  | .arityScan pass=>.base (.pop (.inr .work)
      (if h : pass.val<2 then .arityCopy ⟨pass.val+1,by omega⟩ else .bootstrapClear)
      (.arityPush pass) (.arityPush pass))
  | .arityPush pass=>.base (.push (.inr .depth) true (.arityScan pass))
  | .bootstrapClear=>.call (.clear 0) .build
  | .build=>.call .visit .finish
  | .visit=>.base (.pop (.inr .depth) .leaf .fork .fork)
  | .fork=>.base (.push (.inr .reversed) true .low)
  | .low=>.base (.push (.inr .prefix) false .high)
  | .high=>.call .visit .afterLow
  | .afterLow=>.base (.pop (.inr .prefix) .bad .copySource .copySource)
  | .copySource=>.base (.push (.inr .prefix) true .afterHigh)
  | .afterHigh=>.call .visit .restore
  | .restore=>.base (.pop (.inr .prefix) .bad .returnDone .returnDone)
  | .returnDone=>.base (.push (.inr .depth) true .leafReturn)
  | .leaf=>.call (.copy .prefix 0) .reversePrefix
  | .reversePrefix=>.call (.reverse .prefix 0) .check
  | .check=>.call (.copy .source 0) .verdict
  | .verdict=>.call (.checker .start) .leafClear
  | .leafClear=>.base (.pop (.inl P.output) .bad (.zero 0) (.one 0))
  | .zero pos=>.base (.push (.inr .reversed) (zeroBits pos)
      (if h : pos.val<3 then .zero ⟨pos.val+1,by omega⟩ else .leafCleanup))
  | .one pos=>.base (.push (.inr .reversed) (oneBits pos)
      (if h : pos.val<5 then .one ⟨pos.val+1,by omega⟩ else .leafCleanup))
  | .leafCleanup=>.call (.clear 0) .leafReturn
  | .leafReturn=>.ret
  | .clear pos=>.base (.pop (clearRole pos) (clearNext pos) (.clear pos) (.clear pos))
  | .clearDone=>.ret
  | .finish=>.call (.reverse .table 0) .done
  | .done=>.base .halt
  | .bad=>.base .halt
  | .acquisition pc=>SemiprimeD1StackValidationLink.instruction (fun k=>.inl (.inl k)) Label.acquisition
      (SemiprimeD1BinaryPublicAcquisition.program pc)
  | .checker pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.checker (P.program pc)
  | .copy kind pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack kind) (Label.copy kind) (SemiprimeD1StackCopy.code pc)
  | .reverse kind pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack kind) (Label.reverse kind) (SemiprimeD1StackReverseWord.code pc)
/-- Only original binary N is initialized; depth, assignments and all tables are
physically acquired by the program, never supplied by a caller. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,(fun k=>if k=.inr .source then bits else []),[]⟩
/-- One fixed finite-alphabet machine before every original N and all arities. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inr .source) (.inr .output) .start program
/-- Every data and actual return symbol belongs to a fixed finite alphabet. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No native number/list/assignment/table/predicate inhabits finite control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
end RiemannGaussian.SemiprimeD1StackProductTable
