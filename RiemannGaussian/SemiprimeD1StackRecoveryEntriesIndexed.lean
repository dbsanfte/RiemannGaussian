/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordEqualExecution
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Actual binary-index vector reader for the recovery-entry source
Only an actual framed vector and actual binary query are supplied. Each actual
vector tag drives one real numeric WordEqual against an acquired BINARY ordinal.
A real full adder increments it after each skipped field. Every loop stops at
actual vector EOF, so numeric address magnitude never drives unary work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexed
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace A
export SemiprimeD1StackAdder (Stack Label code store state)
end A
namespace E
export SemiprimeD1StackWordEqual (Label code state)
end E
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eight fixed source/query/scan roles beside the real shared four-role arithmetic bank. -/
inductive Aux where
  | cache | query | counter | reader | parser | value | valid | copy
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.cache,.query,.counter,.reader,.parser,.value,.valid,.copy]
  (by intro k;cases k <;> simp)
/-- All12 physical roles; equality and increment use the SAME four actual arithmetic tapes. -/
abbrev Stack:=A.Stack⊕Aux
/-- Actual arithmetic tape. -/
def arithmetic:A.Stack → Stack:=Sum.inl
/-- Actual input/query/parser/scan tape. -/
def aux:Aux → Stack:=Sum.inr
/-- Five literal preserving-copy sites, fixed before every address and vector. -/
inductive Copy where
  | cache | query | ordinal | increment | result
  deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.cache,.query,.ordinal,.increment,.result]
  (by intro k;cases k <;> simp)
/-- Actual source of a paid preserving copy. -/
def copySource:Copy → Stack
  | .cache=>aux .cache | .query=>aux .query | .ordinal|.increment=>aux .counter | .result=>arithmetic .output
/-- Actual target of a paid preserving copy. -/
def copyTarget:Copy → Stack
  | .cache=>aux .reader | .query|.increment=>arithmetic .left | .ordinal=>arithmetic .right | .result=>aux .counter
/-- Actual restoring copy workspace, independent of address values. -/
def copyStack (site:Copy) (k:Fin 3):Stack:=if k=0 then copySource site else if k=1 then copyTarget site else aux .copy
/-- Actual vector Field parser materializes both selected and discarded words. -/
def fieldStack:F.Stack → Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .parser | .inl .output=>aux .value | .inr () =>aux .valid
/-- Fixed finite scan/parse/arithmetic/cleanup control. -/
inductive Control where
  | start | loop | query | ordinal | compare | compared | field (take:Bool) | parsed (take:Bool)
  | clearValue | increment | clearCounterForAdd | seed | add | result | clearResult
  | clearReader | clearCounter | done | abort
  deriving DecidableEq,Fintype,Repr
/-- All real included component labels and finite return cells. -/
inductive Label where
  | local (pc:Control) | copy (site:Copy) (pc:Fin 9) | field (pc:F.Label)
  | equal (pc:E.Label) | add (pc:A.Label)
  deriving DecidableEq,Fintype,Repr
local notation "ctl"=>Label.local
/-- The ONE finite binary-index reader; no address is decoded or materialized as unary. -/
def program:Label → C.Instruction Stack Label
  | .local .start=>.call (.copy .cache 0) (ctl .loop)
  | .local .loop=>.base (.pop (aux .reader) (ctl .clearCounter) (ctl .clearReader) (ctl .query))
  | .local .query=>.call (.copy .query 0) (ctl .ordinal)
  | .local .ordinal=>.call (.copy .ordinal 0) (ctl .compare)
  | .local .compare=>.call (.equal .loop) (ctl .compared)
  | .local .compared=>.base (.pop (arithmetic .output) (ctl .abort) (ctl (.field false)) (ctl (.field true)))
  | .local (.field take)=>.call (.field (F.active .tagPop (none,false))) (ctl (.parsed take))
  | .local (.parsed take)=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort)
      (if take then ctl .clearReader else ctl .clearValue))
  | .local .clearValue=>.base (.pop (aux .value) (ctl .increment) (ctl .clearValue) (ctl .clearValue))
  | .local .increment=>.call (.copy .increment 0) (ctl .clearCounterForAdd)
  | .local .clearCounterForAdd=>.base (.pop (aux .counter) (ctl .seed) (ctl .clearCounterForAdd) (ctl .clearCounterForAdd))
  | .local .seed=>.base (.push (arithmetic .right) true (ctl .add))
  | .local .add=>.call (.add (.start false)) (ctl .result)
  | .local .result=>.call (.copy .result 0) (ctl .clearResult)
  | .local .clearResult=>.base (.pop (arithmetic .output) (ctl .loop) (ctl .clearResult) (ctl .clearResult))
  | .local .clearReader=>.base (.pop (aux .reader) (ctl .clearCounter) (ctl .clearReader) (ctl .clearReader))
  | .local .clearCounter=>.base (.pop (aux .counter) (ctl .done) (ctl .clearCounter) (ctl .clearCounter))
  | .local .done|.local .abort=>.base .halt
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction arithmetic Label.equal (E.code pc)
  | .add pc=>SemiprimeD1StackMultiplierLink.instruction arithmetic Label.add (A.code pc)
/-- Honest actual vector/query entry, without an ordinal count or selected word. -/
def input (cache query:List Bool):Stack → List Bool:=
  Function.update (Function.update (fun _=>[]) (aux .cache) cache) (aux .query) query
/-- Actual initial source state, empty real returns and every private field clear. -/
def initial (cache query:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input cache query,[]⟩
/-- One fixed finite actual vector/query source. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .cache) (aux .value) (ctl .start) program
/-- All12 tapes are counted, including equality's unused scratch during comparison. -/
theorem stack_card:Fintype.card Stack=12:=by decide
/-- Every real copy has three distinct physical roles. -/
theorem copy_injective (site:Copy):Function.Injective (copyStack site):=by cases site <;> decide
/-- The real parser has four distinct physical roles. -/
theorem field_injective:Function.Injective fieldStack:=by decide
/-- All data and real return alphabets are finite before all addresses. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite (aux .cache) (aux .value) (ctl .start) program
/-- Transient control contains no address, word, count, getter or evaluator. -/
theorem control_finite:Finite machine.σ:=
  SemiprimeD1StackCalls.control_finite (aux .cache) (aux .value) (ctl .start) program
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexed
