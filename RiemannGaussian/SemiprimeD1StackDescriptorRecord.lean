/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticRecordClock
/-! # Physical descriptor fields to a static checker template and actual record
The source map and checker are compile-time constants. Six retained physical
words contain binary N, tag, coord0, coord1, coord2 and coord3, in that order.
Every old template field is physically drained before any selected actual copy.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackDescriptorRecord
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace R
export SemiprimeD1StackStaticRecord (Stack Label program tableStack original history output)
end R
namespace T
export SemiprimeD1StackStaticTable (Static template role)
end T
/-- Complete physical roles, including all static-record alias shadows. -/
abbrev Stack (K : Type) :=R.Stack K⊕(Fin 6⊕Unit)
/-- Actual whole static-record component. -/
def recordStack {K : Type} (k : R.Stack K) : Stack K :=.inl k
/-- Read-only actual binary N and five original descriptor fields. -/
def source {K : Type} (i : Fin 6) : Stack K :=.inr (.inl i)
/-- One actual preserving-copy scratch word. -/
def scratch {K : Type} : Stack K :=.inr (.inr ())
/-- Actual checker-template destination. -/
def templateStack {K : Type} (k : K) : Stack K :=recordStack (R.tableStack (T.template k))
/-- Actual retained binary occurrence-ID bank. -/
def original {K : Type} : Stack K :=recordStack R.original
/-- Caller accumulated reverse row history. -/
def history {K : Type} : Stack K :=recordStack R.history
/-- Caller final output accumulator. -/
def output {K : Type} : Stack K :=recordStack R.output
/-- Literal finite loader/control stages. -/
inductive Control (size : Nat) where
  | start | record | done
  | load (position : Fin (size+1)) | copy (position : Fin size)
  deriving DecidableEq,Fintype
/-- All static-record and copy return labels are finite before original N. -/
abbrev Label (L : Type) (size : Nat) :=Control size⊕(R.Label L size⊕(Fin size×Fin 9))
/-- Included real static-record labels. -/
def recordLabel {L : Type} {n : Nat} (pc : R.Label L n) : Label L n :=.inr (.inl pc)
/-- Included real preserving-copy labels at each static template position. -/
def copyLabel {L : Type} {n : Nat} (p : Fin n) (pc : Fin 9) : Label L n :=.inr (.inr (p,pc))
variable {K L : Type} [DecidableEq K] (s : T.Static K L) (sourceMap : K→Option (Fin 6))
/-- Next literal template position, independent of every runtime field. -/
def loadNext (p : Fin s.roles.length) : Label L s.roles.length :=.inl (.load ⟨p.val+1,by omega⟩)
/-- Three disjoint physical operands for each actual selected source copy. -/
def copyStack (p : Fin s.roles.length) (i : Fin 3) : Stack K :=
  if i=0 then source ((sourceMap (T.role s p)).getD 0)
  else if i=1 then templateStack (T.role s p) else scratch
/-- Whole actual loader, then same static-record compiler/serializer/logger and halt. -/
def program : Label L s.roles.length→C.Instruction (Stack K) (Label L s.roles.length)
  | .inl .start=>.call (.inl (.load 0)) (.inl .record)
  | .inl (.load pos)=>if h:pos.val<s.roles.length then
      .base (.pop (templateStack (T.role s ⟨pos.val,h⟩)) (.inl (.copy ⟨pos.val,h⟩))
        (.inl (.load pos)) (.inl (.load pos))) else .ret
  | .inl (.copy pos)=>match sourceMap (T.role s pos) with
    | none=>.base (.jump (loadNext s pos))
    | some _=>.call (copyLabel pos 0) (loadNext s pos)
  | .inl .record=>.call (recordLabel (.inl .start)) (.inl .done)
  | .inl .done=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction recordStack recordLabel (R.program s pc)
  | .inr (.inr (pos,pc))=>SemiprimeD1StackMultiplierLink.instruction (copyStack s sourceMap pos)
      (copyLabel pos) (SemiprimeD1StackCopy.code pc)
/-- Proof-side exact template selected from actual acquired physical source words. -/
def selected (fields : Fin 6→List Bool) (k : K) : List Bool :=(sourceMap k).elim [] fields
/-- Complete physical store, retaining all actual source fields. -/
def data (component : R.Stack K→List Bool) (fields : Fin 6→List Bool) (work : List Bool) : Stack K→List Bool :=
  Sum.elim component (Sum.elim fields (fun _=>work))
/-- Only acquired source fields, scope/caller words and charged old template;
no computed checker metadata or answers enter the template. -/
def initial (oldTemplate : K→List Bool) (fields : Fin 6→List Bool) (bank hist out : List Bool) :
    C.State (Stack K) (Label L s.roles.length) :=
  ⟨some (.inl .start),none,none,data (SemiprimeD1StackStaticRecord.initial s oldTemplate bank hist out).data fields [],[]⟩
/-- Store after every template position has been physically drained/loaded. -/
def afterLoad (fields : Fin 6→List Bool) (bank hist out : List Bool) : Stack K→List Bool :=
  data (SemiprimeD1StackStaticRecord.initial s (selected sourceMap fields) bank hist out).data fields []
/-- Complete acquired record result with all six source fields retained. -/
def done (fields : Fin 6→List Bool) (words : List (List Bool)) (answer : List Bool→Bool)
    (hist out : List Bool) : C.State (Stack K) (Label L s.roles.length) :=
  ⟨none,none,none,data (SemiprimeD1StackStaticRecord.done s (selected sourceMap fields) words answer hist out).data fields [],[]⟩
/-- Genuine finite machine fixed only by the literal checker and literal source map. -/
def machine [Fintype K] [Fintype L] : Turing.FinTM2 :=
  SemiprimeD1StackCalls.machine original output (.inl .start) (program s sourceMap)
omit [DecidableEq K] in
/-- Complete physical inventory: all2K+28 record roles plus six inputs and scratch. -/
theorem stack_card [Fintype K] : Fintype.card (Stack K)=2*Fintype.card K+35 := by
  rw [Fintype.card_sum,SemiprimeD1StackStaticRecord.stack_card]
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
omit [DecidableEq K] in
/-- Every per-field copy has three disjoint operands, even when map values repeat. -/
theorem copyStack_injective (p : Fin s.roles.length) : Function.Injective (copyStack s sourceMap p) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [copyStack,source,templateStack,recordStack,R.tableStack,T.template,scratch]
end RiemannGaussian.SemiprimeD1StackDescriptorRecord
