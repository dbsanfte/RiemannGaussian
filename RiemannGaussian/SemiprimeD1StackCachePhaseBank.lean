/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankInventory
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual issued-reference phase-bank iterator
Exactly four physical words enter: heap/counter, issued-reference vector and
per-phase child tapes. Each matched phase performs one actual CachePhase238
call, logs its real block output and drains all236 nonpersistent callee words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBank
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace P
export SemiprimeD1StackCachePhase
  (Stack Label program input initial restoreStack foldStack blockStack copyScratch)
end P
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace I
export SemiprimeD1StackCachePhaseBankInventory (roles role roles_length roles_nodup roles_complete role_injective role_complete)
end I
/-- Eight actual retained-stream/parser/logger roles outside the complete238-role callee. -/
inductive Aux where
  | references | children | referenceReader | childReader | valid | history | buffer | output
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.references,.children,.referenceReader,.childReader,.valid,.history,.buffer,.output]
  (by intro k;cases k <;> simp)
/-- All246 allocated physical roles; no source shadow is removed from this inventory. -/
abbrev Stack:=P.Stack⊕Aux
/-- Complete literal238-role cached-phase bank inclusion. -/
def cached:P.Stack→Stack:=Sum.inl
/-- Real retained stream/parser/logger address. -/
def aux:Aux→Stack:=Sum.inr
/-- Original immutable physical cache heap. -/
def heap:Stack:=cached (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .heap))
/-- Original immutable physical allocation counter. -/
def counter:Stack:=cached (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .counter))
/-- Current actual issued reference, supplied only by the real outer Field parser. -/
def reference:Stack:=cached (P.restoreStack (SemiprimeD1StackCachePhase.Restore.heapStack .reference))
/-- Current actual recursive-child tape, supplied only by the matching real Field parser. -/
def child:Stack:=cached (P.foldStack (SemiprimeD1StackCachePhase.Fold.aux .children))
/-- Genuine current per-phase block vector, including a literal false-only rejected vector. -/
def phaseOutput:Stack:=cached (P.blockStack (SemiprimeD1StackCachePhase.Blocks.aux .output))
/-- Borrowed only at proved-empty stopped boundaries; used as final status after every other operation finishes. -/
def scratch:Stack:=cached P.copyScratch
/-- Complete acquired original-order phase bank. -/
def output:Stack:=aux .output
/-- Final singleton true/false status occupies the now idle, actually cleared callee copy scratch. -/
def status:Stack:=scratch
/-- Both real preserving copies use the restored actual scratch. -/
def copyStack (children:Bool) (k:Fin 3):Stack:=
  if k=0 then aux (if children then .children else .references)
  else if k=1 then aux (if children then .childReader else .referenceReader) else scratch
/-- Actual matching stream Field parsers; no reference or child result is supplied separately. -/
def fieldStack (children:Bool):Field.Stack→Stack
  | .inl .input=>aux (if children then .childReader else .referenceReader)
  | .inl .scratch=>scratch
  | .inl .output=>if children then child else reference
  | .inr () =>aux .valid
/-- The actual phase result is preserved while physically framed into the outer log buffer. -/
def frameStack (k:Fin 3):Stack:=if k=0 then phaseOutput else if k=1 then aux .buffer else scratch
/-- Both actual row and final reversals consume their real source bytes. -/
def reverseStack (finish:Bool) (k:Fin 2):Stack:=
  if k=0 then aux (if finish then .history else .buffer)
  else if finish then output else aux .history
/-- The only two actual callee roles excluded from every cleanup pass. -/
def persistent (k:P.Stack):Bool:=decide (cached k=heap ∨cached k=counter)
/-- Six actual abort work words; the two original stream inputs are retained. -/
def abortWord (part:Fin 6):Stack:=aux
  (if part=0 then .referenceReader else if part=1 then .childReader else if part=2 then .valid
    else if part=3 then .history else if part=4 then .buffer else .output)
/-- Finite literal controller, including explicit mismatched/unterminated-stream rejection. -/
inductive Control where
  | start | copyChildren | sentinel | header | referenceField | referenceValid | childHeader | childField | childValid
  | phase | frame | tag | append | clear (aborted:Bool) (part:Fin 238)
  | referenceEOF | childTail | childEOF | finish | accept | done | abort | abortAux (part:Fin 6) | reject
  deriving DecidableEq,Fintype,Repr
/-- Every callee label and genuine saved return is fixed finite before all four input words. -/
inductive Label where
  | local (pc:Control) | phase (pc:P.Label) | copy (children:Bool) (pc:Fin 9)
  | field (children:Bool) (pc:Field.Label) | frame (pc:Fin 11) | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
local notation "ctl"=>Label.local
/-- The finite cleanup successor depends only on its fixed port label, never an input index or value. -/
def nextClear (aborted:Bool) (part:Fin 238):Label:=
  if h:part.val+1<238 then ctl (.clear aborted ⟨part.val+1,h⟩)
  else ctl (if aborted then .abortAux 0 else .header)
/-- Actual fixed abort-work successor. -/
def nextAbort (part:Fin 6):Label:=if h:part.val+1<6 then ctl (.abortAux ⟨part.val+1,h⟩) else ctl .reject
/-- One parameterless physical four-input phase-bank source, with every scan/call/log/cleanup instruction literal. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.call (.copy false 0) (ctl .copyChildren)
  | .local .copyChildren=>.call (.copy true 0) (ctl .sentinel)
  | .local .sentinel=>.base (.push output false (ctl .header))
  | .local .header=>.base (.pop (aux .referenceReader) (ctl .abort) (ctl .referenceEOF) (ctl .referenceField))
  | .local .referenceField=>.call (.field false (Field.active .tagPop (none,false))) (ctl .referenceValid)
  | .local .referenceValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .childHeader))
  | .local .childHeader=>.base (.pop (aux .childReader) (ctl .abort) (ctl .abort) (ctl .childField))
  | .local .childField=>.call (.field true (Field.active .tagPop (none,false))) (ctl .childValid)
  | .local .childValid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .phase))
  | .local .phase=>.call (.phase (.local .start)) (ctl .frame)
  | .local .frame=>.call (.frame 0) (ctl .tag)
  | .local .tag=>.base (.push (aux .buffer) true (ctl .append))
  | .local .append=>.call (.reverse false 0) (ctl (.clear false 0))
  | .local (.clear aborted part)=>
      if persistent (I.role part) then .base (.jump (nextClear aborted part))
      else .base (.pop (cached (I.role part)) (nextClear aborted part) (ctl (.clear aborted part)) (ctl (.clear aborted part)))
  | .local .referenceEOF=>.base (.peek (aux .referenceReader) (ctl .childTail) (ctl .abort) (ctl .abort))
  | .local .childTail=>.base (.pop (aux .childReader) (ctl .abort) (ctl .childEOF) (ctl .abort))
  | .local .childEOF=>.base (.peek (aux .childReader) (ctl .finish) (ctl .abort) (ctl .abort))
  | .local .finish=>.call (.reverse true 0) (ctl .accept)
  | .local .accept=>.base (.push status true (ctl .done))
  | .local .abort=>.base (.jump (ctl (.clear true 0)))
  | .local (.abortAux part)=>.base (.pop (abortWord part) (nextAbort part) (ctl (.abortAux part)) (ctl (.abortAux part)))
  | .local .reject=>.base (.push status false (ctl .done))
  | .local .done=>.base .halt
  | .phase pc=>SemiprimeD1StackValidationLink.instruction cached Label.phase (P.program pc)
  | .copy children pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack children) (Label.copy children) (SemiprimeD1StackCopy.code pc)
  | .field children pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack children) (Label.field children) (Field.code pc)
  | .frame pc=>SemiprimeD1StackMultiplierLink.instruction frameStack Label.frame (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
/-- Only four real words are installed: immutable heap/counter and the two actual outer vectors. -/
def input (hp cn refs children:List Bool):Stack→List Bool:=Sum.elim (P.input hp cn [] [])
  (fun k=>if k=.references then refs else if k=.children then children else [])
/-- The real four-input source starts with every other242 actual role empty. -/
def initial (hp cn refs children:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input hp cn refs children,[]⟩
/-- Genuine fixed246-tape compiled machine, without a child solver or original-N source claim. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine heap output (ctl .start) program
/-- Every238 callee allocation and all8 actual outer words remain counted. -/
theorem stack_card:Fintype.card Stack=246:=by rw [Fintype.card_sum,SemiprimeD1StackCachePhase.stack_card];decide
/-- All physical cached component roles remain distinct. -/
theorem cached_injective:Function.Injective cached:=Sum.inl_injective
/-- Every actual preserving-copy operand is distinct. -/
theorem copy_injective (children:Bool):Function.Injective (copyStack children):=by cases children <;> decide
/-- Both physical stream parsers use distinct real words. -/
theorem field_injective (children:Bool):Function.Injective (fieldStack children):=by cases children <;> decide
/-- Real phase-output frame has distinct source/buffer/scratch words. -/
theorem frame_injective:Function.Injective frameStack:=by decide
/-- Both genuine reversal sources and destinations are distinct. -/
theorem reverse_injective (finish:Bool):Function.Injective (reverseStack finish):=by cases finish <;> decide
/-- Data and real return alphabets are fixed finite before every operand. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite heap output (ctl .start) program
/-- Runtime contains only finite labels and read flags; no phase object, coordinate cache, function or native count. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite heap output (ctl .start) program
end RiemannGaussian.SemiprimeD1StackCachePhaseBank
