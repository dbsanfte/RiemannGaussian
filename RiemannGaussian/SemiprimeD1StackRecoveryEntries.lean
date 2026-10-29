/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexed
import RiemannGaussian.SemiprimeD1StackFrame
import RiemannGaussian.SemiprimeD1StackReverseWord
/-! # Actual recovery-entry acquisition from row and nested-child tapes
Only the actual five-field canonical row tape and actual nested child-word
vector are supplied. Two real binary indexed scans acquire each coefficient.
Four actual frames and two physical reversal stages preserve exact entry order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntries
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace I
export SemiprimeD1StackRecoveryEntriesIndexed (Stack Label Aux program initial input aux)
end I
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Thirteen literal retained/source/row/logger roles beside the whole12-role lookup bank. -/
inductive Aux where
  | rows | reader | node | index | sign | magnitude | denominator | selectedRow | child
  | valid | history | frameBuffer | output
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList [.rows,.reader,.node,.index,.sign,.magnitude,.denominator,
  .selectedRow,.child,.valid,.history,.frameBuffer,.output] (by intro k;cases k <;> simp)
/-- All25 actual roles include both unused original lookup query/value shadows. -/
abbrev Stack:=I.Stack⊕Aux
/-- Complete physical indexed-reader bank, retaining every private/shadow role. -/
def indexed:I.Stack → Stack:=Sum.inl
/-- Original row, parsed metadata and physical entry logger fields. -/
def aux:Aux → Stack:=Sum.inr
/-- Original nested child-word tape remains directly in the actual retained cache role. -/
def children:Stack:=indexed (I.aux .cache)
/-- Complete acquired entry tape. -/
def output:Stack:=aux .output
/-- Restoring-copy scratch is reused only while the indexed reader is genuinely stopped clean. -/
def scratch:Stack:=indexed (I.aux .copy)
/-- Fixed outer/inner lookup inclusion; both allocated original query/value shadows remain counted. -/
def indexStack (inner:Bool) (k:I.Stack):Stack:=
  if k=I.aux .cache then if inner then aux .selectedRow else children
  else if k=I.aux .query then if inner then aux .index else aux .node
  else if k=I.aux .value then if inner then aux .child else aux .selectedRow else indexed k
/-- Actual five source fields, never a field getter runtime operand. -/
def fieldTarget (part:Fin 5):Stack:=
  if part=0 then aux .node else if part=1 then aux .index else if part=2 then aux .sign
  else if part=3 then aux .magnitude else aux .denominator
/-- Actual four-role canonical-row field parser. -/
def fieldStack (part:Fin 5):F.Stack → Stack
  | .inl .input=>aux .reader | .inl .scratch=>scratch | .inl .output=>fieldTarget part | .inr () =>aux .valid
/-- Actual retained input copy, executed once before any row scan. -/
def copyStack (k:Fin 3):Stack:=if k=0 then aux .rows else if k=1 then aux .reader else scratch
/-- Reverse-order framing physically prepends child,D,magnitude,sign onto the row buffer. -/
def frameSource (part:Fin 4):Stack:=
  if part=0 then aux .child else if part=1 then aux .denominator else if part=2 then aux .magnitude else aux .sign
/-- Actual real preserving Frame operands. -/
def frameStack (part:Fin 4) (k:Fin 3):Stack:=if k=0 then frameSource part else if k=1 then aux .frameBuffer else scratch
/-- Both actual reversal stages consume their real source bytes. -/
def reverseStack (finish:Bool) (k:Fin 2):Stack:=
  if k=0 then if finish then aux .history else aux .frameBuffer
  else if finish then output else aux .history
/-- Seven per-row acquired metadata/payload words are physically cleared after logging. -/
def clearTarget (part:Fin 7):Stack:=
  if part=0 then aux .node else if part=1 then aux .index else if part=2 then aux .sign
  else if part=3 then aux .magnitude else if part=4 then aux .denominator
  else if part=5 then aux .selectedRow else aux .child
/-- Fixed finite entry-loop control; no address, row, count or answer inhabits it. -/
inductive Control where
  | start | sentinel | loop | field (part:Fin 5) | valid (part:Fin 5)
  | outer | normalize | emptyRow | inner | frame (part:Fin 4) | tag | rowReverse
  | clear (part:Fin 7) | finish | done | abort
  deriving DecidableEq,Fintype,Repr
/-- Actual component and all real saved return labels are finite before both input tapes. -/
inductive Label where
  | local (pc:Control) | indexed (inner:Bool) (pc:I.Label) | field (part:Fin 5) (pc:F.Label)
  | copy (pc:Fin 9) | frame (part:Fin 4) (pc:Fin 11) | reverse (finish:Bool) (pc:Fin 4)
  deriving DecidableEq,Fintype,Repr
local notation "ctl"=>Label.local
/-- Static successor of an actual source-field parse. -/
def nextField (part:Fin 5):Label:=if h:part.val+1<5 then ctl (.field ⟨part.val+1,h⟩) else ctl .outer
/-- Static successor of an actual preserving frame call. -/
def nextFrame (part:Fin 4):Label:=if h:part.val+1<4 then ctl (.frame ⟨part.val+1,h⟩) else ctl .tag
/-- Static successor of an actual per-row drain. -/
def nextClear (part:Fin 7):Label:=if h:part.val+1<7 then ctl (.clear ⟨part.val+1,h⟩) else ctl .loop
/-- One fixed finite entry source; numeric addresses remain binary and every lookup stops at actual vector EOF. -/
def program:Label → C.Instruction Stack Label
  | .local .start=>.call (.copy 0) (ctl .sentinel)
  | .local .sentinel=>.base (.push output false (ctl .loop))
  | .local .loop=>.base (.pop (aux .reader) (ctl .abort) (ctl .finish) (ctl (.field 0)))
  | .local (.field part)=>.call (.field part (F.active .tagPop (none,false))) (ctl (.valid part))
  | .local (.valid part)=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (nextField part))
  | .local .outer=>.call (.indexed false (.local .start)) (ctl .normalize)
  | .local .normalize=>.base (.peek (aux .selectedRow) (ctl .emptyRow) (ctl .inner) (ctl .inner))
  | .local .emptyRow=>.base (.push (aux .selectedRow) false (ctl .inner))
  | .local .inner=>.call (.indexed true (.local .start)) (ctl (.frame 0))
  | .local (.frame part)=>.call (.frame part 0) (nextFrame part)
  | .local .tag=>.base (.push (aux .frameBuffer) true (ctl .rowReverse))
  | .local .rowReverse=>.call (.reverse false 0) (ctl (.clear 0))
  | .local (.clear part)=>.base (.pop (clearTarget part) (nextClear part) (ctl (.clear part)) (ctl (.clear part)))
  | .local .finish=>.call (.reverse true 0) (ctl .done)
  | .local .done|.local .abort=>.base .halt
  | .indexed inner pc=>SemiprimeD1StackValidationLink.instruction (indexStack inner) (Label.indexed inner) (I.program pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .frame part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
/-- Exactly two real source tapes, with no template, Entry structure, node/index getter or selected coefficient supplied. -/
def input (rowTape childTape:List Bool):Stack → List Bool:=
  Function.update (Function.update (fun _=>[]) (aux .rows) rowTape) children childTape
/-- Actual two-tape source entry starts with all private/result/counter/shadow roles clear. -/
def initial (rowTape childTape:List Bool):C.State Stack Label:=
  ⟨some (ctl .start),none,none,input rowTape childTape,[]⟩
/-- One parameterless fixed finite entry-acquisition machine. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .rows) output (ctl .start) program
/-- Every allocated physical tape and both unused indexed input/result shadows are counted. -/
theorem stack_card:Fintype.card Stack=25:=by decide
/-- Both actual binary reader inclusions have distinct physical roles. -/
theorem index_injective (inner:Bool):Function.Injective (indexStack inner):=by cases inner <;> decide
/-- Every actual row parser has four distinct physical operands. -/
theorem field_injective (part:Fin 5):Function.Injective (fieldStack part):=by fin_cases part <;> decide
/-- The one retained-row copy has three distinct actual operands. -/
theorem copy_injective:Function.Injective copyStack:=by decide
/-- Every real preserving frame has three distinct actual roles. -/
theorem frame_injective (part:Fin 4):Function.Injective (frameStack part):=by fin_cases part <;> decide
/-- Both real reversals have separate source and target words. -/
theorem reverse_injective (finish:Bool):Function.Injective (reverseStack finish):=by cases finish <;> decide
/-- Data and actual saved-return alphabets are fixed finite before both tapes. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite (aux .rows) output (ctl .start) program
/-- No natural value, list, getter, evaluator or answer occupies runtime transient control. -/
theorem control_finite:Finite machine.σ:=
  SemiprimeD1StackCalls.control_finite (aux .rows) output (ctl .start) program
end RiemannGaussian.SemiprimeD1StackRecoveryEntries
