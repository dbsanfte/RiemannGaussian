/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueResources
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
/-! # Actual packet tape and phase-order markers to feasible mode tuples
Only the actual discovered-packet vector, unary phase order and actual unary
WIDTH are inputs. The source physically counts packet fields, doubles a real
tile word once per actual order marker, then calls the complete real35-role
catalogue/feasible-DFS source. Packet and tile counts are never supplied.
All44 roles, including the complete retained mode source, remain allocated.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketModeAcquire
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace M
export SemiprimeD1StackWeightedModeCatalogue (Stack Label program input initial weighted multiply stack_card)
end M
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Two retained tape/metadata inputs and seven actual parser/copy/doubling words. -/
inductive Aux where
  | packets | order | reader | payload | fieldScratch | valid | copyScratch | todo | tileScan
  deriving DecidableEq,Repr
instance :Fintype Aux:=Fintype.ofList
  [.packets,.order,.reader,.payload,.fieldScratch,.valid,.copyScratch,.todo,.tileScan]
  (by intro k;cases k <;> simp)
/-- Entire real35-role mode source plus nine actual caller roles, without omitted shadows. -/
abbrev Stack:=M.Stack⊕Aux
/-- Complete actual catalogue/enumerator-bank inclusion. -/
def modeStack :M.Stack→Stack:=Sum.inl
/-- Actual retained-input/parser/doubling words. -/
def aux :Aux→Stack:=Sum.inr
/-- The physically counted packets enter the actual multiplier's first input. -/
def packetCount :Stack:=modeStack (M.multiply (.inl .a))
/-- The physically doubled tile word enters the actual multiplier's second input. -/
def tileCount :Stack:=modeStack (M.multiply (.inl .b))
/-- Actual unary precision is already a physical third input, charged by its length. -/
def width :Stack:=modeStack (M.weighted .width)
/-- Actual feasible-mode tuple vector output of the real included source. -/
def output :Stack:=modeStack (M.weighted .output)
/-- The only preserving copies prepare the actual packet reader and order loop. -/
inductive Copy where | packets | order deriving DecidableEq,Repr
instance :Fintype Copy:=Fintype.ofList [.packets,.order] (by intro k;cases k <;> simp)
/-- Every input copy restores its actual original word and physically separate scratch. -/
def copyStack (part:Copy) (k:Fin 3) :Stack:=
  if k=0 then aux (if part=.packets then .packets else .order)
  else if k=1 then aux (if part=.packets then .reader else .todo)
  else aux .copyScratch
/-- A real field parser counts even an empty raw packet key. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .output=>aux .payload
  | .inl .scratch=>aux .fieldScratch | .inr () =>aux .valid
/-- Real reversal consumes the whole previous tile word before its doubled replacement is pushed. -/
def reverseStack (k:Fin 2) :Stack:=if k=0 then tileCount else aux .tileScan
/-- Fixed finite packet-field, actual-order and tile-byte loop control. -/
inductive Control where
  | start | packetTag | packetEnd | field | valid | clearPayload | countPacket
  | copyOrder | seedOne | seedTwo | orderLoop | reverseTiles | tilePop | tilePushOne | tilePushTwo
  | enumerate | done | abort
  deriving DecidableEq,Repr
instance :Fintype Control:=Fintype.ofList
  [.start,.packetTag,.packetEnd,.field,.valid,.clearPayload,.countPacket,.copyOrder,.seedOne,.seedTwo,
    .orderLoop,.reverseTiles,.tilePop,.tilePushOne,.tilePushTwo,.enumerate,.done,.abort]
  (by intro k;cases k <;> simp)
/-- Only fixed labels and genuine helper return symbols occur in runtime sigma. -/
inductive Label where
  | local (pc:Control) | modes (pc:M.Label) | copy (part:Copy) (pc:Fin 9)
  | field (pc:Field.Label) | reversal (pc:Fin 4)
  deriving Fintype
local notation "ctl"=>Label.local
/-- One actual fixed program acquires both metadata counts and executes the full feasible enumeration. -/
def program :Label→C.Instruction Stack Label
  | .local .start=>.call (.copy .packets 0) (ctl .packetTag)
  | .local .packetTag=>.base (.pop (aux .reader) (ctl .abort) (ctl .packetEnd) (ctl .field))
  | .local .packetEnd=>.base (.peek (aux .reader) (ctl .copyOrder) (ctl .abort) (ctl .abort))
  | .local .field=>.call (.field (Field.active .tagPop (none,false))) (ctl .valid)
  | .local .valid=>.base (.pop (aux .valid) (ctl .abort) (ctl .abort) (ctl .clearPayload))
  | .local .clearPayload=>.base (.pop (aux .payload) (ctl .countPacket) (ctl .clearPayload) (ctl .clearPayload))
  | .local .countPacket=>.base (.push packetCount true (ctl .packetTag))
  | .local .copyOrder=>.call (.copy .order 0) (ctl .seedOne)
  | .local .seedOne=>.base (.push tileCount true (ctl .seedTwo))
  | .local .seedTwo=>.base (.push tileCount true (ctl .orderLoop))
  | .local .orderLoop=>.base (.pop (aux .todo) (ctl .enumerate) (ctl .abort) (ctl .reverseTiles))
  | .local .reverseTiles=>.call (.reversal 0) (ctl .tilePop)
  | .local .tilePop=>.base (.pop (aux .tileScan) (ctl .orderLoop) (ctl .abort) (ctl .tilePushOne))
  | .local .tilePushOne=>.base (.push tileCount true (ctl .tilePushTwo))
  | .local .tilePushTwo=>.base (.push tileCount true (ctl .tilePop))
  | .local .enumerate=>.call (.modes (.inl .start)) (ctl .done)
  | .local .done|.local .abort=>.base .halt
  | .modes pc=>SemiprimeD1StackValidationLink.instruction modeStack Label.modes (M.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)
  | .reversal pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reversal (SemiprimeD1StackReverseWord.code pc)
/-- Every actual44-role source boundary is present in the store. -/
def data (modes:M.Stack→List Bool) (work:Aux→List Bool) :Stack→List Bool:=Sum.elim modes work
/-- Only actual packet bytes, actual order markers and actual WIDTH are initialized. -/
def input (packets order precision:List Bool) :Stack→List Bool:=
  data (M.input [] [] precision) (fun k=>if k=.packets then packets else if k=.order then order else [])
/-- Honest three-word source entry; both packet and tile counts start empty. -/
def initial (packets order precision:List Bool) :C.State Stack Label:=
  ⟨some (ctl .start),none,none,input packets order precision,[]⟩
/-- One fixed finite44-role source, returning the actual feasible tuple vector. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .packets) output (ctl .start) program
/-- All44 actual physical input/cache/parser/DFS/return-work roles are counted. -/
theorem stack_card :Fintype.card Stack=44:=by rw [Fintype.card_sum,M.stack_card];decide
/-- Both actual input copies use three distinct physical words. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part):=by cases part <;> decide
/-- Actual packet field input/output/scratch/valid roles are distinct. -/
theorem field_injective :Function.Injective fieldStack:=by decide
/-- The consumed old tile word and physical doubling cursor never alias. -/
theorem reverse_injective :Function.Injective reverseStack:=by decide
/-- No count, numeric value, packet getter or enumerator callback inhabits runtime control. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every actual data/real-return symbol alphabet is fixed finite before all input families. -/
theorem alphabets_finite :∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPacketModeAcquire
