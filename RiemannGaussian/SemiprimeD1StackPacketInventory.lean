/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventoryRoles
/-! # Literal sparse packet inventory from selected key vector and catalogue alone
Each actual raw key acquires its OLD class count before the real consuming
increment. Actual row/orientation sources use that retained binary index. Every
class, seen and slot-map write is a paid newest-first physical override. There
is no supplied index, packet, count, edge, Hpad, coordinate width or evaluator.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventory
export SemiprimeD1StackPacketInventoryRoles
  (Stack frequencyStack readerAllocation orientationAllocation source stream raw catalogue classes oldIndex edge seen slots
   packets placementHistory output lookupStack query oldCount count scratch marker success readerStack orientationStack
   packet slot buffer outerBuffer stack_card frequency_injective reader_injective orientation_injective
   orientation_globals_outside reader_globals_outside reader_oldIndex_outside scratch_ne_oldIndex)
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace F
export SemiprimeD1StackSourceKeyFrequency (Stack Label program aux lookupStack fieldStack)
end F
namespace R
export SemiprimeD1StackPacketRows (Stack Label program success Work workStack nextWork)
end R
namespace O
export SemiprimeD1StackPacketOrientation (Stack Label program answer Work work nextWork)
end O
namespace L
export SemiprimeD1StackOwnerLookup (Label program)
end L
namespace K
export SemiprimeD1StackOwnerEqualityKey (Label program)
end K
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
/-- Only two actual dictionary read sites; slot addresses are written without a supplied existing-slot answer. -/
inductive Read where | classes | seen deriving DecidableEq
/-- Literal complete read-site inventory. -/
instance :Fintype Read:=Fintype.ofList [.classes,.seen] (by intro k;cases k <;> simp)
/-- Three actual mutable map words, each retaining every physical override. -/
inductive Map where | classes | seen | slots deriving DecidableEq
/-- Literal complete map inventory. -/
instance :Fintype Map:=Fintype.ofList [.classes,.seen,.slots] (by intro k;cases k <;> simp)
/-- Fixed actual mutable map destinations. -/
def mapWord:Map→Stack | .classes=>classes | .seen=>seen | .slots=>slots
/-- Fixed actual read sources. -/
def readWord:Read→Stack | .classes=>classes | .seen=>seen
/-- Six real preserving-copy choices; the old-index copy precedes its consuming increment. -/
inductive Copy where | stream | dictionary (part:Read) | oldIndex | edgeOperand | edge | slotAddress
  deriving DecidableEq,Fintype
/-- Exact literal copy operands, always using the restored actual scratch word. -/
def copyStack (part:Copy) (k:Fin 3):Stack:=
  if k=0 then match part with
    | .stream=>source | .dictionary what=>readWord what | .oldIndex=>oldCount
    | .edgeOperand=>edge | .edge=>count | .slotAddress=>slot
  else if k=1 then match part with
    | .stream=>stream | .dictionary _=>lookupStack (.inr .reader) | .oldIndex=>oldIndex
    | .edgeOperand=>oldCount | .edge=>edge | .slotAddress=>buffer
  else scratch
/-- Every arbitrary raw class/packet/address key is sentinel-normalized by real instructions. -/
inductive Sentinel where | class | packet | address deriving DecidableEq
/-- Literal complete sentinel-site inventory. -/
instance :Fintype Sentinel:=Fintype.ofList [.class,.packet,.address] (by intro k;cases k <;> simp)
/-- Exact raw source, compact query destination and actual restoration scratch. -/
def sentinelStack (part:Sentinel) (k:Fin 3):Stack:=
  if k=0 then match part with | .class=>raw | .packet=>packet | .address=>buffer
  else if k=1 then query else scratch
/-- NEW frames use restored Copy scratch, NEVER the retained OLD-j word in frozen Frequency.frameScratch. -/
inductive Frame where
  | value (part:Map) | key (part:Map) | packet | address | placement (part:Fin 6) | outer
  deriving DecidableEq,Fintype
/-- Literal reversed six-field construction order: valid, edge, slot, packet, OLDpadding, source. -/
def placementWord (part:Fin 6):Stack:=
  if part=0 then marker else if part=1 then edge else if part=2 then slot else if part=3 then packet
  else if part=4 then oldIndex else raw
/-- Every key/value/placement Frame has a real preserving source, actual destination and separate restored scratch. -/
def frameStack (part:Frame) (k:Fin 3):Stack:=
  if k=0 then match part with
    | .value .classes=>count | .value .seen=>marker | .value .slots=>edge | .key _=>query
    | .packet | .address=>packet | .placement n=>placementWord n | .outer=>buffer
  else if k=1 then match part with
    | .value m | .key m=>mapWord m | .packet=>packets | .address | .placement _=>buffer | .outer=>outerBuffer
  else scratch
/-- Reversed row-fragment and final complete placement-history reversals. -/
inductive Reverse where | row | finish deriving DecidableEq
/-- Literal complete reversal-site inventory. -/
instance :Fintype Reverse:=Fintype.ofList [.row,.finish] (by intro k;cases k <;> simp)
/-- All output words are real buffers; no native List reversal executes. -/
def reverseStack (part:Reverse) (k:Fin 2):Stack:=
  if k=0 then match part with | .row=>outerBuffer | .finish=>placementHistory
  else match part with | .row=>placementHistory | .finish=>output
/-- Actual key-vector Field parser reuses the otherwise idle21-role reader scratch/valid words. -/
def fieldStack:Field.Stack→Stack:=fun k=>frequencyStack (F.fieldStack k)
/-- Fixed complete physical abort-sweep successor, independent of every input word. -/
def nextFrequency:F.Stack→Option F.Stack
  | .inl (.inl .left)=>some (.inl (.inl .right))
  | .inl (.inl .right)=>some (.inl (.inl .scratch))
  | .inl (.inl .scratch)=>some (.inl (.inl .output))
  | .inl (.inl .output)=>some (.inl (.inr .query))
  | .inl (.inr .query)=>some (.inl (.inr .reader))
  | .inl (.inr .reader)=>some (.inl (.inr .valid))
  | .inl (.inr .valid)=>some (.inl (.inr .fieldScratch))
  | .inl (.inr .fieldScratch)=>some (.inl (.inr .copyScratch))
  | .inl (.inr .copyScratch)=>some (.inl (.inr .discard))
  | .inl (.inr .discard)=>some (.inl (.inr .output))
  | .inl (.inr .output)=>some (.inr .source)
  | .inr .source=>some (.inr .reader)
  | .inr .reader=>some (.inr .raw)
  | .inr .raw=>some (.inr .dictionary)
  | .inr .dictionary=>some (.inr .count)
  | .inr .count=>some (.inr .maximum)
  | .inr .maximum=>some (.inr .incScratch)
  | .inr .incScratch=>some (.inr .incNext)
  | .inr .incNext=>some (.inr .trimScratch)
  | .inr .trimScratch=>some (.inr .frameScratch)
  | .inr .frameScratch=>none
/-- Fixed complete physical abort-sweep successor, independent of every input word. -/
def nextReader:R.Stack→Option R.Stack
  | .inl (.inl .left)=>some (.inl (.inl .right))
  | .inl (.inl .right)=>some (.inl (.inl .scratch))
  | .inl (.inl .scratch)=>some (.inl (.inl .output))
  | .inl (.inl .output)=>some (.inl (.inr .query))
  | .inl (.inr .query)=>some (.inl (.inr .reader))
  | .inl (.inr .reader)=>some (.inl (.inr .valid))
  | .inl (.inr .valid)=>some (.inl (.inr .fieldScratch))
  | .inl (.inr .fieldScratch)=>some (.inl (.inr .copyScratch))
  | .inl (.inr .copyScratch)=>some (.inl (.inr .discard))
  | .inl (.inr .discard)=>some (.inl (.inr .output))
  | .inl (.inr .output)=>some (.inr .key)
  | .inr .key=>some (.inr .catalogue)
  | .inr .catalogue=>some (.inr .keyReader)
  | .inr .keyReader=>some (.inr .leftBytes)
  | .inr .leftBytes=>some (.inr .leftHistory)
  | .inr .leftHistory=>some (.inr .rightHistory)
  | .inr .rightHistory=>some (.inr .leftOutput)
  | .inr .leftOutput=>some (.inr .rightOutput)
  | .inr .rightOutput=>none
/-- Fixed complete physical abort-sweep successor, independent of every input word. -/
def nextOrientation:O.Stack→Option O.Stack
  | .inl (.inl .left)=>some (.inl (.inl .right))
  | .inl (.inl .right)=>some (.inl (.inl .scratch))
  | .inl (.inl .scratch)=>some (.inl (.inl .output))
  | .inl (.inl .output)=>some (.inl (.inr ()))
  | .inl (.inr ())=>some (.inr .leftInput)
  | .inr .leftInput=>some (.inr .rightInput)
  | .inr .rightInput=>some (.inr .indexInput)
  | .inr .indexInput=>some (.inr .leftReader)
  | .inr .leftReader=>some (.inr .rightReader)
  | .inr .rightReader=>some (.inr .indexCursor)
  | .inr .indexCursor=>some (.inr .leftColour)
  | .inr .leftColour=>some (.inr .rightColour)
  | .inr .rightColour=>some (.inr .copyScratch)
  | .inr .copyScratch=>some (.inr .keyHistory)
  | .inr .keyHistory=>some (.inr .slotHistory)
  | .inr .slotHistory=>some (.inr .keyOutput)
  | .inr .keyOutput=>some (.inr .slotOutput)
  | .inr .slotOutput=>some (.inr .highOutput)
  | .inr .highOutput=>none
/-- Every runtime choice is a fixed finite label or an actually read Boolean. -/
inductive Control where
  | start | seedSeen | seedSlots | seedPackets | copyStream | header | parse | valid | encodeClass
  | copyMap (part:Read) | lookup (part:Read) | clearLookupReader (part:Read) | copyOldIndex | incrementClass
  | frameValue (part:Map) | frameKey (part:Map) | tagMap (part:Map) | clearClassQuery | clearClassCount
  | readRows | rowsValid | orient | orientationValid | copyEdgeOperand | incrementEdge | clearEdge | saveEdge | clearEdgeCount
  | clearHigh | copyAddress | frameAddress | encodeAddress | clearSlotQuery | clearAddress | encodePacket
  | readSeen | seenEOF | prependPacket | tagPacket | pushMarker | clearSeenQuery | placement (part:Fin 6)
  | tagPlacement | framePlacement | reversePlacement | clearPlacement | clearMarker | clearOldIndex | clearRaw
  | clearReader (part:R.Work) | clearOrientation (part:O.Work) | eof | seedOutput | reverseOutput | accept | done
  | abort | abortFrequency (part:F.Stack) | abortReader (part:R.Stack) | abortOrientation (part:O.Stack) | aborted
  deriving Fintype
/-- All actual helper/callee return labels are finite before every graph, catalogue and occurrence stream. -/
inductive Label where
  | local (pc:Control) | frequency (pc:F.Label) | readerCode (pc:R.Label) | orientationCode (pc:O.Label)
  | lookupCode (pc:L.Label) | sentinel (part:Sentinel) (pc:K.Label) | copier (part:Copy) (pc:Fin 9)
  | field (pc:Field.Label) | frame (part:Frame) (pc:Fin 11) | reverse (part:Reverse) (pc:Fin 4)
  deriving Fintype
local notation "ctl"=>Label.local
/-- One literal two-input sparse inventory program, without key/count/index/packet/Hpad/evaluator suppliers. -/
def program:Label→C.Instruction Stack Label
  | .local .start=>.base (.push classes false (ctl .seedSeen))
  | .local .seedSeen=>.base (.push seen false (ctl .seedSlots))
  | .local .seedSlots=>.base (.push slots false (ctl .seedPackets))
  | .local .seedPackets=>.base (.push packets false (ctl .copyStream))
  | .local .copyStream=>.call (.copier .stream 0) (ctl .header)
  | .local .header=>.base (.pop stream (ctl .abort) (ctl .eof) (ctl .parse))
  | .local .parse=>.call (.field (Field.active .tagPop (none,false))) (ctl .valid)
  | .local .valid=>.base (.pop (lookupStack (.inr .valid)) (ctl .abort) (ctl .abort) (ctl .encodeClass))
  | .local .encodeClass=>.call (.sentinel .class (.inl 0)) (ctl (.copyMap .classes))
  | .local (.copyMap what)=>.call (.copier (.dictionary what) 0) (ctl (.lookup what))
  | .local (.lookup what)=>.call (.lookupCode .loop) (ctl (.clearLookupReader what))
  | .local (.clearLookupReader what)=>.base (.pop (lookupStack (.inr .reader))
      (ctl (match what with | .classes=>.copyOldIndex | .seen=>.readSeen))
      (ctl (.clearLookupReader what)) (ctl (.clearLookupReader what)))
  | .local .copyOldIndex=>.call (.copier .oldIndex 0) (ctl .incrementClass)
  | .local .incrementClass=>.call (.frequency .increment) (ctl (.frameValue .classes))
  | .local (.frameValue what)=>.call (.frame (.value what) 0) (ctl (.frameKey what))
  | .local (.frameKey what)=>.call (.frame (.key what) 0) (ctl (.tagMap what))
  | .local (.tagMap what)=>.base (.push (mapWord what) true
      (ctl (match what with | .classes=>.clearClassQuery | .seen=>.clearSeenQuery | .slots=>.clearSlotQuery)))
  | .local .clearClassQuery=>.base (.pop query (ctl .clearClassCount) (ctl .clearClassQuery) (ctl .clearClassQuery))
  | .local .clearClassCount=>.base (.pop count (ctl .readRows) (ctl .clearClassCount) (ctl .clearClassCount))
  | .local .readRows=>.call (.readerCode (.local .start)) (ctl .rowsValid)
  | .local .rowsValid=>.base (.pop (readerStack R.success) (ctl .abort) (ctl .abort) (ctl .orient))
  | .local .orient=>.call (.orientationCode (.local .start)) (ctl .orientationValid)
  | .local .orientationValid=>.base (.pop (orientationStack O.answer) (ctl .abort) (ctl .abort) (ctl .copyEdgeOperand))
  | .local .copyEdgeOperand=>.call (.copier .edgeOperand 0) (ctl .incrementEdge)
  | .local .incrementEdge=>.call (.frequency .increment) (ctl .clearEdge)
  | .local .clearEdge=>.base (.pop edge (ctl .saveEdge) (ctl .clearEdge) (ctl .clearEdge))
  | .local .saveEdge=>.call (.copier .edge 0) (ctl .clearEdgeCount)
  | .local .clearEdgeCount=>.base (.pop count (ctl .clearHigh) (ctl .clearEdgeCount) (ctl .clearEdgeCount))
  | .local .clearHigh=>.base (.pop buffer (ctl .copyAddress) (ctl .clearHigh) (ctl .clearHigh))
  | .local .copyAddress=>.call (.copier .slotAddress 0) (ctl .frameAddress)
  | .local .frameAddress=>.call (.frame .address 0) (ctl .encodeAddress)
  | .local .encodeAddress=>.call (.sentinel .address (.inl 0)) (ctl (.frameValue .slots))
  | .local .clearSlotQuery=>.base (.pop query (ctl .clearAddress) (ctl .clearSlotQuery) (ctl .clearSlotQuery))
  | .local .clearAddress=>.base (.pop buffer (ctl .encodePacket) (ctl .clearAddress) (ctl .clearAddress))
  | .local .encodePacket=>.call (.sentinel .packet (.inl 0)) (ctl (.copyMap .seen))
  | .local .readSeen=>.base (.pop oldCount (ctl .prependPacket) (ctl .abort) (ctl .seenEOF))
  | .local .seenEOF=>.base (.peek oldCount (ctl .pushMarker) (ctl .abort) (ctl .abort))
  | .local .prependPacket=>.call (.frame .packet 0) (ctl .tagPacket)
  | .local .tagPacket=>.base (.push packets true (ctl .pushMarker))
  | .local .pushMarker=>.base (.push marker true (ctl (.frameValue .seen)))
  | .local .clearSeenQuery=>.base (.pop query (ctl (.placement 0)) (ctl .clearSeenQuery) (ctl .clearSeenQuery))
  | .local (.placement part)=>.call (.frame (.placement part) 0)
      (ctl (if part=0 then .placement 1 else if part=1 then .placement 2 else if part=2 then .placement 3
        else if part=3 then .placement 4 else if part=4 then .placement 5 else .tagPlacement))
  | .local .tagPlacement=>.base (.push placementHistory true (ctl .framePlacement))
  | .local .framePlacement=>.call (.frame .outer 0) (ctl .reversePlacement)
  | .local .reversePlacement=>.call (.reverse .row 0) (ctl .clearPlacement)
  | .local .clearPlacement=>.base (.pop buffer (ctl .clearMarker) (ctl .clearPlacement) (ctl .clearPlacement))
  | .local .clearMarker=>.base (.pop marker (ctl .clearOldIndex) (ctl .clearMarker) (ctl .clearMarker))
  | .local .clearOldIndex=>.base (.pop oldIndex (ctl .clearRaw) (ctl .clearOldIndex) (ctl .clearOldIndex))
  | .local .clearRaw=>.base (.pop raw (ctl (.clearReader .leftWord)) (ctl .clearRaw) (ctl .clearRaw))
  | .local (.clearReader part)=>.base (.pop (readerStack (R.workStack part))
      (ctl (match R.nextWork part with | some p=>.clearReader p | none=>.clearOrientation .leftOperand))
      (ctl (.clearReader part)) (ctl (.clearReader part)))
  | .local (.clearOrientation part)=>.base (.pop (orientationStack (O.work part))
      (ctl (match O.nextWork part with | some p=>.clearOrientation p | none=>.header))
      (ctl (.clearOrientation part)) (ctl (.clearOrientation part)))
  | .local .eof=>.base (.peek stream (ctl .seedOutput) (ctl .abort) (ctl .abort))
  | .local .seedOutput=>.base (.push output false (ctl .reverseOutput))
  | .local .reverseOutput=>.call (.reverse .finish 0) (ctl .accept)
  | .local .accept=>.base (.push success true (ctl .done))
  | .local .done=>.base .halt
  | .local .abort=>.base (.jump (ctl (.abortFrequency (.inl (.inl .left)))))
  | .local (.abortFrequency part)=>
      let next:=ctl (match nextFrequency part with | some p=>.abortFrequency p | none=>.abortReader (.inl (.inl .left)))
      if frequencyStack part=source then .base (.jump next)
      else .base (.pop (frequencyStack part) next (ctl (.abortFrequency part)) (ctl (.abortFrequency part)))
  | .local (.abortReader part)=>.base (.pop (readerAllocation part)
      (ctl (match nextReader part with | some p=>.abortReader p | none=>.abortOrientation (.inl (.inl .left))))
      (ctl (.abortReader part)) (ctl (.abortReader part)))
  | .local (.abortOrientation part)=>
      let next:=ctl (match nextOrientation part with | some p=>.abortOrientation p | none=>.aborted)
      if orientationAllocation part=catalogue then .base (.jump next)
      else .base (.pop (orientationAllocation part) next (ctl (.abortOrientation part)) (ctl (.abortOrientation part)))
  | .local .aborted=>.base (.push success false (ctl .done))
  | .frequency pc=>SemiprimeD1StackValidationLink.instruction frequencyStack Label.frequency (F.program pc)
  | .readerCode pc=>SemiprimeD1StackValidationLink.instruction readerStack Label.readerCode (R.program pc)
  | .orientationCode pc=>SemiprimeD1StackValidationLink.instruction orientationStack Label.orientationCode (O.program pc)
  | .lookupCode pc=>SemiprimeD1StackValidationLink.instruction lookupStack Label.lookupCode (L.program pc)
  | .sentinel part pc=>SemiprimeD1StackValidationLink.instruction (sentinelStack part) (Label.sentinel part) (K.program pc)
  | .copier part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copier part) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)
  | .frame part pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack part) (Label.frame part) (SemiprimeD1StackFrame.code pc)
  | .reverse part pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack part) (Label.reverse part) (SemiprimeD1StackReverseWord.code pc)
/-- Exactly two physically acquired words are present initially. -/
def input (keys alphabet:List Bool):Stack→List Bool:=Function.update (Function.update (fun _=>[]) source keys) catalogue alphabet
/-- Whole actual sparse replay front door, without a supplied old count, row, index, packet or edge. -/
def initial (keys alphabet:List Bool):C.State Stack Label:=⟨some (ctl .start),none,none,input keys alphabet,[]⟩
/-- One fixed finite fifty-nine-role machine before every source vector and alphabet. -/
def machine:Turing.FinTM2:=SemiprimeD1StackCalls.machine source output (ctl .start) program
/-- Every actual copy has three distinct physical roles. -/
theorem copy_injective (part:Copy):Function.Injective (copyStack part):=by cases part <;> first | cases ‹Read› <;> decide | decide
/-- Every actual sentinel source, query and scratch address is distinct. -/
theorem sentinel_injective (part:Sentinel):Function.Injective (sentinelStack part):=by cases part <;> decide
/-- Every actual Frame preserves OLD j by using the real restored Copy scratch. -/
theorem frame_injective (part:Frame):Function.Injective (frameStack part):=by
  cases part with
  | value m=>cases m <;> decide
  | key m=>cases m <;> decide
  | packet=>decide
  | address=>decide
  | placement p=>fin_cases p <;> decide
  | outer=>decide
/-- All actual reverse operands are distinct physical buffers. -/
theorem reverse_injective (part:Reverse):Function.Injective (reverseStack part):=by cases part <;> decide
/-- Field source/output/scratch/valid addresses are actual distinct words. -/
theorem field_injective:Function.Injective fieldStack:=frequency_injective.comp SemiprimeD1StackSourceKeyFrequency.field_injective
/-- All59 Boolean data alphabets and genuine return alphabets are fixed finite. -/
theorem alphabets_finite:∀k,Finite (machine.Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
/-- Runtime sigma contains no numeric count, list, evaluator, callback or decoded packet. -/
theorem control_finite:Finite machine.σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackPacketInventory
