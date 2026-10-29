/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingResources
/-! # N-only actual all-original-owner fibre catalogue source
After actual original routing, the source copies its retained E tally and M-ID
bank. It physically reads the FIRST E bank words, copies the actual routed tape
for every owner, executes real fibre filtering and emits each owner with its
actual ordered scope-ID vector. No owner list, E/M count, scope list, degree or
permutation is supplied. Execution proofs follow in separate modules.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogue
namespace C
export SemiprimeD1StackCalls (Instruction State run step execute)
end C
namespace R
export SemiprimeD1StackPortOwnerRouting (Stack Label program originalInput input)
end R
namespace V
export SemiprimeD1StackOwnerFibre (Stack Label program)
end V
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Nine fixed reader, actual E-loop, parser and output-collector roles. -/
inductive Aux where
  | readerIds | ownerCount | copyScratch | fieldScratch | valid | frameBuffer | frameScratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux :=Fintype.ofList [.readerIds,.ownerCount,.copyScratch,.fieldScratch,.valid,
  .frameBuffer,.frameScratch,.reversed,.output] (by intro k;cases k <;> simp)
/-- Complete actual routing source, real fourteen-role fibre filter and nine private outer roles. -/
abbrev Stack :=R.Stack⊕(V.Stack⊕Aux)
/-- Actual upstream N-only routing inclusion, retained across ALL owners. -/
def source (k:R.Stack) : Stack :=.inl k
/-- Actual numeric owner-fibre filter inclusion. -/
def fibreStack (k:V.Stack) : Stack :=.inr (.inl k)
/-- Actual private outer metadata/reader/output role. -/
def aux (k:Aux) : Stack :=.inr (.inr k)
/-- Only original binary N is initially loaded. -/
def originalInput : Stack :=source R.originalInput
/-- Actual original E tally retained from the physical old edge scan. -/
def sourceCount : Stack :=source (SemiprimeD1StackPortOwnerRouting.mapStack
  (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.wireCount))
/-- Actual original M-word bank retained from real tally allocation and increment generation. -/
def sourceIds : Stack :=source (SemiprimeD1StackPortOwnerRouting.mapStack
  (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.ids))
/-- Actual computed factor-major original owner/scope routing tape. -/
def sourcePairs : Stack :=source (SemiprimeD1StackPortOwnerRouting.aux .output)
/-- Actual preserving E-count, whole M-bank and per-owner routed-tape copies. -/
def copyStack (part:Fin 3) (k:Fin 3) : Stack :=
  if k=0 then (if part=0 then sourceCount else if part=1 then sourceIds else sourcePairs)
  else if k=1 then (if part=0 then aux .ownerCount else if part=1 then aux .readerIds else fibreStack (.inr .reader))
  else aux .copyScratch
/-- The next owner query is physically parsed from the actual bank into the real filter's query role. -/
def fieldStack : F.Stack→Stack
  | .inl .input=>aux .readerIds | .inl .scratch=>aux .fieldScratch
  | .inl .output=>fibreStack (.inr .query) | .inr _=>aux .valid
/-- Actual output is owner ID then its complete ACTUALLY filtered ordered scope-ID vector bytes. -/
def frameStack (scopes:Bool) (k:Fin 3) : Stack :=
  if k=0 then fibreStack (.inr (if scopes then .output else .query))
  else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual per-field or whole-catalogue physical reversal. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- ALL fourteen actually used filter words are physically drained between original owners. -/
def fibreRole : Fin 14→V.Stack :=
  ![.inl .left,.inl .right,.inl .scratch,.inl .output,.inr .query,.inr .reader,
    .inr .fieldScratch,.inr .valid,.inr .copyScratch,.inr .payload,.inr .output,
    .inr .frameBuffer,.inr .frameScratch,.inr .reversed]
/-- Finite original E-loop and physical parser/logger positions. -/
inductive Control where
  | main | copyCount | copyIds | loop | bankTag | field | valid | copyPairs | filter | emitTag
  | emitField (scopes:Bool) | emitReverse (scopes:Bool) | clearFibre (part:Fin 14)
  | finalTag | finalReverse | halt | abort
  deriving Fintype
/-- Static source/filter and real bytecode call labels, all fixed before every N. -/
inductive Label where
  | local (pc:Control) | source (pc:R.Label) | fibre (pc:V.Label)
  | copy (part:Fin 3) (pc:Fin 9) | field (pc:F.Label)
  | frame (scopes:Bool) (pc:Fin 11) | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- Actual original-N acquisition and FIRST-E-owner loop, with no E=M or 2e+endpoint assumption. -/
def program : Label→C.Instruction Stack Label
  | .source pc=>SemiprimeD1StackValidationLink.instruction source Label.source (R.program pc)
  | .fibre pc=>SemiprimeD1StackValidationLink.instruction fibreStack Label.fibre (V.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .frame scopes pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack scopes) (Label.frame scopes) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
  | .local .main=>.call (.source (.local .main)) (.local .copyCount)
  | .local .copyCount=>.call (.copy 0 0) (.local .copyIds)
  | .local .copyIds=>.call (.copy 1 0) (.local .loop)
  | .local .loop=>.base (.pop (aux .ownerCount) (.local .finalTag) (.local .abort) (.local .bankTag))
  | .local .bankTag=>.base (.pop (aux .readerIds) (.local .abort) (.local .abort) (.local .field))
  | .local .field=>.call (.field (F.active .tagPop (none,false))) (.local .valid)
  | .local .valid=>.base (.pop (aux .valid) (.local .abort) (.local .abort) (.local .copyPairs))
  | .local .copyPairs=>.call (.copy 2 0) (.local .filter)
  | .local .filter=>.call (.fibre .loop) (.local .emitTag)
  | .local .emitTag=>.base (.push (aux .reversed) true (.local (.emitField false)))
  | .local (.emitField scopes)=>.call (.frame scopes 0) (.local (.emitReverse scopes))
  | .local (.emitReverse scopes)=>.call (.reverse false 0)
      (if scopes then .local (.clearFibre 0) else .local (.emitField true))
  | .local (.clearFibre part)=>
      let next:Label:=if h:part.val<13 then .local (.clearFibre ⟨part.val+1,by omega⟩) else .local .loop
      .base (.pop (fibreStack (fibreRole part)) next (.local (.clearFibre part)) (.local (.clearFibre part)))
  | .local .finalTag=>.base (.push (aux .reversed) false (.local .finalReverse))
  | .local .finalReverse=>.call (.reverse true 0) (.local .halt)
  | .local .halt | .local .abort=>.base .halt
/-- Original binary N alone, with no owner key, tally, ID bank, scope fibre or count answer input. -/
def input (bits:List Bool) : Stack→List Bool :=Sum.elim (R.input bits) (fun _=>[])
/-- Actual all-owner fibre catalogue entry. -/
def initial (bits:List Bool) :C.State Stack Label:=⟨some (.local .main),none,none,input bits,[]⟩
/-- One fixed genuine finite machine for all original owner-fibre acquisition. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Every data and return alphabet is finite before every original binary input. -/
theorem all_alphabets_finite :∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (aux .output) (.local .main) program
/-- All305 actual data roles, including both retained source banks and real fibre work. -/
theorem stack_card :Fintype.card Stack=305:=by decide
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogue
