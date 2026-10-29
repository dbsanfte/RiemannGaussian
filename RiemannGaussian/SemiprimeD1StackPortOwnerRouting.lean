/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueResources
import RiemannGaussian.SemiprimeD1StackPortScopeBounds
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
/-! # Actual original-N factor-major port-to-owner routing source
The source physically acquires the complete original E endpoint map and the
factor-major nine-field scoped-port tape. Every port's compact endpoint key is
built from its actual local-slot/vertex fields, the retained map is physically
copied, and real numeric lookup computes its owner. Output retains each actual
scope-ID occurrence in original factor-major order. Source proofs follow in
separate modules; the literal program alone is not the routing theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRouting
namespace C
export SemiprimeD1StackCalls (Instruction State run step execute)
end C
namespace Map
export SemiprimeD1StackOwnerCatalogue (Stack Label program originalInput input)
end Map
namespace Scope
export SemiprimeD1StackPortScopeRecords (Stack Label program originalInput input)
end Scope
namespace Lookup
export SemiprimeD1StackOwnerLookup (Stack Label program)
end Lookup
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Eight actual private reader/parser/output Boolean roles. -/
inductive Aux where
  | reader | copyScratch | fieldScratch | valid | frameBuffer | frameScratch | reversed | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.reader,.copyScratch,.fieldScratch,.valid,.frameBuffer,.frameScratch,.reversed,.output]
  (by intro k;cases k <;> simp)
/-- The full two acquired original sources, real lookup and nine actual scoped fields. -/
abbrev Stack := Map.Stack⊕(Scope.Stack⊕(Lookup.Stack⊕(Fin 9⊕Aux)))
/-- Original E-map source inclusion. -/
def mapStack : Map.Stack→Stack := Sum.inl
/-- Original nine-field scoped-port source inclusion. -/
def scopeStack (k:Scope.Stack) : Stack := .inr (.inl k)
/-- Actual numeric comparison/map parser inclusion, with all eleven roles present. -/
def lookupStack (k:Lookup.Stack) : Stack := .inr (.inr (.inl k))
/-- Actual parsed occurrence ID, global ordinal, factor, slot and five vertex fields. -/
def cache (part:Fin 9) : Stack := .inr (.inr (.inr (.inl part)))
/-- Actual private outer reader/parser/collector inclusion. -/
def aux (k:Aux) : Stack := .inr (.inr (.inr (.inr k)))
/-- Original binary N is the ONLY initial runtime data. -/
def originalInput : Stack := mapStack Map.originalInput
/-- The physically computed complete original E endpoint map, retained across all actual lookups. -/
def sourceMap : Stack := mapStack (SemiprimeD1StackOwnerCatalogue.aux .output)
/-- The physically acquired nine-field factor-major scoped-port tape. -/
def sourcePorts : Stack := scopeStack (SemiprimeD1StackPortScopeRecords.aux .output)
/-- The actual preserving binary-N, scoped-port and per-query map copies. -/
def copyStack (part:Fin 3) (k:Fin 3) : Stack :=
  if k=0 then (if part=0 then originalInput else if part=1 then sourcePorts else sourceMap)
  else if k=1 then (if part=0 then scopeStack Scope.originalInput else if part=1 then aux .reader
    else lookupStack (.inr .reader)) else aux .copyScratch
/-- All nine scoped fields come from one actual retained-tape reader. -/
def fieldStack (part:Fin 9) : F.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch
  | .inl .output=>cache part | .inr _=>aux .valid
/-- A literal six-field compact key is physically built from parsed fields 3 through 8.
The true sentinel is pushed first; no ordinal/global/factor field enters this key. -/
def keyStack (part:Fin 6) (k:Fin 3) : Stack :=
  if k=0 then cache ⟨8-part.val,by omega⟩
  else if k=1 then lookupStack (.inr .query) else aux .frameScratch
/-- Actual routing output fields: computed original owner ID, then that occurrence's scope ID. -/
def emitStack (scope:Bool) (k:Fin 3) : Stack :=
  if k=0 then (if scope then cache 0 else lookupStack (.inr .output))
  else if k=1 then aux .frameBuffer else aux .frameScratch
/-- Actual field transfer or complete-output reversal. -/
def reverseStack (finish:Bool) (k:Fin 2) : Stack :=
  if k=0 then (if finish then aux .reversed else aux .frameBuffer)
  else if finish then aux .output else aux .reversed
/-- Fixed inventory of ALL real lookup roles, including its unread map suffix and retained query. -/
def lookupRole : Fin 11→Lookup.Stack :=
  ![.inl .left,.inl .right,.inl .scratch,.inl .output,.inr .query,.inr .reader,
    .inr .fieldScratch,.inr .valid,.inr .copyScratch,.inr .discard,.inr .output]
/-- Finite literal outer positions; no original N, dimension, index or semantic value enters control. -/
inductive Control where
  | main | acquireMap | acquireScope | copyPorts | parse | sentinel | copyMap | lookup
  | field (part:Fin 9) | valid (part:Fin 9) | key (part:Fin 6)
  | emitTag | emitField (scope:Bool) | emitReverse (scope:Bool)
  | clearLookup (part:Fin 11) | clearCache (part:Fin 9)
  | finalTag | finalReverse | halt | abort
  deriving Fintype
/-- Finite source and real component labels, all fixed before original binary N. -/
inductive Label where
  | local (pc:Control) | map (pc:Map.Label) | scope (pc:Scope.Label) | lookup (pc:Lookup.Label)
  | copy (part:Fin 3) (pc:Fin 9) | field (part:Fin 9) (pc:F.Label)
  | key (part:Fin 6) (pc:Fin 11) | emit (scope:Bool) (pc:Fin 11)
  | reverse (finish:Bool) (pc:Fin 4)
  deriving Fintype
/-- SAME physical source: N copies/acquisitions, actual key construction, actual map copy/lookup,
occurrence-preserving output, and real erasure of every parsed/lookup payload. -/
def program : Label→C.Instruction Stack Label
  | .map pc=>SemiprimeD1StackValidationLink.instruction mapStack Label.map (Map.program pc)
  | .scope pc=>SemiprimeD1StackValidationLink.instruction scopeStack Label.scope (Scope.program pc)
  | .lookup pc=>SemiprimeD1StackValidationLink.instruction lookupStack Label.lookup (Lookup.program pc)
  | .copy part pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack part) (Label.copy part) (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .key part pc=>SemiprimeD1StackMultiplierLink.instruction (keyStack part) (Label.key part) (SemiprimeD1StackFrame.code pc)
  | .emit scope pc=>SemiprimeD1StackMultiplierLink.instruction (emitStack scope) (Label.emit scope) (SemiprimeD1StackFrame.code pc)
  | .reverse finish pc=>SemiprimeD1StackMultiplierLink.instruction (reverseStack finish) (Label.reverse finish) (SemiprimeD1StackReverseWord.code pc)
  | .local .main=>.call (.copy 0 0) (.local .acquireMap)
  | .local .acquireMap=>.call (.map (.local .main)) (.local .acquireScope)
  | .local .acquireScope=>.call (.scope (.local .main)) (.local .copyPorts)
  | .local .copyPorts=>.call (.copy 1 0) (.local .parse)
  | .local .parse=>.base (.peek (aux .reader) (.local .finalTag) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part)=>.call (.field part (F.active .tagPop (none,false))) (.local (.valid part))
  | .local (.valid part)=>
      let next:Label:=if h:part.val<8 then .local (.field ⟨part.val+1,by omega⟩) else .local .sentinel
      .base (.pop (aux .valid) (.local .abort) (.local .abort) next)
  | .local .sentinel=>.base (.push (lookupStack (.inr .query)) true (.local (.key 0)))
  | .local (.key part)=>.call (.key part 0)
      (if h:part.val<5 then .local (.key ⟨part.val+1,by omega⟩) else .local .copyMap)
  | .local .copyMap=>.call (.copy 2 0) (.local .lookup)
  | .local .lookup=>.call (.lookup .loop) (.local .emitTag)
  | .local .emitTag=>.base (.push (aux .reversed) true (.local (.emitField false)))
  | .local (.emitField scope)=>.call (.emit scope 0) (.local (.emitReverse scope))
  | .local (.emitReverse scope)=>.call (.reverse false 0)
      (if scope then .local (.clearLookup 0) else .local (.emitField true))
  | .local (.clearLookup part)=>
      let next:Label:=if h:part.val<10 then .local (.clearLookup ⟨part.val+1,by omega⟩) else .local (.clearCache 0)
      .base (.pop (lookupStack (lookupRole part)) next (.local (.clearLookup part)) (.local (.clearLookup part)))
  | .local (.clearCache part)=>
      let next:Label:=if h:part.val<8 then .local (.clearCache ⟨part.val+1,by omega⟩) else .local .parse
      .base (.pop (cache part) next (.local (.clearCache part)) (.local (.clearCache part)))
  | .local .finalTag=>.base (.push (aux .reversed) false (.local .finalReverse))
  | .local .finalReverse=>.call (.reverse true 0) (.local .halt)
  | .local .halt | .local .abort=>.base .halt
/-- Both sources start empty except the original map-source binary input. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (Map.input bits) (fun _=>[])
/-- Original binary-N entry of the actual full factor-major routing source. -/
def initial (bits:List Bool) : C.State Stack Label :=⟨some (.local .main),none,none,input bits,[]⟩
/-- One genuine fixed finite routing machine. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput (aux .output) (.local .main) program
/-- Every data and return alphabet is finite before every original input. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput (aux .output) (.local .main) program
/-- All retained acquisition, real lookup and fresh outer roles are included. -/
theorem stack_card : Fintype.card Stack=282 := by decide
end RiemannGaussian.SemiprimeD1StackPortOwnerRouting
