/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopeFibreBounds
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordClock
import RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds
/-! # Actual binary-N-only ALL original factor-record controller
The pair source and descriptor catalogue are acquired once. Every descriptor
is physically parsed into five real raw fields. The actual eighteen-tag
source acquires its table and unary ports and logs the row. All five raw
fields and retained binary scope are physically drained before key advancement.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogue
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace F
export SemiprimeD1StackFactorScopeFibre (Stack Label program initial originalInput query output)
end F
namespace V
export SemiprimeD1StackVertexCatalogue (Stack Label program originalInput kernelStack)
end V
namespace D
export SemiprimeD1StackAllDescriptorRecord (Stack Label Common program source scopeBank history output copyScratch tagReader cleanData commonData)
end D
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Log
export SemiprimeD1StackVertexRecordStream (Stack Label code)
end Log
/-- All1454 roles, including both unused descriptor-input shadows. -/
abbrev Stack :=F.Stack⊕(V.Stack⊕(D.Stack⊕Unit))
/-- Complete137-role actual pair acquisition and repeated scope filter. -/
def sourceStack :F.Stack→Stack:=Sum.inl
/-- Complete53-role physically acquired original descriptor catalogue. -/
def catalogueStack (k:V.Stack) :Stack:=.inr (.inl k)
/-- Actual descriptor reader is the original catalogue output, with no copy or supplier. -/
def descriptorReader :Stack:=catalogueStack (V.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- Original binary N is loaded only in the actual pair-source input. -/
def originalInput :Stack:=sourceStack F.originalInput
/-- Actual scope vector is shared directly with the eighteen-tag record source. -/
def scope :Stack:=sourceStack F.output
/-- Real descriptor operands share ONLY the acquired original binary N and binary scope. -/
def descriptorStack (k:D.Stack) :Stack:=
  if k=D.source 0 then originalInput else if k=D.scopeBank then scope else .inr (.inr (.inl k))
/-- Actual parsed tag and coordinates occupy raw source fields1 through5. -/
def fieldPart (i:Fin 5) :Fin 6:=⟨i.val+1,by omega⟩
/-- Actual raw descriptor payload role; no descriptor or typed vertex enters control. -/
def cache (i:Fin 5) :Stack:=descriptorStack (D.source (fieldPart i))
/-- One fresh Boolean validity word is physically written and consumed per field. -/
def valid :Stack:=.inr (.inr (.inr ()))
/-- The preserving N copy and real field parser reuse the actual clean copy scratch. -/
def scratch :Stack:=descriptorStack D.copyScratch
/-- The actual factor counter is unary length n, with numeric value2^n-1. -/
def counter :Stack:=sourceStack F.query
/-- Shared actual reverse chronological row log. -/
def history :Stack:=descriptorStack D.history
/-- Actual complete forward factor-record output. -/
def output :Stack:=descriptorStack D.output
/-- Four literal logger roles use the shared accumulators and physically empty consuming fields. -/
def loggerStack :Log.Stack→Stack
  | .ports=>descriptorStack D.tagReader
  | .table=>scratch
  | .history=>history
  | .output=>output
/-- Static preserving binary-N copy operands. -/
def copyStack (k:Fin 3) :Stack:=
  if k=0 then originalInput else if k=1 then catalogueStack V.originalInput else scratch
/-- Static physical parser operands; every raw field is actually parsed. -/
def fieldStack (part:Fin 5) :Field.Stack→Stack
  | .inl .input=>descriptorReader | .inl .scratch=>scratch
  | .inl .output=>cache part | .inr _=>valid
/-- Fixed source, parser, cleanup, unary-key and final-reversal phases. -/
inductive Control where
  | main | copyN | catalogue | seed | loop | field (part:Fin 5) | valid (part:Fin 5)
  | row | clearField (part:Fin 5) | clearScope | advance | next | query | reverse | done | abort
  deriving DecidableEq,Fintype
/-- All source and return labels are finite and fixed before original N. -/
inductive Label where
  | local (pc:Control) | source (pc:F.Label) | catalogue (pc:V.Label)
  | descriptor (pc:D.Label) | copy (pc:Fin 9) | field (part:Fin 5) (pc:Field.Label) | logger (pc:Log.Label)
  deriving Fintype
/-- Next actual field-parser call, or the real eighteen-tag source. -/
def nextField (part:Fin 5) :Label:=
  if h:part.val<4 then .local (.field ⟨part.val+1,by omega⟩) else .local .row
/-- Next actual field drain, or the complete acquired-scope drain. -/
def nextClear (part:Fin 5) :Label:=
  if h:part.val<4 then .local (.clearField ⟨part.val+1,by omega⟩) else .local .clearScope
/-- One fixed actual N-only full-factor compiler; no key, table, arity or mode answer is supplied. -/
def program :Label→C.Instruction Stack Label
  | .local .main=>.call (.source .main) (.local .copyN)
  | .local .copyN=>.call (.copy 0) (.local .catalogue)
  | .local .catalogue=>.call (.catalogue (.inl .main)) (.local .seed)
  | .local .seed=>.base (.push output false (.local .loop))
  | .local .loop=>.base (.peek descriptorReader (.local .reverse) (.local (.field 0)) (.local (.field 0)))
  | .local (.field part)=>.call (.field part (Field.active .tagPop (none,false))) (.local (.valid part))
  | .local (.valid part)=>.base (.pop valid (.local .abort) (.local .abort) (nextField part))
  | .local .row=>.call (.descriptor (.inl .start)) (.local (.clearField 0))
  | .local (.clearField part)=>.base (.pop (cache part) (nextClear part)
      (.local (.clearField part)) (.local (.clearField part)))
  | .local .clearScope=>.base (.pop scope (.local .advance) (.local .clearScope) (.local .clearScope))
  | .local .advance=>.base (.push counter true (.local .next))
  | .local .next=>.base (.peek descriptorReader (.local .reverse) (.local .query) (.local .query))
  | .local .query=>.call (.source .copy) (.local .loop)
  | .local .reverse=>.call (.logger .reverse) (.local .done)
  | .local .done|.local .abort=>.base .halt
  | .source pc=>SemiprimeD1StackValidationLink.instruction sourceStack Label.source (F.program pc)
  | .catalogue pc=>SemiprimeD1StackValidationLink.instruction catalogueStack Label.catalogue (V.program pc)
  | .descriptor pc=>SemiprimeD1StackValidationLink.instruction descriptorStack Label.descriptor (D.program pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (Field.code pc)
  | .logger pc=>SemiprimeD1StackMultiplierLink.instruction loggerStack Label.logger (Log.code pc)
/-- Standard initialization contains original binary N alone. -/
def input (bits:List Bool) :Stack→List Bool:=Sum.elim (F.initial bits []).data (fun _=>[])
/-- The output terminator, all keys and all original descriptors are physically acquired. -/
def initial (bits:List Bool) :C.State Stack Label:=⟨some (.local .main),none,none,input bits,[]⟩
/-- Genuine fixed finite machine with all actual enlarged return labels. -/
def machine :Turing.FinTM2:=SemiprimeD1StackCalls.machine originalInput output (.local .main) program
/-- All actual source, catalogue, table/serializer/logger and validity roles are counted. -/
theorem stack_card :Fintype.card Stack=1454:=by
  change Fintype.card (F.Stack⊕(V.Stack⊕(D.Stack⊕Unit)))=1454
  rw [Fintype.card_sum]
  conv_lhs =>
    arg 2
    rw [Fintype.card_sum]
    arg 2
    rw [Fintype.card_sum]
  rw [SemiprimeD1StackFactorScopeFibre.stack_card,SemiprimeD1StackVertexCatalogue.stack_card,
    SemiprimeD1StackAllDescriptorRecord.stack_card,Fintype.card_unit]
/-- Static role inverse used solely to prove that the two physical aliases cannot collide. -/
def descriptorInverse :Stack→D.Stack
  | .inl k=>if k=F.output then D.scopeBank else D.source 0
  | .inr (.inr (.inl k))=>k
  | _=>D.source 0
/-- Every real record-source role has its unique physical outer target. -/
theorem descriptor_inverse (k:D.Stack) :descriptorInverse (descriptorStack k)=k:=by
  by_cases h0:k=D.source 0
  · subst k;rfl
  · by_cases hb:k=D.scopeBank
    · subst k;rfl
    · simp only [descriptorStack,h0,hb,ite_false,descriptorInverse]
/-- Actual source inclusion is injective without enumerating its1252 private slots. -/
theorem descriptor_injective :Function.Injective descriptorStack:=by
  intro a b h
  have hh:=congrArg descriptorInverse h
  simpa only [descriptor_inverse] using hh
/-- Field-cache roles are private raw fields1..5 and cannot hit either shared alias. -/
theorem cache_private (i:Fin 5) :cache i=.inr (.inr (.inl (D.source (fieldPart i)))):=by
  have hn:fieldPart i≠0:=by intro h;have hv:=congrArg Fin.val h;dsimp only [fieldPart] at hv;omega
  simp only [cache,descriptorStack,D.source,Sum.inl.injEq,SemiprimeD1StackAllDescriptorRecord.Common.source.injEq,hn,ite_false]
  rfl
/-- Four distinct actual common words support the single final physical reversal. -/
theorem logger_injective :Function.Injective loggerStack:=by decide
/-- The one original N copy has distinct source, catalogue target and clean scratch roles. -/
theorem copy_injective :Function.Injective copyStack:=by decide
/-- Every real field parser has four distinct physical roles. -/
theorem field_injective :∀part:Fin 5,Function.Injective (fieldStack part):=by decide
/-- Runtime control and flags, including return labels, are finite before every original input. -/
theorem control_finite :Finite machine.σ:=SemiprimeD1StackCalls.control_finite originalInput output (.local .main) program
/-- Every data and actual return alphabet is fixed finite before original N. -/
theorem all_alphabets_finite :∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput output (.local .main) program
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogue
