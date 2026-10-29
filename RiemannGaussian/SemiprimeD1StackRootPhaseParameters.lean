/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseGridOriginal
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersInventory
import RiemannGaussian.SemiprimeD1StackHeapAllocate
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackVertexRecordStream
/-! # N-only chronological heap of complete actual per-phase working banks
One whole original-input root/grid call is retained. Each actual framed binary
phase index supplies a real working-precision call. Forty-eight paid frames cache
its entire stopped bank, including rejected phases. A real unary heap ordinal is
logged and all private phase words are physically drained before the next row.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParameters
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace G
export SemiprimeD1StackRootPhaseGrid (Stack Label program input initial originalInput output exponent rootStack)
end G
namespace P
export SemiprimeD1StackPhaseWorkingPrecision (Stack Label program input initial metadataStack aux)
end P
namespace I
export SemiprimeD1StackRootPhaseParametersInventory (roles role)
end I
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
namespace B
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end B
namespace V
export SemiprimeD1StackVertexRecordStream (Stack Label code)
end V
/-- Fourteen actual reader, record, heap, ordinal and chronological-reference roles. -/
inductive Aux where
  | reader | index | fieldScratch | valid | copyScratch | record | recordScratch
  | heap | counter | reference | counterScratch | refsHistory | refsOutput | refScratch
  deriving DecidableEq,Repr
instance : Fintype Aux :=Fintype.ofList
  [.reader,.index,.fieldScratch,.valid,.copyScratch,.record,.recordScratch,.heap,.counter,.reference,.counterScratch,.refsHistory,.refsOutput,.refScratch]
  (by intro k;cases k <;> simp)
/-- All retained126 root/grid cells, actual48 phase cells and fourteen new fields. -/
abbrev Stack :=G.Stack⊕(P.Stack⊕Aux)
/-- Literal retention of every actual original-input root and phase-grid cell. -/
def gridStack : G.Stack→Stack :=Sum.inl
/-- Actual forty-eight-word working-precision bank; no stopped result is supplied. -/
def phaseStack (k:P.Stack) : Stack :=.inr (.inl k)
/-- Fourteen disjoint new physical words. -/
def aux (k:Aux) : Stack :=.inr (.inr k)
/-- Only original binary N is present at the whole front door. -/
def originalInput : Stack :=gridStack G.originalInput
/-- Chronological vector of stable actual heap ordinal references. -/
def output : Stack :=aux .refsOutput
/-- Retained actual heap bytes, newest framing first, logical addresses oldest first. -/
def heap : Stack :=aux .heap
/-- Actual parent u0, acquired by the root source rather than its successor. -/
def levels : Stack :=gridStack (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.levels))
/-- Actual root occurrence count M=2E, physically acquired and retained. -/
def edges : Stack :=gridStack (G.rootStack (SemiprimeD1StackRootRecursiveControl.sourceStack SemiprimeD1StackRootParameters.edges))
/-- Actual phase-source exponent input. -/
def phaseExponent : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.guardStack
  (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .exponent))))
/-- Actual phase-source parent-u input. -/
def phaseLevels : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.guardStack
  (SemiprimeD1StackPhaseGeometryGuard.aux .levels)))
/-- Actual phase-source root-M input. -/
def phaseEdges : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .edges))
/-- Actual phase-source retained binary index input. -/
def phaseIndex : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.guardStack
  (SemiprimeD1StackPhaseGeometryGuard.geometryStack (SemiprimeD1StackPhaseGeometry.aux .index))))
/-- Actual binary root precision input; two literal writes produce [false,true]. -/
def phasePrecision : Stack :=phaseStack (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .precision))
/-- Paid copy sources are actual retained grid/root words or the physically parsed t. -/
def copySource (site:Fin 5) : Stack :=
  if site=0 then gridStack G.output else if site=1 then gridStack G.exponent
  else if site=2 then levels else if site=3 then edges else aux .index
/-- Paid copy destinations have physically cleared prior contents. -/
def copyTarget (site:Fin 5) : Stack :=
  if site=0 then aux .reader else if site=1 then phaseExponent
  else if site=2 then phaseLevels else if site=3 then phaseEdges else phaseIndex
/-- Each actual preserving copy uses three distinct operands. -/
def copyStack (site:Fin 5) (i:Fin 3) : Stack :=
  if i=0 then copySource site else if i=1 then copyTarget site else aux .copyScratch
/-- Actual four-stack parser consumes one field and writes its physical validity bit. -/
def fieldStack : F.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch
  | .inl .output=>aux .index | .inr _=>aux .valid
/-- Actual frame input is one finite selected stopped phase role, never a getter opcode. -/
def frameStack (i:Fin 48) (k:Fin 3) : Stack :=
  if k=0 then phaseStack (I.role i) else if k=1 then aux .record else aux .copyScratch
/-- Actual allocator receives record/heap/two scratch words/counter/reference. -/
def heapStack (k:Fin 6) : Stack :=
  if k=0 then aux .record else if k=1 then aux .heap else if k=2 then aux .recordScratch
  else if k=3 then aux .counter else if k=4 then aux .reference else aux .counterScratch
/-- Actual restoring reference logger reads the physically acquired heap ordinal. -/
def bodyStack : B.Stack→Stack
  | .word=>aux .reference | .scratch=>aux .refScratch | .history=>aux .refsHistory
/-- One final actual reference-history reversal; both spare fields remain counted. -/
def reverseStack : V.Stack→Stack
  | .ports=>aux .recordScratch | .table=>aux .refScratch
  | .history=>aux .refsHistory | .output=>aux .refsOutput
/-- All finite source stages and real component return labels are fixed before N. -/
inductive Label where
  | start | copySite (site:Fin 5) | header | parse | check | pHigh | pLow | phaseCall
  | serialize (position:Fin 49) | allocate | logReference | clear (position:Fin 52)
  | finishSeed | reverseCall | done | abort
  | grid (pc:G.Label) | phase (pc:P.Label) | copy (site:Fin 5) (pc:Fin 9)
  | field (pc:F.Label) | frame (i:Fin 48) (pc:Fin 11) | allocator (pc:Fin 22)
  | body (pc:B.Label) | reverse (pc:V.Label)
  deriving Fintype
/-- Fixed stage following each of the five paid source copies. -/
def afterCopy (site:Fin 5) : Label :=
  if site=0 then .header else if h:site.val<4 then .copySite ⟨site.val+1,by omega⟩ else .pHigh
/-- Fixed drained phase role, or one of the three row-local fields. -/
def clearStack (i:Fin 51) : Stack :=
  if h:i.val<48 then phaseStack (I.role ⟨i.val,h⟩)
  else if i.val=48 then aux .index else if i.val=49 then aux .record else aux .reference
/-- One fixed original-N program with actual parsing, acquisition, framing,
allocation, stable-reference logging, physical cleanup and final reversal. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.grid (.inl .start)) (.copySite 0)
  | .copySite site=>.call (.copy site 0) (afterCopy site)
  | .header=>.base (.pop (aux .reader) .finishSeed .finishSeed .parse)
  | .parse=>.call (.field (F.active .tagPop (none,false))) .check
  | .check=>.base (.pop (aux .valid) .abort .abort (.copySite 1))
  | .pHigh=>.base (.push phasePrecision true .pLow)
  | .pLow=>.base (.push phasePrecision false .phaseCall)
  | .phaseCall=>.call (.phase .start) (.serialize 0)
  | .serialize i=>if h:i.val<48 then
      .call (.frame ⟨47-i.val,by omega⟩ 0) (.serialize ⟨i.val+1,by omega⟩)
      else .base (.jump .allocate)
  | .allocate=>.call (.allocator 0) .logReference
  | .logReference=>.call (.body B.entry) (.clear 0)
  | .clear i=>if h:i.val<51 then
      .base (.pop (clearStack ⟨i.val,h⟩) (.clear ⟨i.val+1,by omega⟩) (.clear i) (.clear i))
      else .base (.jump .header)
  | .finishSeed=>.base (.push output false .reverseCall)
  | .reverseCall=>.call (.reverse .reverse) .done
  | .done=>.base .halt
  | .abort=>.base .halt
  | .grid pc=>SemiprimeD1StackValidationLink.instruction gridStack Label.grid (G.program pc)
  | .phase pc=>SemiprimeD1StackValidationLink.instruction phaseStack Label.phase (P.program pc)
  | .copy site pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack site) (Label.copy site) (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .frame i pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack i) (Label.frame i) (SemiprimeD1StackFrame.code pc)
  | .allocator pc=>SemiprimeD1StackMultiplierLink.instruction heapStack Label.allocator (SemiprimeD1StackHeapAllocate.code pc)
  | .body pc=>SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (B.code pc)
  | .reverse pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reverse (V.code pc)
/-- Complete188-role physical bank, with no runtime list/numeric/cache instruction. -/
def data (root:G.Stack→List Bool) (phase:P.Stack→List Bool) (work:Aux→List Bool) : Stack→List Bool :=
  Sum.elim root (Sum.elim phase work)
/-- Original binary N alone; all sixty-two new roles are initially empty. -/
def input (bits:List Bool) : Stack→List Bool :=data (G.input bits) (fun _=>[]) (fun _=>[])
/-- Whole N-only initial state before any root, phase or heap acquisition. -/
def initial (bits:List Bool) : C.State Stack Label :=⟨some .start,none,none,input bits,[]⟩
/-- One genuine fixed finite binary machine with actual finite return cells. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output .start program
/-- All retained126, actual48 and fourteen private physical roles are counted. -/
theorem stack_card : Fintype.card Stack=188 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootPhaseGrid.stack_card,Fintype.card_sum,SemiprimeD1StackPhaseWorkingPrecision.stack_card]
  decide
/-- Actual grid call retains every component role injectively. -/
theorem grid_injective : Function.Injective gridStack :=Sum.inl_injective
/-- Actual phase call uses a distinct literal forty-eight-role bank. -/
theorem phase_injective : Function.Injective phaseStack :=by intro i j h;exact Sum.inl.inj (Sum.inr.inj h)
/-- All five actual source copies have disjoint source/destination/scratch. -/
theorem copy_injective (site:Fin 5) : Function.Injective (copyStack site) :=by fin_cases site <;> decide
/-- The actual parser's four physical operands are distinct. -/
theorem field_injective : Function.Injective fieldStack :=by decide
/-- Each paid stopped-word frame has three distinct physical operands. -/
theorem frame_injective (i:Fin 48) : Function.Injective (frameStack i) :=by
  intro j k h;fin_cases j <;> fin_cases k <;> simp [frameStack,aux,phaseStack] at h ⊢
/-- All six actual allocator operands are distinct. -/
theorem heap_injective : Function.Injective heapStack :=by decide
/-- Actual reference logging restores the ordinal via distinct scratch. -/
theorem body_injective : Function.Injective bodyStack :=by decide
/-- The one final reference reversal has four distinct counted operands. -/
theorem reverse_injective : Function.Injective reverseStack :=by decide
/-- Actual Boolean and real-return alphabets are fixed finite before N. -/
theorem alphabets_finite (k:machine.K) : Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
/-- Internal control contains only finite labels and flags, never numeric operands. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootPhaseParameters
