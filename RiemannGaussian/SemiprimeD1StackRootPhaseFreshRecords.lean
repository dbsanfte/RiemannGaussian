/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersOriginal
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsInventory
/-! # N-only chronological complete fresh-coefficient cache records
The actual phase-bank producer runs ONCE. Its actual issued-reference vector is
copied ONCE, physically parsed and dereferenced by the real143-role cache/Fresh
consumer. All85 actual Fresh words are framed into a SEPARATE actual heap. The
source heap/counter and the literal root old-axis header are physically retained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecords
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace R
export SemiprimeD1StackRootPhaseParameters (Stack Label program input initial originalInput output heap aux)
end R
namespace Q
export SemiprimeD1StackPhaseCacheFresh (Stack Label program initial freshStack restoreStack)
end Q
namespace F
export SemiprimeD1StackPhaseChildContextFresh (Stack)
end F
namespace I
export SemiprimeD1StackRootPhaseFreshRecordsInventory (role clearRole sourceHeap sourceCounter sourceReference oldHeader)
end I
namespace Field
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end Field
namespace Body
export SemiprimeD1StackAssignmentBody (Stack Label code entry)
end Body
namespace V
export SemiprimeD1StackVertexRecordStream (Stack Label code)
end V
/-- Fourteen actual pointer, fresh-record, independent-heap and chronological-log fields. -/
inductive Aux where
  | reader | pointer | fieldScratch | valid | copyScratch | record | recordScratch
  | heap | counter | reference | counterScratch | refsHistory | refsOutput | refScratch
  deriving DecidableEq,Repr
instance :Fintype Aux :=Fintype.ofList
  [.reader,.pointer,.fieldScratch,.valid,.copyScratch,.record,.recordScratch,.heap,.counter,.reference,.counterScratch,.refsHistory,.refsOutput,.refScratch]
  (by intro k;cases k <;> simp)
/-- All345 actual roles include retained188, allocated143 with all alias-shadows and14 new words. -/
abbrev Stack :=R.Stack⊕(Q.Stack⊕Aux)
/-- Every original-N phase-source cell is retained in its literal own address. -/
def rootStack :R.Stack→Stack :=Sum.inl
/-- Every allocated private client address exists, including all three new unused alias-shadows. -/
def cachePrivate (k:Q.Stack) :Stack :=.inr (.inl k)
/-- Literal new pointer/record/heap/log role inclusion. -/
def aux (k:Aux) :Stack :=.inr (.inr k)
/-- The client reads the ACTUAL retained source heap/counter and the ACTUALLY parsed
pointer. All other client roles keep their own private addresses. -/
def cacheStack :Q.Stack→Stack
  | .inl (.inr .heap)=>rootStack R.heap
  | .inl (.inr .counter)=>rootStack (R.aux .counter)
  | .inl (.inr .reference)=>aux .pointer
  | k=>cachePrivate k
/-- Fixed left inverse shows the whole actual client map is injective despite intentional sharing. -/
def cacheInverse :Stack→Q.Stack
  | .inl (.inr (.inr .heap))=>I.sourceHeap
  | .inl (.inr (.inr .counter))=>I.sourceCounter
  | .inr (.inr .pointer)=>I.sourceReference
  | .inr (.inl k)=>k
  | _=>I.sourceHeap
/-- Actual85-word Fresh projection uses the client's SHARED restored P48 bank,
never its forty-eight unused private P48 shadow slots. -/
def freshStack (k:F.Stack) :Stack :=cacheStack (Q.freshStack k)
/-- Persistent root old-axis header. The program writes its singleton false ONCE. -/
def oldHeader :Stack :=cacheStack I.oldHeader
/-- Original binary N is the ONLY whole-entry payload. -/
def originalInput :Stack :=rootStack R.originalInput
/-- Separate fresh-record heap; the input phase heap is never allocated into. -/
def heap :Stack :=aux .heap
/-- Chronological issued references into the separate fresh-record heap. -/
def output :Stack :=aux .refsOutput
/-- Paid whole-reference-vector copy has three disjoint literal operands. -/
def copyStack (i:Fin 3) :Stack :=
  if i=0 then rootStack R.output else if i=1 then aux .reader else aux .copyScratch
/-- Real parser consumes one actual issued unary ordinal field from the copied vector. -/
def fieldStack :Field.Stack→Stack
  | .inl .input=>aux .reader | .inl .scratch=>aux .fieldScratch
  | .inl .output=>aux .pointer | .inr _=>aux .valid
/-- One fixed logical Fresh role is physically framed and restored at each static position. -/
def frameStack (i:Fin 85) (k:Fin 3) :Stack :=
  if k=0 then freshStack (I.role i) else if k=1 then aux .record else aux .copyScratch
/-- Separate actual record heap/counter/reference and both restoration scratch fields. -/
def heapStack (k:Fin 6) :Stack :=
  if k=0 then aux .record else if k=1 then aux .heap else if k=2 then aux .recordScratch
  else if k=3 then aux .counter else if k=4 then aux .reference else aux .counterScratch
/-- Actual restoring body logs the issued NEW heap ordinal, not a predicted ordinal. -/
def bodyStack :Body.Stack→Stack
  | .word=>aux .reference | .scratch=>aux .refScratch | .history=>aux .refsHistory
/-- Exactly one final real reversal of the complete issued-reference history. -/
def reverseStack :V.Stack→Stack
  | .ports=>aux .recordScratch | .table=>aux .refScratch
  | .history=>aux .refsHistory | .output=>aux .refsOutput
/--140logical client drains exclude immutable sourceheap/counter/header. Then
three RAW alias-shadows, currentrecord and newreference are explicitly drained.
The shared issued-source pointer is included exactly ONCE in the logical140. -/
def clearStack (i:Fin 145) :Stack :=
  if h:i.val<140 then cacheStack (I.clearRole ⟨i.val,h⟩)
  else if i.val=140 then cachePrivate I.sourceHeap
  else if i.val=141 then cachePrivate I.sourceCounter
  else if i.val=142 then cachePrivate I.sourceReference
  else if i.val=143 then aux .record else aux .reference
/-- Whole-source, pointer-read, actual-client, finite85-frame and finite145-drain labels. -/
inductive Label where
  | start | copy | seedHeader | header | parse | check | freshCall
  | serialize (position:Fin 86) | allocate | logReference | clear (position:Fin 146)
  | finishSeed | reverseCall | done | abort
  | root (pc:R.Label) | cache (pc:Q.Label) | copier (pc:Fin 9) | field (pc:Field.Label)
  | frame (i:Fin 85) (pc:Fin 11) | allocator (pc:Fin 22) | body (pc:Body.Label) | reverse (pc:V.Label)
  deriving Fintype
/-- ONE fixed original-N program, with no decoded bank/phase/coefficient/rank/P/value/clock operand. -/
def program :Label→C.Instruction Stack Label
  | .start=>.call (.root .start) .copy
  | .copy=>.call (.copier 0) .seedHeader
  | .seedHeader=>.base (.push oldHeader false .header)
  | .header=>.base (.pop (aux .reader) .finishSeed .finishSeed .parse)
  | .parse=>.call (.field (Field.active .tagPop (none,false))) .check
  | .check=>.base (.pop (aux .valid) .abort .abort .freshCall)
  | .freshCall=>.call (.cache (.inl .start)) (.serialize 0)
  | .serialize i=>if h:i.val<85 then
      .call (.frame ⟨84-i.val,by omega⟩ 0) (.serialize ⟨i.val+1,by omega⟩)
      else .base (.jump .allocate)
  | .allocate=>.call (.allocator 0) .logReference
  | .logReference=>.call (.body Body.entry) (.clear 0)
  | .clear i=>if h:i.val<145 then
      .base (.pop (clearStack ⟨i.val,h⟩) (.clear ⟨i.val+1,by omega⟩) (.clear i) (.clear i))
      else .base (.jump .header)
  | .finishSeed=>.base (.push output false .reverseCall)
  | .reverseCall=>.call (.reverse .reverse) .done
  | .done|.abort=>.base .halt
  | .root pc=>SemiprimeD1StackValidationLink.instruction rootStack Label.root (R.program pc)
  | .cache pc=>SemiprimeD1StackValidationLink.instruction cacheStack Label.cache (Q.program pc)
  | .copier pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copier (SemiprimeD1StackCopy.code pc)
  | .field pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (Field.code pc)
  | .frame i pc=>SemiprimeD1StackMultiplierLink.instruction (frameStack i) (Label.frame i) (SemiprimeD1StackFrame.code pc)
  | .allocator pc=>SemiprimeD1StackMultiplierLink.instruction heapStack Label.allocator (SemiprimeD1StackHeapAllocate.code pc)
  | .body pc=>SemiprimeD1StackMultiplierLink.instruction bodyStack Label.body (Body.code pc)
  | .reverse pc=>SemiprimeD1StackMultiplierLink.instruction reverseStack Label.reverse (V.code pc)
/-- Complete physical payload; the mathematical views never become runtime suppliers. -/
def data (root:R.Stack→List Bool) (cache:Q.Stack→List Bool) (work:Aux→List Bool) :Stack→List Bool :=
  Sum.elim root (Sum.elim cache work)
/-- Only original binary N is initially populated across all345 physical fields. -/
def input (bits:List Bool) :Stack→List Bool :=data (R.input bits) (fun _=>[]) (fun _=>[])
/-- Whole N-only source entry before original phase/grid/heap/coefficient acquisition. -/
def initial (bits:List Bool) :C.State Stack Label :=⟨some .start,none,none,input bits,[]⟩
/-- Genuine fixed345-role finite machine with real finite return cells. -/
def machine :Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output .start program
/-- Every real client role has an exact static inverse on its actual included address. -/
theorem cache_inverse (k:Q.Stack) :cacheInverse (cacheStack k)=k :=by
  rcases k with k|k
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
  · rfl
/-- Whole-client sharing does not identify two different client operands. -/
theorem cache_injective :Function.Injective cacheStack :=by
  intro a b h
  have he:=congrArg cacheInverse h
  simpa only [cache_inverse] using he
/-- Every original-N source field remains physically distinct. -/
theorem root_injective :Function.Injective rootStack :=Sum.inl_injective
/-- The exact actual Fresh85 projection lies in private client storage; no source heap operand is framed. -/
theorem fresh_private (k:F.Stack) :freshStack k=cachePrivate (Q.freshStack k) :=by
  rcases k with k|k
  · rcases k with k|k <;> rfl
  · rfl
/-- Paid source-reference copy has distinct source/destination/scratch fields. -/
theorem copy_injective :Function.Injective copyStack :=by decide
/-- Every physical pointer parse uses four distinct operands. -/
theorem field_injective :Function.Injective fieldStack :=by decide
/-- Every85word framing call has disjoint actual input/record/restoration operands. -/
theorem frame_injective (i:Fin 85) :Function.Injective (frameStack i) :=by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [frameStack,fresh_private,cachePrivate,aux] at h ⊢
/-- Independent fresh-record heap operands are physically distinct. -/
theorem heap_injective :Function.Injective heapStack :=by decide
/-- Actual issued-reference logging has separate word/scratch/history fields. -/
theorem body_injective :Function.Injective bodyStack :=by decide
/-- Exactly one final reverse has distinct actual data roles. -/
theorem reverse_injective :Function.Injective reverseStack :=by decide
/-- All source/client/alias-shadow/new fields are included in the physical345 count. -/
theorem stack_card :Fintype.card Stack=345 :=by
  rw [Fintype.card_sum,SemiprimeD1StackRootPhaseParameters.stack_card,Fintype.card_sum,SemiprimeD1StackPhaseCacheFresh.stack_card]
  decide
/-- All flags and remembered return labels are fixed finite before original N. -/
theorem control_finite :Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every Boolean and actual return alphabet is fixed finite before original N. -/
theorem alphabets_finite (k:machine.K) :Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _ k
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecords
