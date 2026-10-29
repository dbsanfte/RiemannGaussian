/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCounterEntry
import RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
import RiemannGaussian.SemiprimeD1StackPacketOrientationOriginal
/-! # Fixed physical inventory for sparse real-occurrence replay
All fifty-nine allocations are real. Five displaced component-input allocations
are repurposed as catalogue, maps and histories, and counted explicitly. The
actual old class index has its own retained word through increment and reading.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryRoles
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace F
export SemiprimeD1StackSourceKeyFrequency (Stack Label Aux program aux lookupStack oldCount query copyScratch)
end F
namespace R
export SemiprimeD1StackPacketRows (Stack Label Aux program output success)
end R
namespace O
export SemiprimeD1StackPacketOrientation (Stack Label Aux program aux answer)
end O
/-- All21 real frequency/counter words, all19 reader allocations and all19 orientation allocations. -/
abbrev Stack:=F.Stack⊕(R.Stack⊕O.Stack)
/-- Direct complete bank for the actual reusable real-ret counter. -/
def frequencyStack:F.Stack→Stack:=Sum.inl
/-- Real allocated reader address; two displaced input allocations hold persistent output histories. -/
def readerAllocation:R.Stack→Stack:=fun k=>.inr (.inl k)
/-- Real allocated orientation address; three displaced input allocations hold the original catalogue and two maps. -/
def orientationAllocation:O.Stack→Stack:=fun k=>.inr (.inr k)
/-- The only retained selected-key vector, with no supplied key list, count or index. -/
def source:Stack:=frequencyStack (F.aux .source)
/-- Actual paid copy of the selected-key vector, consumed once in original occurrence order. -/
def stream:Stack:=frequencyStack (F.aux .reader)
/-- The real current parsed joint key, retained until its placement is logged. -/
def raw:Stack:=frequencyStack (F.aux .raw)
/-- The only retained actual alphabet catalogue. Its physical allocation is outside the mapped orientation image. -/
def catalogue:Stack:=orientationAllocation (O.aux .leftInput)
/-- Newest-first class-counter overrides, with real sentinel-encoded raw keys. -/
def classes:Stack:=frequencyStack (F.aux .dictionary)
/-- Exact OLD class count copied before its consuming real increment; never frame scratch in this client. -/
def oldIndex:Stack:=frequencyStack (F.aux .frameScratch)
/-- Actual compact positive occurrence counter, shared unchanged through class operations. -/
def edge:Stack:=frequencyStack (F.aux .maximum)
/-- Real fresh/seen marker overrides, outside the complete mapped orientation image. -/
def seen:Stack:=orientationAllocation (O.aux .rightInput)
/-- Real packet/slot-address to positive-edge overrides, outside the complete mapped orientation image. -/
def slots:Stack:=orientationAllocation (O.aux .indexInput)
/-- Actual packet vector in newest-first first-discovery order, outside the mapped reader image. -/
def packets:Stack:=readerAllocation (.inr .key)
/-- Actual reversed placement-row history, outside the mapped reader image. -/
def placementHistory:Stack:=readerAllocation (.inr .catalogue)
/-- Final chronological placement vector; this real counter scratch is reused only after all counter calls finish. -/
def output:Stack:=frequencyStack (F.aux .trimScratch)
/-- Real lookup/parser/copy words stay in the included21-role bank. -/
def lookupStack:SemiprimeD1StackOwnerLookup.Stack→Stack:=fun k=>frequencyStack (F.lookupStack k)
/-- Actual shared numeric query, always supplied by a real sentinel procedure. -/
def query:Stack:=frequencyStack F.query
/-- Actual lookup payload and consuming counter operand. -/
def oldCount:Stack:=frequencyStack F.oldCount
/-- Actually acquired successor count, not a supplied numeric answer. -/
def count:Stack:=frequencyStack (F.aux .count)
/-- Copy/Sentinel restoration word, also used by NEW Frame injections after its actual restoration. -/
def scratch:Stack:=frequencyStack F.copyScratch
/-- A physically written singleton true used for seen markers and placement validity after real guards pass. -/
def marker:Stack:=frequencyStack (F.aux .incNext)
/-- Public whole-source success, written only after every replay call and drain. -/
def success:Stack:=lookupStack (.inl .output)
/-- Exact physical reader inclusion: only the key and catalogue input addresses are redirected. -/
def readerStack:R.Stack→Stack
  | .inr .key=>raw
  | .inr .catalogue=>catalogue
  | k=>readerAllocation k
/-- Exact physical orientation inclusion: its three input addresses directly reference actual acquired words. -/
def orientationStack:O.Stack→Stack
  | .inr .leftInput=>readerStack (R.output false)
  | .inr .rightInput=>readerStack (R.output true)
  | .inr .indexInput=>oldIndex
  | k=>orientationAllocation k
/-- Actual orientation key after its complete frozen source returns. -/
def packet:Stack:=orientationStack (O.aux .keyOutput)
/-- Actual orientation slot word after its complete frozen source returns. -/
def slot:Stack:=orientationStack (O.aux .slotOutput)
/-- Drained orientation high-output word becomes a real raw address/placement-frame buffer. -/
def buffer:Stack:=orientationStack (O.aux .highOutput)
/-- Already drained orientation slot history becomes the real outer-placement frame buffer. -/
def outerBuffer:Stack:=orientationStack (O.aux .slotHistory)
/-- Every actual physical allocation, including the five repurposed globals, is counted. -/
theorem stack_card:Fintype.card Stack=59:=by
  rw [Fintype.card_sum,SemiprimeD1StackSourceKeyFrequency.stack_card,Fintype.card_sum,
    SemiprimeD1StackPacketRows.stack_card,SemiprimeD1StackPacketOrientation.stack_card]
/-- Complete counter bank inclusion is physically distinct. -/
theorem frequency_injective:Function.Injective frequencyStack:=Sum.inl_injective
/-- Redirected reader inputs remain distinct from each other and all seventeen real reader work/output roles. -/
theorem reader_injective:Function.Injective readerStack:=by decide
/-- Redirected orientation inputs remain distinct from each other and all sixteen real orientation work/output roles. -/
theorem orientation_injective:Function.Injective orientationStack:=by decide
/-- Catalogue and persistent maps are outside ALL mapped orientation fields, not merely its cleanup loop. -/
theorem orientation_globals_outside (k:O.Stack):
    orientationStack k≠catalogue ∧ orientationStack k≠seen ∧ orientationStack k≠slots :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> decide
  · cases k <;> decide
/-- Packet-discovery vector and placement history are outside ALL mapped reader fields. -/
theorem reader_globals_outside (k:R.Stack):readerStack k≠packets ∧ readerStack k≠placementHistory :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> decide
  · cases k <;> decide
/-- OLD j is outside every actual reader address and survives all real reading work. -/
theorem reader_oldIndex_outside (k:R.Stack):readerStack k≠oldIndex :=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> decide
  · cases k <;> decide
/-- The NEW actual Frame scratch is separate from the retained OLD-j cache. -/
theorem scratch_ne_oldIndex:scratch≠oldIndex:=by decide
end RiemannGaussian.SemiprimeD1StackPacketInventoryRoles
