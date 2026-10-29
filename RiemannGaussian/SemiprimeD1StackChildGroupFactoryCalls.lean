/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPrimitives
/-! # Actual included source calls with complete115-word postconditions
The bank constructors describe physical postconditions only. They are not
instructions, input suppliers, or operations in the fixed program control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryWiringFacts SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel)
end Link
/-- Complete actual lookup subbank, preserving every other physical word. -/
def withLookup (before:Stack→List Bool) (d:L.Stack→List Bool):Stack→List Bool
  | .inl k=>d k
  | k=>before k
/-- Exact included subbank and all untouched115-role cells. -/
theorem withLookup_rel (before:Stack→List Bool) (d:L.Stack→List Bool):
    Link.DataRel lookup before d (withLookup before d):=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k
    · exact False.elim ((hk k) rfl)
    · rfl
/-- Complete actual rows subbank, preserving every other physical word. -/
def withRows (before:Stack→List Bool) (d:R.Stack→List Bool):Stack→List Bool
  | .inr (.inl k)=>d k
  | k=>before k
/-- Exact included subbank and all untouched115-role cells. -/
theorem withRows_rel (before:Stack→List Bool) (d:R.Stack→List Bool):
    Link.DataRel rows before d (withRows before d):=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k|k
    · rfl
    · exact False.elim ((hk k) rfl)
    · rfl
/-- Complete actual arithmetic subbank, preserving every other physical word. -/
def withArithmetic (before:Stack→List Bool) (d:A.Stack→List Bool):Stack→List Bool
  | .inr (.inr (.inl k))=>d k
  | k=>before k
/-- Exact included subbank and all untouched115-role cells. -/
theorem withArithmetic_rel (before:Stack→List Bool) (d:A.Stack→List Bool):
    Link.DataRel arithmetic before d (withArithmetic before d):=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k|k|k
    · rfl
    · rfl
    · exact False.elim ((hk k) rfl)
    · rfl
/-- Complete actual ordinal subbank, preserving every other physical word. -/
def withOrdinal (before:Stack→List Bool) (d:O.Stack→List Bool):Stack→List Bool
  | .inr (.inr (.inr (.inr (.inl k))))=>d k
  | k=>before k
/-- Exact included subbank and all untouched115-role cells. -/
theorem withOrdinal_rel (before:Stack→List Bool) (d:O.Stack→List Bool):
    Link.DataRel ordinal before d (withOrdinal before d):=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k|k|k|k|k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact False.elim ((hk k) rfl)
    · rfl
/-- Whole physical first-match lookup; the returned value is computed from acquired rows. -/
theorem lookup_call (pc next:Label) (hc:program pc=.call (.lookup .loop) next)
    (before:Stack→List Bool) (query:List Bool) (entries:List (List Bool×List Bool)) (tail:List Bool)
    (hp:∀k,before (lookup k)=(SemiprimeD1StackOwnerLookup.initial query
      (SemiprimeD1StackOwnerLookup.records entries tail)).data k):
    Runs program (SemiprimeD1StackOwnerLookupExecution.loopTime query entries+2) pc before next
      (withLookup before (SemiprimeD1StackOwnerLookup.done query entries tail).data):=by
  have h:=SemiprimeD1StackProcedureCallsTrace.included_call program lookup Label.lookup lookup_injective
    L.program .loop (fun _=>rfl) pc next hc _ _ _ before _ rfl rfl rfl rfl
    (SemiprimeD1StackOwnerLookupExecution.source_run query entries tail)
    ⟨hp,fun _ _=>rfl⟩ (withLookup_rel before _)
  simpa only [Nat.add_assoc] using h
/-- Both catalogue rows are acquired by the real nineteen-role paired-row source. -/
theorem rows_call (pc next:Label) (hc:program pc=.call (.rows (.local .start)) next)
    (before:Stack→List Bool) (owner factor:List Bool) (entries:List (List Bool×List Bool))
    (left right:List (List Bool))
    (hl:SemiprimeD1StackPacketRowsEncoding.present owner entries=true)
    (hr:SemiprimeD1StackPacketRowsEncoding.present factor entries=true)
    (hleft:SemiprimeD1StackPacketRowsAcquire.payload owner entries=SemiprimeD1PacketRows.serialize left)
    (hright:SemiprimeD1StackPacketRowsAcquire.payload factor entries=SemiprimeD1PacketRows.serialize right)
    (hlen:left.length=right.length)
    (hp:∀k,before (rows k)=(SemiprimeD1StackPacketRows.initial
      (SemiprimeSourceHistogramKeyBits.frame owner factor)
      (SemiprimeD1StackOwnerLookup.records entries [])).data k):
    ∃t≤SemiprimeD1StackPacketRowsExecution.timeBound owner factor entries left right+1,
      Runs program t pc before next (withRows before (SemiprimeD1StackPacketRowsExecution.result
        (SemiprimeSourceHistogramKeyBits.frame owner factor)
        (SemiprimeD1StackOwnerLookup.records entries []) left right)):=by
  obtain ⟨t,ht,hs⟩:=SemiprimeD1StackPacketRowsExecution.source_run owner factor entries left right
    hl hr hleft hright hlen
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program rows Label.rows rows_injective
    R.program (.local .start) (fun _=>rfl) pc next hc t _ _ before _ rfl rfl rfl rfl hs
    ⟨hp,fun _ _=>rfl⟩ (withRows_rel before _)
/-- Real numeric equality consumes both padded operands and physically cleans its workspace. -/
theorem equal_call (pc next:Label) (hc:program pc=.call (.equal .loop) next)
    (before:Stack→List Bool) (left right:List Bool)
    (hp:∀k,before (arithmetic k)=SemiprimeD1StackAdder.store left right [] [] k):
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime left right+1) pc before next
      (withArithmetic before (SemiprimeD1StackAdder.store [] [] []
        [decide (SemiprimeBitArithmetic.bitValue left=SemiprimeBitArithmetic.bitValue right)])):=by
  exact included_call program arithmetic Label.equal arithmetic_injective E.code .loop
    (fun _=>rfl) pc next hc _ _ _ before _ rfl rfl
    (SemiprimeD1StackWordEqualExecution.source_run left right none)
    ⟨hp,fun _ _=>rfl⟩ (withArithmetic_rel before _)
/-- Real full binary addition; no unary materialization of a binary counter value. -/
theorem add_call (pc next:Label) (hc:program pc=.call (.add (.start false)) next)
    (before:Stack→List Bool) (left right:List Bool)
    (hp:∀k,before (arithmetic k)=SemiprimeD1StackAdder.store left right [] [] k):
    Runs program (3*(max left.length right.length+1)+
      2*(SemiprimeBitArithmetic.addBits left right false).bits.length+3) pc before next
      (withArithmetic before (SemiprimeD1StackAdder.store [] [] []
        (SemiprimeBitArithmetic.addBits left right false).bits)):=by
  have h:=included_call program arithmetic Label.add arithmetic_injective A.code (.start false)
    (fun _=>rfl) pc next hc _ _ _ before _ rfl rfl
    (SemiprimeD1StackAdderExecution.source_run left right false)
    ⟨hp,fun _ _=>rfl⟩ (withArithmetic_rel before _)
  simpa [Nat.add_assoc,SemiprimeD1StackAdder.state] using h
/-- Actual binary-port to unary-port stream, with its value-sensitive own clock. -/
theorem ordinal_call (pc next:Label) (hc:program pc=.call (.ordinal (.control .start)) next)
    (before:Stack→List Bool) (words:List (List Bool))
    (hp:∀k,before (ordinal k)=(SemiprimeD1StackPortOrdinalStream.initial
      (SemiprimeD1TensorTapeCodec.vectorBits words)).data k):
    ∃t≤SemiprimeD1StackPortOrdinalStreamExecution.timeBound words+1,
      Runs program t pc before next (withOrdinal before
        (SemiprimeD1StackPortOrdinalStreamExecution.done words).data):=by
  obtain ⟨t,ht,hs⟩:=SemiprimeD1StackPortOrdinalStreamExecution.source_run words
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program ordinal Label.ordinal ordinal_injective
    O.program (.control .start) (fun _=>rfl) pc next hc t _ _ before _ rfl rfl rfl rfl hs
    ⟨hp,fun _ _=>rfl⟩ (withOrdinal_rel before _)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
