/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDescriptorRecord
import RiemannGaussian.SemiprimeD1StackPublicInputRecordOriginal
/-! # Actual six-field input descriptor to the concrete139-role input record
Only N and original coord1 input-index markers enter the actual52-role checker
template. Tag/other coordinates remain physically retained caller data.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackInputDescriptorRecord
namespace I
export SemiprimeD1StackPublicInputTable (static inputTemplate)
end I
namespace D
export SemiprimeD1StackDescriptorRecord (source scratch recordStack templateStack original history output)
end D
/-- Frozen actual52-role input-checker bank. -/
abbrev Checker :=SemiprimeD1StackPublicInput.Stack
/-- Exactly the original N input role, independent of original N. -/
def numberRole : Checker :=.inl SemiprimeD1StackPublicInput.H.original
/-- Exactly the physical original input-index marker role. -/
def indexRole : Checker :=SemiprimeD1StackPublicInput.index
/-- Static map ONLY N→source0 and original coord1 index markers→source3. -/
def sourceMap (k : Checker) : Option (Fin 6) :=
  if k=numberRole then some 0 else if k=indexRole then some 3 else none
/-- Actual six physically acquired input words in their authoritative order. -/
def fields (bits tag coord0 indexWord coord2 coord3 : List Bool) : Fin 6→List Bool :=
  fun i=>if i=0 then bits else if i=1 then tag else if i=2 then coord0
    else if i=3 then indexWord else if i=4 then coord2 else coord3
/-- Full concrete139-role inventory, including unused shared-component aliases. -/
abbrev Stack :=SemiprimeD1StackDescriptorRecord.Stack Checker
/-- All static loader, table, serializer, logger and return labels. -/
abbrev Label :=SemiprimeD1StackDescriptorRecord.Label SemiprimeD1StackPublicInput.Label I.static.roles.length
/-- One literal physical program before ALL original N and descriptor values. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackDescriptorRecord.program I.static sourceMap
/-- Charged arbitrary old template, only acquired original fields/scope and caller accumulators. -/
def initial (oldTemplate : Checker→List Bool) (inputFields : Fin 6→List Bool) (bank hist out : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackDescriptorRecord.initial I.static oldTemplate inputFields bank hist out
/-- One genuine finite machine, independent of original N and descriptor fields. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackDescriptorRecord.machine I.static sourceMap
/-- Every physical register, including all shadows, is counted. -/
theorem stack_card : Fintype.card Stack=139 := by
  rw [SemiprimeD1StackDescriptorRecord.stack_card,SemiprimeD1StackPublicInput.stack_card]
/-- Actual selected source words equal the frozen input initialization EXACTLY;
no metadata, cached arithmetic, assignment, result or clock is initialized. -/
theorem selected_template (bits tag coord0 indexWord coord2 coord3 : List Bool) :
    SemiprimeD1StackDescriptorRecord.selected sourceMap (fields bits tag coord0 indexWord coord2 coord3)=
      I.inputTemplate bits indexWord := by
  funext k
  rw [SemiprimeD1StackPublicInputTableTrace.template_only]
  change (if k=numberRole then some 0 else if k=indexRole then some 3 else none).elim []
    (fields bits tag coord0 indexWord coord2 coord3)=
      if k=numberRole then bits else if k=indexRole then indexWord else []
  by_cases hn:k=numberRole
  · subst k;rfl
  · by_cases hi:k=indexRole
    · subst k;rfl
    · simp only [hn,hi,ite_false];rfl

end RiemannGaussian.SemiprimeD1StackInputDescriptorRecord
