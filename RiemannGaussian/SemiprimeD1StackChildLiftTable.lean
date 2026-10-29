/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVectorTableBounds
import RiemannGaussian.SemiprimeD1StackChildTableEntryOriginal
/-! # One fixed whole child-table source with real individual integer lifts
The fixed Entry61 executes at every actual false-first assignment. The scope
record count is acquired physically. Source/template shadows, both context
banks and all actual DFS returns are counted; no entry vector is an input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTable
namespace E
export SemiprimeD1StackChildTableEntry
  (Stack Label program initial context gather treeAllocation reduce aux stack_card)
end E
namespace J
export SemiprimeD1StackJetContext (Stack unaryStack axesCache precisionBits copyWork)
end J
namespace V
export SemiprimeD1StackVectorTable (Static)
end V
/-- Literal complete fifteen-role context inventory, including all suffix and decoder shadows. -/
def contextRoles : List J.Stack :=
  ([(.axes : SemiprimeD1StackJetSuffix.Stack),.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid].map Sum.inl)++
    [J.unaryStack .left,J.unaryStack .right,J.unaryStack .scratch,J.unaryStack .output,
      J.axesCache,J.precisionBits,J.copyWork]
/-- Literal complete real Entry61 inventory; no finite enumeration oracle supplies runtime addresses. -/
def roles : List E.Stack :=
  contextRoles.map (E.context false)++contextRoles.map (E.context true)++
    [E.gather .input,E.gather .assignment,E.gather .reader,E.gather .scratch,E.gather .accumulator,E.gather .output]++
    [E.treeAllocation .input,E.treeAllocation .tasks,E.treeAllocation .path,E.treeAllocation .scratch,E.treeAllocation .output]++
    [E.reduce .input,E.reduce .word,E.reduce .precision,E.reduce .width,E.reduce .work,E.reduce .temporary,E.reduce .result,E.reduce .valid]++
    [E.aux .parentTable,E.aux .order,E.aux .remaining,E.aux .oldRemaining,E.aux .coefficient,E.aux .valid,
      E.aux .scratch,E.aux .buffer,E.aux .history,E.aux .output,E.aux .success,E.aux .parentEntry]
/-- Every allocated actual source role appears exactly once. -/
theorem roles_nodup : roles.Nodup := by decide
/-- All61 real old/new-context, gather, tree, reducer and helper fields are allocated. -/
theorem roles_length : roles.length=61 := rfl
/-- Cardinality and literal distinctness prove the physical inventory exhaustive. -/
theorem roles_complete (k : E.Stack) : k∈roles := by
  have hc : roles.toFinset.card=Fintype.card E.Stack := by
    rw [List.toFinset_card_of_nodup roles_nodup,roles_length,E.stack_card]
  have hu := Finset.eq_univ_of_card roles.toFinset hc
  apply List.mem_toFinset.mp
  rw [hu]
  exact Finset.mem_univ k
/-- The only leaf implementation is the concrete fixed physical Entry61 program. -/
def source : V.Static E.Stack E.Label :=
  ⟨E.program,.local .start,E.gather .assignment,E.aux .output,roles,roles_complete,roles_nodup⟩
/-- All61 live source,61 original-template,7 scanner and5 traversal roles. -/
abbrev Stack := SemiprimeD1StackVectorTable.Stack E.Stack
/-- Literal finite labels; inventory positions are bounded by the fixed61 roles. -/
abbrev Label := SemiprimeD1StackVectorTable.Label E.Label source.roles.length
/-- One fixed whole-table program, with no callback or native table builder in runtime control. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackVectorTable.program source
/-- Only parent-table/order bytes, both original context headers and actual scope-ID bytes enter. -/
def initial (table order oldAxes oldp newAxes newp scope : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackVectorTable.initial source (E.initial table order [] oldAxes oldp newAxes newp).data scope
/-- Genuine fixed machine; its multiword prepared source is distinct from an N-only front door. -/
def machine : Turing.FinTM2 := SemiprimeD1StackVectorTable.machine source
/-- ALL134 allocations are counted, including both full61-role banks and every shadow. -/
theorem stack_card : Fintype.card Stack=134 := by
  rw [SemiprimeD1StackVectorTable.stack_card,E.stack_card]
/-- Actual finite control contains no input value, assignment, table, coefficient or getter. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackVectorTable.control_finite source
end RiemannGaussian.SemiprimeD1StackChildLiftTable
