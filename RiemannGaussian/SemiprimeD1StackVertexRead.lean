/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGatherBytecode
import RiemannGaussian.SemiprimeD1StackTreeBytecode
import RiemannGaussian.SemiprimeD1StackProcedureTrace
import RiemannGaussian.SemiprimeD1TensorTapeLeaf

/-! # Fixed physical gather-to-table vertex read
The runtime receives actual framed unary ports, a Boolean assignment and a
serialized table on physical stacks. It contains both literal callees and real
calls/returns; no vertex, array, bit getter or entry evaluator is an operand.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackVertexRead
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace G
export SemiprimeD1StackGatherBytecode (Label code entry)
end G
namespace T
export SemiprimeD1StackTreeBytecode (Label code entry)
end T

/-- Fixed Boolean argument/work/result stack bank. -/
inductive Stack
  | ports | assignment | reader | scratch | accumulator | path | tableTape | tasks | output
  deriving DecidableEq,Inhabited,Repr
instance : Fintype Stack where
  elems := {.ports,.assignment,.reader,.scratch,.accumulator,.path,.tableTape,.tasks,.output}
  complete := by intro k; cases k <;> simp

/-- Three fixed caller positions, independent of every vertex/scope. -/
inductive Control | start | gathered | done deriving DecidableEq,Inhabited,Repr
instance : Fintype Control where
  elems := {.start,.gathered,.done}
  complete := by intro k; cases k <;> simp

/-- Disjoint finite component labels, fixed before all runtime argument tapes. -/
abbrev Label := G.Label ⊕ (T.Label ⊕ Control)

/-- Gather's result stack IS the subsequent tree's physical query path. -/
def gatherStack : SemiprimeD1StackBitGather.Stack → Stack
  | .input => .ports
  | .assignment => .assignment
  | .reader => .reader
  | .scratch => .scratch
  | .accumulator => .accumulator
  | .output => .path

/-- Tree stacks share only cleared scratch with the earlier gather. -/
def treeStack : SemiprimeD1TensorTapeTreeMachine.Stack → Stack
  | .input => .tableTape
  | .tasks => .tasks
  | .path => .path
  | .scratch => .scratch
  | .output => .output

/-- Literal gather label inclusion. -/
def gatherLabel (l : G.Label) : Label := .inl l
/-- Literal tree label inclusion. -/
def treeLabel (l : T.Label) : Label := .inr (.inl l)
/-- Literal caller label. -/
def control (c : Control) : Label := .inr (.inr c)

/-- Actual fixed whole pipeline code, including real frame pushes and returns. -/
def code : Label → C.Instruction Stack Label
  | .inl l => SemiprimeD1StackMultiplierLink.instruction gatherStack gatherLabel (G.code l)
  | .inr (.inl l) => SemiprimeD1StackMultiplierLink.instruction treeStack treeLabel (T.code l)
  | .inr (.inr .start) => .call (gatherLabel G.entry) (control .gathered)
  | .inr (.inr .gathered) => .call (treeLabel T.entry) (control .done)
  | .inr (.inr .done) => .base .halt

/-- The actual fixed finite machine; other argument stacks are prepared explicitly. -/
def machine := SemiprimeD1StackCalls.machine Stack.tableTape Stack.output (control .start) code

/-- Literal nine-stack data contract. -/
def data (ports assignment reader scratch accumulator path tableTape tasks output : List Bool) :
    Stack → List Bool
  | .ports => ports
  | .assignment => assignment
  | .reader => reader
  | .scratch => scratch
  | .accumulator => accumulator
  | .path => path
  | .tableTape => tableTape
  | .tasks => tasks
  | .output => output

/-- Gather's stack inclusion has no aliases. -/
theorem gatherStack_injective : Function.Injective gatherStack := by
  intro a b h
  cases a <;> cases b <;> simp [gatherStack] at h ⊢

/-- Tree's stack inclusion has no aliases. -/
theorem treeStack_injective : Function.Injective treeStack := by
  intro a b h
  cases a <;> cases b <;> simp [treeStack] at h ⊢

end RiemannGaussian.SemiprimeD1StackVertexRead
