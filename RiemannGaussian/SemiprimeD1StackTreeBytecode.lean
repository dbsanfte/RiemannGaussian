/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlPaths
import RiemannGaussian.SemiprimeD1TensorTapeTreeBounds
import RiemannGaussian.SemiprimeD1StackReturnLink

/-! # Callable literal bytecode for actual serialized table lookup -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackTreeBytecode
namespace T
export SemiprimeD1TensorTapeTreeMachine (Stack PC Registers contents)
end T
namespace B
export SemiprimeD1StackBytecode (run)
end B
namespace F
export SemiprimeD1StackFiniteControl (Label code entry depth)
end F
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1TensorTables (Table lookup)

/-- Fixed finite labels specialize ALL source finite flags, not input data. -/
abbrev Label := F.Label SemiprimeD1TensorTapeTreeMachine.program
/-- Actual literal generated table-lookup code. -/
def code := F.code SemiprimeD1TensorTapeTreeMachine.program
/-- Fixed finite entry, which physically acquires the initial seek task. -/
def entry : Label := F.entry SemiprimeD1TensorTapeTreeMachine.program .start (none,false)

/-- Actual source syntax depth, checked for every fixed label. -/
theorem program_depth (pc : T.PC) : F.depth (SemiprimeD1TensorTapeTreeMachine.program pc)≤8 := by
  cases pc <;> decide

/-- Concrete actual instruction bound from serialized storage alone. -/
def budget (tableTape : ℕ) : ℕ := 8*(4*tableTape+3)

/-- Exact selected raw vector, suffix, path consumption and empty scratch/tasks. -/
theorem tree_run {n : ℕ} (table : Table n) (path tail : List Bool) :
    ∃m≤budget (tape table).length,
      B.run code m ⟨some entry,none,T.contents (tape table++tail) [] path [] []⟩=
      some ⟨none,none,T.contents tail [] (path.drop n) [] (vectorBits (lookup table path).words)⟩ := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackFiniteControlPaths.halted_run
    SemiprimeD1TensorTapeTreeMachine.program 8 program_depth .start (none,false) (none,false) _ _
    (SemiprimeD1TensorTapeTreeExecution.scanSteps table+(vectorBits (lookup table path).words).length+3)
    (SemiprimeD1TensorTapeTreeBounds.prepared_exec table path tail).iterates
  have hs := SemiprimeD1TensorTapeTreeBounds.scanSteps_le table
  have hv := SemiprimeD1TensorTapeTreeBounds.selected_length_le table path
  refine ⟨m,hm.trans (Nat.mul_le_mul_left 8 ?_),hr⟩
  omega

/-- Actual real call/return includes every selected and skipped-subtree instruction. -/
theorem linked_run {n : ℕ} (table : Table n) (path tail : List Bool) :
    ∃m≤budget (tape table).length+2,
      SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) m
        (SemiprimeD1StackReturnLink.initial (T.contents (tape table++tail) [] path [] []))=
      some (SemiprimeD1StackReturnLink.final
        (T.contents tail [] (path.drop n) [] (vectorBits (lookup table path).words))) := by
  obtain ⟨m,hm,hr⟩ := tree_run table path tail
  exact ⟨m+2,by omega,SemiprimeD1StackReturnLink.linked_run entry code m _ _ hr⟩

end RiemannGaussian.SemiprimeD1StackTreeBytecode
