/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlPaths
import RiemannGaussian.SemiprimeD1StackBitGatherBounds
import RiemannGaussian.SemiprimeD1StackReturnLink

/-! # Callable literal bytecode for the actual physical gather -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackGatherBytecode
namespace G
export SemiprimeD1StackBitGather (Stack PC Alphabet contents values gather_exec)
end G
namespace B
export SemiprimeD1StackBytecode (run)
end B
namespace F
export SemiprimeD1StackFiniteControl (Label code entry depth)
end F

/-- Fixed finite instruction labels, independent of all indices/assignments. -/
abbrev Label := F.Label SemiprimeD1StackBitGather.program
/-- Actual literal compiled gather program. -/
def code := F.code SemiprimeD1StackBitGather.program
/-- Actual finite entry label. -/
def entry : Label := F.entry SemiprimeD1StackBitGather.program .marker none

/-- Original instruction-depth cap, discharged from the literal program. -/
theorem program_depth (pc : G.PC) : F.depth (SemiprimeD1StackBitGather.program pc)≤5 := by
  cases pc <;> decide

/-- Closed computed time bound in the actual physical input lengths. -/
def budget (assignment indexTape : ℕ) : ℕ := 5*SemiprimeD1StackBitGatherBounds.budget assignment indexTape

/-- Actual bytecode gather execution preserves the complete literal stack contract. -/
theorem gather_run (assignment : List Bool) (indices : List (List Bool)) (tail out : List Bool) :
    ∃m≤budget assignment.length (SemiprimeD1TensorTapeCodec.vectorBits indices).length,
      B.run code m ⟨some entry,none,G.contents (SemiprimeD1TensorTapeCodec.vectorBits indices++tail)
        assignment [] [] [] out⟩=
      some ⟨none,none,G.contents tail assignment [] [] [] (G.values assignment indices++out)⟩ := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackFiniteControlPaths.halted_run
    SemiprimeD1StackBitGather.program 5 program_depth .marker none none _ _
    (SemiprimeD1StackBitGather.scanSteps assignment indices+indices.length+1)
    (G.gather_exec assignment indices tail out).iterates
  exact ⟨m,hm.trans (Nat.mul_le_mul_left 5
    (SemiprimeD1StackBitGatherBounds.gather_steps_le assignment indices)),hr⟩

/-- Original literal port order, repeats/defaults included, with no getter callback. -/
theorem original_gather_run (assignment : List Bool) (ports : List ℕ) (tail out : List Bool) :
    ∃m≤budget assignment.length
      (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (fun i => List.replicate i true))).length,
      B.run code m ⟨some entry,none,G.contents
        (SemiprimeD1TensorTapeCodec.vectorBits (ports.map (fun i => List.replicate i true))++tail)
        assignment [] [] [] out⟩=
      some ⟨none,none,G.contents tail assignment [] [] []
        ((SemiprimeD1LeafCounter.gather assignment ports).bits++out)⟩ := by
  simpa [G.values,List.map_map,Function.comp_def,SemiprimeD1LeafCounter.gather_value] using
    gather_run assignment (ports.map (fun i => List.replicate i true)) tail out

/-- Actual real call and return for the literal gathered component. -/
theorem linked_run (assignment : List Bool) (indices : List (List Bool)) (tail out : List Bool) :
    ∃m≤budget assignment.length (SemiprimeD1TensorTapeCodec.vectorBits indices).length+2,
      SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) m
        (SemiprimeD1StackReturnLink.initial (G.contents (SemiprimeD1TensorTapeCodec.vectorBits indices++tail)
          assignment [] [] [] out))=
      some (SemiprimeD1StackReturnLink.final
        (G.contents tail assignment [] [] [] (G.values assignment indices++out))) := by
  obtain ⟨m,hm,hr⟩ := gather_run assignment indices tail out
  exact ⟨m+2,by omega,SemiprimeD1StackReturnLink.linked_run entry code m _ _ hr⟩

end RiemannGaussian.SemiprimeD1StackGatherBytecode
