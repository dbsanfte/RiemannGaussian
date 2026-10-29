/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFiniteControlPaths
import RiemannGaussian.SemiprimeD1StackIncrement
import RiemannGaussian.SemiprimeD1StackReturnLink

/-! # Actual literal bytecode and real procedure call for the incrementer
The generic lowering specializes the six finite flags into fixed labels. No
runtime count/body/arithmetic evaluator is supplied to this concrete program.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackIncrementBytecode
open Turing Turing.TM2
open SemiprimeD1TensorTapeFieldMachine (Stack Registers contents)
namespace I
export SemiprimeD1StackIncrement (program wrapped overflow increment_exec)
end I
namespace F
export SemiprimeD1StackFiniteControl (Label code entry depth)
end F
namespace B
export SemiprimeD1StackBytecode (State run)
end B

/-- Fixed finite labels, independent of word width/data. -/
abbrev Label := F.Label I.program

/-- Literal generated instruction table, not a source evaluator callback. -/
def code := F.code I.program

/-- Fixed finite incrementer entry, including its specialized initial flags. -/
def entry : Label := F.entry I.program .carry (none,false)

/-- Computable actual target machine. -/
def machine := SemiprimeD1StackBytecode.machine Stack.input Stack.output entry code

/-- Original syntactic depth, instantiated to the actual fixed program. -/
theorem program_depth (pc : SemiprimeD1StackIncrement.PC) : F.depth (I.program pc)≤5 := by
  cases pc <;> decide

/-- Literal Bytecode execution ends with the actual overflow/wrapped output. -/
theorem increment_run (xs out : List Bool) :
    ∃m≤5*(2*xs.length+3),B.run code m ⟨some entry,none,contents xs [] out⟩=
      some ⟨none,none,contents [] [] (I.overflow xs::(I.wrapped xs++out))⟩ := by
  have h := (I.increment_exec xs out).iterates
  exact SemiprimeD1StackFiniteControlPaths.halted_run I.program 5 program_depth
    .carry (none,false) (none,I.overflow xs) _ _ (2*xs.length+3) h

/-- Exact actual call/return execution; the caller adds two transitions. -/
theorem linked_run (xs out : List Bool) :
    ∃m≤5*(2*xs.length+3)+2,
      SemiprimeD1StackCalls.run (SemiprimeD1StackReturnLink.code entry code) m
        (SemiprimeD1StackReturnLink.initial (contents xs [] out))=
      some (SemiprimeD1StackReturnLink.final
        (contents [] [] (I.overflow xs::(I.wrapped xs++out)))) := by
  obtain ⟨m,hm,hr⟩ := increment_run xs out
  exact ⟨m+2,by omega,SemiprimeD1StackReturnLink.linked_run entry code m _ _ hr⟩

/-- Actual compiled-machine certificate; proof-only path selection never enters code. -/
noncomputable def incrementInTime (xs out : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackBytecode.configuration ⟨some entry,none,contents xs [] out⟩)
      (some (SemiprimeD1StackBytecode.configuration
        ⟨none,none,contents [] [] (I.overflow xs::(I.wrapped xs++out))⟩))
      (5*(2*xs.length+3)) :=
  SemiprimeD1StackFiniteControlPaths.haltedInTime I.program 5 program_depth
    .input .output .carry (none,false) (none,I.overflow xs) _ _ (2*xs.length+3)
    (I.increment_exec xs out).iterates

end RiemannGaussian.SemiprimeD1StackIncrementBytecode
