/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanEntryExecution
import RiemannGaussian.SemiprimeMacroEntryBitCheck
/-! # Exact original public OR/input-check and subdivided equality entries
These endpoints have only the ORIGINAL ordered finite assignment as data.
Neither a truth value nor an entry evaluator is supplied to the machine.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackBooleanEntryOriginal
open SemiprimeD1StackBooleanEntry SemiprimeD1StackBooleanEntryExecution
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroParameters

/-- Literal first/second/output ordering of original OR ports. -/
theorem ofFn_three (input : Fin 3→Bool) :
    List.ofFn input=[input 0,input 1,input 2] := by simp [List.ofFn_succ]
/-- Literal sole ordered input-check port. -/
theorem ofFn_one (input : Fin 1→Bool) : List.ofFn input=[input 0] := by simp [List.ofFn_succ]
/-- Literal zero/one ordering of the actual subdivided equality ports. -/
theorem ofFn_two (input : Fin 2→Bool) : List.ofFn input=[input 0,input 1] := by simp [List.ofFn_succ]

/-- All original OR assignments, not a supplied local truth-table answer. -/
theorem or_public (N : ℕ) (hN : 0<N) (side : Fin 2)
    (j : Fin (digitCount (bitLength N)-1)) (input : Fin 3→Bool) :
    C.run program 25 (initial .orGate (List.ofFn input))=
      some (done (List.ofFn input)
        (SemiprimeMacroEntryBitCheck.publicBitEntry N hN (.orGate side j) input).accepted) := by
  have hv : (SemiprimeMacroEntryBitCheck.publicBitEntry N hN (.orGate side j) input).accepted=
      decide (input 2=(input 0 || input 1)) := rfl
  rw [hv,ofFn_three]
  exact or_run _ _ _

/-- All original one-port input checks, including the actual false branch. -/
theorem input_public (N : ℕ) (hN : 0<N) (side : Fin 2) (input : Fin 1→Bool) :
    C.run program 13 (initial .inputCheck (List.ofFn input))=
      some (done (List.ofFn input)
        (SemiprimeMacroEntryBitCheck.publicBitEntry N hN (.inputCheck side) input).accepted) := by
  have hv : (SemiprimeMacroEntryBitCheck.publicBitEntry N hN (.inputCheck side) input).accepted=input 0 := rfl
  rw [hv,ofFn_one]
  exact input_run _

/-- Actual two-port equality tensor on ANY original signal and configuration. -/
theorem equality_original (p : Config) (signal : BitSignal p.r p.t p.digits) (input : Fin 2→Bool) :
    C.run program 19 (initial .equality (List.ofFn input))=
      some (done (List.ofFn input) (subdividedTable p (.inr signal) input)) := by
  rw [ofFn_two]
  exact equality_run _ _

end RiemannGaussian.SemiprimeD1StackBooleanEntryOriginal
