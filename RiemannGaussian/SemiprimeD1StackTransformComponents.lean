/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransform

/-! # Actual original-input transform component effects
Every bootstrap/copy is a literal included procedure with physical call/return.
The original binary N is retained; the mathematical tally notation below only
specifies actual marker stacks produced by those loops.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformComponents
open SemiprimeD1StackTransform
open SemiprimeD1StackProcedureFragments (At Runs included_call one_base)

/-- Exact completed-bootstrap data and every physical transform work counter. -/
def data (bits threshold radius square exponent sw tw temporary radix:List Bool) : Stack→List Bool
  | .input => bits
  | .width => List.replicate bits.length true
  | .nonzero => [Boot.seenOne bits]
  | .threshold => threshold
  | .radius => radius
  | .square => square
  | .exponent => exponent
  | .squareWork => sw
  | .thresholdWork => tw
  | .temporary => temporary
  | .radix => radix

/-- Input projection of an actual Copy instance, with its actual empty temporary. -/
theorem copy_input (mode:Fin 4) (store:Stack→List Bool) (ht:store .temporary=[]) :
    Link.DataRel (copyStack mode) store
      (SemiprimeD1StackCopy.payload (store (copyInput mode)) (store (copyOutput mode)) []) store := by
  constructor
  · intro k
    fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,ht]
  · intro k _
    rfl

/-- The actual Copy loop writes only its destination while preserving original counters/N. -/
theorem copy_output (mode:Fin 4) (store:Stack→List Bool) (ht:store .temporary=[]) :
    Link.DataRel (copyStack mode) store
      (SemiprimeD1StackCopy.payload (store (copyInput mode))
        (store (copyInput mode)++store (copyOutput mode)) [])
      (Function.update store (copyOutput mode) (store (copyInput mode)++store (copyOutput mode))) := by
  constructor
  · intro k
    fin_cases mode <;> fin_cases k <;>
      simp [copyStack,copyInput,copyOutput,SemiprimeD1StackCopy.payload,Function.update,ht]
  · intro k hk
    have hne:k≠copyOutput mode:=by
      intro he
      apply hk 1
      simpa only [copyStack,show ¬((1:Fin 3)=0) by decide,ite_false,ite_true] using he.symm
    exact Function.update_of_ne hne _ _

/-- Actual included copy call, with real continuation push/pop and no source/cost oracle. -/
theorem copy_call (mode:Fin 4) (store:Stack→List Bool) (ht:store .temporary=[])
    (pc next:Label) (hcall:program pc=.call (copyLabel mode 0) next) :
    Runs program (5*(store (copyInput mode)).length+4) pc store next
      (Function.update store (copyOutput mode) (store (copyInput mode)++store (copyOutput mode))) := by
  apply included_call program (copyStack mode) (copyLabel mode) (copyStack_injective mode)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall
    (5*(store (copyInput mode)).length+3)
    (SemiprimeD1StackCopy.state 0 none (store (copyInput mode)) (store (copyOutput mode)) [])
    (SemiprimeD1StackCopy.done (store (copyInput mode)) (store (copyInput mode)++store (copyOutput mode)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · exact copy_input mode store ht
  · exact copy_output mode store ht

/-- Bootstrap original-input projection contains no prepared width/zero flag. -/
theorem boot_input (bits:List Bool) :
    Link.DataRel bootStack (input bits) (Boot.state .scan false none bits [] [] []).store (input bits) := by
  constructor
  · intro k
    cases k <;> rfl
  · intro k _
    rfl

/-- Actual bootstrap output supplies all small metadata operands, preserving all other empty stacks. -/
theorem boot_output (bits:List Bool) :
    Link.DataRel bootStack (input bits) (Boot.done bits).store (data bits [] [] [] [] [] [] [] []) := by
  constructor
  · intro k
    cases k <;> rfl
  · intro k hk
    cases k <;> first | rfl | exact False.elim (hk .input rfl) |
      exact False.elim (hk .width rfl) | exact False.elim (hk .nonzero rfl)

/-- First actual caller step invokes the real input-only bootstrap, acquiring WIDTH and flag. -/
theorem bootstrap_call (bits:List Bool) :
    Runs program (5*bits.length+5) (.inl .start) (input bits) (setupLabel 0)
      (data bits [] [] [] [] [] [] [] []) := by
  apply included_call program bootStack bootLabel bootStack_injective Boot.code (.scan,false)
    (fun _=>rfl) (.inl .start) (setupLabel 0) rfl (5*bits.length+4)
    (Boot.state .scan false none bits [] [] []) (Boot.done bits)
  · rfl
  · rfl
  · exact SemiprimeD1BinaryBootstrap.bootstrap_run bits
  · exact boot_input bits
  · exact boot_output bits
end RiemannGaussian.SemiprimeD1StackTransformComponents
