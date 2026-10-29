/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeParametricFactorLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame

/-! # Upper-register frame for a supplied physical factor callback

The actual setup, record parser, copies and cleanup touch only registers below
16. Thus preserving a caller register in the supplied callback suffices for
preserving it throughout the actual assignment command, on every execution.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeParametricFactorFrame
open OAI.Algorithms
open SubexponentialSAT SubexponentialSAT.SqrtLog
open BitProgram StructuredCalls LeafProgram MomentsProgram
open MomentsAssembly.RegisterFrame
open SemiprimeParametricFactorLoop

/-- Record parsing preserves each upper register preserved by its callback. -/
theorem loop_preserves (callback : Cmd 40 768) (i : Fin 40) (hi : 16 ≤ i.val)
    (hc : Preserves callback i) : Preserves (SemiprimeParametricFactorLoop.loop callback) i := by
  unfold SemiprimeParametricFactorLoop.loop
  exact fun {n} {a} {b} => LeafAssignmentRegisterFrame.records Factor.ports callback
    (by decide) (by decide) (by decide) i hi hc

/-- Copying the input and moving the output adds no upper-register writes. -/
theorem command_preserves (callback : Cmd 40 768) (i : Fin 40) (hi : 16 ≤ i.val)
    (hc : Preserves callback i) : Preserves (command callback) i := by
  unfold command
  exact fun {n} {a} {b} => seq (LeafAssignmentRegisterFrame.copy 175 150 159 i hi)
    (seq (LeafAssignmentRegisterFrame.copy 69 151 159 i hi)
      (seq (loop_preserves callback i hi hc) (LeafAssignmentRegisterFrame.factorMove 151 67 i hi)))

/-- The hypothesis required by the generic framed dense moment controller. -/
theorem assignment_preserves (callback : Cmd 40 768) (i : Fin 40) (hi : 16 ≤ i.val)
    (hc : Preserves callback i) : Preserves (assignment callback) i := by
  unfold assignment
  exact fun {n} {a} {b} => seq (LeafAssignmentRegisterFrame.setupBefore i hi)
    (seq (command_preserves callback i hi hc) (LeafAssignmentRegisterFrame.setupAfter i hi))

/-- An actual assignment execution retains the supplied caller frame. -/
theorem assignment_eval_register (callback : Cmd 40 768) {n : ℕ} {a b : Factor.Data}
    (hc : ∀ i : Fin 40, 16 ≤ i.val → Preserves callback i)
    (he : Eval (assignment callback) n a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i = a.regs i := assignment_preserves callback i hi (hc i hi) he

end RiemannGaussian.SemiprimeParametricFactorFrame
