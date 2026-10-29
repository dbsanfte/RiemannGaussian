/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseView
/-! # Actual final array reader/output views and disjoint cache updates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishBuffers
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
/-- These are the two real words consumed and emitted by the final chronological array reversal. -/
def finishBuffers (w : Words) (remaining out : List Bool) : Words :=
  {w with auxiliary:=fun k=>if k=.prefixReverse then remaining else if k=.output then out else w.auxiliary k}
/-- An actual prefix pop/parser drain changes only that physical word. -/
theorem update_prefix (w : Words) (remaining out fresh : List Bool) :
    Function.update (store (finishBuffers w remaining out)) (aux .prefixReverse) fresh=
      store (finishBuffers w fresh out) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [finishBuffers]
/-- An actual frame/tag output write retains every other cache/source word. -/
theorem update_output (w : Words) (remaining out fresh : List Bool) :
    Function.update (store (finishBuffers w remaining out)) (aux .output) fresh=
      store (finishBuffers w remaining fresh) := by
  rw [update_aux]
  apply congrArg (fun f=>store ({w with auxiliary:=f}:Words))
  funext k;cases k <;> simp [finishBuffers]
/-- Actual final parser acquisition commutes with the disjoint prefix/output writes. -/
theorem put_finish (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) (remaining out : List Bool) :
    putReg (finishBuffers w remaining out) r word=finishBuffers (putReg w r word) remaining out := rfl
/-- Actual final cache drains commute with the retained chronological output. -/
theorem empty_finish (w : Words) (r : Reg) (remaining out : List Bool) :
    emptyReg (finishBuffers w remaining out) r=finishBuffers (emptyReg w r) remaining out := rfl
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishBuffers
