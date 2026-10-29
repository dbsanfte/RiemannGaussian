/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCartesian4Components

/-! # Concrete five-field Cartesian record body
Every output field is acquired by a real included Frame call from its actual
cached word. The source indices and the constructor tag are preserved.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4Body
open SemiprimeD1StackCartesian4 SemiprimeD1StackCartesian4Components
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeSourceHistogramKeyBits (frame)

/-- Mathematical schema of the actual five-field record. -/
def record (tag:List Bool) (indices:Fin 4→List Bool) (output:List Bool) : List Bool :=
  frame tag (frame (indices 0) (frame (indices 1) (frame (indices 2) (frame (indices 3) output))))
/-- Exact real Frame call instruction sum, in chronological order. -/
def bodyClock (indices:Fin 4→List Bool) (tag:List Bool) : ℕ :=
  (6*(indices 3).length+5)+((6*(indices 2).length+5)+((6*(indices 1).length+5)+
    ((6*(indices 0).length+5)+(6*tag.length+5))))

/-- Actual physical leaf body; no tuple-value or record-producing callback exists. -/
theorem body_run (limits indices:Fin 4→List Bool) (tag output:List Bool) :
    Runs program (bodyClock indices tag) (.inl (.fields 0)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (record tag indices output)) := by
  have h0:=frame_store 0 limits indices tag output
  change Runs program (6*(indices 3).length+5) (.inl (.fields 0)) (store limits indices tag output)
    (.inl (.fields 1)) (store limits indices tag (frame (indices 3) output)) at h0
  have h1:=frame_store 1 limits indices tag (frame (indices 3) output)
  change Runs program (6*(indices 2).length+5) (.inl (.fields 1))
    (store limits indices tag (frame (indices 3) output)) (.inl (.fields 2))
    (store limits indices tag (frame (indices 2) (frame (indices 3) output))) at h1
  have h2:=frame_store 2 limits indices tag (frame (indices 2) (frame (indices 3) output))
  change Runs program (6*(indices 1).length+5) (.inl (.fields 2))
    (store limits indices tag (frame (indices 2) (frame (indices 3) output))) (.inl (.fields 3))
    (store limits indices tag (frame (indices 1) (frame (indices 2) (frame (indices 3) output)))) at h2
  have h3:=frame_store 3 limits indices tag (frame (indices 1) (frame (indices 2) (frame (indices 3) output)))
  change Runs program (6*(indices 0).length+5) (.inl (.fields 3))
    (store limits indices tag (frame (indices 1) (frame (indices 2) (frame (indices 3) output)))) (.inl (.fields 4))
    (store limits indices tag (frame (indices 0) (frame (indices 1) (frame (indices 2) (frame (indices 3) output))))) at h3
  have h4:=frame_store 4 limits indices tag
    (frame (indices 0) (frame (indices 1) (frame (indices 2) (frame (indices 3) output))))
  change Runs program (6*tag.length+5) (.inl (.fields 4))
    (store limits indices tag (frame (indices 0) (frame (indices 1) (frame (indices 2) (frame (indices 3) output)))))
    (.inl .ret) (store limits indices tag (record tag indices output)) at h4
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

/-- A common original coordinate cap pays every actual field read/copy/frame operation. -/
theorem bodyClock_le (indices:Fin 4→List Bool) (tag:List Bool) (D:ℕ)
    (hi:∀j,(indices j).length≤D) : bodyClock indices tag≤6*(4*D+tag.length)+25 := by
  have h0:=hi 0
  have h1:=hi 1
  have h2:=hi 2
  have h3:=hi 3
  unfold bodyClock
  omega
end RiemannGaussian.SemiprimeD1StackCartesian4Body
