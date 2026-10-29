/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCopies
/-! # Actual square, four-N subtraction and clean whole-square-root entry -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryDiscriminant
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackPackedFactorRecoveryCopies (adder_left adder_right multiply_input multiply_factor)
end P
/-- Every not-yet-called source field is explicitly empty outside the two active arithmetic banks. -/
def work (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (a : A.Stack→List Bool) (x : X.Stack→List Bool) : Stack→List Bool :=
  view r m a x (fun _=>[]) (fun _=>[]) (words [] [] [] [])
/-- Exactly the metadata input word is populated before the real square-root call. -/
def metadataInput (d : List Bool) : SemiprimeD1StackPackedRootMetadata.Stack→List Bool :=
  Function.update (fun _=>[]) (SemiprimeD1StackPackedRootMetadata.boot .input) d
/-- This physical one-word metadata bank is the frozen source's actual input, not a result cache. -/
theorem metadataInput_eq (d : List Bool) : metadataInput d=SemiprimeD1StackPackedRootMetadata.input d := by
  funext k
  rcases k with k|k|k
  · cases k <;> rfl
  · cases k <;> rfl
  · cases k <;> rfl
/-- Empty active arithmetic stores really give the wholly empty33 bank. -/
theorem work_empty (r : R.Stack→List Bool) :
    work r (fun _=>[]) (A.store [] [] [] []) (X.payload [] [] [] [] [] [] [] [] [])=
      bank r (fun _=>[]) (words [] [] [] []) := by
  funext k
  rcases k with k|k|k
  · rfl
  · rcases k with k|k|k|k|k
    · rfl
    · cases k <;> rfl
    · rcases k with k|k|k
      · cases k <;> rfl
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · rfl
    · rfl
  · rfl
/-- All33 square-root input roles match exactly after the paid operand cleanup. -/
theorem work_input (r : R.Stack→List Bool) (d : List Bool) :
    work r (metadataInput d) (A.store [] [] [] []) (X.payload [] [] [] [] [] [] [] [] [])=
      bank r (S.input d) (words [] [] [] []) := by
  rw [work,metadataInput_eq]
  funext k
  rcases k with k|k|k
  · rfl
  · rcases k with k|k|k|k|k
    · rfl
    · cases k <;> rfl
    · rcases k with k|k|k
      · cases k <;> rfl
      · fin_cases k <;> rfl
      · cases k <;> rfl
    · rfl
    · rfl
  · rfl
/-- Exact sum of the actual copies, arithmetic, flag pop and all cleanup transitions. -/
def time (n s : List Bool) : ℕ :=
  (5*s.length+4)+(5*s.length+4)+multiplyTime s s+(5*(squareWord s).length+4)+(5*n.length+4)+2+
    subtractTime (squareWord s) (fourWord n)+1+(5*(discriminant n s).length+4)+
      ((discriminant n s).length+1)+((squareWord s).length+1)
/-- Whole actual discriminant preparation; every borrowed arithmetic field is empty before SQ starts. -/
theorem prepare_run (r : R.Stack→List Bool) (n s : List Bool)
    (hn : r R.originalInput=n) (hs : r (R.aux .sum)=s) (hb : (discriminantReport n s).borrow=false) :
    Runs program (time n s) (ctl (.copy .squareLeft)) (bank r (fun _=>[]) (words [] [] [] []))
      (ctl .root) (bank r (S.input (discriminant n s)) (words [] [] [] [])) := by
  let m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool:=fun _=>[]
  let a:=A.store [] [] [] []
  let x:=X.payload [] [] [] [] [] [] [] [] []
  let w : W.Stack→List Bool:=fun _=>[]
  let v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool:=fun _=>[]
  let u:=words [] [] [] []
  have h0:=P.multiply_input .squareLeft (ctl (.copy .squareLeft)) (ctl (.copy .squareRight))
    r m a w v u [] [] [] [] [] [] [] [] [] s rfl rfl hs rfl
  simp only [List.append_nil] at h0
  have h1:=P.multiply_factor .squareRight (ctl (.copy .squareRight)) (ctl .square)
    r m a w v u s [] [] [] [] [] [] [] [] s rfl rfl hs rfl
  simp only [List.append_nil] at h1
  have h2:=multiply_call r m a w v u s s (ctl .square) (ctl (.copy .squareResult)) rfl
  have h3:=P.adder_left .squareResult (ctl (.copy .squareResult)) (ctl (.copy .number))
    r m (X.payload [] [] [] [] (squareWord s) [] [] [] []) w v u [] [] [] [] (squareWord s) rfl rfl rfl rfl
  simp only [List.append_nil] at h3
  have h4:=P.adder_right .number (ctl (.copy .number)) (ctl .times4a)
    r m (X.payload [] [] [] [] (squareWord s) [] [] [] []) w v u (squareWord s) [] [] [] n rfl rfl hn rfl
  simp only [List.append_nil] at h4
  let xSquare:=X.payload [] [] [] [] (squareWord s) [] [] [] []
  have h5:=push_bit (ctl .times4a) (ctl .times4b) (adder .right) false
    (work r m (A.store (squareWord s) n [] []) xSquare) rfl
  rw [work,view_adder,SemiprimeD1StackAdder.store_right] at h5
  have h6:=push_bit (ctl .times4b) (ctl .subtractD) (adder .right) false
    (work r m (A.store (squareWord s) (false::n) [] []) xSquare) rfl
  rw [work,view_adder,SemiprimeD1StackAdder.store_right] at h6
  have h7:=subtract_call r m xSquare w v u (squareWord s) (fourWord n) (ctl .subtractD) (ctl .borrowD) rfl
  change Runs program _ _ _ _ (work r m (A.store [] [] [] ((discriminantReport n s).borrow::discriminant n s)) xSquare) at h7
  rw [hb] at h7
  have h8:=pop_false (ctl .borrowD) (ctl (.copy .discriminant)) (ctl (.abort 0)) (ctl (.abort 0))
    (adder .output) (work r m (A.store [] [] [] (false::discriminant n s)) xSquare) (discriminant n s) rfl rfl
  rw [work,view_adder,SemiprimeD1StackAdder.store_output] at h8
  have h9:=copy_call .discriminant (ctl (.copy .discriminant)) (ctl .clearD) rfl
    (work r m (A.store [] [] [] (discriminant n s)) xSquare) (discriminant n s) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (squareRoot (SemiprimeD1StackBinarySquareRoot.metadata
    (SemiprimeD1StackPackedRootMetadata.boot .input))) (discriminant n s++[])) at h9
  rw [List.append_nil,work,view_metadata] at h9
  have h10:=drain_call (ctl .clearD) (ctl .clearSquare) (adder .output)
    (work r (metadataInput (discriminant n s)) (A.store [] [] [] (discriminant n s)) xSquare)
    (discriminant n s) rfl rfl
  rw [work,view_adder,SemiprimeD1StackAdder.store_output] at h10
  have h11:=drain_call (ctl .clearSquare) (ctl .root) (multiply (.inl .right))
    (work r (metadataInput (discriminant n s)) a xSquare) (squareWord s) rfl rfl
  rw [work,view_multiply,SemiprimeD1StackMultiplierExecution.payload_acc] at h11
  have h:=join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11
  change Runs program (time n s) _ (work r (fun _=>[]) a x) _ (work r (metadataInput (discriminant n s)) a x) at h
  rw [work_empty,work_input] at h
  exact h
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryDiscriminant
