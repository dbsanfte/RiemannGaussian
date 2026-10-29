/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprWiring
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Executed framing, copies, draining and restored operands for recursion -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprValueStack
open SemiprimeD1StackExpr SemiprimeD1StackExprWiring SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)

/-- Actual left-value framing preserves its result until the separate drain. -/
theorem save_left (op : Op) (code cached saved word : List Bool) :
    Runs program (6*word.length+5) (.saveLeft op) (bank code cached saved word [] [] [] [])
      (.clearLeft op) (bank code cached (frame word saved) word [] [] [] []) := by
  apply included_call program frameStack Label.frame frame_injective SemiprimeD1StackFrame.code 0
    (fun _=>rfl) (.saveLeft op) (.clearLeft op) rfl (6*word.length+4)
    (SemiprimeD1StackFrame.state 0 none word saved []) (SemiprimeD1StackFrame.done word (frame word saved))
    _ _ rfl rfl (SemiprimeD1StackFrame.frame_words word saved none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk 1 rfl).elim

/-- Every left result cell is physically cleared before the right recursive call. -/
theorem clear_left (op : Op) (code cached saved word : List Bool) :
    Runs program (word.length+1) (.clearLeft op) (bank code cached saved word [] [] [] [])
      (.rightEval op) (bank code cached saved [] [] [] [] []) := by
  simpa only [update_result] using SemiprimeD1StackPhysicalLoops.drain program
    (.clearLeft op) (.rightEval op) .result rfl (bank code cached saved word [] [] [] []) word

/-- Real copy supplies the right arithmetic operand, preserving the result until draining. -/
theorem copy_right (op : Op) (code cached saved word : List Bool) :
    Runs program (5*word.length+4) (.copyRight op) (bank code cached saved word [] [] [] [])
      (.clearRight op) (bank code cached saved word [] word [] []) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (.copyRight op) (.clearRight op) rfl (5*word.length+3)
    (SemiprimeD1StackCopy.state 0 none word [] []) (SemiprimeD1StackCopy.done word word)
    _ _ rfl rfl (by simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words word [] none)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk 1 rfl).elim

/-- Every right result cell is physically cleared before saved-left parsing. -/
theorem clear_right (op : Op) (code cached saved word : List Bool) :
    Runs program (word.length+1) (.clearRight op) (bank code cached saved word [] word [] [])
      (.readLeft op) (bank code cached saved [] [] word [] []) := by
  simpa only [update_result] using SemiprimeD1StackPhysicalLoops.drain program
    (.clearRight op) (.readLeft op) .result rfl (bank code cached saved word [] word [] []) word

/-- Saved-left parsing visits its actual physical field and retains the exact older suffix. -/
theorem read_left (op : Op) (code cached saved left right : List Bool) :
    Runs program (8*left.length+7) (.readLeft op) (bank code cached (frame left saved) [] [] right [] [])
      (.checkLeft op) (bank code cached saved [] left right [true] []) := by
  apply included_call program fieldStack Label.field field_injective Field.code (Field.active .tagPop (none,false))
    (fun _=>rfl) (.readLeft op) (.checkLeft op) rfl (8*left.length+6)
    (SemiprimeD1TensorTapeFieldBytecode.initial (frame left saved) [])
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents saved [] left) (fun _=>[true])⟩
    _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run left saved [])
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
    · intro k hk
      cases k <;> first | rfl | exact (hk (.inl .input) rfl).elim | exact (hk (.inl .output) rfl).elim | exact (hk (.inr ()) rfl).elim

/-- The actual parser's true validity cell is consumed before applying arithmetic. -/
theorem check_left (op : Op) (code cached saved left right : List Bool) :
    Runs program 1 (.checkLeft op) (bank code cached saved [] left right [true] [])
      (.applyOp op) (bank code cached saved [] left right [] []) := by
  apply one_base program (.checkLeft op) (.applyOp op)
    (.pop .flag .bad .bad (.applyOp op)) _ _ rfl
  · simp [SemiprimeD1StackBytecode.execute,SemiprimeD1StackBytecode.choose]
  · simp [SemiprimeD1StackBytecode.execute]
end RiemannGaussian.SemiprimeD1StackExprValueStack
