/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputMeaning
/-! # Exact physical states of the closed original public input program
These payload functions describe executed configurations only. They are not
runtime/cache/getter/guard/verdict inputs to the fixed Core52 program.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
namespace RiemannGaussian.SemiprimeD1StackPublicInputState
open SemiprimeD1StackPublicInput
namespace M
export SemiprimeD1StackPublicInputMeaning (cached word rawFlag actualBound expected)
end M
/-- Complete actual header source result, including original public metadata. -/
def acquired (bits indexWord : List Bool) : H.Stack→List Bool :=
  SemiprimeD1StackPublicInputWidthExecution.result bits indexWord
/-- Only the ACTUAL disposable header bound changes after comparison/draining. -/
def header (bits indexWord bd : List Bool) : H.Stack→List Bool :=
  fun k=>if k=H.output then bd else acquired bits indexWord k
/-- Exact52-role payload; every unused private/shadow/work cell is explicit empty.
The physical alias for the template/right operand is in the header, not the
unused private shadow. Equality's output aliases the real comparison cell. -/
def store (h : H.Stack→List Bool) (raw reader word left comparison result : List Bool) : Stack→List Bool :=
  Sum.elim h (Sum.elim
    (fun k=>if k=0 then reader else if k=4 then word else [])
    (Sum.elim (SemiprimeD1StackWordLess.store left [] [] [] comparison)
      (Sum.elim (SemiprimeD1StackAdder.store [] [] [] result) (fun _=>raw))))
/-- Actual original raw suffix after width-sized fitting (including short input). -/
def suffix (bits raw : List Bool) : List Bool := raw.drop (M.cached bits).length
/-- Reached cells after the single real H37 call. -/
def ready (bits raw indexWord : List Bool) : Stack→List Bool :=
  store (acquired bits indexWord) raw [] [] [] [] []
/-- Reached cells after actual preserving raw-assignment Copy. -/
def afterCopy (bits raw indexWord : List Bool) : Stack→List Bool :=
  store (acquired bits indexWord) raw raw [] [] [] []
/-- Actual completed WordBlock, preserving every suffix byte and the original raw. -/
def afterBlock (bits raw indexWord : List Bool) : Stack→List Bool :=
  store (acquired bits indexWord) raw (suffix bits raw) (M.word bits raw) [] [] []
/-- Exact final state retains public metadata/index/raw/suffix, clears all
bound/word/comparison work, and returns only the ACTUALLY computed verdict. -/
def done (bits raw indexWord : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (header bits indexWord []) raw (suffix bits raw) [] [] []
    [M.expected bits raw indexWord],[]⟩
/-- The SAME source's template is the actual shared block width. -/
@[simp] theorem acquired_modulus (bits indexWord : List Bool) : acquired bits indexWord modulusKey=M.cached bits := rfl
/-- The SAME actual source supplies the strict comparison bound. -/
@[simp] theorem acquired_bound (bits indexWord : List Bool) : acquired bits indexWord H.output=M.actualBound bits indexWord := rfl
/-- Updating the disposable bound preserves the shared original template. -/
@[simp] theorem header_modulus (bits indexWord bd : List Bool) : header bits indexWord bd modulusKey=M.cached bits := rfl
/-- Exact disposable bound projection. -/
@[simp] theorem header_bound (bits indexWord bd : List Bool) : header bits indexWord bd H.output=bd := by simp [header]
/-- The original header itself is this payload at its actually produced bound. -/
theorem header_acquired (bits indexWord : List Bool) :
    header bits indexWord (M.actualBound bits indexWord)=acquired bits indexWord := by
  funext k
  by_cases hk:k=H.output
  · subst k; rw [header_bound,acquired_bound]
  · simp [header,hk]
/-- The closed entry contains only original N, raw assignment and physical index. -/
theorem initial_data (bits raw indexWord : List Bool) :
    (initial bits raw indexWord).data=store (SemiprimeD1StackPublicInputWidth.input bits indexWord) raw [] [] [] [] [] := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · fin_cases k <;> rfl
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · rcases k with k|k <;> cases k <;> rfl
/-- Exact real pop/push update of the physical extracted-word cell. -/
theorem update_word (h : H.Stack→List Bool) (raw reader word left cmp out fresh : List Bool) :
    Function.update (store h raw reader word left cmp out) (blockStack 4) fresh=
      store h raw reader fresh left cmp out := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · fin_cases k <;> rfl
    · rfl
/-- Exact real update of the only comparison-result cell. -/
theorem update_comparison (h : H.Stack→List Bool) (raw reader word left cmp out fresh : List Bool) :
    Function.update (store h raw reader word left cmp out) comparison fresh=
      store h raw reader word left fresh out := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rcases k with k|k <;> cases k <;> rfl
      · rfl
/-- Exact real update of the private final-output cell. -/
theorem update_output (h : H.Stack→List Bool) (raw reader word left cmp out fresh : List Bool) :
    Function.update (store h raw reader word left cmp out) output fresh=
      store h raw reader word left cmp fresh := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k <;> cases k <;> rfl
/-- Actual bound consumption preserves EVERY other original header cell. -/
theorem update_bound (bits indexWord bd raw reader word left cmp out fresh : List Bool) :
    Function.update (store (header bits indexWord bd) raw reader word left cmp out) bound fresh=
      store (header bits indexWord fresh) raw reader word left cmp out := by
  funext k
  rcases k with k|k
  · by_cases hk:k=H.output
    · subst k; rfl
    · simp [Function.update,store,bound,header,hk]
  · rfl

/-- Exact final computed singleton, with no supplied verdict input. -/
@[simp] theorem done_output (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data output=[M.expected bits raw indexWord] := rfl
/-- Entire original assignment is retained literally. -/
@[simp] theorem done_raw (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data assignment=raw := rfl
/-- The actual unread suffix, including any flag cell, is retained literally. -/
@[simp] theorem done_suffix (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data (blockStack 0)=suffix bits raw := rfl
/-- The original physical index is not normalized, consumed or replaced. -/
@[simp] theorem done_index (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data index=indexWord := rfl
/-- Every actual original public metadata cache survives the whole checker. -/
@[simp] theorem done_public (bits raw indexWord : List Bool) (k : SemiprimeD1BinaryPublicAcquisition.Stack) :
    (done bits raw indexWord).data (.inl (.inl k))=
      SemiprimeD1BinaryPublicAcquisitionComponents.result bits k := rfl
/-- The physically acquired disposable bound has been completely drained. -/
@[simp] theorem done_bound (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data bound=[] := rfl
/-- No fitted word remains in a private arithmetic cell. -/
@[simp] theorem done_word (bits raw indexWord : List Bool) :
    (done bits raw indexWord).data (blockStack 4)=[] := rfl

end RiemannGaussian.SemiprimeD1StackPublicInputState
