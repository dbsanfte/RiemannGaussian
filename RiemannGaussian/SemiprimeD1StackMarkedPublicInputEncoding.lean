/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInput
/-! # Proof-side physical bank views for the marked coefficient source
These views describe actual configurations only and never enter runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInput
/-- Every private physical work word; all unmentioned fields are actually empty. -/
structure Work where
  /-- Physical reader word. -/
  reader : List Bool := []
  /-- Physical count word. -/
  count : List Bool := []
  /-- Physical reverse word. -/
  reverse : List Bool := []
  /-- Physical digit word. -/
  digit : List Bool := []
  /-- Physical multiplier word. -/
  multiplier : List Bool := []
  /-- Physical radix word. -/
  radix : List Bool := []
  /-- Physical productScratch word. -/
  productScratch : List Bool := []
  /-- Physical offset word. -/
  offset : List Bool := []
  /-- Physical side word. -/
  side : List Bool := []
  /-- Physical template word. -/
  template : List Bool := []
  /-- Physical shifted word. -/
  shifted : List Bool := []
  /-- Physical scratch word. -/
  scratch : List Bool := []
  /-- Physical output word. -/
  output : List Bool := []
/-- Whole66-role physical view; extractor template shadow is explicitly empty. -/
def data (p : P.Stack → List Bool) (w : Work) : Stack → List Bool :=
  Sum.elim p (Sum.elim
    (fun k => if k=0 then w.reader else if k=2 then w.count else if k=3 then w.reverse
      else if k=4 then w.digit else [])
    (Sum.elim (SemiprimeD1StackUnaryProduct.contents w.multiplier w.radix w.productScratch w.offset)
      (fun k => match k with
        | .side => w.side | .widthTemplate => w.template | .shifted => w.shifted
        | .copyScratch => w.scratch | .output => w.output)))
/-- The exact retained checker bank after its real completed source. -/
def acquired (bits raw indexWord : List Bool) : P.Stack → List Bool :=
  (SemiprimeD1StackPublicInputState.done bits raw indexWord).data
/-- Actual retained ell cache, not a template input. -/
def ellWord (bits raw indexWord : List Bool) : List Bool :=
  acquired bits raw indexWord (.inl (.inl SemiprimeD1StackPublicInputWidth.widthKey))
/-- Actual retained radix cache, distinct from the full signal-width template. -/
def radixWord (bits raw indexWord : List Bool) : List Bool :=
  acquired bits raw indexWord (.inl (.inl SemiprimeD1StackPublicInputWidth.radixKey))
/-- Actual twice-copied precision template. -/
def template (bits raw indexWord : List Bool) : List Bool :=
  ellWord bits raw indexWord ++ ellWord bits raw indexWord
/-- Positive-shift marking bytes before the actual final fit. -/
def marked (shift : Nat) (digit : List Bool) : List Bool :=
  true :: (List.replicate (shift-1) false ++ digit)
/-- Physical branch result before fitting, with no supplied verdict operand. -/
def operand (bits raw indexWord : List Bool) (side : Bool) : List Bool :=
  if SemiprimeD1StackPublicInputMeaning.expected bits raw indexWord then
    if side then [true] else
      marked ((ellWord bits raw indexWord).length+
        indexWord.length*(radixWord bits raw indexWord).length)
        (SemiprimeD1StackPublicInputMeaning.word bits raw)
  else []
/-- Literal fixed-width binary coefficient specification. -/
def coefficient (bits raw indexWord : List Bool) (side : Bool) : List Bool :=
  SemiprimeD1StackWordFitExecution.result (operand bits raw indexWord side) (template bits raw indexWord)
/-- Exact stopped66-role state: whole checker bank, side and precision template
survive; every disposable word and unused template shadow is empty. -/
def result (bits raw indexWord : List Bool) (side : Bool) : Stack → List Bool :=
  data (acquired bits raw indexWord)
    { side := [side], template := template bits raw indexWord,
      output := coefficient bits raw indexWord side }
/-- Actual halt configuration, including empty real return cells. -/
def done (bits raw indexWord : List Bool) (side : Bool) : C.State Stack Label :=
  ⟨none,none,none,result bits raw indexWord side,[]⟩
/-- The four physical source inputs agree with this empty-work bank view. -/
theorem initial_data (bits raw indexWord : List Bool) (side : Bool) :
    (initial bits raw indexWord [side]).data =
      data (P.initial bits raw indexWord).data {side := [side]} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Exact retained checker projection. -/
@[simp] theorem data_checker (p : P.Stack → List Bool) (w : Work) (k : P.Stack) :
    data p w (checker k)=p k := rfl
/-- Actual reader cell of the complete physical view. -/
@[simp] theorem data_reader (p : P.Stack → List Bool) (w : Work) :
    data p w (word 0)=w.reader := rfl
/-- Actual one-cell reader update preserves the entire other physical bank. -/
theorem update_reader (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (word 0) xs = data p {w with reader := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual count cell of the complete physical view. -/
@[simp] theorem data_count (p : P.Stack → List Bool) (w : Work) :
    data p w (word 2)=w.count := rfl
/-- Actual one-cell count update preserves the entire other physical bank. -/
theorem update_count (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (word 2) xs = data p {w with count := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual reverse cell of the complete physical view. -/
@[simp] theorem data_reverse (p : P.Stack → List Bool) (w : Work) :
    data p w (word 3)=w.reverse := rfl
/-- Actual one-cell reverse update preserves the entire other physical bank. -/
theorem update_reverse (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (word 3) xs = data p {w with reverse := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual digit cell of the complete physical view. -/
@[simp] theorem data_digit (p : P.Stack → List Bool) (w : Work) :
    data p w (word 4)=w.digit := rfl
/-- Actual one-cell digit update preserves the entire other physical bank. -/
theorem update_digit (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (word 4) xs = data p {w with digit := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual multiplier cell of the complete physical view. -/
@[simp] theorem data_multiplier (p : P.Stack → List Bool) (w : Work) :
    data p w (product .multiplier)=w.multiplier := rfl
/-- Actual one-cell multiplier update preserves the entire other physical bank. -/
theorem update_multiplier (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (product .multiplier) xs = data p {w with multiplier := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual radix cell of the complete physical view. -/
@[simp] theorem data_radix (p : P.Stack → List Bool) (w : Work) :
    data p w (product .multiplicand)=w.radix := rfl
/-- Actual one-cell radix update preserves the entire other physical bank. -/
theorem update_radix (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (product .multiplicand) xs = data p {w with radix := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual productScratch cell of the complete physical view. -/
@[simp] theorem data_productScratch (p : P.Stack → List Bool) (w : Work) :
    data p w (product .scratch)=w.productScratch := rfl
/-- Actual one-cell productScratch update preserves the entire other physical bank. -/
theorem update_productScratch (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (product .scratch) xs = data p {w with productScratch := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual offset cell of the complete physical view. -/
@[simp] theorem data_offset (p : P.Stack → List Bool) (w : Work) :
    data p w (product .product)=w.offset := rfl
/-- Actual one-cell offset update preserves the entire other physical bank. -/
theorem update_offset (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (product .product) xs = data p {w with offset := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual side cell of the complete physical view. -/
@[simp] theorem data_side (p : P.Stack → List Bool) (w : Work) :
    data p w (aux .side)=w.side := rfl
/-- Actual one-cell side update preserves the entire other physical bank. -/
theorem update_side (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (aux .side) xs = data p {w with side := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual template cell of the complete physical view. -/
@[simp] theorem data_template (p : P.Stack → List Bool) (w : Work) :
    data p w (aux .widthTemplate)=w.template := rfl
/-- Actual one-cell template update preserves the entire other physical bank. -/
theorem update_template (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (aux .widthTemplate) xs = data p {w with template := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual shifted cell of the complete physical view. -/
@[simp] theorem data_shifted (p : P.Stack → List Bool) (w : Work) :
    data p w (aux .shifted)=w.shifted := rfl
/-- Actual one-cell shifted update preserves the entire other physical bank. -/
theorem update_shifted (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (aux .shifted) xs = data p {w with shifted := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual scratch cell of the complete physical view. -/
@[simp] theorem data_scratch (p : P.Stack → List Bool) (w : Work) :
    data p w (aux .copyScratch)=w.scratch := rfl
/-- Actual one-cell scratch update preserves the entire other physical bank. -/
theorem update_scratch (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (aux .copyScratch) xs = data p {w with scratch := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
/-- Actual output cell of the complete physical view. -/
@[simp] theorem data_output (p : P.Stack → List Bool) (w : Work) :
    data p w (aux .output)=w.output := rfl
/-- Actual one-cell output update preserves the entire other physical bank. -/
theorem update_output (p : P.Stack → List Bool) (w : Work) (xs : List Bool) :
    Function.update (data p w) (aux .output) xs = data p {w with output := xs} := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · fin_cases k <;> rfl
    · rcases k with k | k <;> cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputEncoding

