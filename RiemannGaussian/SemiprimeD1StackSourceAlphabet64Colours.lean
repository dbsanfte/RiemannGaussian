/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Digits
import RiemannGaussian.SemiprimeD1StackPhysicalLoops
/-! # Actual six-bit compact-colour normalization and paid row framing -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Colours
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackSourceAlphabet64Digits
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Six actual active words replace only their physical addresses in an arbitrary retained caller bank. -/
def view (base:Stack→List Bool) (bits raw tr col buf hist:List Bool) :Stack→List Bool
  | .inr .bitsReverse=>bits | .inr .colourRaw=>raw | .inr .trimScratch=>tr
  | .inr .colour=>col | .inr .frameBuffer=>buf | .inr .rowHistory=>hist | k=>base k
/-- One real physical bitsReverse write changes only that word. -/
theorem update_bits (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .bitsReverse) next=
      view base next raw tr col buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One real physical colourRaw write changes only that word. -/
theorem update_raw (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .colourRaw) next=
      view base bits next tr col buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One real physical trimScratch write changes only that word. -/
theorem update_tr (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .trimScratch) next=
      view base bits raw next col buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One real physical colour write changes only that word. -/
theorem update_col (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .colour) next=
      view base bits raw tr next buf hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One real physical frameBuffer write changes only that word. -/
theorem update_buf (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .frameBuffer) next=
      view base bits raw tr col next hist :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- One real physical rowHistory write changes only that word. -/
theorem update_hist (base:Stack→List Bool) (bits raw tr col buf hist next:List Bool) :
    Function.update (view base bits raw tr col buf hist) (aux .rowHistory) next=
      view base bits raw tr col buf next :=by
  funext k
  rcases k with k|k
  · rfl
  · cases k <;> rfl
/-- Every complete physical six-bit block is read, compacted, framed and logged;
all thirty caller/source/power/ID words outside these six live addresses are retained. -/
theorem colour_run (base:Stack→List Bool) (bits tail hist:List Bool) (hlen:bits.length=6)
    (hl:base (aux .trimLeft)=[]) (hr:base (aux .trimRight)=[]) (hs:base (aux .frameScratch)=[]) :
    ∃q ≤ 200,Runs program q .colourStart (view base (bits++tail) [] [] [] [] hist) .colourStart
      (view base tail [] [] [] [] ((frame (compact bits.reverse) []).reverse++hist)) :=by
  let col:=compact bits.reverse
  have h0:Runs program 1 .colourStart (view base (bits++tail) [] [] [] [] hist)
      (.readColour 0) (view base (bits++tail) [] [] [] [] hist):=by
    cases bits with
    | nil=>simp only [List.length_nil] at hlen;omega
    | cons b bits=>
      exact SemiprimeD1StackPhysicalLoops.peek_nonempty program .colourStart .reverseRow
        (.readColour 0) (aux .bitsReverse) rfl _ b (bits++tail) rfl
  have h1:=read_colour 6 0 rfl (view base (bits++tail) [] [] [] [] hist) bits tail hlen rfl
  rw [update_bits,update_raw] at h1
  change Runs program 13 (.readColour 0) _ .reverseColour (view base tail (bits.reverse++[]) [] [] [] hist) at h1
  rw [List.append_nil] at h1
  have h2:=reverse_call .colour .reverseColour (.normalize .colour) rfl
    (view base tail bits.reverse [] [] [] hist)
  change Runs program (2*bits.reverse.length+3) .reverseColour _ (.normalize .colour)
    (Function.update (Function.update (view base tail bits.reverse [] [] [] hist) (aux .colourRaw) [])
      (aux .trimScratch) (bits.reverse.reverse++[])) at h2
  rw [update_raw,update_tr,List.reverse_reverse,List.append_nil] at h2
  have h3:=trim_call .colour (view base tail [] bits [] [] hist) hl hr
  change Runs program (SemiprimeD1StackReduceExecution.trimTime bits+1) (.normalize .colour) _ .frameColour
    (Function.update (Function.update (view base tail [] bits [] [] hist) (aux .trimScratch) [])
      (aux .colour) (SemiprimeD1StackReduceExecution.trimReverse bits++[])) at h3
  have ht:=trim_reverse bits.reverse
  rw [List.reverse_reverse] at ht
  rw [update_tr,update_col,List.append_nil,ht] at h3
  have h4:=frame_call .colour .frameColour .reverseColourFrame rfl (view base tail [] [] col [] hist) hs
  rw [update_buf] at h4
  change Runs program (6*col.length+5) .frameColour _ .reverseColourFrame
    (view base tail [] [] col (frame col []) hist) at h4
  have h5:=reverse_call .colourFrame .reverseColourFrame .clearColour rfl
    (view base tail [] [] col (frame col []) hist)
  change Runs program (2*(frame col []).length+3) .reverseColourFrame _ .clearColour
    (Function.update (Function.update (view base tail [] [] col (frame col []) hist) (aux .frameBuffer) [])
      (aux .rowHistory) ((frame col []).reverse++hist)) at h5
  rw [update_buf,update_hist] at h5
  have h6:=SemiprimeD1StackPhysicalLoops.drain program .clearColour .colourStart (aux .colour) rfl
    (view base tail [] [] col [] ((frame col []).reverse++hist)) col
  rw [update_col,update_col] at h6
  have hall:=compose (compose (compose (compose (compose (compose h0 h1) h2) h3) h4) h5) h6
  refine ⟨_,?_,hall⟩
  have hc:col.length ≤ 6:=(SemiprimeSourceCompactBits.trim_length bits.reverse).trans (by rw [List.length_reverse,hlen])
  have hp:=SemiprimeD1StackReduceExecution.trimTime_le bits
  rw [SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil,List.length_reverse,hlen] at *
  omega
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Colours
