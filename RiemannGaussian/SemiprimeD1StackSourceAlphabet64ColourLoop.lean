/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Colours
/-! # Whole actual colour-block loop preserves original head-major coordinate order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64ColourLoop
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Primitives SemiprimeD1StackSourceAlphabet64Colours
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Complete physical fixed-block loop leaves exactly the reversed original-order
compact-colour field bytes; no native coordinate count occurs in its control. -/
theorem colours_run (base:Stack→List Bool) (n:Nat) (bits hist:List Bool) (hlen:bits.length=6*n)
    (hl:base (aux .trimLeft)=[]) (hr:base (aux .trimRight)=[]) (hs:base (aux .frameScratch)=[]) :
    ∃q ≤ 200*n+1,Runs program q .colourStart (view base bits [] [] [] [] hist) .reverseRow
      (view base [] [] [] [] [] ((fields (colours n bits)).reverse++hist)) :=by
  induction n generalizing bits hist with
  | zero=>
    have he:bits=[]:=List.length_eq_zero_iff.mp (by simpa only [Nat.mul_zero] using hlen)
    subst bits
    refine ⟨1,by omega,?_⟩
    simpa only [colours,fields,List.foldr_nil,List.reverse_nil,List.nil_append] using
      SemiprimeD1StackPhysicalLoops.peek_empty program .colourStart .reverseRow (.readColour 0) (.readColour 0)
        (aux .bitsReverse) rfl (view base [] [] [] [] [] hist) rfl
  | succ n ih=>
    have ht:(bits.take 6).length=6:=by rw [List.length_take];omega
    have hd:(bits.drop 6).length=6*n:=by rw [List.length_drop];omega
    obtain ⟨r,hrBound,h0⟩:=colour_run base (bits.take 6) (bits.drop 6) hist ht hl hr hs
    rw [List.take_append_drop] at h0
    obtain ⟨s,hsBound,h1⟩:=ih (bits.drop 6)
      ((frame (compact (bits.take 6).reverse) []).reverse++hist) hd
    have he:(fields (colours n (bits.drop 6))).reverse++
        ((frame (compact (bits.take 6).reverse) []).reverse++hist)=
        (fields (colours (n+1) bits)).reverse++hist:=by
      have hf:fields (colours (n+1) bits)=
          frame (compact (bits.take 6).reverse) []++fields (colours n (bits.drop 6)):=by
        change frame _ (fields (colours n (bits.drop 6)))=_
        exact (SemiprimeD1TensorTapeCodec.frame_append _ [] _).symm
      rw [hf,List.reverse_append,List.append_assoc]
    rw [he] at h1
    exact ⟨r+s,by omega,compose h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64ColourLoop
