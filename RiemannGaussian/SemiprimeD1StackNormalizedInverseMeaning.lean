/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOuter
/-! # Whole raw native normalized-inverse equality, including all zero defaults and W=0 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseMeaning
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseCoefficient
open SemiprimeD1StackNormalizedInverseOuter SemiprimeD1StackNormalizedInverseRecurrence
/-- One source step appends exactly the ENTIRE old native next coefficient, without a value-only replacement. -/
theorem next_prefix (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) (n : ℕ) (hn : 0<n) :
    (SemiprimeNormalizedInverseBits.build width a.toArray (n+1)).words.toList.reverse=
      nextWord width a (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse n::
        (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse := by
  rw [next_original width a.toArray n (by omega)]
  rw [Array.toList_push,List.reverse_append,List.reverse_singleton,List.singleton_append]
  rfl
/-- ALL remaining acquired marker iterations reproduce the exact cached native inverse prefix. -/
theorem more_original (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) (remaining n : ℕ)
    (hn : 0<n) :
    more a width remaining n (SemiprimeNormalizedInverseBits.build width a.toArray n).words.toList.reverse=
      (SemiprimeNormalizedInverseBits.build width a.toArray (n+remaining)).words.toList.reverse := by
  induction remaining generalizing n with
  | zero=>rfl
  | succ remaining ih=>
    rw [more,←next_prefix a width n hn,ih (n+1) (by omega)]
    have he : n+(remaining+1)=(n+1)+remaining := by omega
    rw [he]
/-- The physical literal initial ONE is exactly the native first prefix, including W=0. -/
theorem first_original (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) :
    (SemiprimeNormalizedInverseBits.build width a.toArray 1).words.toList.reverse=[SemiprimeJetBits.oneWord] := rfl
/-- Whole positive-q source prefix has exactly the chronological old native array after final reversal. -/
theorem whole_original (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) (q : ℕ) :
    more a width q 1 [SemiprimeJetBits.oneWord]=
      (SemiprimeNormalizedInverseBits.build width a.toArray (q+1)).words.toList.reverse := by
  rw [←first_original a width]
  have h:=more_original a width q 1 (by decide)
  simpa only [Nat.add_comm] using h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseMeaning
