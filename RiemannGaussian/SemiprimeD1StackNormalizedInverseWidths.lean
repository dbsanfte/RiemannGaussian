/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseRecurrence
import RiemannGaussian.SemiprimeD1StackNormalizedInverseView
/-! # Actual coefficient and encoded-prefix byte bounds, including W=0 and missing ZERO -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseWidths
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseSpec SemiprimeD1StackNormalizedInverseRecurrence
open SemiprimeRationalBits SemiprimeJetBits
/-- Both real cache fields are counted, including the actual signed prefix. -/
def bytes (word : RationalWord) : ℕ := (signed word).length+word.denominator.length
/-- EVERY operation returns exactly both actual fitted widths and its physical sign, without validity/Fits advice. -/
theorem execute_bytes (op : Operation) (x y : RationalWord) (width : List Bool) :
    bytes (executeOperation op x y width).word=2*width.length+1 := by
  have h:=fitRationalBits_width (rawOperation op x y).word width
  change (signed (fitRationalBits (rawOperation op x y).word width).word).length+
    (fitRationalBits (rawOperation op x y).word width).word.denominator.length=_
  rw [signed,List.length_cons,h.1,h.2]
  omega
/-- The exact product-first/suffix-second result has fitted width even for zero denominators and W=0. -/
theorem combine_bytes (width : List Bool) (pair : RationalWord×RationalWord) (acc : RationalWord) :
    bytes (combine width pair acc)=2*width.length+1 := execute_bytes .add _ _ width
/-- The original ONE has its literal three physical cache bytes, independently of W. -/
theorem one_bytes : bytes oneWord=3 := rfl
/-- The default/initial ZERO is literal and unfitted, even when W=0. -/
theorem zero_bytes : bytes zeroWord=2 := rfl
/-- Every decreasing-loop accumulator remains physically bounded by W or its actual initial fields. -/
theorem dotLoop_bytes (width : List Bool) (a : Array RationalWord) (reversed : List RationalWord) (n : ℕ)
    (acc : RationalWord) (hacc : bytes acc≤2*width.length+3) :
    bytes (dotLoop width a reversed n acc)≤2*width.length+3 := by
  induction n generalizing acc with
  | zero=>exact hacc
  | succ n ih=>
    rw [dotLoop]
    exact ih _ (by rw [combine_bytes];omega)
/-- A typed physical row contains both entire coefficient fields, delimiters and its tag. -/
theorem row_bytes (word : RationalWord) (tail : List Bool) :
    (row word tail).length=2*bytes word+tail.length+3 := by
  rw [row_length]
  unfold bytes
  omega
/-- Any zero-extended physical read is paid by the actual array bytes, including its default ZERO. -/
theorem read_bytes (words : List RationalWord) (n : ℕ) : bytes (readWord words n)≤(tape words).length+2 := by
  induction words generalizing n with
  | nil=>simp only [readWord,List.getElem?_nil,Option.getD_none,zero_bytes,tape,List.foldr_nil,List.length_cons,List.length_nil];omega
  | cons word words ih=>
    cases n with
    | zero=>
      change bytes word≤(row word (tape words)).length+2
      rw [row_bytes]
      omega
    | succ n=>
      have h:=ih n
      change bytes (readWord words n)≤(row word (tape words)).length+2
      rw [row_bytes]
      omega
/-- Encoded-array storage is charged coefficient-by-coefficient, preserving all raw padding. -/
theorem tape_bytes (words : List RationalWord) (cap : ℕ) (hc : ∀word∈words,bytes word≤cap) :
    (tape words).length≤words.length*(2*cap+3)+1 := by
  induction words with
  | nil=>simp only [tape,List.foldr_nil,List.length_cons,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons word words ih=>
    have hw:=hc word List.mem_cons_self
    have hh:=ih (fun w h=>hc w (List.mem_cons_of_mem word h))
    change (row word (tape words)).length≤(words.length+1)*(2*cap+3)+1
    rw [row_bytes,Nat.add_mul]
    omega
/-- ALL native cached inverse coefficients have the actual fitted width or the literal initial ONE width. -/
theorem build_bytes (width : List Bool) (a : Array RationalWord) (n : ℕ) :
    ∀word∈(SemiprimeNormalizedInverseBits.build width a n).words.toList,bytes word≤2*width.length+3 := by
  induction n with
  | zero=>intro word h;exact (List.not_mem_nil h).elim
  | succ n ih=>
    intro word hw
    by_cases hz:n=0
    · subst n
      change word∈[oneWord] at hw
      have he:=List.mem_singleton.mp hw
      rw [he,one_bytes]
      omega
    · simp only [SemiprimeNormalizedInverseBits.build,SemiprimeNormalizedInverseBits.extend,hz,ite_false,
        Array.toList_push,List.mem_append,List.mem_singleton] at hw
      rcases hw with hw|hw
      · exact ih word hw
      · rw [hw,execute_bytes]
        omega
/-- Complete physical inverse-prefix storage is quadratic in acquired q/W bytes, even for arbitrary invalid denominator words. -/
theorem build_tape_bytes (width : List Bool) (a : Array RationalWord) (n : ℕ) :
    (tape (SemiprimeNormalizedInverseBits.build width a n).words.toList.reverse).length≤n*(4*width.length+9)+1 := by
  have h:=tape_bytes (SemiprimeNormalizedInverseBits.build width a n).words.toList.reverse (2*width.length+3)
    (by intro word hw;exact build_bytes width a n word (List.mem_reverse.mp hw))
  simpa only [List.length_reverse,Array.length_toList,SemiprimeNormalizedInverseBits.build_size,
    show 2*(2*width.length+3)+3=4*width.length+9 by omega] using h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseWidths
