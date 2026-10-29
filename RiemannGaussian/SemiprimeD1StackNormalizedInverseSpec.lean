/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNormalizedInverseBits
/-! # Exact physical-word order for a descending normalized-inverse source
These definitions are proof specifications only. The actual source must acquire
each coefficient by paid physical parsing and execute every fitted operation.
No associativity or rational-value-only replacement of a raw word is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
open SemiprimeRationalBits SemiprimeJetBits
/-- Exact native product-FIRST/suffix-SECOND operation, including every normalization/fit. -/
def combine (template : List Bool) (pair : RationalWord×RationalWord) (suffix : RationalWord) : RationalWord :=
  (executeOperation .add (executeOperation .mul pair.1 pair.2 template).word suffix template).word
/-- Literal dot words have this exact right fold, independently of validity, fitting or W. -/
theorem dot_fold (template : List Bool) (pairs : List (RationalWord×RationalWord)) :
    (SemiprimeDotBits.dotBits template pairs).word=pairs.foldr (combine template) zeroWord := by
  induction pairs with
  | nil=>rfl
  | cons pair pairs ih=>
    change (executeOperation .add (executeOperation .mul pair.1 pair.2 template).word
      (SemiprimeDotBits.dotBits template pairs).word template).word=_
    rw [ih]
    rfl
/-- Descending physical pair execution reproduces the ENTIRE raw native word, not just its value. -/
theorem dot_descending (template : List Bool) (pairs : List (RationalWord×RationalWord)) :
    pairs.reverse.foldl (fun suffix pair=>combine template pair suffix) zeroWord=
      (SemiprimeDotBits.dotBits template pairs).word := by
  rw [List.foldl_reverse,dot_fold]
/-- Exact zero-extended list-array read; no executable source uses this as an opcode. -/
def readWord (words : List RationalWord) (i : ℕ) : RationalWord := (words[i]?).getD zeroWord
/-- Actual native array and physical list-array codecs share the same zero default. -/
theorem read_toList (a : Array RationalWord) (i : ℕ) : readWord a.toList i=wordAt a i := by
  simp only [readWord,wordAt,Array.getElem?_toList]
/-- A newest-first physical prefix at index i contains the original coefficient n-1-i. -/
theorem read_reverse (words : List RationalWord) (i : ℕ) (hi : i<words.length) :
    readWord words.reverse i=readWord words (words.length-1-i) := by
  rw [readWord,List.getElem?_reverse hi]
  rfl
/-- Pair selected by the two actually decreasing unary indices. -/
def pairAt (a : Array RationalWord) (reversed : List RationalWord) (i : ℕ) : RationalWord×RationalWord :=
  (wordAt a (i+1),readWord reversed i)
/-- Proof-only chronological pair list for the physical descending loop. -/
def descendingPairs (a : Array RationalWord) (reversed : List RationalWord) (n : ℕ) : List (RationalWord×RationalWord) :=
  (List.range n).reverse.map (pairAt a reversed)
/-- Every descending pair matches the exact original cached-inverse read order. -/
theorem pairs_original (a b : Array RationalWord) (n : ℕ) (hb : b.size=n) :
    descendingPairs a b.toList.reverse n=(SemiprimeNormalizedInverseBits.pairs a b n).reverse := by
  apply List.ext_getElem
  · simp only [descendingPairs,List.length_map,List.length_reverse,List.length_range,
      SemiprimeNormalizedInverseBits.pairs_length]
  · intro i hi hj
    have hin : i<n := by simpa only [descendingPairs,List.length_map,List.length_reverse,List.length_range] using hi
    simp only [descendingPairs,List.getElem_map,List.getElem_reverse,List.getElem_range,
      SemiprimeNormalizedInverseBits.pairs,List.getElem_ofFn,List.length_ofFn,List.length_range]
    apply Prod.ext
    · rfl
    · change readWord b.toList.reverse (n-1-i)=wordAt b (n-1-(n-1-i))
      rw [read_reverse b.toList (n-1-i) (by simpa only [Array.length_toList,hb] using (show n-1-i<n by omega)),
        Array.length_toList,hb,read_toList]
/-- Whole descending accumulation is byte-exact for the native right-fold dot. -/
theorem descending_dot (template : List Bool) (a b : Array RationalWord) (n : ℕ) (hb : b.size=n) :
    (descendingPairs a b.toList.reverse n).foldl (fun suffix pair=>combine template pair suffix) zeroWord=
      (SemiprimeDotBits.dotBits template (SemiprimeNormalizedInverseBits.pairs a b n)).word := by
  rw [pairs_original a b n hb,dot_descending]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
