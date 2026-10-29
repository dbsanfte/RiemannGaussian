/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseSpec
/-! # Exact decreasing-index recursion for the physical inverse accumulator -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseRecurrence
open SemiprimeRationalBits SemiprimeJetBits SemiprimeD1StackNormalizedInverseSpec
/-- Proof specification of the physically decreasing pair counter, with an actual accumulator. -/
def dotLoop (width : List Bool) (a : Array RationalWord) (revWords : List RationalWord) :
    ℕ→RationalWord→RationalWord
  | 0,acc=>acc
  | n+1,acc=>dotLoop width a revWords n (combine width (pairAt a revWords n) acc)
/-- Each actual descending pair is evaluated before its already accumulated suffix. -/
theorem dotLoop_fold (width : List Bool) (a : Array RationalWord) (revWords : List RationalWord)
    (n : ℕ) (acc : RationalWord) :
    dotLoop width a revWords n acc=
      (descendingPairs a revWords n).foldl (fun suffix pair=>combine width pair suffix) acc := by
  induction n generalizing acc with
  | zero=>rfl
  | succ n ih=>
    rw [dotLoop,ih]
    simp only [descendingPairs,List.range_succ,List.reverse_append,List.reverse_singleton,
      List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
/-- Starting with the actual literal ZERO yields the entire old raw right-fold word. -/
theorem dotLoop_original (width : List Bool) (a b : Array RationalWord) (n : ℕ) (hb : b.size=n) :
    dotLoop width a b.toList.reverse n zeroWord=
      (SemiprimeDotBits.dotBits width (SemiprimeNormalizedInverseBits.pairs a b n)).word := by
  rw [dotLoop_fold,descending_dot width a b n hb]
/-- Exact final negation for one noninitial coefficient, including the native fit and normalization. -/
theorem next_original (width : List Bool) (a : Array RationalWord) (n : ℕ) (hn : n≠0) :
    (SemiprimeNormalizedInverseBits.build width a (n+1)).words=
      (SemiprimeNormalizedInverseBits.build width a n).words.push
        (executeOperation .neg
          (dotLoop width a (SemiprimeNormalizedInverseBits.build width a n).words.toList.reverse n zeroWord)
          zeroWord width).word := by
  rw [dotLoop_original width a _ n (SemiprimeNormalizedInverseBits.build_size width a n)]
  simp only [SemiprimeNormalizedInverseBits.build,SemiprimeNormalizedInverseBits.extend,hn,ite_false]

end RiemannGaussian.SemiprimeD1StackNormalizedInverseRecurrence
