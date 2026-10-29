/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolution
/-! # Every actual descending pair equals the original complete convolution list -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolutionOriginal
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineConvolution
open SemiprimeRationalBits (RationalWord)
/-- Finite gap-class interpretation is proof-only; no numeric gap enters runtime labels. -/
def classify:Nat→Part | 0=>.unit | 1=>.slope | _+2=>.zero
/-- One actual k decrement advances precisely the fixed finite factor class. -/
theorem next_classify (n:Nat):nextPart (classify n)=classify (n+1):=by
  cases n with
  | zero=>rfl
  | succ n=>cases n <;> rfl
/-- Raw factor bytes equal the original literal two-word factor array with genuine zero extension. -/
theorem factor_original (c:RationalWord) (n:Nat):
    SemiprimeD1StackRecoveryAffineFactor.value (classify n) c=
      SemiprimeJetBits.wordAt #[SemiprimeJetBits.oneWord,c] n:=by
  cases n with
  | zero=>rfl
  | succ n=>cases n with
    | zero=>rfl
    | succ n=>
      change SemiprimeRationalBits.zeroWord=SemiprimeJetBits.wordAt #[SemiprimeJetBits.oneWord,c] (n+2)
      rw [SemiprimeJetBits.wordAt,Array.getElem?_eq_none (by simp)]
      rfl
/-- Ordered pair expansion retains every k from zero through the current physical byte index. -/
theorem pairs_classified (xs:List RationalWord) (c:RationalWord) (gap n:Nat):
    pairs xs c (classify gap) n=(List.range (n+1)).map (fun j=>
      (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs j,
        SemiprimeD1StackRecoveryAffineFactor.value (classify (gap+n-j)) c)):=by
  induction n generalizing gap with
  | zero=>rfl
  | succ n ih=>
    rw [pairs,next_classify,ih]
    rw [show List.range (n+1+1)=List.range (n+1)++[n+1] from List.range_succ]
    rw [List.map_append,List.map_singleton]
    have he:(fun j=>(SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs j,
          SemiprimeD1StackRecoveryAffineFactor.value (classify (gap+1+n-j)) c))=
        (fun j=>(SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs j,
          SemiprimeD1StackRecoveryAffineFactor.value (classify (gap+(n+1)-j)) c)):=by
      funext j
      rw [show gap+1+n-j=gap+(n+1)-j by omega]
    rw [he,show gap+(n+1)-(n+1)=gap by omega]
/-- The finite list/counter correspondence is a proof identity, never an acquired runtime enumeration operand. -/
theorem range_map_ofFn {α:Type} (f:Nat→α) (n:Nat):
    (List.range n).map f=List.ofFn (fun i:Fin n=>f i.val):=by
  simpa only [List.length_range,List.getElem_range,Fin.val_cast] using (List.ofFn_getElem_eq_map (List.range n) f).symm
/-- Exact original pair order and both raw operand words, not just a commutative value equality. -/
theorem pairs_original (xs:List RationalWord) (c:RationalWord) (n:Nat):
    pairs xs c .unit n=SemiprimeJetBits.convolutionPairs xs.toArray #[SemiprimeJetBits.oneWord,c] n:=by
  rw [show Part.unit=classify 0 from rfl,pairs_classified,range_map_ofFn]
  unfold SemiprimeJetBits.convolutionPairs
  apply congrArg List.ofFn
  funext i
  rw [SemiprimeD1StackRecoveryAffineReadLoop.wordAt_original,factor_original]
  simp only [Nat.zero_add]
/-- Actual descending convolution computes exact legacy dot bytes in the original forward k order. -/
theorem coefficient_original (width:List Bool) (xs:List RationalWord) (c:RationalWord) (n:Nat):
    descend width xs c .unit n SemiprimeRationalBits.zeroWord=
      (SemiprimeDotBits.dotBits width
        (SemiprimeJetBits.convolutionPairs xs.toArray #[SemiprimeJetBits.oneWord,c] n)).word:=by
  rw [descend_dot,pairs_original]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolutionOriginal
