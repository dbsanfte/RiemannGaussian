/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePairMeaning
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadLoop
/-! # Exact descending evaluation of the original ordered raw-byte convolution -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolution
open SemiprimeD1StackRecoveryAffine
open SemiprimeRationalBits (RationalWord)
open SemiprimeD1StackRecoveryAffinePairMeaning (step)
/-- Proof interpretation of the same descending finite-class/current-k physical loop. -/
def descend (width:List Bool) (xs:List RationalWord) (c:RationalWord) (part:Part):Nat→RationalWord→RationalWord
  | 0,suffix=>step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs 0)
      (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix
  | n+1,suffix=>descend width xs c (nextPart part) n
      (step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs (n+1))
        (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix)
/-- Every ordered pair is retained, including factor-zero extensions and diagonal terms. -/
def pairs (xs:List RationalWord) (c:RationalWord) (part:Part):Nat→List (RationalWord×RationalWord)
  | 0=>[(SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs 0,SemiprimeD1StackRecoveryAffineFactor.value part c)]
  | n+1=>pairs xs c (nextPart part) n++
      [(SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs (n+1),SemiprimeD1StackRecoveryAffineFactor.value part c)]
/-- The descending actual fold computes the exact ascending-pair right fold, with no omitted zero operations. -/
theorem descend_fold (width:List Bool) (xs:List RationalWord) (c:RationalWord) (part:Part) (n:Nat) (suffix:RationalWord):
    descend width xs c part n suffix=
      (pairs xs c part n).foldr (fun p tail=>step width p.1 p.2 tail) suffix:=by
  induction n generalizing part suffix with
  | zero=>rfl
  | succ n ih=>
    simp only [descend,pairs,List.foldr_append,List.foldr_cons,List.foldr_nil]
    exact ih (nextPart part) _
/-- Native dot recursion retains exactly the same product-FIRST/suffix-SECOND byte operations. -/
theorem dot_fold (width:List Bool) (ps:List (RationalWord×RationalWord)):
    (SemiprimeDotBits.dotBits width ps).word=
      ps.foldr (fun p tail=>step width p.1 p.2 tail) SemiprimeRationalBits.zeroWord:=by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    change step width p.1 p.2 (SemiprimeDotBits.dotBits width ps).word=_
    rw [ih]
    rfl
/-- Exact bytes, rather than only rational values, agree with the authoritative native dot. -/
theorem descend_dot (width:List Bool) (xs:List RationalWord) (c:RationalWord) (part:Part) (n:Nat):
    descend width xs c part n SemiprimeRationalBits.zeroWord=
      (SemiprimeDotBits.dotBits width (pairs xs c part n)).word:=by
  rw [descend_fold,dot_fold]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolution
