/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficients
import RiemannGaussian.SemiprimeD1StackRecoveryAffineConvolutionOriginal
/-! # Complete acquired affine-coefficient array equals original multiplyBits raw bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsOriginal
open SemiprimeD1StackRecoveryAffineView
/-- Proof-side chronological list of all actually computed original coefficients. -/
def values (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (n:Nat):
    List SemiprimeRationalBits.RationalWord:=
  (List.range n).map (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width)
/-- Exact array bytes preserve original ordered dot operations, signs, padding, zero extensions and W0. -/
theorem values_original (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (n:Nat):
    values xs c width n=(SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] n).words.toList:=by
  unfold values
  rw [SemiprimeD1StackRecoveryAffineConvolutionOriginal.range_map_ofFn]
  simp only [SemiprimeJetBits.multiplyBits,SemiprimeJetBits.collect,Array.toList_map,Array.toList_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact SemiprimeD1StackRecoveryAffineConvolutionOriginal.coefficient_original width xs c i.val
/-- The whole physical coefficient tape is exactly the original complete rational-array codec. -/
theorem rows_original (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (n:Nat):
    SemiprimeD1StackRecoveryAffineCoefficients.rows xs c width n [false]=
      vector (SemiprimeJetBits.multiplyBits width xs.toArray #[SemiprimeJetBits.oneWord,c] n).words.toList:=by
  rw [SemiprimeD1StackRecoveryAffineCoefficients.rows_fold,←values_original]
  simp only [vector,values,SemiprimeD1StackRecoveryGridView.slopeTape,List.foldr_map]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsOriginal
