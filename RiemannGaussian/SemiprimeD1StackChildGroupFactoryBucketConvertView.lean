/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvert
/-! # Exact postconversion reuse boundary and retained physical source caches -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvertView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketConvert
namespace Reuse
export SemiprimeD1StackChildGroupFactoryBucketReuse (role result_role result_other)
end Reuse
/-- The actual twelve converter words are among the actual fifteen erased roles. -/
def ordinalIndex:O.Stack→Fin 15
  | .bank=>3 | .reader=>4 | .word=>5 | .fieldScratch=>6 | .valid=>7 | .copyScratch=>8
  | .digits=>9 | .unaryScratch=>10 | .unary=>11 | .logScratch=>12 | .history=>13 | .output=>14
/-- Exact literal role identity, not a supplied mapping between input records. -/
theorem ordinalIndex_role (k:O.Stack):Reuse.role (ordinalIndex k)=ordinal k:=by cases k <;> rfl
/-- Complete actual conversion retains every physical word outside its twelve-role bank. -/
theorem converted_other (before:Stack→List Bool) (words:List (List Bool)) (k:Stack)
    (h:∀j,ordinal j≠k):converted before words k=before k:=by
  rw [converted, (SemiprimeD1StackChildGroupFactoryCalls.withOrdinal_rel _ _).2 k h]
  exact Function.update_of_ne (Ne.symm (h .bank)) _ _
/-- Every explicitly erased packet/converter role is physically empty. -/
theorem result_role (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)) (j:Fin 15):
    result before packet children words (Reuse.role j)=[]:=Reuse.result_role _ _
/-- All caller words outside the fifteen actually drained roles and the actual bucket log are retained. -/
theorem result_other (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)) (k:Stack)
    (hf:∀j,Reuse.role j≠k) (hh:k≠aux .factorHistory):result before packet children words k=before k:=by
  rw [result,Reuse.result_other _ _ hf,logged,Function.update_of_ne hh]
  exact converted_other _ _ k (by intro j;rw [←ordinalIndex_role j];exact hf _)
/-- All twelve actual converter tapes are really empty, including retained bank and unary output. -/
theorem result_ordinal (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)) (k:O.Stack):
    result before packet children words (ordinal k)=[]:=by
  rw [←ordinalIndex_role k]
  exact result_role _ _ _ _ _
/-- Exact actual bucket record in newest-first physical history, with all previous buckets retained. -/
theorem result_factorHistory (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)):
    result before packet children words (aux .factorHistory)=
      (Record.row packet children (Ordinal.result words)).reverse++before (aux .factorHistory):=by
  rw [result,Reuse.result_other _ _ (by intro j;fin_cases j <;> decide),logged,Function.update_self]
  rw [converted_other _ _ _ (by intro k;cases k <;> decide)]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvertView
