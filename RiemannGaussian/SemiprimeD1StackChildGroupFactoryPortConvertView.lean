/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
/-! # Exact actual unary-tape logging and full thirteen-word reuse boundary -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryPortConvert
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (role result_role result_other)
end Reuse
/-- All actual converter roles are among the same thirteen physically erased words. -/
def ordinalIndex:O.Stack→Fin 13
  | .bank=>1 | .reader=>2 | .word=>3 | .fieldScratch=>4 | .valid=>5 | .copyScratch=>6
  | .digits=>7 | .unaryScratch=>8 | .unary=>9 | .logScratch=>10 | .history=>11 | .output=>12
/-- Exact fixed role identity, independent of every input word and computed index. -/
theorem ordinalIndex_role (ordering:Bool) (k:O.Stack):Reuse.role ordering (ordinalIndex k)=ordinal k:=by cases k <;> rfl
/-- The real converter call retains every caller word outside its allocated twelve tapes. -/
theorem converted_other (before:Stack→List Bool) (words:List (List Bool)) (k:Stack)
    (h:∀j,ordinal j≠k):converted before words k=before k:=by
  rw [converted,(SemiprimeD1StackChildGroupFactoryCalls.withOrdinal_rel _ _).2 k h]
  exact Function.update_of_ne (Ne.symm (h .bank)) _ _
/-- Every one of the thirteen actual metadata/converter tapes is physically empty. -/
theorem result_role (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)) (j:Fin 13):
    result ordering before words (Reuse.role ordering j)=[]:=Reuse.result_role _ _ _
/-- Every actual caller/cache word outside physical drains and the one actual log is retained. -/
theorem result_other (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)) (k:Stack)
    (hf:∀j,Reuse.role ordering j≠k) (hh:k≠Log.historyRole (logSite ordering)):
    result ordering before words k=before k:=by
  rw [result,Reuse.result_other _ _ _ hf,logged,Function.update_of_ne hh]
  exact converted_other _ _ k (by intro j;rw [←ordinalIndex_role ordering j];exact hf _)
/-- Every actual converter tape, including its retained input shadow and output, is really clear. -/
theorem result_ordinal (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)) (k:O.Stack):
    result ordering before words (ordinal k)=[]:=by
  rw [←ordinalIndex_role ordering k]
  exact result_role _ _ _ _
/-- The actual metadata bank is really clear after its own drain. -/
theorem result_bank (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)):
    result ordering before words (Reuse.bankRole ordering)=[]:=result_role _ _ _ 0
/-- The actual unary scope/order vector is logged in its exact real row order. -/
theorem result_history (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)):
    result ordering before words (Log.historyRole (logSite ordering))=
      (Log.row (Ordinal.result words)).reverse++before (Log.historyRole (logSite ordering)):=by
  rw [result,Reuse.result_other _ _ _ (by intro j;fin_cases j <;> cases ordering <;> decide),logged,Function.update_self]
  rw [converted_other _ _ _ (by intro k;cases k <;> cases ordering <;> decide)]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvertView
