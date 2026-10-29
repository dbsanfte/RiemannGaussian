/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOne
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvertView
/-! # Complete actual packet-iteration cache and reuse invariant -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketOne
namespace CV
export SemiprimeD1StackChildGroupFactoryBucketConvertView (result_other result_role result_ordinal result_factorHistory)
end CV
namespace Reuse
export SemiprimeD1StackChildGroupFactoryBucketReuse (role)
end Reuse
namespace LV
export SemiprimeD1StackChildGroupFactoryBucketLoopView (result_reader finalPosition)
end LV
namespace SV
export SemiprimeD1StackChildGroupFactoryBucketScanView (result_position result_histories)
end SV
/-- Every physical caller word outside actual scan/read/log/counter work is retained literally. -/
theorem result_other (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hu:∀j,Reuse.role j≠k)
    (hpr:k≠aux .packetReader) (her:k≠aux .endpointReader) (hbh:k≠aux .bucketHistory)
    (hph:k≠aux .portHistory) (hpos:k≠aux .globalPosition) (hfh:k≠aux .factorHistory):
    result before es packet tail position k=before k:=by
  rw [result,CV.result_other _ _ _ _ _ hu hfh,scanned,
    SV.result_other _ _ _ _ _ hf her hbh hph hpos (Ne.symm (hu 1)) (Ne.symm (hu 2))]
  have hpk:=Ne.symm (hu 0)
  change k≠aux .packetKey at hpk
  simp only [prepared,Function.update_of_ne hpk,Function.update_of_ne hpr]
/-- Actual unread observed-packet suffix, retained through every source and cleanup. -/
theorem result_packetReader (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):
    result before es packet tail position (aux .packetReader)=tail:=by
  rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide),scanned,
    SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl
/-- Actual endpoint scan really consumed its terminator and left its private reader empty. -/
theorem result_endpointReader (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):
    result before es packet tail position (aux .endpointReader)=[]:=by
  rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
  simpa [scanned,SemiprimeD1StackChildGroupFactoryBucketScan.result,
    SemiprimeD1StackChildGroupFactoryBucketScan.reversed,aux] using
      LV.result_reader es (SemiprimeD1StackChildGroupFactoryBucketScan.copied (prepared before packet tail) es) packet position
/-- Every one of the fifteen actual packet/converter work tapes is empty. -/
theorem result_reuse (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool) (j:Fin 15):
    result before es packet tail position (Reuse.role j)=[]:=CV.result_role _ _ _ _ _
/-- Every actual converter tape is empty, including its retained binary bank and unary result. -/
theorem result_ordinal (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool) (k:O.Stack):
    result before es packet tail position (ordinal k)=[]:=CV.result_ordinal _ _ _ _ _
/-- Every parser and raw field is actually fresh for the next packet scan. -/
theorem result_clean (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result before es packet tail position k=[]:=by
  have hz':∀k∈Parse.cleanRoles,prepared before packet tail k=[]:=by simpa [prepared,Parse.cleanRoles,aux,field] using hz
  have h:=SV.result_clean (prepared before packet tail) es packet position hz'
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
    exact h _ (by simp [Parse.cleanRoles])
/-- Fresh binary position after the entire actual bucket, not an original occurrence address. -/
theorem result_position (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool)
    (hp:before (aux .globalPosition)=position):
    result before es packet tail position (aux .globalPosition)=LV.finalPosition es packet position:=by
  rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide),scanned]
  exact SV.result_position _ _ _ _ (by simpa [prepared,aux] using hp)
/-- Both real histories are cleared after their actual consuming reversals. -/
theorem result_histories (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):
    result before es packet tail position (aux .bucketHistory)=[] ∧
      result before es packet tail position (aux .portHistory)=[]:=by
  constructor
  · rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
    exact (SV.result_histories _ _ _ _).1
  · rw [result,CV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide)]
    exact (SV.result_histories _ _ _ _).2
/-- The actual bucket record, including its real converted unary port tape. -/
def bucketRow (es:List Parse.Endpoint) (packet position:List Bool):List Bool:=
  SemiprimeD1StackChildGroupFactoryBucketRecord.row packet (View.records es packet position++[false])
    (SemiprimeD1StackPortOrdinalStream.result (View.portWords es packet position))
/-- Every observed packet, even an empty bucket or a repeated prepared packet, contributes one actual ordered row. -/
theorem result_factorHistory (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):
    result before es packet tail position (aux .factorHistory)=
      (bucketRow es packet position).reverse++before (aux .factorHistory):=by
  rw [result,CV.result_factorHistory,scanned,
    SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneView
