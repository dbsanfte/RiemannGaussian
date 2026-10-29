/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoop
/-! # Exact entire chronological observed-packet output of the real loop
The fresh child-global counter spans all buckets; neither repeated prepared
packets nor observed zero-arity buckets are deleted or identified.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketsLoop
namespace OV
export SemiprimeD1StackChildGroupFactoryBucketOneView (result_other result_factorHistory bucketRow result_position)
end OV
/-- Exact ordered raw bucket-record stream, before its final FALSE. -/
def records:List (List Bool)→List Parse.Endpoint→List Bool→List Bool
  | [],_,_=>[]
  | packet::packets,es,position=>OV.bucketRow es packet position++records packets es (LV.finalPosition es packet position)
/-- Actual final fresh binary position after every observed packet. -/
def finalPosition:List (List Bool)→List Parse.Endpoint→List Bool→List Bool
  | [],_,position=>position
  | packet::packets,es,position=>finalPosition packets es (LV.finalPosition es packet position)
/-- All actual observed buckets are retained in exact input order. -/
theorem result_factorHistory (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool):
    result packets before es position (aux .factorHistory)=
      (records packets es position).reverse++before (aux .factorHistory):=by
  induction packets generalizing before position with
  | nil=>simp only [result,atEOF,records,List.reverse_nil,List.nil_append];rfl
  | cons packet packets ih=>
    rw [result,ih,OV.result_factorHistory]
    simp only [records,List.reverse_append,List.append_assoc]
/-- Entire actual scan leaves its observed-packet reader empty. -/
theorem result_packetReader (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool):
    result packets before es position (aux .packetReader)=[]:=by
  induction packets generalizing before position with
  | nil=>rfl
  | cons packet packets ih=>exact ih _ _
/-- The actual fresh counter has advanced once for every emitted child occurrence. -/
theorem result_position (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (hp:before (aux .globalPosition)=position):
    result packets before es position (aux .globalPosition)=finalPosition packets es position:=by
  induction packets generalizing before position with
  | nil=>simpa [result,atEOF,finalPosition,aux] using hp
  | cons packet packets ih=>exact ih _ _ (OV.result_position _ _ _ _ _ hp)
/-- All retained caller/cache bytes outside the exact actual work roles are unchanged. -/
theorem result_other (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hu:∀j,Reuse.role j≠k)
    (hpr:k≠aux .packetReader) (her:k≠aux .endpointReader) (hbh:k≠aux .bucketHistory)
    (hph:k≠aux .portHistory) (hpos:k≠aux .globalPosition) (hfh:k≠aux .factorHistory):
    result packets before es position k=before k:=by
  induction packets generalizing before position with
  | nil=>simp only [result,atEOF,Function.update_of_ne hpr]
  | cons packet packets ih=>rw [result,ih];exact OV.result_other _ _ _ _ _ _ hf hu hpr her hbh hph hpos hfh
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoopView
