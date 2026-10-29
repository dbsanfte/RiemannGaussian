/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOneView
/-! # Complete actual observed-packet loop, with chronological multiplicities
Every real packet record is parsed, even when its bucket is empty or its raw key
repeats. Real private banks are cleared before reusing the same actual sources.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace One
export SemiprimeD1StackChildGroupFactoryBucketOne (result timeBound source_trace)
end One
namespace View
export SemiprimeD1StackChildGroupFactoryBucketOneView
  (result_other result_packetReader result_endpointReader result_reuse result_ordinal result_clean result_position result_histories)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint cleanRoles records)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryBucketCleanup (role)
end Cleanup
namespace Reuse
export SemiprimeD1StackChildGroupFactoryBucketReuse (role)
end Reuse
namespace LV
export SemiprimeD1StackChildGroupFactoryBucketLoopView (finalPosition)
end LV
/-- Exact actual observed-packet EOF stop. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .packetReader) []
/-- Full repeated source bank, with a distinct fresh global counter spanning every bucket. -/
def result:List (List Bool)→(Stack→List Bool)→List Parse.Endpoint→List Bool→Stack→List Bool
  | [],before,_,_=>atEOF before
  | packet::packets,before,es,position=>result packets
      (One.result before es packet (vectorBits packets) position) es (LV.finalPosition es packet position)
/-- Only actual per-packet source caps and two real final EOF instructions are summed. -/
def timeBound:List (List Bool)→(Stack→List Bool)→List Parse.Endpoint→List Bool→Nat
  | [],_,_,_=>2
  | packet::packets,before,es,position=>One.timeBound before es packet (vectorBits packets) position+
      timeBound packets (One.result before es packet (vectorBits packets) position) es (LV.finalPosition es packet position)
/-- Real terminating FALSE pop followed by an actual EOF peek. -/
theorem eof_run (before:Stack→List Bool) (hr:before (aux .packetReader)=[false]):
    Runs program 2 (.local 6 18) before (.local 9 0) (atEOF before):=by
  have h0:=pop_run (.local 6 18) abort (.local 6 19) (.local 6 20) (aux .packetReader) before [false] rfl hr
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  have h1:=peek_run (.local 6 19) (.local 9 0) abort abort (aux .packetReader) (atEOF before) [] rfl
    (Function.update_self _ _ _)
  simp only [List.head?_nil,SemiprimeD1StackBytecode.choose] at h1
  exact join h0 h1
/-- Whole real packet traversal from actual tapes alone, preserving all115 roles and real returns. -/
theorem source_trace (packets:List (List Bool)) (before:Stack→List Bool) (es:List Parse.Endpoint) (position:List Bool)
    (ht:before (aux .packetReader)=vectorBits packets)
    (he:before (aux .endpoints)=Parse.records es) (her:before (aux .endpointReader)=[])
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hpk:before (aux .packetKey)=[]) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]) (ho:∀k,before (ordinal k)=[])
    (hbh:before (aux .bucketHistory)=[]) (hph:before (aux .portHistory)=[])
    (hj:before (aux .jointKey)=[]) (hpb:before (aux .portBank)=[]):
    ∃t≤timeBound packets before es position,
      Runs program t (.local 6 18) before (.local 9 0) (result packets before es position):=by
  induction packets generalizing before position with
  | nil=>exact ⟨2,le_rfl,eof_run before ht⟩
  | cons packet packets ih=>
    obtain ⟨x,hx,h0⟩:=One.source_trace before es packet (vectorBits packets) position ht he her hz hpk hpos hb hc ha ho hbh hph hj hpb
    let after:=One.result before es packet (vectorBits packets) position
    have ht':after (aux .packetReader)=vectorBits packets:=View.result_packetReader _ _ _ _ _
    have he':after (aux .endpoints)=Parse.records es:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
        (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans he
    have her':after (aux .endpointReader)=[]:=View.result_endpointReader _ _ _ _ _
    have hz':∀k∈Parse.cleanRoles,after k=[]:=View.result_clean _ _ _ _ _ hz
    have hpk':after (aux .packetKey)=[]:=View.result_reuse _ _ _ _ _ 0
    have hpos':after (aux .globalPosition)=LV.finalPosition es packet position:=View.result_position _ _ _ _ _ hpos
    have hb':after (aux .frameBuffer)=[]:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
        (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
    have hc':after (aux .copyScratch)=[]:=
      (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> decide)
        (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    have ha':∀k,after (arithmetic k)=[]:=by
      intro k
      exact (View.result_other _ _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,arithmetic,aux])
        (by intro j;fin_cases j <;> simp [Reuse.role,arithmetic,aux,ordinal])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])
        (by simp [arithmetic,aux]) (by simp [arithmetic,aux]) (by simp [arithmetic,aux])).trans (ha k)
    have ho':∀k,after (ordinal k)=[]:=View.result_ordinal _ _ _ _ _
    have hbh':after (aux .bucketHistory)=[]:=(View.result_histories _ _ _ _ _).1
    have hph':after (aux .portHistory)=[]:=(View.result_histories _ _ _ _ _).2
    have hj':after (aux .jointKey)=[]:=View.result_reuse _ _ _ _ _ 1
    have hpb':after (aux .portBank)=[]:=View.result_reuse _ _ _ _ _ 2
    obtain ⟨y,hy,h1⟩:=ih after (LV.finalPosition es packet position) ht' he' her' hz' hpk' hpos' hb' hc' ha' ho' hbh' hph' hj' hpb'
    refine ⟨x+y,?_,join h0 h1⟩
    dsimp only [timeBound]
    dsimp only [after] at hy
    omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoop
