/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsLoopView
/-! # Entire actual packet-bucket catalogue source
One paid copy of the retained actual observed-packet vector drives the entire
real loop. One final FALSE seed and consuming reversal emits exact ordered
bucket records, including empty observed factors and repeated prepared keys.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Loop
export SemiprimeD1StackChildGroupFactoryBucketsLoop (result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryBucketsLoopView (records result_other result_factorHistory)
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
/-- Actual retained source-vector copy, with no packet count or bucket supplied. -/
def copied (before:Stack→List Bool) (packets:List (List Bool)):Stack→List Bool:=
  Function.update before (aux .packetReader) (vectorBits packets)
/-- Full actual stopped bank before acquiring all old vertices' ports and order. -/
def result (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool):Stack→List Bool:=
  let out:=Loop.result packets (copied before packets) es position
  Function.update (Function.update out (aux .factorHistory) []) (aux .buckets) (View.records packets es position++[false])
/-- All actual acquisition, ordinal conversion, logging, reuse and final reversal are included. -/
def timeBound (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool):Nat:=
  (5*(vectorBits packets).length+4)+Loop.timeBound packets (copied before packets) es position+
    1+(2*(View.records packets es position).length+3)
/-- The whole literal bucket acquisition, from retained actual source words to its real next continuation. -/
theorem source_trace (before:Stack→List Bool) (packets:List (List Bool)) (es:List Parse.Endpoint) (position:List Bool)
    (ht:before (aux .packets)=vectorBits packets) (hpr:before (aux .packetReader)=[])
    (he:before (aux .endpoints)=Parse.records es) (her:before (aux .endpointReader)=[])
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hpk:before (aux .packetKey)=[]) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]) (ho:∀k,before (ordinal k)=[])
    (hbh:before (aux .bucketHistory)=[]) (hph:before (aux .portHistory)=[])
    (hj:before (aux .jointKey)=[]) (hpb:before (aux .portBank)=[])
    (hfh:before (aux .factorHistory)=[]) (hbo:before (aux .buckets)=[]):
    ∃t≤timeBound before packets es position,
      Runs program t (.local 6 17) before (.local 9 2) (result before packets es position):=by
  have h0:=copy_call 19 (.local 6 17) (.local 6 18) rfl before (vectorBits packets) [] ht hpr hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before packets) at h0
  obtain ⟨x,hx,h1⟩:=Loop.source_trace packets (copied before packets) es position rfl
    (by simpa [copied,aux] using he) (by simpa [copied,aux] using her)
    (by simpa [copied,Parse.cleanRoles,aux,field] using hz)
    (by simpa [copied,aux] using hpk) (by simpa [copied,aux] using hpos)
    (by simpa [copied,aux] using hb) (by simpa [copied,aux] using hc)
    (by intro k;simpa [copied,aux,arithmetic] using ha k)
    (by intro k;simpa [copied,aux,ordinal] using ho k)
    (by simpa [copied,aux] using hbh) (by simpa [copied,aux] using hph)
    (by simpa [copied,aux] using hj) (by simpa [copied,aux] using hpb)
  let out:=Loop.result packets (copied before packets) es position
  have hh:out (aux .factorHistory)=(View.records packets es position).reverse:=by
    dsimp only [out]
    rw [View.result_factorHistory]
    simp only [aux] at hfh
    simp [copied,aux,hfh]
  have hb':out (aux .buckets)=[]:=by
    dsimp only [out]
    rw [View.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hbo
  let seeded:=Function.update out (aux .buckets) [false]
  have h2:=push_run (.local 9 0) (.local 9 1) (aux .buckets) false out rfl
  rw [hb'] at h2
  have h3:=reverse_call 10 (.local 9 1) (.local 9 2) rfl seeded (View.records packets es position).reverse [false]
    (by simpa [seeded,aux,reverseStack,reversePorts] using hh) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h3
  change Runs program _ _ seeded _ (Function.update (Function.update seeded (aux .factorHistory) [])
    (aux .buckets) (View.records packets es position++[false])) at h3
  have heq:Function.update (Function.update seeded (aux .factorHistory) []) (aux .buckets)
      (View.records packets es position++[false])=result before packets es position:=by
    dsimp only [seeded,result,out]
    rw [Function.update_comm (by decide:aux .buckets≠aux .factorHistory),Function.update_idem]
  rw [heq] at h3
  refine ⟨(5*(vectorBits packets).length+4)+x+1+(2*(View.records packets es position).length+3),?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketsSource
