/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
/-! # Whole actual unary original-port order acquisition for one old vertex
The retained original endpoint tape is really copied and every original port
is really parsed. Matching ports execute the entire first-index search. The
actual binary answers are then reversed, really converted to unary, logged and
all thirteen converter/work tapes cleared before the old vertex advances.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Loop
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (Fresh freshRole orderWords result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryOldPortsLoopView (result_fresh result_orderHistory result_other)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end Parse
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
namespace Early
export SemiprimeD1StackChildGroupFactoryTagEarlyClear (role)
end Early
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
namespace Convert
export SemiprimeD1StackChildGroupFactoryPortConvert (result timeBound source_trace)
end Convert
/-- Actual preserving copy of the retained complete original-port stream. -/
def copied (before:Stack→List Bool) (points:List Parse.Point):Stack→List Bool:=
  Function.update before (aux .oldReader) (Parse.records points)
/-- Actual complete original-port ordering-loop stop. -/
def scanned (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):Stack→List Bool:=
  Loop.result points (copied before points) buckets target
/-- Actual generated binary original-order vector at the real ordinal-converter entry. -/
def prepared (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):Stack→List Bool:=
  Function.update (Function.update (scanned before points buckets target) (aux .orderHistory) [])
    (aux .orderBank) (vectorBits (Loop.orderWords buckets points target))
/-- Complete actual unary-order row and workspace reuse boundary before incrementing the old vertex. -/
def result (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):Stack→List Bool:=
  Convert.result true (prepared before points buckets target) (Loop.orderWords buckets points target)
/-- Only own actual source/copy/query/reversal/ordinal/logger/cleanup clocks are summed. -/
def timeBound (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool):Nat:=
  (5*(Parse.records points).length+4)+Loop.timeBound points (copied before points) buckets target+
    1+(2*((Loop.orderWords buckets points target).flatMap Log.row).length+3)+
      Convert.timeBound true (prepared before points buckets target) (Loop.orderWords buckets points target)
/-- Whole actual original-port order acquisition, with no supplied order/index/permutation/clock or table answer. -/
theorem source_trace (before:Stack→List Bool) (points:List Parse.Point) (buckets:List Buckets.Bucket) (target:List Bool)
    (hp:before (aux .oldEndpoints)=Parse.records points) (hr:before (aux .oldReader)=[])
    (hs:before (aux .buckets)=Buckets.records buckets) (ht:before (aux .vertexKey)=target)
    (hf:Loop.Fresh before) (ha:∀k,before (arithmetic k)=[]) (hord:∀k,before (ordinal k)=[])
    (hh:before (aux .orderHistory)=[]) (hb:before (aux .orderBank)=[]):
    ∃t≤timeBound before points buckets target,
      Runs program t (.local 11 6) before (.local 14 29) (result before points buckets target):=by
  have h0:=copy_call 29 (.local 11 6) (.local 11 7) rfl before (Parse.records points) [] hp hr (hf 19)
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before points) at h0
  have hf':Loop.Fresh (copied before points):=by
    intro j
    have hn:Loop.freshRole j≠aux .oldReader:=by fin_cases j <;> decide
    exact (Function.update_of_ne hn _ _).trans (hf j)
  have h1:=Loop.source_trace points (copied before points) buckets target rfl
    (by simpa [copied,aux] using hs) (by simpa [copied,aux] using ht) hf'
    (by intro k;simpa [copied,aux,arithmetic] using ha k)
  change Runs program _ _ _ _ (scanned before points buckets target) at h1
  have hhist:scanned before points buckets target (aux .orderHistory)=
      ((Loop.orderWords buckets points target).flatMap Log.row).reverse:=by
    rw [scanned,View.result_orderHistory]
    simp only [aux] at hh
    simp [copied,aux,hh]
  have hbank:scanned before points buckets target (aux .orderBank)=[]:=by
    rw [scanned,View.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hb
  let seeded:=Function.update (scanned before points buckets target) (aux .orderBank) [false]
  have h2:=push_run (.local 14 9) (.local 14 10) (aux .orderBank) false (scanned before points buckets target) rfl
  rw [hbank] at h2
  have h3:=reverse_call 13 (.local 14 10) (.local 14 11) rfl seeded
    ((Loop.orderWords buckets points target).flatMap Log.row).reverse [false]
    (by simpa [seeded,aux,reverseStack,reversePorts] using hhist) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h3
  change Runs program _ _ seeded _ (Function.update (Function.update seeded (aux .orderHistory) [])
    (aux .orderBank) (((Loop.orderWords buckets points target).flatMap Log.row)++[false])) at h3
  have hv:((Loop.orderWords buckets points target).flatMap Log.row)++[false]=vectorBits (Loop.orderWords buckets points target):=
    SemiprimeD1StackChildGroupFactoryBucketScan.port_records_vector _
  rw [hv] at h3
  have he3:Function.update (Function.update seeded (aux .orderHistory) []) (aux .orderBank)
      (vectorBits (Loop.orderWords buckets points target))=prepared before points buckets target:=by
    dsimp only [seeded,prepared]
    rw [Function.update_comm (by decide:aux .orderBank≠aux .orderHistory),Function.update_idem]
  rw [he3] at h3
  have hpost:Loop.Fresh (scanned before points buckets target):=View.result_fresh _ _ _ _ hf'
  have hframe:prepared before points buckets target (aux .frameBuffer)=[]:=by
    change scanned before points buckets target (aux .frameBuffer)=[]
    exact hpost 18
  have hscratch:prepared before points buckets target (aux .copyScratch)=[]:=by
    change scanned before points buckets target (aux .copyScratch)=[]
    exact hpost 19
  have hord':∀k,prepared before points buckets target (ordinal k)=[]:=by
    intro k
    change scanned before points buckets target (ordinal k)=[]
    rw [scanned,View.result_other _ _ _ _ _ (by intro j;fin_cases j <;> simp [Early.role,ordinal,aux])
      (by simp [ordinal,aux]) (by simp [ordinal,aux]) (by simp [ordinal,aux])
      (by simp [ordinal,aux]) (by simp [ordinal,aux])]
    simpa [copied,aux,ordinal] using hord k
  obtain ⟨t,htime,h4⟩:=Convert.source_trace true (prepared before points buckets target) (Loop.orderWords buckets points target) rfl hord' hframe hscratch
  change Runs program t (.local 14 11) _ (.local 14 29) _ at h4
  refine ⟨(5*(Parse.records points).length+4)+Loop.timeBound points (copied before points) buckets target+
      1+(2*((Loop.orderWords buckets points target).flatMap Log.row).length+3)+t,?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 (join h3 h4)))
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsSource
