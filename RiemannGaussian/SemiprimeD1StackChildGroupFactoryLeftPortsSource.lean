/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoopView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
/-! # Whole actual unary left-port acquisition for one old vertex
The real saved counter is erased, the retained actual bucket tape is copied,
the complete nested filter executes, and its actual generated port words are
really converted/logged/cleared before original-port order acquisition starts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSource
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Loop
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records portWords result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryLeftPortsLoopView (result_portHistory result_other)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Parse
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryChildCleanup (role)
end Cleanup
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
namespace Convert
export SemiprimeD1StackChildGroupFactoryPortConvert (result timeBound source_trace)
end Convert
/-- The actual old current-global metadata word is physically erased, never reused as an address answer. -/
def drained (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .globalPosition) []
/-- Actual preserving copy of the acquired bucket tape. -/
def copied (before:Stack→List Bool) (buckets:List Loop.Bucket):Stack→List Bool:=
  Function.update (drained before) (aux .outerReader) (Loop.records buckets)
/-- Complete actual nested-filter stop. -/
def filtered (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):Stack→List Bool:=
  Loop.result buckets (copied before buckets) target
/-- Actual generated binary left-port vector at the ordinal-converter entry. -/
def prepared (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):Stack→List Bool:=
  Function.update (Function.update (filtered before buckets target) (aux .portHistory) [])
    (aux .portBank) (vectorBits (Loop.portWords buckets target))
/-- Exact actual stop before original old-port/tag acquisition. -/
def result (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):Stack→List Bool:=
  Convert.result false (prepared before buckets target) (Loop.portWords buckets target)
/-- Own erase/copy/fullnestedfilter/reversal/converter/logger/reuse clock. -/
def timeBound (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool):Nat:=
  (before (aux .globalPosition)).length+1+(5*(Loop.records buckets).length+4)+Loop.timeBound buckets target+
    1+(2*((Loop.portWords buckets target).flatMap Log.row).length+3)+
      Convert.timeBound false (prepared before buckets target) (Loop.portWords buckets target)
/-- The complete actual left-port source uses only actual retained words, without supplied ports/order. -/
theorem source_trace (before:Stack→List Bool) (buckets:List Loop.Bucket) (target:List Bool)
    (hs:before (aux .buckets)=Loop.records buckets) (ho:before (aux .outerReader)=[])
    (hh:∀k∈Header.cleanRoles,before k=[])
    (hz:∀k∈Parse.cleanRoles,k≠aux .globalPosition→before k=[])
    (ht:before (aux .vertexKey)=target) (hb:before (aux .frameBuffer)=[])
    (hc:before (aux .copyScratch)=[]) (ha:∀k,before (arithmetic k)=[]) (hord:∀k,before (ordinal k)=[])
    (hph:before (aux .portHistory)=[]) (hpb:before (aux .portBank)=[]):
    ∃t≤timeBound before buckets target,
      Runs program t (.local 9 5) before (.local 11 6) (result before buckets target):=by
  have h0:=drain_loop (.local 9 5) (.local 9 6) (aux .globalPosition) rfl before (before (aux .globalPosition)) rfl
  change Runs program _ _ before _ (drained before) at h0
  have h1:=copy_call 26 (.local 9 6) (.local 9 7) rfl (drained before) (Loop.records buckets) []
    (by simpa [drained,aux,copyStack,copyPorts] using hs)
    (by simpa [drained,aux,copyStack,copyPorts] using ho)
    (by simpa [drained,aux,copyStack] using hc)
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ (copied before buckets) at h1
  have hz':∀k∈Parse.cleanRoles,drained before k=[]:=by
    intro k hk
    by_cases he:k=aux .globalPosition
    · subst k;exact Function.update_self _ _ _
    · exact (Function.update_of_ne he _ _).trans (hz k hk he)
  have h2:=Loop.source_trace buckets (copied before buckets) target rfl
    (by simpa [copied,drained,Header.cleanRoles,aux,field] using hh)
    (by simpa [copied,Parse.cleanRoles,aux,field] using hz')
    (by simpa [copied,drained,aux] using ht) (by simpa [copied,drained,aux] using hb)
    (by simpa [copied,drained,aux] using hc) (by intro k;simpa [copied,drained,aux,arithmetic] using ha k)
  change Runs program _ _ _ _ (filtered before buckets target) at h2
  have hhist:filtered before buckets target (aux .portHistory)=((Loop.portWords buckets target).flatMap Log.row).reverse:=by
    rw [filtered,View.result_portHistory]
    simp only [aux] at hph
    simp [copied,drained,aux,hph]
  have hbank:filtered before buckets target (aux .portBank)=[]:=by
    rw [filtered,View.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)]
    simpa [copied,drained,aux] using hpb
  let seeded:=Function.update (filtered before buckets target) (aux .portBank) [false]
  have h3:=push_run (.local 10 18) (.local 10 19) (aux .portBank) false (filtered before buckets target) rfl
  rw [hbank] at h3
  have h4:=reverse_call 8 (.local 10 19) (.local 10 20) rfl seeded
    ((Loop.portWords buckets target).flatMap Log.row).reverse [false]
    (by simpa [seeded,aux,reverseStack,reversePorts] using hhist) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h4
  change Runs program _ _ seeded _ (Function.update (Function.update seeded (aux .portHistory) [])
    (aux .portBank) (((Loop.portWords buckets target).flatMap Log.row)++[false])) at h4
  have hv:((Loop.portWords buckets target).flatMap Log.row)++[false]=vectorBits (Loop.portWords buckets target):=
    SemiprimeD1StackChildGroupFactoryBucketScan.port_records_vector _
  rw [hv] at h4
  have he4:Function.update (Function.update seeded (aux .portHistory) []) (aux .portBank)
      (vectorBits (Loop.portWords buckets target))=prepared before buckets target:=by
    dsimp only [seeded,prepared]
    rw [Function.update_comm (by decide:aux .portBank≠aux .portHistory),Function.update_idem]
  rw [he4] at h4
  have hb':prepared before buckets target (aux .frameBuffer)=[]:=by
    change filtered before buckets target (aux .frameBuffer)=[]
    rw [filtered,View.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)]
    simpa [copied,drained,aux] using hb
  have hc':prepared before buckets target (aux .copyScratch)=[]:=by
    change filtered before buckets target (aux .copyScratch)=[]
    rw [filtered,View.result_other _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide) (by decide)]
    simpa [copied,drained,aux] using hc
  have hord':∀k,prepared before buckets target (ordinal k)=[]:=by
    intro k
    change filtered before buckets target (ordinal k)=[]
    rw [filtered,View.result_other _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,ordinal,aux])
      (by simp [ordinal,aux]) (by simp [ordinal,aux]) (by simp [ordinal,aux])]
    simpa [copied,drained,aux,ordinal] using hord k
  obtain ⟨t,htime,h5⟩:=Convert.source_trace false (prepared before buckets target) (Loop.portWords buckets target) rfl hord' hb' hc'
  change Runs program t (.local 10 20) _ (.local 11 6) _ at h5
  refine ⟨(before (aux .globalPosition)).length+1+(5*(Loop.records buckets).length+4)+Loop.timeBound buckets target+
      1+(2*((Loop.portWords buckets target).flatMap Log.row).length+3)+t,?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 (join h3 (join h4 h5))))
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsSource
