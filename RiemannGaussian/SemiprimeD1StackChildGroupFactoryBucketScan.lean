/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketLoopView
/-! # Complete actual endpoint copy, packet scan and both ordered log reversals
The generated binary port tape is proved to be exactly the real converter's
vector input. Its later unary conversion is charged separately, by actual values.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Loop
export SemiprimeD1StackChildGroupFactoryBucketLoop (result timeBound source_trace)
end Loop
namespace View
export SemiprimeD1StackChildGroupFactoryBucketLoopView
  (selected records portWords portRecords result_bucketHistory result_portHistory result_other)
end View
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint records cleanRoles)
end Parse
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryBucketCleanup (role)
end Cleanup
/-- Exact physical reversals from histories to two FALSE-terminated ordered vectors. -/
def reversed (before:Stack→List Bool) (children ports:List Bool):Stack→List Bool:=
  Function.update (Function.update (Function.update (Function.update before
    (aux .bucketHistory) []) (aux .jointKey) (children++[false]))
      (aux .portHistory) []) (aux .portBank) (ports++[false])
/-- Every seed, reversal byte and real return of the two actual logs. -/
def reverseTime (children ports:List Bool):Nat:=1+(2*children.length+3)+1+(2*ports.length+3)
/-- The literal two seed-and-reverse sequences. -/
theorem reverse_trace (before:Stack→List Bool) (children ports:List Bool)
    (hh:before (aux .bucketHistory)=children.reverse) (hp:before (aux .portHistory)=ports.reverse)
    (hj:before (aux .jointKey)=[]) (hb:before (aux .portBank)=[]):
    Runs program (reverseTime children ports) (.local 8 4) before (.local 8 8) (reversed before children ports):=by
  let b1:=Function.update before (aux .jointKey) [false]
  have h0:=push_run (.local 8 4) (.local 8 5) (aux .jointKey) false before rfl
  rw [hj] at h0
  have h1:=reverse_call 7 (.local 8 5) (.local 8 6) rfl b1 children.reverse [false]
    (by simpa [b1,aux,reverseStack,reversePorts] using hh) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h1
  change Runs program _ _ b1 _ (Function.update (Function.update b1 (aux .bucketHistory) [])
    (aux .jointKey) (children++[false])) at h1
  let b2:=Function.update (Function.update before (aux .bucketHistory) []) (aux .jointKey) (children++[false])
  have he:Function.update (Function.update b1 (aux .bucketHistory) []) (aux .jointKey) (children++[false])=b2:=by
    dsimp only [b1,b2]
    rw [Function.update_comm (by decide:aux .jointKey≠aux .bucketHistory),Function.update_idem]
  rw [he] at h1
  let b3:=Function.update b2 (aux .portBank) [false]
  have hb2:b2 (aux .portBank)=[]:=by simpa [b2,aux] using hb
  have h2:=push_run (.local 8 6) (.local 8 7) (aux .portBank) false b2 rfl
  rw [hb2] at h2
  have h3:=reverse_call 8 (.local 8 7) (.local 8 8) rfl b3 ports.reverse [false]
    (by simpa [b3,b2,aux,reverseStack,reversePorts] using hp) (Function.update_self _ _ _)
  simp only [List.length_reverse,List.reverse_reverse] at h3
  change Runs program _ _ b3 _ (Function.update (Function.update b3 (aux .portHistory) [])
    (aux .portBank) (ports++[false])) at h3
  have he3:Function.update (Function.update b3 (aux .portHistory) []) (aux .portBank) (ports++[false])=
      reversed before children ports:=by
    dsimp only [b3,b2,reversed]
    rw [Function.update_comm (by decide:aux .portBank≠aux .portHistory),Function.update_idem]
  rw [he3] at h3
  have hwhole:=join h0 (join h1 (join h2 h3))
  simpa only [reverseTime,Nat.add_assoc] using hwhole
/-- Actual preserved endpoint source copy, never a supplied filtered bucket. -/
def copied (before:Stack→List Bool) (es:List Parse.Endpoint):Stack→List Bool:=
  Function.update before (aux .endpointReader) (Parse.records es)
/-- Full physical bank at the actual ordinal-converter copy site. -/
def result (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool):Stack→List Bool:=
  reversed (Loop.result es (copied before es) packet position)
    (View.records es packet position) (View.portRecords es packet position)
/-- Copy, complete actual EOF-controlled scan, and both real reversals. -/
def timeBound (es:List Parse.Endpoint) (packet position:List Bool):Nat:=
  (5*(Parse.records es).length+4)+Loop.timeBound es packet position+
    reverseTime (View.records es packet position) (View.portRecords es packet position)
/-- Entire actual scan and ordered vectors, preserving the actual cached original endpoint source. -/
theorem source_trace (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool)
    (he:before (aux .endpoints)=Parse.records es) (hr:before (aux .endpointReader)=[])
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hp:before (aux .packetKey)=packet) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[])
    (hbh:before (aux .bucketHistory)=[]) (hph:before (aux .portHistory)=[])
    (hj:before (aux .jointKey)=[]) (hpb:before (aux .portBank)=[]):
    Runs program (timeBound es packet position) (.local 6 22) before (.local 8 8) (result before es packet position):=by
  have h0:=copy_call 20 (.local 6 22) (.local 6 23) rfl before (Parse.records es) [] he hr hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before es) at h0
  have h1:=Loop.source_trace es (copied before es) packet position rfl
    (by simpa [copied,Parse.cleanRoles,aux,field] using hz)
    (by simpa [copied,aux] using hp) (by simpa [copied,aux] using hpos)
    (by simpa [copied,aux] using hb) (by simpa [copied,aux] using hc)
    (by intro k;simpa [copied,aux,arithmetic] using ha k)
  let out:=Loop.result es (copied before es) packet position
  have hh:out (aux .bucketHistory)=(View.records es packet position).reverse:=by
    dsimp only [out]
    rw [View.result_bucketHistory]
    simp only [aux] at hbh
    simp [copied,aux,hbh]
  have hports:out (aux .portHistory)=(View.portRecords es packet position).reverse:=by
    dsimp only [out]
    rw [View.result_portHistory]
    simp only [aux] at hph
    simp [copied,aux,hph]
  have hj':out (aux .jointKey)=[]:=by
    dsimp only [out]
    rw [View.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hj
  have hpb':out (aux .portBank)=[]:=by
    dsimp only [out]
    rw [View.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide)]
    simpa [copied,aux] using hpb
  have h2:=reverse_trace out (View.records es packet position) (View.portRecords es packet position) hh hports hj' hpb'
  have hwhole:=join h0 (join h1 h2)
  simpa only [timeBound,result,Nat.add_assoc] using hwhole
/-- The binary port logger is exactly the actual vector input to the real converter. -/
theorem port_records_vector (words:List (List Bool)):
    (words.flatMap SemiprimeD1StackChildGroupFactoryBucketEmit.portRow)++[false]=
      SemiprimeD1TensorTapeCodec.vectorBits words:=by
  induction words with
  | nil=>rfl
  | cons w ws ih=>
    simpa only [List.flatMap_cons,List.append_assoc,SemiprimeD1StackChildGroupFactoryBucketEmit.portRow,
      List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append,
      SemiprimeD1TensorTapeCodec.vectorBits] using congrArg (fun tail=>true::SemiprimeSourceHistogramKeyBits.frame w tail) ih
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
