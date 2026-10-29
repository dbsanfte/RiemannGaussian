/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanView
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvert
/-! # Complete actual one-packet factory iteration
The observed packet is physically parsed, all acquired endpoints are scanned,
its empty or nonempty bucket is logged, the real ordinal converter runs, and
all fifteen packet/callee words are physically cleared before the next packet.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOne
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace SemiprimeD1StackChildGroupFactoryFields
namespace Scan
export SemiprimeD1StackChildGroupFactoryBucketScan (result timeBound source_trace)
end Scan
namespace SV
export SemiprimeD1StackChildGroupFactoryBucketScanView (result_children result_ports result_clean result_other)
end SV
namespace Parse
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint cleanRoles records)
end Parse
namespace View
export SemiprimeD1StackChildGroupFactoryBucketLoopView (records portWords)
end View
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryBucketCleanup (role)
end Cleanup
namespace Convert
export SemiprimeD1StackChildGroupFactoryBucketConvert (result timeBound source_trace)
end Convert
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual one-field packet parse bank. -/
def prepared (before:Stack→List Bool) (packet tail:List Bool):Stack→List Bool:=
  Function.update (Function.update before (aux .packetReader) tail) (aux .packetKey) packet
/-- Actual scanned bucket bank, with both ordered binary vectors physically present. -/
def scanned (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):Stack→List Bool:=
  Scan.result (prepared before packet tail) es packet position
/-- Full actual iteration result, with all private packet/converter words cleared. -/
def result (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):Stack→List Bool:=
  Convert.result (scanned before es packet tail position) packet (View.records es packet position++[false])
    (View.portWords es packet position)
/-- Every actual parse/copy/scan/reverse/conversion/logger/cleanup clock is retained. -/
def timeBound (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool):Nat:=
  1+(8*packet.length+8)+Scan.timeBound es packet position+
    Convert.timeBound (scanned before es packet tail position) packet (View.records es packet position++[false])
      (View.portWords es packet position)
/-- One COMPLETE actual loop iteration, including every observed empty bucket and every repeated prepared packet. -/
theorem source_trace (before:Stack→List Bool) (es:List Parse.Endpoint) (packet tail position:List Bool)
    (ht:before (aux .packetReader)=true::frame packet tail)
    (he:before (aux .endpoints)=Parse.records es) (her:before (aux .endpointReader)=[])
    (hz:∀k∈Parse.cleanRoles,before k=[])
    (hpk:before (aux .packetKey)=[]) (hpos:before (aux .globalPosition)=position)
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[])
    (ha:∀k,before (arithmetic k)=[]) (ho:∀k,before (ordinal k)=[])
    (hbh:before (aux .bucketHistory)=[]) (hph:before (aux .portHistory)=[])
    (hj:before (aux .jointKey)=[]) (hpb:before (aux .portBank)=[]):
    ∃t≤timeBound before es packet tail position,
      Runs program t (.local 6 18) before (.local 6 18) (result before es packet tail position):=by
  have h0:=pop_run (.local 6 18) abort (.local 6 19) (.local 6 20) (aux .packetReader) before
    (true::frame packet tail) rfl ht
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
  let b1:=Function.update before (aux .packetReader) (frame packet tail)
  have hscratch:=hz (field (.inl .scratch)) (by simp [Parse.cleanRoles])
  have hvalid:=hz (field (.inr ())) (by simp [Parse.cleanRoles])
  have h1:=field_read 10 (.local 6 20) (.local 6 21) (.local 6 22) abort abort rfl rfl b1 packet tail
    (Function.update_self _ _ _) (by simpa [b1,aux,fieldStack,fieldPorts] using hpk)
    (by simpa [b1,aux,field] using hscratch) (by simpa [b1,aux,field] using hvalid)
  change Runs program _ _ b1 _ (Function.update (Function.update b1 (aux .packetReader) tail) (aux .packetKey) packet) at h1
  have he1:Function.update (Function.update b1 (aux .packetReader) tail) (aux .packetKey) packet=prepared before packet tail:=by
    dsimp only [b1,prepared]
    rw [Function.update_idem]
  rw [he1] at h1
  have hz':∀k∈Parse.cleanRoles,prepared before packet tail k=[]:=by
    simpa [prepared,Parse.cleanRoles,aux,field] using hz
  have h2:=Scan.source_trace (prepared before packet tail) es packet position
    (by simpa [prepared,aux] using he) (by simpa [prepared,aux] using her) hz' rfl
    (by simpa [prepared,aux] using hpos) (by simpa [prepared,aux] using hb)
    (by simpa [prepared,aux] using hc) (by intro k;simpa [prepared,aux,arithmetic] using ha k)
    (by simpa [prepared,aux] using hbh) (by simpa [prepared,aux] using hph)
    (by simpa [prepared,aux] using hj) (by simpa [prepared,aux] using hpb)
  change Runs program _ _ _ _ (scanned before es packet tail position) at h2
  have hp':scanned before es packet tail position (aux .packetKey)=packet:=by
    rw [scanned,SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  have ho':∀k,scanned before es packet tail position (ordinal k)=[]:=by
    intro k
    rw [scanned,SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> simp [Cleanup.role,ordinal,aux])
      (by simp [ordinal,aux]) (by simp [ordinal,aux]) (by simp [ordinal,aux])
      (by simp [ordinal,aux]) (by simp [ordinal,aux]) (by simp [ordinal,aux])]
    simpa [prepared,aux,ordinal] using ho k
  have hr':scanned before es packet tail position (aux .rowBuffer)=[]:=
    SV.result_clean _ _ _ _ hz' _ (by simp [Parse.cleanRoles])
  have hb':scanned before es packet tail position (aux .frameBuffer)=[]:=by
    rw [scanned,SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [prepared,aux] using hb
  have hc':scanned before es packet tail position (aux .copyScratch)=[]:=by
    rw [scanned,SV.result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [prepared,aux] using hc
  obtain ⟨t,htime,h3⟩:=Convert.source_trace (scanned before es packet tail position) packet
    (View.records es packet position++[false]) (View.portWords es packet position) hp'
      (SV.result_children _ _ _ _) (SV.result_ports _ _ _ _) ho' hr' hb' hc'
  refine ⟨1+(8*packet.length+8)+Scan.timeBound es packet position+t,?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketOne
