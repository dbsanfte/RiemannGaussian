/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketRecord
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketReuse
/-! # Real ordinal conversion, whole-bucket logging and complete reuse
Only the actually generated binary port vector is copied to the real twelve-role
converter. Its value-sensitive trace and every callee cleanup byte are paid.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvert
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Ordinal
export SemiprimeD1StackPortOrdinalStream (initial result)
export SemiprimeD1StackPortOrdinalStreamExecution (done timeBound)
end Ordinal
namespace Record
export SemiprimeD1StackChildGroupFactoryBucketRecord (row timeBound source_trace)
end Record
namespace Reuse
export SemiprimeD1StackChildGroupFactoryBucketReuse (result timeBound source_trace)
end Reuse
/-- Actual converter operand is the paid copy of the actual fresh-ID bank. -/
def copied (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  Function.update before (ordinal .bank) (vectorBits words)
/-- Complete retained115-word bank after the actual ordinal source. -/
def converted (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  withOrdinal (copied before words) (Ordinal.done words).data
/-- Actual entire bucket log in the real factor history, including empty buckets. -/
def logged (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)):Stack→List Bool:=
  Function.update (converted before words) (aux .factorHistory)
    ((Record.row packet children (Ordinal.result words)).reverse++converted before words (aux .factorHistory))
/-- Complete physical reuse boundary before the next observed packet. -/
def result (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)):Stack→List Bool:=
  Reuse.result (logged before packet children words)
/-- Same actual converter clock, preserving copy, bucket logger and fifteen physical drains. -/
def timeBound (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool)):Nat:=
  (5*(vectorBits words).length+4)+(Ordinal.timeBound words+1)+
    Record.timeBound packet children (Ordinal.result words)+Reuse.timeBound (logged before packet children words)
/-- No supplied unary answer: the real ordinal converter consumes the generated binary vector. -/
theorem source_trace (before:Stack→List Bool) (packet children:List Bool) (words:List (List Bool))
    (hp:before (aux .packetKey)=packet) (hj:before (aux .jointKey)=children)
    (hw:before (aux .portBank)=vectorBits words) (hz:∀k,before (ordinal k)=[])
    (hr:before (aux .rowBuffer)=[]) (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    ∃t≤timeBound before packet children words,
      Runs program t (.local 8 8) before (.local 6 18) (result before packet children words):=by
  have h0:=copy_call 25 (.local 8 8) (.local 8 9) rfl before (vectorBits words) []
    hw (hz .bank) hc
  simp only [List.append_nil] at h0
  change Runs program _ _ before _ (copied before words) at h0
  have hf:∀k,copied before words (ordinal k)=(Ordinal.initial (vectorBits words)).data k:=by
    intro k
    cases k <;> simp [copied,ordinal,Ordinal.initial]
    all_goals exact hz _
  obtain ⟨t,ht,h1⟩:=ordinal_call (.local 8 9) (.local 8 10) rfl (copied before words) words hf
  change Runs program t _ _ _ (converted before words) at h1
  have hp':converted before words (aux .packetKey)=packet:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hp
  have hj':converted before words (aux .jointKey)=children:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hj
  have hr':converted before words (aux .rowBuffer)=[]:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hr
  have hb':converted before words (aux .frameBuffer)=[]:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hb
  have hc':converted before words (aux .copyScratch)=[]:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hc
  have h2:=Record.source_trace (converted before words) packet children (Ordinal.result words) hp' hj' rfl hr' hb' hc'
  change Runs program _ _ _ _ (logged before packet children words) at h2
  have h3:=Reuse.source_trace (logged before packet children words)
  refine ⟨(5*(vectorBits words).length+4)+t+Record.timeBound packet children (Ordinal.result words)+
      Reuse.timeBound (logged before packet children words),?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketConvert
