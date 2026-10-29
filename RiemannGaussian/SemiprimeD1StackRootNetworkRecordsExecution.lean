/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsAcquisition
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsJoin

/-! # Whole same-program original-N root-network record acquisition
All source calls, original input/prefix copies, both output copies, marker
removal, byte reversals and the actual final halt share this one own clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsExecution
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsPrimitives
open SemiprimeD1StackRootNetworkRecordsAcquisition SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual acquired factor output; this projection is mathematical notation only. -/
def factorTape (bits:List Bool) : List Bool :=(F.done bits).data F.output
/-- Actual acquired owner payload before its sole terminal false marker. -/
def ownerBytes (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) : List Bool :=
  SemiprimeD1StackOwnerRecordsLoop.bytes
    (SemiprimeD1StackOwnerRecordsOriginal.originalRows (bitValue bits) hN)
    (SemiprimeD1StackOwnerRecordsOriginal.prefixRows (bitValue bits) fixed)
/-- The real owner source always supplies exactly the final marker the join removes. -/
theorem owner_output (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (O.done bits hN fixed tail).data O.output=ownerBytes bits hN fixed++[false] :=rfl
/-- The factor source's actual output is retained literally through all later byte operations. -/
theorem factor_output (bits:List Bool) : (F.done bits).data F.output=factorTape bits :=rfl
/-- Whole actual stopped payload retains both sources and the original input/prefix. -/
def result (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) : Stack→List Bool :=work (F.done bits).data (O.done bits hN fixed tail).data bits
      (prescription bits fixed tail) [] [] (ownerBytes bits hN fixed++factorTape bits)
/-- Genuine clean halt after both actual full sources and the actual owner/factor byte join. -/
def done (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) : C.State Stack Label :=⟨none,none,none,result bits hN fixed tail,[]⟩
/-- Own full caller-prefix clock, not a transported native root-network report. -/
def timeBound (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) : Nat :=O.budget bits hN fixed tail+F.timeBound bits+10*bits.length+
      5*(prescription bits fixed tail).length+5*(factorTape bits).length+9*(ownerBytes bits hN fixed).length+37
attribute [local irreducible] factorTape ownerBytes
/-- One trace contains both true acquisitions and every actual joining step up to the final halt. -/
theorem source_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃t,t+1 ≤ timeBound bits hN fixed tail ∧ Runs program t (ctl .main)
      (initialPrefix bits (prescription bits fixed tail)).data (ctl .done) (result bits hN fixed tail) := by
  obtain ⟨a,ha,h0⟩:=acquire_trace bits hc hN fixed tail
  have h1:=SemiprimeD1StackRootNetworkRecordsJoin.join_trace (F.done bits).data (O.done bits hN fixed tail).data
    bits (prescription bits fixed tail) (ownerBytes bits hN fixed) (factorTape bits)
    (owner_output bits hN fixed tail) (factor_output bits)
  refine ⟨a+(5*(factorTape bits).length+9*(ownerBytes bits hN fixed).length+22),?_,join h0 h1⟩
  unfold timeBound
  omega
/-- Whole actual caller-prefix source execution, including all returns and final halt. -/
theorem source_run_prefix (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃t ≤ timeBound bits hN fixed tail,SemiprimeD1StackCalls.run program t
      (initialPrefix bits (prescription bits fixed tail))=some (done bits hN fixed tail) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN fixed tail
  obtain ⟨finish,hf,hs⟩:=h [] (initialPrefix bits (prescription bits fixed tail)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN fixed tail) [] finish hs
  refine ⟨t+1,ht,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Standard entry starts from N alone and physically seeds its own empty prefix. -/
theorem source_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ timeBound bits hN [] []+1,SemiprimeD1StackCalls.run program t (initial bits)=
      some (done bits hN [] []) := by
  obtain ⟨t,ht,h⟩:=source_trace bits hc hN [] []
  rw [prescription_empty] at h
  have h0:=seed_run bits
  have h1:=join h0 h
  obtain ⟨finish,hf,hs⟩:=h1 [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits hN [] []) [] finish hs
  refine ⟨(1+t)+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Every actual factor-source cell is retained through both output copies and the byte join. -/
theorem factor_preserved (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) (k:F.Stack) : result bits hN fixed tail (factorStack k)=(F.done bits).data k :=rfl
/-- Every actual owner-source cell is retained, including its actual prescribed-prefix data. -/
theorem owner_preserved (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) (k:O.Stack) : result bits hN fixed tail (ownerStack k)=(O.done bits hN fixed tail).data k :=rfl
/-- The standard and caller-prefix programs both retain the exact original binary N. -/
theorem input_preserved (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    result bits hN fixed tail originalInput=bits :=rfl
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsExecution
