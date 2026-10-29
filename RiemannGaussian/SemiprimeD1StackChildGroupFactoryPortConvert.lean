/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryCalls
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryWordLog
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortReuse
/-! # Actual unary left-port/original-order conversion, logging and complete reuse
Each fixed source family copies its actual binary metadata vector, runs the
real twelve-role converter, logs its real unary result, then drains all work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackChildGroupFactoryCalls SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace Ordinal
export SemiprimeD1StackPortOrdinalStream (initial result)
export SemiprimeD1StackPortOrdinalStreamExecution (done timeBound)
end Ordinal
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row wordRole historyRole timeBound source_trace)
end Log
namespace Reuse
export SemiprimeD1StackChildGroupFactoryPortReuse (bankRole pc result timeBound source_trace)
end Reuse
/-- The two fixed actual preserving-copy sites. -/
def copySite (ordering:Bool):Fin 38:=if ordering then 37 else 25
/-- The two fixed actual unary-tape loggers. -/
def logSite (ordering:Bool):Fin 4:=if ordering then 3 else 2
/-- Actual fixed copy, converter-call and logger entry sites. -/
def pc (ordering:Bool) (slot:Fin 3):Label:=if ordering then match slot.val with
  | 0=>.local 14 11 | 1=>.local 14 12 | _=>.local 14 13
else match slot.val with
  | 0=>.local 10 20 | 1=>.local 10 21 | _=>.local 10 22
/-- Actual paid converter operand. -/
def copied (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  Function.update before (ordinal .bank) (vectorBits words)
/-- Complete actual callee halt bank. -/
def converted (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  withOrdinal (copied before words) (Ordinal.done words).data
/-- Actual real unary-tape log row, before thirteen real workspace drains. -/
def logged (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  Function.update (converted before words) (Log.historyRole (logSite ordering))
    ((Log.row (Ordinal.result words)).reverse++converted before words (Log.historyRole (logSite ordering)))
/-- Complete actual cleaned caller boundary. -/
def result (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)):Stack→List Bool:=
  Reuse.result ordering (logged ordering before words)
/-- Value-sensitive own converter trace, all real logs and cleanup bytes are retained. -/
def timeBound (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool)):Nat:=
  (5*(vectorBits words).length+4)+(Ordinal.timeBound words+1)+Log.timeBound (Ordinal.result words)+
    Reuse.timeBound ordering (logged ordering before words)
/-- Actual ordinal conversion source at either fixed program site, with all115 tapes and real returns. -/
theorem source_trace (ordering:Bool) (before:Stack→List Bool) (words:List (List Bool))
    (hw:before (Reuse.bankRole ordering)=vectorBits words) (hz:∀k,before (ordinal k)=[])
    (hb:before (aux .frameBuffer)=[]) (hc:before (aux .copyScratch)=[]):
    ∃t≤timeBound ordering before words,
      Runs program t (pc ordering 0) before (Reuse.pc ordering 13) (result ordering before words):=by
  have h0a:=copy_call (copySite ordering) (pc ordering 0) (pc ordering 1) (by cases ordering <;> rfl)
    before (vectorBits words) [] (by cases ordering <;> exact hw) (by cases ordering <;> exact hz .bank) hc
  have h0:Runs program (5*(vectorBits words).length+4) (pc ordering 0) before (pc ordering 1) (copied before words):=by
    cases ordering <;> simpa [copied,copyStack,copyPorts,copySite] using h0a
  have hf:∀k,copied before words (ordinal k)=(Ordinal.initial (vectorBits words)).data k:=by
    intro k
    cases k <;> simp [copied,ordinal,Ordinal.initial]
    all_goals exact hz _
  obtain ⟨t,ht,h1⟩:=ordinal_call (pc ordering 1) (pc ordering 2) (by cases ordering <;> rfl)
    (copied before words) words hf
  change Runs program t _ _ _ (converted before words) at h1
  have hb':converted before words (aux .frameBuffer)=[]:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hb
  have hc':converted before words (aux .copyScratch)=[]:=by
    simpa [converted,copied,withOrdinal,ordinal,aux] using hc
  have h2a:=Log.source_trace (logSite ordering) (converted before words) (Ordinal.result words)
    (by cases ordering <;> rfl) hb' hc'
  have h2:Runs program (Log.timeBound (Ordinal.result words)) (pc ordering 2) (converted before words)
      (Reuse.pc ordering 0) (logged ordering before words):=by cases ordering <;> exact h2a
  have h3:=Reuse.source_trace ordering (logged ordering before words)
  refine ⟨(5*(vectorBits words).length+4)+t+Log.timeBound (Ordinal.result words)+Reuse.timeBound ordering (logged ordering before words),?_,?_⟩
  · dsimp only [timeBound]
    omega
  · have hwhole:=join h0 (join h1 (join h2 h3))
    simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryPortConvert
