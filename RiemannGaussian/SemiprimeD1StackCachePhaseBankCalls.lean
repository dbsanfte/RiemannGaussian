/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseBankPrimitives
import RiemannGaussian.SemiprimeD1StackCachePhaseBankStopped
/-! # ONE actual cached-phase source call per actual issued reference
The actual frozen restore+guard supplies accepted/rejected behavior. No branch
flag, q, rank, precision, output or evaluator is a caller input instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankCalls
open SemiprimeD1StackCachePhaseBank SemiprimeD1StackCachePhaseBankState
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackJetFoldWords (Modes)
namespace O
export SemiprimeD1StackCachePhaseRootOriginal (rootSource rootDone root_source_run rootDone_halted rootSize)
end O
/-- A full actual callee-bank replacement retains ALL8 actual outer words. -/
theorem whole_data_rel (before after:P.Stack→List Bool) (w:Aux→List Bool):
    SemiprimeD1StackMultiplierLink.DataRel cached (data before w) after (data after w):=by
  constructor
  · intro k;rfl
  · intro k hk
    rcases k with k|k
    · exact False.elim (hk k rfl)
    · rfl
/-- Own actual whole frozen source cap, plus its genuine outer call/return. -/
def callBound (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length) (modes:Modes):Nat:=
  10^80*(O.rootSize bits i modes+1)^16+1
/-- Real per-issued-phase call; accepted/rejected choice follows the actual restored original guard. -/
theorem original_call (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length)
    (modes:Modes) (w:Aux→List Bool):
    ∃t ≤callBound bits i modes,Runs program t (.local .phase) (data (O.rootSource bits i modes).data w)
      (.local .frame) (data (O.rootDone bits i modes).data w):=by
  obtain ⟨t,ht,hr⟩:=O.root_source_run bits i modes
  have hh:=O.rootDone_halted bits i modes
  have hp:(O.rootDone bits i modes).pc=none:=congrArg (fun q:C.State P.Stack P.Label=>q.pc) hh
  have hf:(O.rootDone bits i modes).frames=[]:=congrArg (fun q:C.State P.Stack P.Label=>q.frames) hh
  have h0:=SemiprimeD1StackProcedureCallsTrace.included_call program cached Label.phase cached_injective P.program
    (.local .start) (fun _=>rfl) (.local .phase) (.local .frame) rfl t
    (O.rootSource bits i modes) (O.rootDone bits i modes) _ _ rfl rfl hp hf hr
    (whole_data_rel _ _ w) (whole_data_rel _ _ w)
  exact ⟨t+1,Nat.add_le_add_right ht 1,h0⟩
/-- Borrowing the real shared copy scratch AFTER the source is justified by the actual stopped result. -/
theorem after_call_scratch (bits:List Bool) (i:Fin (SemiprimeD1StackRootPhaseParametersEncoding.phases bits).length)
    (modes:Modes) (w:Aux→List Bool):data (O.rootDone bits i modes).data w scratch=[]:=
  SemiprimeD1StackCachePhaseBankStopped.original_scratch bits i modes
end RiemannGaussian.SemiprimeD1StackCachePhaseBankCalls
