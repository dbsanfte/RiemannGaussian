/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsView
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsPrimitives
/-! # Reused concrete physical read/arithmetic fragments, actual calls/returns and flag pops
The immutable power tape is an arbitrary retained field of the helper bank.
Both original scalar words are foreign to every included helper instruction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackRecoveryWeightsPrimitives (join push_run pop_run drain_loop copy_call frame_call)
end P
namespace H
export SemiprimeD1StackNormalizedInverseReadBuffers (success)
export SemiprimeD1StackNormalizedInverseView (store getReg signed_getReg)
end H
/-- Concrete included helper execution retains both acquired scalar words and all actual caller returns. -/
theorem fragment_call (entry stopped:I.Label) (pc next:Label) (time:Nat) (w:Words) (after:Old.Words)
    (hc:program pc=.call (.helper entry) next) (hret:I.program stopped=.ret)
    (hr:Runs I.program time entry (Old.store w.toWords) stopped (Old.store after)):
    Runs program (time+2) pc (bank w) next (bank (replace w after)):=by
  apply SemiprimeD1StackRecoveryWeightsIncluded.called_fragment program helper Label.helper Sum.inl_injective
    I.program entry stopped (fun _=>rfl) pc next hc time _ _ _ _ hret hr
  · exact ⟨fun _=>rfl,fun _ _=>rfl⟩
  · constructor
    · intro slot;rfl
    · intro slot hk;rcases slot with slot|slot
      · exact (hk slot rfl).elim
      · rfl
/-- Actual TRUE marker consumption restores the caller's originally empty validity word. -/
theorem clear_success (w:Words) (after:Old.Words) (hv:after.auxiliary .valid=[]):
    Function.update (bank (replace w (H.success after))) (aux .valid) []=bank (replace w after):=by
  rw [show aux .valid=helper (SemiprimeD1StackNormalizedInverse.aux .valid) from rfl,update_helper,
    SemiprimeD1StackNormalizedInverseView.update_aux]
  change Sum.elim (Old.store {after with auxiliary:=Function.update (Function.update after.auxiliary .valid [true]) .valid []}) w.scalarInputs=_
  rw [Function.update_idem,←hv,Function.update_eq_self]
  rfl
/-- Physical complete zero-extended array read, including BOTH copies/parsers/drains, actual call/return and TRUE pop. -/
theorem read_call (part:I.ReadSite) (pc checked next:Label)
    (hc:program pc=.call (.helper (.read part .copyArray)) checked)
    (hp:program checked=.base (.pop (aux .valid) abort abort next))
    (w:Words) (words:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (ha:Old.store w.toWords (SemiprimeD1StackNormalizedInverse.readSource part)=SemiprimeD1StackNormalizedInverse.tape words)
    (hi:Old.store w.toWords (SemiprimeD1StackNormalizedInverse.readIndex part)=List.replicate n true)
    (hr:w.auxiliary .reader=[]) (ht:w.auxiliary .readTodo=[])
    (hn:w.registers (SemiprimeD1StackNormalizedInverse.readReg part,false)=[])
    (hd:w.registers (SemiprimeD1StackNormalizedInverse.readReg part,true)=[])
    (hs:w.auxiliary .fieldFrameScratch=[]) (hv:w.auxiliary .valid=[]) (hcopy:w.auxiliary .copyScratch=[]):
    Runs program (SemiprimeD1StackNormalizedInverseReadCall.helperTime words n+3) pc (bank w) next
      (bank (replace w (Old.putReg w.toWords (SemiprimeD1StackNormalizedInverse.readReg part)
        (SemiprimeD1StackNormalizedInverseSpec.readWord words n)))):=by
  let after:=Old.putReg w.toWords (SemiprimeD1StackNormalizedInverse.readReg part)
    (SemiprimeD1StackNormalizedInverseSpec.readWord words n)
  have hh:=SemiprimeD1StackNormalizedInverseReadCall.helper_run part w.toWords words n ha hi hr ht hn hd hs hv hcopy
  have h0:=fragment_call (.read part .copyArray) (.read part .return) pc checked _ w (H.success after) hc rfl hh
  have h1:=P.pop_run checked abort abort next (aux .valid) (bank (replace w (H.success after))) [true] hp rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  rw [clear_success w after hv] at h1
  simpa only [Nat.add_assoc] using P.join h0 h1
/-- Actual complete normalized/twice-fitted operation endpoint, preserving all foreign input tapes. -/
def afterOperation (site:SemiprimeD1StackNormalizedInverse.Site) (w:Words) (width:List Bool):Words:=
  replace w (SemiprimeD1StackNormalizedInverseOperationCall.after site w.toWords width)
/-- Each actual multiply/add includes ALL4 operand copies before aliased erase, fullR36, sign acquisition, ALL35 drains, call/ret/TRUEpop. -/
theorem operation_call (site:SemiprimeD1StackNormalizedInverse.Site) (pc checked next:Label)
    (hc:program pc=.call (.helper (.operation site (.copyInput false false))) checked)
    (hp:program checked=.base (.pop (aux .valid) abort abort next))
    (w:Words) (width:List Bool) (hr:w.rational=Old.emptyRational width)
    (hs:w.auxiliary .copyScratch=[]) (hv:w.auxiliary .valid=[])
    (hx:w.registers (SemiprimeD1StackNormalizedInverse.operand site false,false)≠[])
    (hy:w.registers (SemiprimeD1StackNormalizedInverse.operand site true,false)≠[]):
    ∃time ≤ SemiprimeD1StackNormalizedInverseOperationCall.callBound site w.toWords width,
      Runs program time pc (bank w) next (bank (afterOperation site w width)):=by
  let x:=H.getReg w.toWords (SemiprimeD1StackNormalizedInverse.operand site false)
  let y:=H.getReg w.toWords (SemiprimeD1StackNormalizedInverse.operand site true)
  have hls:=H.signed_getReg w.toWords (SemiprimeD1StackNormalizedInverse.operand site false) hx
  have hrs:=H.signed_getReg w.toWords (SemiprimeD1StackNormalizedInverse.operand site true) hy
  obtain ⟨time,ht,hh⟩:=SemiprimeD1StackNormalizedInverseOperation.operation_run site w.toWords
    x.numerator.negative x.numerator.magnitude x.denominator y.numerator.negative y.numerator.magnitude y.denominator width
    hr hs hv hls rfl hrs rfl
  rw [SemiprimeD1StackNormalizedInverseOperationOutput.word_legacy] at hh
  let after:=SemiprimeD1StackNormalizedInverseOperationCall.after site w.toWords width
  change Runs I.program time _ _ _ (Old.store (H.success after)) at hh
  have h0:=fragment_call (.operation site (.copyInput false false)) (.operation site .return) pc checked time w (H.success after) hc rfl hh
  have h1:=P.pop_run checked abort abort next (aux .valid) (bank (replace w (H.success after))) [true] hp rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  rw [clear_success w after hv] at h1
  refine ⟨time+2+1,?_,P.join h0 h1⟩
  change time+2+1 ≤ SemiprimeD1StackNormalizedInverseOperation.timeBound site w.toWords x.numerator.negative
    x.numerator.magnitude x.denominator y.numerator.negative y.numerator.magnitude y.denominator width+3
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsCalls
