/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuterView
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsSeed
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCounterInput
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndexClear
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsScalar
/-! # Complete actual coefficient: paid counters, all descending pairs, scalar, two frames and drains -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficient
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryWeightsOuterView
open SemiprimeRationalBits (RationalWord zeroWord)
namespace Inner
export SemiprimeD1StackRecoveryWeightsInner (inner_run timeBound)
end Inner
namespace Spec
export SemiprimeD1StackRecoveryWeightsSpec (dotLoop weight)
end Spec
/-- Sum of the SAME actual setup, pair, cleanup, scalar and framing traces. -/
def timeBound (inverse powers:List RationalWord) (scalar:RationalWord) (j n:Nat) (width:List Bool) (out:List Bool):Nat:=
  let w:=outer inverse powers scalar (j+(n+1)) width j out
  let total:=Spec.dotLoop width inverse powers j (n+1) zeroWord
  2+SemiprimeD1StackRecoveryWeightsCounterInput.timeBound j n+
    Inner.timeBound w inverse powers width j (n+1) zeroWord+
    (j-1)+2+SemiprimeD1StackRecoveryWeightsScalar.timeBound (putReg w .acc total) scalar total width
/-- A complete coefficient is acquired from actual original inputs and current markers, without any supplied sum or index. -/
theorem coefficient_run (inverse powers:List RationalWord) (scalar:RationalWord) (j n:Nat) (width:List Bool) (out:List Bool):
    ∃time ≤ timeBound inverse powers scalar j n width out,
      Runs program time (.local (.seedZero false)) (bank (outer inverse powers scalar (j+(n+1)) width j out)) (.local .outer)
        (bank (outer inverse powers scalar (j+(n+1)) width j
          (SemiprimeD1StackNormalizedInverse.row (Spec.weight width (j+(n+1)) j scalar inverse powers) out))):=by
  let w:=outer inverse powers scalar (j+(n+1)) width j out
  let total:=Spec.dotLoop width inverse powers j (n+1) zeroWord
  have h0:=SemiprimeD1StackRecoveryWeightsSeed.seed_run w rfl rfl
  have h1:=SemiprimeD1StackRecoveryWeightsCounterInput.counters_run (putReg w .acc zeroWord) j n rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨m,hm,h2⟩:=Inner.inner_run w inverse powers width j (n+1) zeroWord rfl rfl rfl (fun _ _=>rfl) rfl rfl rfl rfl rfl
  have h3:=SemiprimeD1StackRecoveryWeightsIndexClear.clear_run (indexed w 0 0 (j-1) total)
  rw [SemiprimeD1StackRecoveryWeightsIndexClear.clear_indexed w j total rfl rfl rfl] at h3
  change Runs program ((unary 0).length+1+(unary (j-1)).length+1) _ _ _ _ at h3
  have he:∀r≠(.acc:I.Reg),∀den,(putReg w .acc total).registers (r,den)=[]:=by
    intro r hr den
    exact SemiprimeD1StackNormalizedInverseView.putReg_other w.toWords .acc r total den hr
  obtain ⟨s,hs,h4⟩:=SemiprimeD1StackRecoveryWeightsScalar.scalar_run (putReg w .acc total) scalar total width
    rfl rfl rfl rfl he rfl rfl rfl rfl
  have hend:SemiprimeD1StackRecoveryWeightsScalar.result (putReg w .acc total) scalar total width=
      outer inverse powers scalar (j+(n+1)) width j
        (SemiprimeD1StackNormalizedInverse.row (Spec.weight width (j+(n+1)) j scalar inverse powers) out):=by
    have hn:j+(n+1)-j=n+1:=by omega
    change {w with registers:=fun _=>[],auxiliary:=Function.update w.auxiliary .output (SemiprimeD1StackNormalizedInverse.row (SemiprimeD1StackRecoveryWeightsScalar.output scalar total width) out)}=_
    rw [show SemiprimeD1StackRecoveryWeightsScalar.output scalar total width=Spec.weight width (j+(n+1)) j scalar inverse powers by
      simp only [SemiprimeD1StackRecoveryWeightsScalar.output,Spec.weight,hn,total]]
    exact update_output inverse powers scalar (j+(n+1)) width j out _
  rw [hend] at h4
  have hh:=P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
  refine ⟨2+SemiprimeD1StackRecoveryWeightsCounterInput.timeBound j n+m+((j-1)+2)+s,?_,?_⟩
  · dsimp only [timeBound]
    dsimp only [w,total] at hm hs
    omega
  · convert hh using 1
    simp only [unary,List.length_replicate]
    omega
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficient
