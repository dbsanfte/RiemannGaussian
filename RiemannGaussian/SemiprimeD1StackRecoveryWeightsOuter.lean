/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsCoefficient
/-! # Complete actual descending coefficient loop, chronological raw array order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuter
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeD1StackRecoveryWeightsOuterView
open SemiprimeRationalBits (RationalWord)
namespace Spec
export SemiprimeD1StackRecoveryWeightsSpec (weight array)
end Spec
/-- Exact ordered row prefix; every field was acquired by the actual coefficient source. -/
def rows (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r:Nat) (out:List Bool):List Bool:=
  ((List.range r).map (fun j=>Spec.weight width q j scalar inverse powers)).foldr SemiprimeD1StackNormalizedInverse.row out
/-- Literal descending/prepend preserves the original increasing index order, including every repeat. -/
theorem rows_succ (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r:Nat) (out:List Bool):
    rows inverse powers scalar q width (r+1) out=rows inverse powers scalar q width r
      (SemiprimeD1StackNormalizedInverse.row (Spec.weight width q r scalar inverse powers) out):=by
  simp only [rows,List.range_succ,List.map_append,List.map_singleton,List.foldr_append,List.foldr_cons,List.foldr_nil]
/-- SAME actual counter/complete coefficient traces, with no native report clock. -/
def timeBound (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool):Nat→List Bool→Nat
  | 0,_=>1
  | r+1,out=>1+SemiprimeD1StackRecoveryWeightsCoefficient.timeBound inverse powers scalar r (q-(r+1)) width out+
      timeBound inverse powers scalar q width r (SemiprimeD1StackNormalizedInverse.row (Spec.weight width q r scalar inverse powers) out)
/-- The actual loop visits EVERY j descending, executes every complete coefficient, and prepends the exact chronological native rows. -/
theorem outer_run (inverse powers:List RationalWord) (scalar:RationalWord) (q:Nat) (width:List Bool) (r:Nat) (out:List Bool) (hr:r≤q):
    ∃time ≤ timeBound inverse powers scalar q width r out,
      Runs program time (.local .outer) (bank (outer inverse powers scalar q width r out)) (.local (.clean false 0))
        (bank (outer inverse powers scalar q width 0 (rows inverse powers scalar q width r out))):=by
  induction r generalizing out with
  | zero=>
    have h0:=P.pop_run (.local .outer) (.local (.clean false 0)) abort (.local (.seedZero false)) (aux .remaining)
      (bank (outer inverse powers scalar q width 0 out)) [] rfl rfl
    change Runs program 1 _ _ (.local (.clean false 0)) (Function.update (bank (outer inverse powers scalar q width 0 out)) (aux .remaining) (unary 0)) at h0
    rw [update_remaining] at h0
    exact ⟨1,le_rfl,h0⟩
  | succ r ih=>
    have hq:r+(q-(r+1)+1)=q:=by omega
    have h0:=P.pop_run (.local .outer) (.local (.clean false 0)) abort (.local (.seedZero false)) (aux .remaining)
      (bank (outer inverse powers scalar q width (r+1) out)) (true::unary r) rfl rfl
    change Runs program 1 _ _ (.local (.seedZero false))
      (Function.update (bank (outer inverse powers scalar q width (r+1) out)) (aux .remaining) (unary r)) at h0
    rw [update_remaining] at h0
    obtain ⟨m,hm,h1⟩:=SemiprimeD1StackRecoveryWeightsCoefficient.coefficient_run inverse powers scalar r (q-(r+1)) width out
    rw [hq] at h1
    obtain ⟨s,hs,h2⟩:=ih (SemiprimeD1StackNormalizedInverse.row (Spec.weight width q r scalar inverse powers) out) (by omega)
    have hh:=P.join (P.join h0 h1) h2
    rw [←rows_succ] at hh
    exact ⟨1+m+s,by dsimp only [timeBound];omega,hh⟩
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsOuter
