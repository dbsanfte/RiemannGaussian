/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthGates
/-! # Actual complete64-gate trace and every-intermediate VALUE resource cap -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthLoop
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthPrimitives SemiprimeD1StackRecoveryWidthGates SemiprimeD1StackProcedureTrace
/-- Degree-five VALUE cap for all physically acquired gate/cache/input words. -/
def wordCap (a M N:Nat) :Nat:=2000*(V.envelope a M N)^5
/-- Every fixed input/cache/earlier gate word is paid by original dimensions including N by VALUE. -/
theorem source_bound (s:W.Source) (a M N:Nat) :V.sourceValue a M N s≤ wordCap a M N:=by
  have he:1≤ V.envelope a M N:=by unfold V.envelope;omega
  have hp:V.envelope a M N≤(V.envelope a M N)^5:=Nat.le_pow (by decide:0<(5:Nat))
  cases s with
  | a=>change a≤ wordCap a M N;unfold wordCap V.envelope at *;omega
  | m=>change M≤ wordCap a M N;unfold wordCap V.envelope at *;omega
  | n=>change N≤ wordCap a M N;unfold wordCap V.envelope at *;omega
  | reg g=>exact SemiprimeD1StackRecoveryWidthPolynomial.value_bound g a M N
/-- Same-program gate cap pays every copied unary byte and every actual nested unary-product traversal. -/
def gateCap (a M N:Nat) :Nat:=100*(wordCap a M N+1)^2
/-- Uniform actual gate cost follows from each REAL component's physical-word bound. -/
theorem gate_bound (g:W.Gate) (a M N:Nat) :gateBound g a M N≤ gateCap a M N:=by
  have hw:1≤ wordCap a M N:=by
    have he:1≤ V.envelope a M N:=by unfold V.envelope;omega
    have hp:=Nat.one_le_pow 5 (V.envelope a M N) he
    unfold wordCap
    omega
  cases hg:W.node g with
  | literal k=>
    have h:W.literalValue k≤20:=(SemiprimeD1StackRecoveryWidthCircuit.literal_bounds k).2
    unfold gateBound gateCap
    rw [hg]
    dsimp only
    nlinarith only [h,hw]
  | add l r=>
    have hl:=source_bound l a M N
    have hr:=source_bound r a M N
    unfold gateBound gateCap
    rw [hg]
    dsimp only
    nlinarith only [hl,hr,hw]
  | mul l r=>
    have hl:=source_bound l a M N
    have hr:=source_bound r a M N
    have hm:V.sourceValue a M N l*(2*V.sourceValue a M N r+3)≤ wordCap a M N*(2*wordCap a M N+3):=
      Nat.mul_le_mul hl (by omega)
    unfold gateBound gateCap
    rw [hg]
    dsimp only
    nlinarith only [hl,hr,hw,hm]
/-- Every actual gate runs in original fixed order, producing its own actual intermediate instead of receiving any answer. -/
theorem gates_loop (a M N remaining stage:Nat) (hs:stage+remaining=64) :
    ∃q≤ remaining*gateCap a M N,Runs program q (gateLabel stage) (bank (atGate stage a M N)) .fill
      (bank (atGate 64 a M N)) :=by
  induction remaining generalizing stage with
  | zero=>
    have he:stage=64:=by omega
    subst stage
    exact ⟨0,by omega,runs_refl program .fill _⟩
  | succ remaining ih=>
    have hstage:stage<64:=by omega
    let g:W.Gate:=⟨stage,hstage⟩
    obtain ⟨q,hq,h0⟩:=gate_run g a M N
    obtain ⟨p,hp,h1⟩:=ih (stage+1) (by omega)
    rw [next_gate] at h0
    change Runs program q (.gate g) (bank (atGate stage a M N)) (gateLabel (stage+1)) (bank (atGate (stage+1) a M N)) at h0
    have he:gateLabel stage=.gate g:=by unfold gateLabel;rw [dite_eq_left hstage]
    rw [he]
    refine ⟨q+p,?_,join h0 h1⟩
    have hb:=hq.trans (gate_bound g a M N)
    nlinarith only [hb,hp]
end RiemannGaussian.SemiprimeD1StackRecoveryWidthLoop
