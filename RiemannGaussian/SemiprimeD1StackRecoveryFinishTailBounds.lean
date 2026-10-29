/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishLoopBounds
import RiemannGaussian.SemiprimeD1StackRecoveryFinishFrontBounds
import RiemannGaussian.SemiprimeD1StackRecoveryFinishRetention
/-! # Own actual sign/final-product/all-helper cleanup bounds
All helper word sizes are derived from actual reached source caches and retained
original inputs; no cleanup size, inverse answer or output-width advice is given.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishTailBounds
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishExecution
open SemiprimeBitIndexClipping (SignedWord)
namespace B
export SemiprimeD1StackRecoveryFinishOperatorBounds
  (Small sizedSlots small_update small_multiply multiply_time linear_cube)
end B
namespace L
export SemiprimeD1StackRecoveryFinishLoopBounds (prepared_small states_small)
end L
namespace W
export SemiprimeD1StackRecoveryFinishWords (odd content zeros_le)
end W
/-- Actual inverse boundary scalar caps derive from real initial reductions and all actually executed stage outputs. -/
theorem inverse_small (n:SignedWord) (d:List Bool) (p:Nat):B.Small (inverseValues n d p) p:=
  L.states_small p _ p (L.prepared_small n d p)
/-- Actual sign-circuit output has intrinsic target precision width. -/
theorem sign_word_length (v:Values) (p:Nat) (hv:B.Small v p) (negative:Bool):(S.word v negative).length≤p:=by
  cases negative with
  | false=>exact hv.bounded (.aux .numeratorResidue) (by simp [B.sizedSlots])
  | true=>
    have h:=SemiprimeD1JetScalarBits.mul_length (v .width).length (v (.aux .negative)) (v (.aux .numeratorResidue))
    simpa only [S.word,ite_true,hv.width] using h
/-- All actual post-sign scalar caches remain intrinsically bounded. -/
theorem signed_small (n:SignedWord) (d:List Bool) (p:Nat):B.Small (signedValues n d p) p:=
  B.small_update _ p (inverse_small n d p) (.aux .signedResidue) (by decide) _
    (sign_word_length _ p (inverse_small n d p) n.negative)
/-- Actual final-product cache bounds derive from the real final multiplier output. -/
theorem final_small (n:SignedWord) (d:List Bool) (p:Nat):B.Small (finalValues n d p) p:=
  B.small_multiply _ p (signed_small n d p) .final
/-- The actual finite sign branch pays its real peek and actual copy-or-product path. -/
theorem sign_time (v:Values) (p:Nat) (hv:B.Small v p) (negative:Bool):S.time v negative≤200000*(p+1)^3:=by
  have hm:=B.multiply_time v p hv .signed
  have hq:=hv.bounded (.aux .numeratorResidue) (by simp [B.sizedSlots])
  have hl:=B.linear_cube p
  unfold S.time
  split <;> omega
/-- Original acquired non-stage metadata survives the actual whole inverse/sign/final-product pipeline. -/
theorem final_preserved (n:SignedWord) (d:List Bool) (p:Nat) (s:Slot)
    (hs:N.Stable s) (ht:s≠.aux .todo) (hn:s≠.aux .signedResidue) (ho:s≠.output):
    finalValues n d p s=P.result n d (List.replicate p true) s:=by
  unfold finalValues MP.result SemiprimeD1StackRecoveryFinishMultiply.target
  rw [Function.update_of_ne ho]
  unfold signedValues S.result
  rw [Function.update_of_ne hn]
  exact N.states_preserved p _ s hs ht
/-- Actual marker EOF leaves no todo bytes for final cleanup. -/
theorem final_todo (n:SignedWord) (d:List Bool) (p:Nat):finalValues n d p (.aux .todo)=[]:=by
  unfold finalValues MP.result SemiprimeD1StackRecoveryFinishMultiply.target
  rw [Function.update_of_ne (by decide:Slot.aux Aux.todo≠.output)]
  unfold signedValues S.result
  rw [Function.update_of_ne (by decide:Slot.aux Aux.todo≠.aux .signedResidue)]
  exact SemiprimeD1StackRecoveryFinishNewtonOriginal.states_todo p _ rfl
/-- Complete actual cleanup byte mass is bounded from retained original binary denominator and intrinsic real scalar outputs. -/
theorem cleanup_mass (n:SignedWord) (d:List Bool) (p:Nat):G.mass (finalValues n d p) 0≤9*p+2*d.length+3:=by
  let v:=finalValues n d p
  have hv:=final_small n d p
  have h0:=hv.bounded (.aux .inverseInput) (by simp [B.sizedSlots])
  have h1:=hv.bounded (.aux .negative) (by simp [B.sizedSlots])
  have h2:=hv.bounded (.aux .two) (by simp [B.sizedSlots])
  have h3:=hv.bounded (.aux .current) (by simp [B.sizedSlots])
  have h4:=hv.bounded (.aux .product) (by simp [B.sizedSlots])
  have h5:=hv.bounded (.aux .opposite) (by simp [B.sizedSlots])
  have h6:=hv.bounded (.aux .correction) (by simp [B.sizedSlots])
  have h7:=hv.bounded (.aux .signedResidue) (by simp [B.sizedSlots])
  have h8:=hv.bounded (.aux .numeratorResidue) (by simp [B.sizedSlots])
  have hs:v (.aux .sign)=[n.negative]:=
    (final_preserved n d p (.aux .sign) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have hn:v (.aux .numeratorWork)=[]:=
    (final_preserved n d p (.aux .numeratorWork) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have hd:v (.aux .denominatorWork)=W.odd d:=
    (final_preserved n d p (.aux .denominatorWork) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have hc:v (.aux .content)=W.content d:=
    (final_preserved n d p (.aux .content) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have hl:v (.aux .lost)=[SemiprimeD1StackRecoveryFinishWords.lost d n.magnitude]:=
    (final_preserved n d p (.aux .lost) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have ht:v (.aux .todo)=[]:=final_todo n d p
  have hw:v (.aux .copyScratch)=[]:=
    (final_preserved n d p (.aux .copyScratch) (by simp [N.Stable]) (by decide) (by decide) (by decide)).trans rfl
  have hod:=SemiprimeD1StackRecoveryFinishFrontBounds.odd_length d
  have hco:(W.content d).length≤d.length+1:=by
    have hz:=W.zeros_le d
    simp only [W.content,List.length_append,List.length_replicate,List.length_cons,List.length_nil] at *
    omega
  change G.mass v 0≤_
  simp only [G.mass,cleanup,List.drop_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    hs,hn,hd,hc,hl,ht,hw,List.length_cons,List.length_nil]
  change (v (.aux .inverseInput)).length≤p at h0
  change (v (.aux .negative)).length≤p at h1
  change (v (.aux .two)).length≤p at h2
  change (v (.aux .current)).length≤p at h3
  change (v (.aux .product)).length≤p at h4
  change (v (.aux .opposite)).length≤p at h5
  change (v (.aux .correction)).length≤p at h6
  change (v (.aux .signedResidue)).length≤p at h7
  change (v (.aux .numeratorResidue)).length≤p at h8
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryFinishTailBounds
