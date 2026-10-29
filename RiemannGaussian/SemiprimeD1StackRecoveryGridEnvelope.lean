/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridStageBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridResource
/-! # Fixed numerical envelopes for actual grid stage clocks -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridEnvelope
namespace S
export SemiprimeD1StackRecoveryGridStageBounds (siteCap powerCap)
end S
/-- The cubic physical-word envelope and sixth-power arithmetic width are both charged to the original paid resource. -/
theorem sum_le (r b l:Nat) (hr:1≤r) (hb:b≤2*r) (hl:l≤2*10^9*r^3) :
    104*l+b^6+1≤10^12*r^6:=by
  have hp: r^3≤r^6:=Nat.pow_le_pow_right hr (by decide:3≤6)
  have hp0:1≤r^6:=Nat.one_le_pow 6 _ hr
  have hb6:=Nat.pow_le_pow_left hb 6
  rw [mul_pow] at hb6
  norm_num1 at hb6 ⊢
  omega
/-- Each same-trace actual normalized/fitted operation has a fixed sixth-degree cap. -/
theorem site_le (r b l:Nat) (hr:1≤r) (hb:b≤2*r) (hl:l≤2*10^9*r^3) :
    S.siteCap b l≤10^49*r^6:=by
  have h:=sum_le r b l hr hb hl
  unfold S.siteCap
  calc
    _≤10^36*(10^12*r^6):=Nat.mul_le_mul_left _ h
    _≤_:=by norm_num1;omega
/-- Each actual acquired-count power loop has a fixed seventh-degree cap, paying count VALUE. -/
theorem power_le (r b l m:Nat) (hr:1≤r) (hb:b≤2*r) (hl:l≤10^9*r^3) (hm:m≤3*r) :
    S.powerCap m b l≤10^53*r^7:=by
  have h0:=sum_le r b l hr hb (by omega)
  have hs:l+b^6+1≤10^12*r^6:=by omega
  have hm0:m+2≤5*r:=by omega
  have hp:=Nat.mul_le_mul hm0 hs
  unfold S.powerCap
  have he:(5*r)*(10^12*r^6)=5*10^12*r^7:=by ring
  rw [he] at hp
  calc
    _=10^40*((m+2)*(l+b^6+1)):=by ring
    _≤10^40*(5*10^12*r^7):=Nat.mul_le_mul_left _ hp
    _≤_:=by norm_num1;omega
/-- Every repeated slope frame newly emitted in a row fits the global physical-word envelope. -/
theorem frame_bytes_le (r w m:Nat) (hr:1≤r) (hw:w≤r) (hm:m≤3*r) :
    m*(4*w+5)≤10^9*r^3:=by
  have h0:4*w+5≤9*r:=by omega
  have h1:=Nat.mul_le_mul hm h0
  have h2:r^2≤r^3:=Nat.pow_le_pow_right hr (by decide:2≤3)
  norm_num1
  nlinarith
/-- The whole actual row-body clock is bounded from physical source widths, acquired multiplicity and emitted frame bytes. -/
theorem work_le (r h u order w m b l:Nat) (hr:1≤r) (hh:h≤3*r) (hu:u≤r) (ho:order≤r)
    (hw:w≤r) (hm:m≤3*r) (hb:b≤2*r) (hl:l=10^9*r^3) :
    100*(h+u+order+1)^2+5*S.siteCap b l+2*S.powerCap m b l+
      100*(m+1)*(w+1)+2*S.siteCap b (2*l)+3000*(2*l+1)≤10^54*r^8:=by
  have hs:=site_le r b l hr hb (by omega)
  have hs2:=site_le r b (2*l) hr hb (by omega)
  have hp:=power_le r b l m hr hb (by omega) hm
  have hsum:h+u+order+1≤6*r:=by omega
  have hsquare:=Nat.pow_le_pow_left hsum 2
  have hmw:=Nat.mul_le_mul (show m+1≤4*r by omega) (show w+1≤2*r by omega)
  have h28:r^2≤r^8:=Nat.pow_le_pow_right hr (by decide:2≤8)
  have h38:r^3≤r^8:=Nat.pow_le_pow_right hr (by decide:3≤8)
  have h68:r^6≤r^8:=Nat.pow_le_pow_right hr (by decide:6≤8)
  have h78:r^7≤r^8:=Nat.pow_le_pow_right hr (by decide:7≤8)
  have h08:1≤r^8:=Nat.one_le_pow 8 _ hr
  rw [mul_pow] at hsquare
  have he:(4*r)*(2*r)=8*r^2:=by ring
  rw [he] at hmw
  rw [hl] at hs hs2 hp ⊢
  norm_num1 at hsquare hs hs2 hp ⊢
  nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryGridEnvelope
