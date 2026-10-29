/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishTailBounds
/-! # Fixed quartic bound for the same complete actual recovery source
All input binary bytes and actual unary WIDTH markers pay their own copying,
shifting, full padding scans, scalar calls, precision rounds and cleanup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishBounds
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishExecution
open SemiprimeBitIndexClipping (SignedWord)
/-- Actual total input bytes, including the physically parsed sign and WIDTH markers. -/
def resource (n:SignedWord) (d:List Bool) (p:Nat):Nat:=(B.signedTape n).length+d.length+p
/-- Fixed coefficient and degree, independent of every actual input and result. -/
def runBound (n:SignedWord) (d:List Bool) (p:Nat):Nat:=1000000000000*(resource n d p+1)^4
/-- Actual complete source clock is bounded without identifying it with any old native report clock. -/
theorem timeBound_le (n:SignedWord) (d:List Bool) (p:Nat):timeBound n d p ≤runBound n d p:=by
  let z:=resource n d p+1
  have hz:1 ≤z:=by dsimp [z];omega
  have hp:p+1 ≤z:=by dsimp [z,resource];omega
  have hl:z ≤z^4:=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by decide:1 ≤4)
  have h4:(p+1)^4 ≤z^4:=Nat.pow_le_pow_left hp 4
  have h3:(p+1)^3 ≤z^4:=(Nat.pow_le_pow_left hp 3).trans (Nat.pow_le_pow_right hz (by decide:3 ≤4))
  have h0:=SemiprimeD1StackRecoveryFinishFrontBounds.floor_time n d
  have h1:=SemiprimeD1StackRecoveryFinishFrontBounds.preparation_time n d (List.replicate p true)
  simp only [List.length_replicate] at h1
  have h2:=SemiprimeD1StackRecoveryFinishLoopBounds.original_loop n d p
  have h3t:=SemiprimeD1StackRecoveryFinishTailBounds.sign_time _ p
    (SemiprimeD1StackRecoveryFinishTailBounds.inverse_small n d p) n.negative
  have h4t:=SemiprimeD1StackRecoveryFinishOperatorBounds.multiply_time _ p
    (SemiprimeD1StackRecoveryFinishTailBounds.signed_small n d p) .final
  have h5:=SemiprimeD1StackRecoveryFinishTailBounds.cleanup_mass n d p
  have h0':F.floorTime n d ≤1000*z^4:=by
    have hh:(B.signedTape n).length+d.length+1 ≤z:=by dsimp [z,resource];omega
    exact h0.trans (Nat.mul_le_mul_left 1000 (hh.trans hl))
  have h1':P.time n d (List.replicate p true) ≤1000*z^4:=by
    change P.time n d (List.replicate p true) ≤1000*z at h1
    exact h1.trans (Nat.mul_le_mul_left 1000 hl)
  have h2':N.budget p (P.result n d (List.replicate p true)) ≤500000*z^4:=
    h2.trans (Nat.mul_le_mul_left 500000 h4)
  have h3':S.time (inverseValues n d p) n.negative ≤200000*z^4:=
    h3t.trans (Nat.mul_le_mul_left 200000 h3)
  have h4':MP.time (signedValues n d p) .final ≤100000*z^4:=
    h4t.trans (Nat.mul_le_mul_left 100000 h3)
  have h5':G.mass (finalValues n d p) 0+49 ≤100*z^4:=by
    have hh:9*p+2*d.length+3+49 ≤100*z:=by dsimp [z,resource];omega
    have hx:=Nat.mul_le_mul_left 100 hl
    omega
  unfold timeBound bodyTime
  change _ ≤1000000000000*z^4
  omega
/-- The same actual parameterless finite program halts within the fixed quartic input-byte bound. -/
theorem source_run_bounded (n:SignedWord) (d:List Bool)
    (hd:0 < SemiprimeBitArithmetic.bitValue d) (p:Nat):
    ∃q ≤runBound n d p,SemiprimeD1StackCalls.run program q
      (initial (B.signedTape n) d (List.replicate p true))=some (done n d p):=
  ⟨timeBound n d p,timeBound_le n d p,source_run n d hd p⟩
end RiemannGaussian.SemiprimeD1StackRecoveryFinishBounds
