/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperatorBounds
import RiemannGaussian.SemiprimeD1StackRecoveryFinishNewtonOriginal
/-! # Actual precision-marker loop has its own fixed quartic source clock
Intrinsic real scalar-output widths are propagated through every physical stage.
No intermediate width premise remains in the original three-input endpoint.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishLoopBounds
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
namespace B
export SemiprimeD1StackRecoveryFinishOperatorBounds
  (Small sizedSlots small_update small_foreign small_multiply small_correction multiply_time correction_time linear_cube)
end B
namespace N
export SemiprimeD1StackRecoveryFinishNewton (first second correction stepResult stepTime advance budget states)
end N
namespace O
export SemiprimeD1StackRecoveryFinishNewtonOriginal
  (prepared_width prepared_a prepared_negative prepared_two prepared_one)
end O
namespace P
export SemiprimeD1StackRecoveryFinishPreparation (result)
end P
open SemiprimeBitIndexClipping (SignedWord)
/-- Each actual three-product/one-sum stage preserves all intrinsic scalar widths. -/
theorem small_step (v:Values) (p:Nat) (hv:B.Small v p):B.Small (N.stepResult v) p:=
  B.small_multiply _ p (B.small_correction _ p
    (B.small_multiply _ p (B.small_multiply v p hv .product) .opposite)) .update
/-- Actual todo pop touches no scalar cache or precision WIDTH. -/
theorem small_popped (v:Values) (p:Nat) (hv:B.Small v p):
    B.Small (Function.update v (.aux .todo) (v (.aux .todo)).tail) p:=
  B.small_foreign v p hv (.aux .todo) (by decide) (by simp [B.sizedSlots]) _
/-- Actual marker pop and complete physical stage preserve intrinsic scalar cache widths. -/
theorem small_advance (v:Values) (p:Nat) (hv:B.Small v p):B.Small (N.advance v) p:=small_step _ p (small_popped v p hv)
/-- SAME complete actual Newton stage clock, including every copy, old-cache drain and real return. -/
theorem step_time (v:Values) (p:Nat) (hv:B.Small v p):N.stepTime v≤400000*(p+1)^3:=by
  have h1:=B.small_multiply v p hv .product
  have h2:=B.small_multiply (N.first v) p h1 .opposite
  have h3:=B.small_correction (N.second v) p h2
  have t0:=B.multiply_time v p hv .product
  have t1:=B.multiply_time (N.first v) p h1 .opposite
  have t2:=B.correction_time (N.second v) p h2
  have t3:=B.multiply_time (N.correction v) p h3 .update
  unfold N.stepTime
  omega
/-- Actual n-marker source clock is linear in actual visits, with the genuine final EOF test. -/
theorem budget_linear (n:Nat) (v:Values) (p:Nat) (hv:B.Small v p):
    N.budget n v≤1+n*(400000*(p+1)^3+1):=by
  induction n generalizing v with
  | zero=>simp only [N.budget,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ n ih=>
    have hs:=step_time (Function.update v (.aux .todo) (v (.aux .todo)).tail) p (small_popped v p hv)
    have hr:=ih (N.advance v) (small_advance v p hv)
    change 1+N.stepTime (Function.update v (.aux .todo) (v (.aux .todo)).tail)+N.budget n (N.advance v)≤_
    rw [Nat.succ_mul]
    omega
/-- Actual P-marker loop has a fixed quartic own-source bound, with no native inverse report-clock equation. -/
theorem budget_quartic (v:Values) (p:Nat) (hv:B.Small v p):N.budget p v≤500000*(p+1)^4:=by
  have h:=budget_linear p v p hv
  have hp:=B.linear_cube p
  calc
    _≤(p+1)*(400000*(p+1)^3+1):=by nlinarith
    _≤(p+1)*(500000*(p+1)^3):=by gcongr;omega
    _=500000*(p+1)^4:=by ring
/-- Actual acquired initial scalar caches satisfy all width caps intrinsically, including P0 and P1. -/
theorem prepared_small (n:SignedWord) (d:List Bool) (p:Nat):B.Small (P.result n d (List.replicate p true)) p:=by
  constructor
  · rw [O.prepared_width,List.length_replicate]
  · intro s hs
    simp only [B.sizedSlots,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [O.prepared_a,List.length_replicate]
      exact SemiprimeD1JetScalarBits.reduce_length _ _
    · rw [O.prepared_negative,List.length_replicate]
    · rw [O.prepared_two,List.length_replicate]
      exact SemiprimeD1JetScalarBits.reduce_length _ _
    · rw [O.prepared_one,List.length_replicate]
      exact SemiprimeD1JetScalarBits.reduce_length _ _
    · exact Nat.zero_le p
    · exact Nat.zero_le p
    · exact Nat.zero_le p
    · exact Nat.zero_le p
    · change (SemiprimeD1JetScalarBits.reduce (List.replicate p true).length
        (SemiprimeD1StackRecoveryFinishWords.corrected n.negative d n.magnitude)).bits.length≤p
      simpa only [List.length_replicate] using SemiprimeD1JetScalarBits.reduce_length p
        (SemiprimeD1StackRecoveryFinishWords.corrected n.negative d n.magnitude)
    · exact Nat.zero_le p
/-- Actual loop beginning with ONLY source-acquired scalar caches has the fixed quartic own-source clock. -/
theorem original_loop (n:SignedWord) (d:List Bool) (p:Nat):
    N.budget p (P.result n d (List.replicate p true))≤500000*(p+1)^4:=budget_quartic _ p (prepared_small n d p)
/-- Every scalar cache after any number of actual stages retains the original precision-byte bound. -/
theorem states_small (n:Nat) (v:Values) (p:Nat) (hv:B.Small v p):B.Small (N.states n v) p:=by
  induction n generalizing v with
  | zero=>exact hv
  | succ n ih=>exact ih (N.advance v) (small_advance v p hv)
end RiemannGaussian.SemiprimeD1StackRecoveryFinishLoopBounds
