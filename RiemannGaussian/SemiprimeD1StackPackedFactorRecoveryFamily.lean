/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryClock
/-! # The complete actual quartic source factors every semiprime from its acquired scalar
This is a prepared two-word source. The N-only recursive counter producing
the scalar is still a separate explicit caller obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFamily
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryMeaning
open SemiprimeD1StackPackedFactorRecoveryClock SemiprimeBitArithmetic SemiprimeSourceCompactBits
/-- BOTH original orientations are handled by the SAME fixed actual program and physical factor checks. -/
theorem source_factorization (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ polynomial bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) ∧
      2≤bitValue ((done bits scalar).data (aux .small)) ∧ 2≤bitValue ((done bits scalar).data (aux .large)) ∧
      bitValue ((done bits scalar).data (aux .small))*bitValue ((done bits scalar).data (aux .large))=bitValue bits := by
  by_cases hpq:p≤q
  · obtain ⟨t,ht,hr,hs,hl⟩:=source_ordered bits scalar hc p q hp hq hpq hN hscalar
    exact ⟨t,ht.trans (timeBound_le bits scalar),hr,by rw [hs];exact hp.two_le,
      by rw [hl];exact hq.two_le,by rw [hs,hl,hN]⟩
  · have hN' : bitValue bits=q*p := hN.trans (Nat.mul_comm p q)
    have hscalar' : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (q*p) (Nat.mul_pos hq.pos hp.pos) := by
      simpa only [Nat.mul_comm q p] using hscalar
    obtain ⟨t,ht,hr,hs,hl⟩:=source_ordered bits scalar hc q p hq hp (by omega) hN' hscalar'
    exact ⟨t,ht.trans (timeBound_le bits scalar),hr,by rw [hs];exact hq.two_le,
      by rw [hl];exact hp.two_le,by rw [hs,hl,hN']⟩
/-- SAME complete source trace, with one fixed quartic bound before all physical inputs. -/
theorem source_run_bounded (bits scalar : List Bool) (hc : Compact bits) (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hN : bitValue bits=p*q)
    (hscalar : bitValue scalar=SemiprimeD1PackedMomentSemiprime.packedValue (p*q) (Nat.mul_pos hp.pos hq.pos)) :
    ∃t ≤ polynomial bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) := by
  obtain ⟨t,ht,hr,_⟩:=source_factorization bits scalar hc p q hp hq hN hscalar
  exact ⟨t,ht,hr⟩
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFamily
