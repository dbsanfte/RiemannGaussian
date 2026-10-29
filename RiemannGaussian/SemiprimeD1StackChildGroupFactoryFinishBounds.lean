/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactorySuffix
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTraceBounds
/-! # The actual six-frame final output and complete115-role sweep have linear cost
Every allocated private/shadow role is charged to its actual final bank, even
when empty. No output length or cleanup clock is supplied to the finite source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinishBounds
open SemiprimeD1StackChildGroupFactoryRoles
namespace F
export SemiprimeD1StackChildGroupFactoryFinalFrames (buffer result stage timeBound wordRole)
end F
namespace H
export SemiprimeD1StackChildGroupFactoryFinish (timeBound)
end H
/-- Whole actual six-call frame clock is linear in the complete incoming physical cap. -/
theorem frame_time (before:Stack→List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap):
    F.timeBound before≤36*cap+30:=by
  have h0:=hc (aux .oldEndpoints)
  have h1:=hc (aux .orders)
  have h2:=hc (aux .leftPorts)
  have h3:=hc (aux .buckets)
  have h4:=hc (aux .endpoints)
  have h5:=hc (aux .activation)
  dsimp only [F.timeBound]
  omega
/-- Real preserving frames have only additive literal payload/delimiter growth. -/
theorem buffer_length (before:Stack→List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap) (n:Nat):
    (F.buffer before n).length≤cap+n*(2*cap+1):=by
  induction n with
  | zero=>simpa only [F.buffer,Nat.zero_mul,Nat.add_zero] using hc (aux .output)
  | succ n ih=>
    have h:=hc (F.wordRole ⟨n%6,Nat.mod_lt _ (by decide)⟩)
    simp only [F.buffer,SemiprimeSourceHistogramKeyBits.frame_length ]
    nlinarith
/-- ALL115 completed frame-source words, not only the public output, are covered. -/
theorem frame_word (before:Stack→List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap):
    ∀k,(F.result before k).length≤13*cap+6:=by
  have hb:=buffer_length before cap hc 6
  intro k
  by_cases h:k=aux .output
  · subst k
    simp only [F.result,F.stage,Function.update_self]
    omega
  · rw [F.result,F.stage,Function.update_of_ne h]
    exact (hc k).trans (by omega)
/-- Generic full finite-store sum, instantiated only after abstract summation. -/
theorem finite_word_sum {K:Type} [Fintype K] (words:K→List Bool) (cap:Nat)
    (hc:∀k,(words k).length≤cap): (∑k,(words k).length)≤Fintype.card K*cap:=by
  calc
    _≤∑_k:K,cap:=Finset.sum_le_sum (fun k _=>hc k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- SAME actual six-frame output source followed by the literal full physical sweep has linear time. -/
theorem timeBound_le (before:Stack→List Bool) (cap:Nat) (hc:∀k,(before k).length≤cap):
    F.timeBound before+H.timeBound (F.result before)≤1000000*(cap+1):=by
  have hf:=frame_time before cap hc
  have hw:=frame_word before cap hc
  have hm:=finite_word_sum (F.result before) (13*cap+6) hw
  rw [stack_card] at hm
  change SemiprimeD1StackChildGroupFactoryCleanup.mass (F.result before)≤115*(13*cap+6) at hm
  dsimp only [H.timeBound]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryFinishBounds
