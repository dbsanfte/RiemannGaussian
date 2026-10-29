/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IncidenceAcquisitionBounds
import RiemannGaussian.SemiprimeD1CounterMaximum
import RiemannGaussian.SemiprimeD1PacketRoundBounds

/-! # Original-input acquired maximum and D.3 packet padding
The original source is acquired once and retained. No maximum, label load,
encoded padded answer, or frequency oracle is an input.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketPadding
open SemiprimeBitArithmetic SemiprimeD1CollisionOriginal
open SemiprimeD1IncidenceAcquisition SemiprimeD1IncidenceAcquisitionBounds

/-- Original acquired selection/keys/state and its physically rounded packet count. -/
structure Result (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- Actual source retained for later packet orientations and slot assignment. -/
  source : Acquired n F a arity
  /-- Physical multiple of2^a dominating all original pair-class loads. -/
  padding : List Bool
  /-- All original acquisition, maximum, rounding and finite report control. -/
  clock : ℕ

/-- Execute selection/key/trie acquisition once, maximum once, rounding once. -/
def acquire (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Result n F a arity :=
  let source := SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner
  let maximum := SemiprimeD1CounterMaximum.maxState source.state
  let out := SemiprimeD1PacketRoundBits.round a maximum.bits
  ⟨source,out.bits,maximum.clock+out.clock+3⟩

/-- No original acquisition is repeated or replaced by proof-only labels. -/
theorem acquire_source (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).source=
      SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner := rfl

/-- Original source acquisition report is retained. -/
theorem retains_source (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).source.state.clock≤(acquire n F r a arity owner).clock := by
  unfold acquire SemiprimeD1CounterMaximum.maxState
  dsimp only
  omega

/-- Every actual class, including empty classes, fits within the returned padding. -/
theorem stored_le_padding (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (key : List Bool) :
    SemiprimeSourceHistogramTrie.value (acquire n F r a arity owner).source.state.trie key≤
      bitValue (acquire n F r a arity owner).padding := by
  exact (SemiprimeD1CounterMaximum.lookup_le_maximum _ key).trans
    (SemiprimeD1PacketRoundBits.le_round a _)

/-- The acquired output is an actual packet-size multiple. -/
theorem packet_dvd_padding (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    2^a∣bitValue (acquire n F r a arity owner).padding :=
  SemiprimeD1PacketRoundBounds.packet_dvd_round a _

/-- No high-order zero bits remain in the returned physical packet count. -/
theorem padding_compact (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    SemiprimeSourceCompactBits.Compact (acquire n F r a arity owner).padding :=
  SemiprimeD1PacketRoundBits.round_compact a _

/-- Original graph degrees and D.3 size conditions give at most3M padded slots. -/
theorem padding_scaled_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => (owner i).val)
        (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun i => n+i.1.val)
        (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (hsize : r^(2*a)*2^a≤(ports n F a arity).length) :
    r^(2*a)*bitValue (acquire n F r a arity owner).padding≤3*(ports n F a arity).length := by
  have hc:=original_countCap n F r a arity owner Δ ho hf hsmall
  have hm:=SemiprimeD1CounterMaximum.maximumTrie_le _ _ hc
  have hload : r^(2*a)*bitValue (SemiprimeD1CounterMaximum.maxState
      (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).state).bits≤
        2*(ports n F a arity).length := by
    change r^(2*a)*bitValue (SemiprimeD1CounterMaximum.maximumTrie _).bits≤_
    exact (Nat.mul_le_mul_left _ hm).trans (Nat.mul_div_le _ _)
  exact SemiprimeD1PacketRoundBounds.round_scaled_le a _ _ _ hload hsize

/-- Literal fixed polynomial mixed acquisition/physical maximum/rounding report. -/
def budget (n F r a M : ℕ) : ℕ :=
  SemiprimeD1IncidenceAcquisitionBounds.budget n F r a M+
    M*(3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+2)*
      (88*(Nat.clog 2 (M+1)+1)+7)+1+
    40*(a+Nat.clog 2 (M+1)+3)+6

/-- Output width comes from actual stored frequencies, not supplied output Fits. -/
theorem padding_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).padding.length≤a+Nat.clog 2 ((∑e,arity e)+1)+2 := by
  apply SemiprimeD1PacketRoundBounds.round_length
  exact SemiprimeD1CounterMaximum.maximumTrie_length _ _ (stored_length n F r a arity owner)

/-- Every actual producer report remains in the original-input total bound. -/
theorem acquire_clock (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a arity owner).clock≤budget n F r a (∑e,arity e) := by
  have hs:=SemiprimeD1IncidenceAcquisitionBounds.acquire_work n F r a arity owner
  have hn:=nodes_bound n F r a arity owner
  have hm:=SemiprimeD1CounterMaximum.maximumTrie_clock _ _ (stored_length n F r a arity owner)
  have hl:=SemiprimeD1CounterMaximum.maximumTrie_length _ _ (stored_length n F r a arity owner)
  have hr:=SemiprimeD1PacketRoundBounds.round_clock a _ _ hl
  change _≤_ at hm hr
  unfold acquire SemiprimeD1CounterMaximum.maxState budget
  dsimp only
  have hmono:=Nat.mul_le_mul_right (88*(Nat.clog 2 ((∑e,arity e)+1)+1)+7) hn
  omega

end RiemannGaussian.SemiprimeD1PacketPadding
