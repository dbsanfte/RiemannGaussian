/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingMeaning
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingExecution
import RiemannGaussian.SemiprimeD1PacketPadding
/-! # Entire original packet-padding bytes from acquired raw keys and acquired unary exponent -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingOriginal
open SemiprimeD1StackSourcePacketPadding SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeD1StackSourcePacketPaddingMeaning SemiprimeD1StackSourcePacketPaddingExecution
attribute [local irreducible] SemiprimeD1IncidenceAcquisition.acquire SemiprimeD1PacketPadding.acquire
/-- Every actual stopped frequency cell is retained, including all original raw bytes, historical records and compact maximum. -/
theorem frequency_preserved (keys:List (List Bool)) (a:Nat) (k:F.Stack) :
    (done keys a).data (frequencyStack k)=(SemiprimeD1StackSourceKeyFrequencyEncoding.done keys).data k :=rfl
/-- Acquired exponent markers are physically retained; the two paid copies are separately consumed. -/
theorem exponent_retained (keys:List (List Bool)) (a:Nat) :
    (done keys a).data (aux .exponent)=List.replicate a true :=rfl
/-- Both actual unary work copies are empty after every successful whole source. -/
theorem copies_clear (keys:List (List Bool)) (a:Nat) :
    (done keys a).data (aux .cutTodo)=[] ∧ (done keys a).data (aux .prefixTodo)=[] :=⟨rfl,rfl⟩
/-- The entire output is the frozen original compact binary ceiling to a multiple of2^a, not the next power of the maximum. -/
theorem output_original (keys:List (List Bool)) (a:Nat) :
    (done keys a).data (aux .padding)=(SemiprimeD1PacketRoundBits.round a
      (SemiprimeD1CounterMaximum.maxState (SemiprimeSourceHistogramSquares.acquire keys)).bits).bits :=by
  change rounded a (FE.acquire keys).maximum=_
  rw [rounded_original,SemiprimeD1StackSourceKeyFrequencyMeaning.maximum_original]
/-- Exactly zero maximum remains exactly empty zero padding, for every acquired exponent. -/
theorem empty_output (a:Nat) :(done [] a).data (aux .padding)=[] :=rounded_zero a
/-- All original graph inputs give the exact original PacketPadding output when their actual selected-key vector and unary exponent reach this source. -/
theorem packet_output_original (n F r a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    (done (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys a).data (aux .padding)=
      (SemiprimeD1PacketPadding.acquire n F r a arity owner).padding :=by
  have hm:=SemiprimeD1StackSourceKeyFrequencyOriginal.maximum_of_good _ _
    (SemiprimeD1IncidenceAcquisition.acquire_good n F r a arity owner)
  change rounded a (FE.acquire (SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys).maximum=_
  rw [rounded_original,hm]
  unfold SemiprimeD1PacketPadding.acquire
  rfl
/-- Same whole physical source and own trace yield the exact original rounded maximum; no native clock is transported. -/
theorem source_run_original (keys:List (List Bool)) (a:Nat) :∃t≤ runBound keys a,
    SemiprimeD1StackCalls.run program t (source keys a)=some (done keys a) ∧
      (done keys a).data (aux .padding)=(SemiprimeD1PacketRoundBits.round a
        (SemiprimeD1CounterMaximum.maxState (SemiprimeSourceHistogramSquares.acquire keys)).bits).bits ∧
      (∀k,(done keys a).data (frequencyStack k)=(SemiprimeD1StackSourceKeyFrequencyEncoding.done keys).data k) :=by
  obtain ⟨t,ht,hr⟩:=source_run keys a
  exact ⟨t,ht,hr,output_original keys a,frequency_preserved keys a⟩
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingOriginal
