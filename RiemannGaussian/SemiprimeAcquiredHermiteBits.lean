/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness
import RiemannGaussian.SemiprimeHermiteNodeBitsBounds
import RiemannGaussian.SemiprimeScalarWordSum
import RiemannGaussian.SemiprimeAcquiredHermite

/-! # Complete acquired physical Hermite reconstruction
Packets are acquired once per actual node, and every node and accumulation
report is retained. Original common packet bounds derive every scalar fit.
Semantic comparison to the scalar consumer never substitutes its work report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeAcquiredHermiteBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeDotBits
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeLocalExecutionHeight
open SemiprimeHermiteArrayHeight (hermiteDenominator hermiteNodeBound)

/-- Allocated literal zero with its constant construction allowance. -/
def zero : RationalReport := ⟨zeroWord,4⟩

/-- A chronological node callback; its packet is cached exactly once. -/
def nodeAt (template : List Bool) (Q J : ℕ) (acquire : Fin Q → JetReport) (i : ℕ) : RationalReport :=
  if hi : i<Q then
    let packet := acquire ⟨i,hi⟩
    SemiprimeHermiteNodeBits.node template Q J ⟨i,hi⟩ packet
  else zero

/-- Complete physical reconstruction in literal increasing node order. -/
def reconstruct (template : List Bool) (Q J : ℕ) (acquire : Fin Q → JetReport) : RationalReport :=
  SemiprimeScalarWordSum.sumFrom template (nodeAt template Q J acquire) Q 0 zero

/-- Structural storage width of the accumulated physical result. -/
theorem reconstruct_width (template : List Bool) (Q J : ℕ) (acquire : Fin Q → JetReport)
    (ht : 0<template.length) : Width (reconstruct template Q J acquire).word template.length := by
  apply SemiprimeScalarWordSum.sumFrom_width
  exact ⟨by simp [zero,zeroWord],by simpa [zero,zeroWord] using (show 1≤template.length by omega)⟩

/-- Actual acquisition plus physical reconstruction equals intrinsic Hermite,
with a single original-data common denominator across every accumulation. -/
theorem reconstruct_correct (template : List Bool) (b Q J d B : ℕ)
    (acquire : Fin Q → JetReport) (hJ : 0<J) (hd : 0<d)
    (hvalid : ∀ t,Valid (acquire t).words)
    (hrep : ∀ t,ArrayBound (decode (acquire t).words) J d B)
    (hdb : d≤2^b) (hBb : B≤2^b)
    (hw : SemiprimeHermiteWordWidth.width b Q J≤template.length) :
    (reconstruct template Q J acquire).word.value=
        (SemiprimeHermiteArrayHeight.hermite Q J (fun t => decode (acquire t).words)).value ∧
      (reconstruct template Q J acquire).word.Valid ∧
      Representation (reconstruct template Q J acquire).word.value
        (hermiteDenominator Q J d) (Q*hermiteNodeBound Q J B) := by
  have hden : 0<hermiteDenominator Q J d := by
    unfold hermiteDenominator
    exact Nat.mul_pos (SemiprimeCardinalHeight.cardinalDenominator_pos Q J)
      (Nat.mul_pos hd (pow_pos (SemiprimeCardinalHeight.cardinalDenominator_pos Q J) _))
  have hcaps := SemiprimeHermiteWordWidth.final_caps b Q J d B hdb hBb
  have hpow := Nat.pow_le_pow_right (by decide : 0<2) hw
  have hnode (t : Fin Q) := SemiprimeHermiteNodeBitsCorrectness.node_correct
    template b Q J d B t (acquire t) hJ hd (hvalid t) (hrep t) hdb hBb hw
  have hs := SemiprimeScalarWordSum.sumFrom_correct template (nodeAt template Q J acquire)
    Q 0 zero (hermiteDenominator Q J d) 0 (hermiteNodeBound Q J B) hden
    (hcaps.1.trans_le hpow) (by simpa using hcaps.2.trans_le hpow)
    ⟨zeroWord_valid,⟨0,by simp [zero,zeroWord_value],by simp⟩⟩ (by
      intro i hi
      simpa only [Nat.zero_add,nodeAt,dite_eq_left hi] using (hnode ⟨i,hi⟩).2)
  refine ⟨?_,hs.2.1,by simpa only [reconstruct,Nat.zero_add] using hs.2.2⟩
  change (SemiprimeScalarWordSum.sumFrom template _ Q 0 zero).word.value=_
  rw [hs.1,SemiprimeHermiteArrayHeight.hermite_value_sum,Finset.sum_fin_eq_sum_range]
  simp only [zero,zeroWord_value,zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [nodeAt,dite_eq_left (Finset.mem_range.mp hi)]
  exact (hnode ⟨i,Finset.mem_range.mp hi⟩).1

/-- Every actual acquisition clock, node stage and chronological addition is paid. -/
theorem reconstruct_clock (template : List Bool) (Q J : ℕ) (acquire : Fin Q → JetReport)
    (A : ℕ) (hW : Q+2≤template.length)
    (hsize : ∀ t,(acquire t).words.size≤A)
    (hbounded : ∀ t,Bounded (acquire t).words template.length) :
    (reconstruct template Q J acquire).clock≤
      (∑ t : Fin Q,(acquire t).clock)+Q*SemiprimeHermiteNodeBitsBounds.budget template.length A Q J+
      Q*(20000*(template.length+1)^3+8*template.length+8)+4 := by
  have ht : 0<template.length := by omega
  have hs := SemiprimeScalarWordSum.sumFrom_clock template (nodeAt template Q J acquire) Q 0 zero
    (show Width zero.word template.length from
      ⟨by simp [zero,zeroWord],by simpa [zero,zeroWord] using (show 1≤template.length by omega)⟩) (by
      intro i hi
      simpa only [Nat.zero_add,nodeAt,dite_eq_left hi] using
        SemiprimeHermiteNodeBitsBounds.node_width template Q J ⟨i,hi⟩ (acquire ⟨i,hi⟩))
  have hn : (∑ i∈Finset.range Q,(nodeAt template Q J acquire (0+i)).clock)≤
      (∑ t : Fin Q,(acquire t).clock)+Q*SemiprimeHermiteNodeBitsBounds.budget template.length A Q J := by
    have he : (∑ i∈Finset.range Q,(nodeAt template Q J acquire (0+i)).clock)=
        ∑ t : Fin Q,(SemiprimeHermiteNodeBits.node template Q J t (acquire t)).clock := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.zero_add,nodeAt,dite_eq_left (Finset.mem_range.mp hi)]
    rw [he]
    calc
      _ ≤ ∑ t : Fin Q,((acquire t).clock+SemiprimeHermiteNodeBitsBounds.budget template.length A Q J) := by
        apply Finset.sum_le_sum
        intro t _
        exact SemiprimeHermiteNodeBitsBounds.node_clock template Q J t (acquire t) A hW (hsize t) (hbounded t)
      _ = _ := by simp [Finset.sum_add_distrib]
  change (reconstruct template Q J acquire).clock≤_ at hs
  change (reconstruct template Q J acquire).clock≤_
  simp only [zero] at hs
  omega

/-- Copying an already exact-length packet preserves its complete coefficient array. -/
theorem packet_eq_decode (J : ℕ) (H : JetReport) (hsize : H.words.size=J) :
    SemiprimeAcquiredHermite.packet J (SemiprimeNativeGroupBits.toScalarRun H)=decode H.words := by
  apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
    (by simp [SemiprimeAcquiredHermite.packet]) (by simpa using hsize)
  intro k hk
  exact SemiprimeArrayOps.ofFn_coefficient _ k hk

/-- Semantic comparison to the existing acquired scalar consumer. Its work is
not substituted for any physical execution report. -/
theorem reconstruct_value_eq_acquired (template : List Bool) (b Q J d B : ℕ)
    (acquire : Fin Q → JetReport) (hJ : 0<J) (hd : 0<d)
    (hvalid : ∀ t,Valid (acquire t).words)
    (hrep : ∀ t,ArrayBound (decode (acquire t).words) J d B)
    (hdb : d≤2^b) (hBb : B≤2^b)
    (hw : SemiprimeHermiteWordWidth.width b Q J≤template.length)
    (hsize : ∀ t,(acquire t).words.size=J) :
    (reconstruct template Q J acquire).word.value=
      (SemiprimeAcquiredHermite.reconstruct Q J
        (fun t => SemiprimeNativeGroupBits.toScalarRun (acquire t))).value := by
  rw [(reconstruct_correct template b Q J d B acquire hJ hd hvalid hrep hdb hBb hw).1,
    SemiprimeAcquiredHermite.reconstruct_value]
  have he : (fun t : Fin Q => SemiprimeAcquiredHermite.packet J
      (SemiprimeNativeGroupBits.toScalarRun (acquire t)))=(fun t => decode (acquire t).words) := by
    funext t
    exact packet_eq_decode J (acquire t) (hsize t)
  rw [he]

end RiemannGaussian.SemiprimeAcquiredHermiteBits
