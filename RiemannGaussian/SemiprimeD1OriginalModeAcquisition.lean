/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayBudget
import RiemannGaussian.SemiprimeD1PacketReplayCapacity
import RiemannGaussian.SemiprimeD1ModeRate

/-! # Original sparse packet acquisition followed by the actual D1 mode menu
No packet count, labels, catalogue or tuple list is an input. The actual sparse
replay supplies M and the observed packet count, and D.11 supplies the precision.
Arithmetic mode factors and the recursive contraction/recovery remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OriginalModeAcquisition
open SemiprimeD1CollisionOriginal

/-- Original sparse packets and their acquired positive-weight mode tuples. -/
structure Acquired (n F a : ℕ) (arity : Fin F→ℕ) where
  /-- Single original selector/physical-padding/read/replay acquisition. -/
  packets : SemiprimeD1PacketReplayOriginal.Acquired n F a arity
  /-- Actual D.11 working precision at this node. -/
  precision : ℕ
  /-- Cached catalogue and actually enumerated weighted tuples/report. -/
  modes : SemiprimeD1WeightedTuples.Report
  /-- Both actual producer reports plus finite parameter/list-control stages. -/
  work : ℕ

/-- Acquire the sparse inventory once, then enumerate its actual padded tile modes. -/
def acquire (n F r a u i p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Acquired n F a arity :=
  let packets := SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner
  let M := packets.placements.length
  let count := packets.state.packets.length
  let precision := SemiprimeD1ModeRate.workingPrecision M u a i p
  let modes := SemiprimeD1ModeCatalog.acquireModes count (2^(i+1)) (precision-1)
  ⟨packets,precision,modes,packets.state.clock+modes.work+M+count+a+i+u+p+20⟩

/-- M is the actual original incidence count, including every parallel occurrence. -/
theorem original_size (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length=
      (ports n F a arity).length := by
  have h := congrArg List.length (SemiprimeD1PacketReplayOriginal.sources n F r a arity owner)
  rw [List.length_map,SemiprimeD1IncidenceAcquisition.keys_original,List.length_map] at h
  exact h

/-- The actual precision uses the original real-port count, not an advised M. -/
theorem precision_original (n F r a u i p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a u i p arity owner).precision=
      SemiprimeD1ModeRate.workingPrecision (ports n F a arity).length u a i p := by
  change SemiprimeD1ModeRate.workingPrecision _ _ _ _ _=_
  rw [original_size]

/-- The exact acquired tuple list is the actual mode catalogue execution. -/
theorem modes_original (n F r a u i p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (acquire n F r a u i p arity owner).modes=
      SemiprimeD1ModeCatalog.acquireModes
        (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length
        (2^(i+1)) (SemiprimeD1ModeRate.modeBudget (ports n F a arity).length u a i p) := by
  unfold acquire SemiprimeD1ModeRate.modeBudget
  dsimp only
  rw [original_size]

/-- Exact admissibility and absence of duplicate tuples for the executed menu. -/
theorem modes_correct (n F r a u i p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (es : List ℕ) :
    let count := (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length
    let P := SemiprimeD1ModeRate.modeBudget (ports n F a arity).length u a i p
    (es∈(acquire n F r a u i p arity owner).modes.values ↔
      SemiprimeD1WeightedTuples.Admissible
        (SemiprimeD1ModeCatalog.weights (count*2^(i+1)) P) es P) ∧
    (acquire n F r a u i p arity owner).modes.values.Nodup := by
  dsimp only
  rw [modes_original]
  exact SemiprimeD1ModeCatalog.acquireModes_correct _ _ _ es

/-- Both real original producers' reports are retained, not equated to old reports. -/
theorem retains_packets (n F r a u i p : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.clock≤
      (acquire n F r a u i p arity owner).work := by
  unfold acquire
  dsimp only
  omega

/-- The actually acquired original packet menu has the D1 node exponent. -/
theorem menu_bound (n F r a u i p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ e∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun e => (owner e).val)
        (ports n F a arity) (owner e).val≤Δ)
    (hf : ∀ e∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun e => n+e.1.val)
        (ports n F a arity) (n+e.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (hsize : r^(2*a)*2^a≤(ports n F a arity).length)
    (hi : i≤a) (hu0 : 0<u) (hu : u≤(ports n F a arity).length)
    (hp : p*u≤(ports n F a arity).length*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    (((acquire n F r a u i p arity owner).modes.values.length):ℝ)≤
      Real.exp (48*((ports n F a arity).length:ℝ)/Real.sqrt (u:ℝ)) := by
  rw [modes_original]
  exact SemiprimeD1ModeRate.menu_bound _ _ u a i p hi hu0 hu
    (SemiprimeD1PacketReplayCapacity.threeM_capacity n F r a arity owner Δ ho hf hsmall hsize) hp ha

/-- The entire actual acquisition/enumeration report keeps the original node
exponent, with explicit retained original setup and catalogue overhead. -/
theorem work_bound (n F r a u i p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ e∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun e => (owner e).val)
        (ports n F a arity) (owner e).val≤Δ)
    (hf : ∀ e∈ports n F a arity,
      SemiprimeSourceHistogramGrouping.multiplicity (fun e => n+e.1.val)
        (ports n F a arity) (n+e.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (hsize : r^(2*a)*2^a≤(ports n F a arity).length)
    (hi : i≤a) (hu0 : 0<u) (hu : u≤(ports n F a arity).length)
    (hp : p*u≤(ports n F a arity).length*2^(a-i)) (ha : (a+1)*u≤2^(a-i)) :
    let count := (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.packets.length
    let M := (ports n F a arity).length
    let P := SemiprimeD1ModeRate.modeBudget M u a i p
    ((acquire n F r a u i p arity owner).work:ℝ)≤
      (SemiprimeD1PacketReplayBudget.budget n F r a M+M+count+a+i+u+p+20:ℕ)+
      (SemiprimeD1WeightedCardinality.modeFactor (count*2^(i+1)) P:ℝ)*
        Real.exp (48*(M:ℝ)/Real.sqrt (u:ℝ))+
      (SemiprimeD1WeightedCardinality.modeOverhead (count*2^(i+1)) P:ℝ) := by
  dsimp only
  have hm := SemiprimeD1PacketReplayCapacity.threeM_capacity n F r a arity owner Δ ho hf hsmall hsize
  have he := SemiprimeD1ModeRate.work_bound _ _ u a i p hi hu0 hu hm hp ha
  have hs := SemiprimeD1PacketReplayBudget.acquire_work n F r a arity owner
  have hM : (ports n F a arity).length=∑e,arity e :=
    (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.1
  rw [←hM] at hs
  have hs' := (Nat.cast_le (α:=ℝ)).mpr hs
  unfold acquire
  dsimp only
  rw [original_size]
  simp only [SemiprimeD1ModeRate.modeBudget] at he ⊢
  push_cast
  linarith

end RiemannGaussian.SemiprimeD1OriginalModeAcquisition
