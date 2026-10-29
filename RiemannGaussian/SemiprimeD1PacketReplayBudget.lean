/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketReplayOriginal
import RiemannGaussian.SemiprimeD1OrientationBounds
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Actual sparse replay report budget
Reached counter widths are derived from actual prefix counts and compactness.
The final original-input endpoint supplies neither row answers nor Fits advice.
This bounds retained primitive/list reports, not a complete tape/address machine.
-/
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace RiemannGaussian.SemiprimeD1PacketReplayBudget
open SemiprimeD1PacketInventory SemiprimeSourceHistogramTrie
open SemiprimeSourceHistogramTrieBounds SemiprimeBitArithmetic

/-- Coarse packet-key bound from the actual parsed rows and class counter width. -/
def packetLength (a R C : ℕ) : ℕ := a*(6*R+3)+C

/-- Sum of the literal primitive bounds in one executed replay step. -/
def stepBudget (a K R C : ℕ) : ℕ :=
  let P := packetLength a R C
  (20*K+30*(C+1)+30)+(22*K+6*R+2*(a+1)*(6*R+8)+40)+
    (100*a*(R+1)+3*C+4)+(20*(C+1)+10)+(6*P+3)+
    (20*(2*P+a+1)+3*C+21)+(8*P+3+12)+(20*P+3+21)+(3*P+1)+25

/-- Every physical orientation slot uses at most one bit per original row field. -/
theorem slots_length (left right : List (List Bool)) (j : List Bool) :
    (SemiprimeD1OrientationBits.acquire left right j).slots.length≤left.length := by
  induction left generalizing right j with
  | nil => cases right <;> simp [SemiprimeD1OrientationBits.acquire]
  | cons x xs ih =>
    cases right with
    | nil => simp [SemiprimeD1OrientationBits.acquire]
    | cons y ys =>
      simpa only [SemiprimeD1OrientationBits.acquire,List.length_cons,Nat.add_le_add_iff_right]
        using ih ys (SemiprimeD1OrientationBits.coordinate x y j).next

/-- A compact original counter of value at most M fits the derived update width. -/
theorem counter_length (bits : List Bool) (M : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hv : bitValue bits≤M) :
    bits.length≤clockWidth M := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ hc
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+2)
  change bitValue bits<2^(Nat.clog 2 (M+2))
  omega

/-- A single actual step, with all widths derived from literal state invariants. -/
theorem step_work (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (state : State) (key : List Bool) (K R M : ℕ)
    (hk : key.length≤K) (hrow : ∀ id,(stored dict.trie id).length≤R)
    (hc : CompactCounters state.classes) (hv : CountCap state.classes M)
    (hn : SemiprimeSourceCompactBits.Compact state.next) (hnext : bitValue state.next≤M)
    (hseen : SeenGood state) :
    (step dict a state key).2.clock≤ state.clock+stepBudget a K R (clockWidth M) := by
  let changed := bump state.classes key
  let rows := SemiprimeD1PacketRows.read dict a key
  let out := SemiprimeD1OrientationBits.acquire rows.left rows.right changed.old
  let C := clockWidth M
  let P := packetLength a R C
  have hj : changed.old.length≤C := by
    rw [show changed.old=stored state.classes key from bump_old _ _]
    exact stored_clockWidth _ _ _ hc (hv key)
  have hnextlen := counter_length state.next M hn hnext
  have hidlen := SemiprimeSourceCompactBits.increment_length state.next M hnext
  have hlraw : (SemiprimeSourceHistogramRows.readRow dict
      (SemiprimeSourceHistogramKeyBits.split key).first).bits.length≤R := by
    simpa only [SemiprimeSourceHistogramRows.readRow,lookup_bits] using
      hrow (SemiprimeSourceHistogramKeyBits.split key).first
  have hrraw : (SemiprimeSourceHistogramRows.readRow dict
      (SemiprimeSourceHistogramKeyBits.split key).rest).bits.length≤R := by
    simpa only [SemiprimeSourceHistogramRows.readRow,lookup_bits] using
      hrow (SemiprimeSourceHistogramKeyBits.split key).rest
  have hll : rows.left.length≤a := SemiprimeD1PacketRows.parse_length _ _
  have hrl : rows.right.length≤a := SemiprimeD1PacketRows.parse_length _ _
  have hl : ∀ x∈rows.left,x.length≤R := by
    intro x hx
    exact le_trans (SemiprimeD1PacketRows.parse_fields_bound _ _ x hx) hlraw
  have hr : ∀ x∈rows.right,x.length≤R := by
    intro x hx
    exact le_trans (SemiprimeD1PacketRows.parse_fields_bound _ _ x hx) hrraw
  have hp : out.key.length≤P := by
    have h := SemiprimeD1OrientationBounds.acquire_key_length rows.left rows.right changed.old R hl hr
    dsimp only [P,packetLength]
    nlinarith
  have hs : out.slots.length≤a := (slots_length rows.left rows.right changed.old).trans hll
  have hmarker : (stored state.seen out.key).length≤1 := by
    rw [hseen.2]
    split_ifs <;> simp
  have hb := bump_clock_of_count state.classes key M hc (hv key)
  have hrclock := SemiprimeD1PacketRows.read_clock dict a key R (hrow _) (hrow _)
  have hoclock := SemiprimeD1OrientationBounds.acquire_clock rows.left rows.right changed.old R hl hr
  have hiclock := SemiprimeSourceCompactBits.increment_clock state.next C (clockWidth_pos M) hnextlen
  have haddr := SemiprimeSourceHistogramKeyBits.pair_clock out.key out.slots
  have haddrlen := SemiprimeSourceHistogramKeyBits.frame_length out.key out.slots
  have hwrite := SemiprimeSourceHistogramTrieStore.put_clock state.slots
    (SemiprimeSourceHistogramKeyBits.pair out.key out.slots).bits
    (SemiprimeSourceCompactBits.increment state.next).bits
  rw [SemiprimeSourceHistogramKeyBits.pair_bits,haddrlen] at hwrite
  have hlookup := lookup_clock state.seen out.key 1 hmarker
  have hmark := SemiprimeSourceHistogramTrieStore.put_clock state.seen out.key [true]
  have hcopy := SemiprimeSourceCompactBits.copy_clock out.key
  have hb' : changed.clock≤20*K+30*(C+1)+30 := hb.trans (by gcongr)
  have hr' : rows.clock≤22*K+6*R+2*(a+1)*(6*R+8)+40 := hrclock.trans (by gcongr)
  have ho' : out.clock≤100*a*(R+1)+3*C+4 := hoclock.trans (by gcongr)
  have ha' : (SemiprimeSourceHistogramKeyBits.pair out.key out.slots).clock≤6*P+3 := by
    rw [haddr]
    gcongr
  have hw' : (SemiprimeSourceHistogramTrieStore.put state.slots
      (SemiprimeSourceHistogramKeyBits.pair out.key out.slots).bits
      (SemiprimeSourceCompactBits.increment state.next).bits).clock≤20*(2*P+a+1)+3*C+21 := by
    rw [SemiprimeSourceHistogramKeyBits.pair_bits]
    apply hwrite.trans
    change _≤20*(2*P+a+1)+3*(Nat.clog 2 (M+2))+21
    gcongr
  have hl' : (lookup state.seen out.key).clock≤8*P+3+12 := hlookup.trans (by gcongr)
  have hm' : (SemiprimeSourceHistogramTrieStore.put state.seen out.key [true]).clock≤20*P+3+21 := by
    apply hmark.trans
    simp only [List.length_cons,List.length_nil]
    gcongr
  have hco' : (SemiprimeSourceCompactBits.copy out.key).clock≤3*P+1 := by
    rw [hcopy]
    gcongr
  change state.clock+changed.clock+rows.clock+out.clock+_+_+_+_+_+_+25≤_
  dsimp only [stepBudget]
  dsimp only [P,C] at hb' hr' ho' ha' hw' hl' hm' hco' hiclock
  dsimp only [changed,rows,out] at hb' hr' ho' ha' hw' hl' hm' hco' ⊢
  omega

/-- Prefix-count induction pays every reached original replay step. -/
theorem replay_work (dict : SemiprimeSourceHistogramRows.Dictionary) (a : ℕ)
    (keys : List (List Bool)) (state : State) (K R M spent : ℕ)
    (hk : ∀ key∈keys,key.length≤K) (hrow : ∀ id,(stored dict.trie id).length≤R)
    (hc : CompactCounters state.classes) (hv : CountCap state.classes spent)
    (hn : SemiprimeSourceCompactBits.Compact state.next) (hnext : bitValue state.next≤ spent)
    (hseen : SeenGood state) (hroom : spent+keys.length≤M) :
    (replay dict a keys state).2.clock≤ state.clock+keys.length*stepBudget a K R (clockWidth M) := by
  induction keys generalizing state spent with
  | nil => simp only [replay,List.length_nil,Nat.zero_mul,Nat.add_zero,Nat.le_refl]
  | cons key keys ih =>
    have hspent : spent≤M := by simp only [List.length_cons] at hroom;omega
    have hb := step_work dict a state key K R M (hk key List.mem_cons_self) hrow hc
      (fun query => (hv query).trans hspent) hn (hnext.trans hspent) hseen
    have hcap : CountCap (step dict a state key).2.classes (spent+1) := by
      intro query
      rw [step_frequency]
      split_ifs <;> have hh := hv query <;> omega
    have hnext' : bitValue (step dict a state key).2.next≤ spent+1 := by
      change bitValue (SemiprimeSourceCompactBits.increment state.next).bits≤_
      rw [SemiprimeSourceCompactBits.increment_value]
      omega
    have hroom' : spent+1+keys.length≤M := by
      simp only [List.length_cons] at hroom
      omega
    have ht := ih (step dict a state key).2 (spent+1)
      (fun q hq => hk q (List.mem_cons_of_mem _ hq))
      (bump_compact state.classes key hc) hcap
      (SemiprimeSourceCompactBits.increment_compact state.next) hnext'
      (step_seen dict a state key hseen) hroom'
    change (replay dict a keys (step dict a state key).2).2.clock≤_
    simp only [List.length_cons]
    nlinarith

/-- Actual original-input report budget; bank size enters through the original
already-paid selector/padding report, never an advised catalogue. -/
def budget (n F r a M : ℕ) : ℕ :=
  SemiprimeD1PacketPadding.budget n F r a M+2+
    M*stepBudget a (3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1)
      (a*(2*(r+1)+1)) (clockWidth M)

/-- Actual complete replay report is bounded using original dimensions alone. -/
theorem acquire_work (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).state.clock≤budget n F r a (∑e,arity e) := by
  let padding := SemiprimeD1PacketPadding.acquire n F r a arity owner
  let dict := padding.source.selection.cache.rows.source.dictionary
  let K := 3*SemiprimeSourceHistogramFeatureBitsBounds.width (n+F) (r^a)+1
  let R := a*(2*(r+1)+1)
  let M := ∑e,arity e
  have hk := SemiprimeD1IncidenceAcquisitionBounds.key_length n F r a arity owner
  have hlen := SemiprimeD1IncidenceAcquisitionBounds.keys_length n F r a arity owner
  have hd : dict=SemiprimeSourceHistogramRows.acquire r a := rfl
  have hrow : ∀ id,(stored dict.trie id).length≤R := by
    intro id
    rw [hd]
    exact SemiprimeSourceHistogramRowsBounds.acquire_width r a id
  have hi := replay_work dict a padding.source.keys (initial padding.clock) K R M 0 hk hrow
    empty_compact (by intro key; simp only [initial,value,stored_empty,bitValue,Nat.le_refl])
    (by trivial) (by rfl) (initial_seen _)
    (by change 0+(SemiprimeD1IncidenceAcquisition.acquire n F r a arity owner).keys.length≤∑e,arity e
        simpa only [Nat.zero_add] using hlen.le)
  have hp := SemiprimeD1PacketPadding.acquire_clock n F r a arity owner
  change _≤padding.clock+2+padding.source.keys.length*stepBudget a K R (clockWidth M) at hi
  change _≤budget n F r a M
  dsimp only [budget]
  change padding.clock≤_ at hp
  change padding.source.keys.length=M at hlen
  rw [hlen] at hi
  dsimp only [K,R,M] at hi hp ⊢
  exact hi.trans (by omega)

/-- Only fixed additions and multiplications occur in the replay-step envelope. -/
theorem stepBudget_mono {a K R C a' K' R' C' : ℕ}
    (ha : a≤a') (hK : K≤K') (hR : R≤R') (hC : C≤C') :
    stepBudget a K R C≤ stepBudget a' K' R' C' := by
  unfold stepBudget packetLength
  dsimp only
  gcongr

/-- Fixed witnesses precede the entire resource family; no report is assumed. -/
theorem stepBudget_monomial : SemiprimeReportPolynomialGrowth.Bound
    (fun S => stepBudget S S S S) := by
  unfold stepBudget packetLength
  dsimp only
  open SemiprimeReportPolynomialGrowth in
    boundArithmetic

end RiemannGaussian.SemiprimeD1PacketReplayBudget
