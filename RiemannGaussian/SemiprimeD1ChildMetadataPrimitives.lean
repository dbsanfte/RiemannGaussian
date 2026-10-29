/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildPortPullback
import RiemannGaussian.SemiprimeD1ReplayMetadataBounds

/-! # Literal physical metadata scan/copy report bounds
These are the actual frozen constructor recurrences, including failed reads and
filters. Native finite descriptor and owner-function evaluation remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1ChildMetadataPrimitives
open SemiprimeD1ChildGraph SemiprimeD1PacketInventory SemiprimeMaterializedWords
open SemiprimeSourceHistogramTrie SemiprimeBitArithmetic

/-- Total read of one actual coordinate never enlarges a stored byte payload. -/
theorem coordinate_length (row : List (List Bool)) (q R : ℕ)
    (hr : ∀x∈row,x.length ≤ R) : (readCoordinate row q).bits.length ≤ R := by
  rw [readCoordinate_bits]
  cases he : row[q]? with
  | none => simp
  | some x =>
    simpa only [he,Option.getD_some] using hr x (List.mem_of_getElem? he)

/-- Explicit physical read/two-borrow comparison allowance. -/
def colourBudget (q R G : ℕ) : ℕ := 4*q+3*R+40*(R+G+1)+8

/-- Actual physical colour test report, without a semantic colour answer. -/
theorem colour_work (target : List Bool) (q : ℕ) (row : List (List Bool)) (R G : ℕ)
    (hr : ∀x∈row,x.length ≤ R) (hg : target.length ≤ G) :
    (testColour target q row).work ≤ colourBudget q R G := by
  have hc:=readCoordinate_clock row q R hr
  have hl:=coordinate_length row q R hr
  have ho:=SemiprimeBitIndexClipping.leSignedBits_cost
    (left:=⟨false,(readCoordinate row q).bits⟩) (right:=⟨false,target⟩)
    (show (readCoordinate row q).bits.length ≤ R+G by omega)
    (show target.length ≤ R+G by omega)
  unfold testColour colourBudget
  dsimp only
  omega

/-- Literal pair-read plus two endpoint classification allowance. -/
def oneBudget (a q K R G : ℕ) : ℕ :=
  22*K+6*R+2*(a+1)*(6*R+8)+40+2*colourBudget q R G+20

/-- One original occurrence emits at most its two actual endpoints. -/
theorem one_length {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (arity e)) (p : Placement) :
    (one owner dict a q target i p).value.length ≤ 2 := by
  simp only [one,List.length_append]
  split_ifs <;> simp

/-- Actual source byte reads and classifications are all retained. -/
theorem one_work {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (arity e)) (p : Placement) (K R G : ℕ)
    (hk : p.source.length ≤ K) (hg : target.length ≤ G)
    (hr : ∀id,(stored dict.trie id).length ≤ R) :
    (one owner dict a q target i p).work ≤ oneBudget a q K R G := by
  let rows:=SemiprimeD1PacketRows.read dict a p.source
  have hread:=SemiprimeD1PacketRows.read_clock dict a p.source R (hr _) (hr _)
  have hleft : ∀x∈rows.left,x.length ≤ R := by
    intro x hx
    have hh:=SemiprimeD1PacketRows.parse_fields_bound a
      (SemiprimeSourceHistogramRows.readRow dict (SemiprimeSourceHistogramKeyBits.split p.source).first).bits x hx
    exact hh.trans (by simpa only [SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits] using hr _)
  have hright : ∀x∈rows.right,x.length ≤ R := by
    intro x hx
    have hh:=SemiprimeD1PacketRows.parse_fields_bound a
      (SemiprimeSourceHistogramRows.readRow dict (SemiprimeSourceHistogramKeyBits.split p.source).rest).bits x hx
    exact hh.trans (by simpa only [SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits] using hr _)
  change rows.clock ≤ _ at hread
  have hl:=colour_work target q rows.left R G hleft hg
  have hc:=colour_work target q rows.right R G hright hg
  change rows.clock+(testColour target q rows.left).work+(testColour target q rows.right).work+20 ≤ _
  unfold oneBudget
  omega

/-- Filtering endpoints keeps their actual packet/ID/slot payloads verbatim. -/
theorem one_payload {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (i : (e : Fin F)×Fin (arity e)) (p : Placement) (W : ℕ)
    (hp : p.packet.length ≤ W) (he : p.edge.length ≤ W) (hs : p.slot.length ≤ a) :
    ∀e∈(one owner dict a q target i p).value,
      e.packet.length ≤ W ∧ e.edge.length ≤ W ∧ e.slot.length ≤ a := by
  simp only [one]
  split_ifs <;> simp_all [endpoints]


/-- Actual endpoint count bound for the complete same-order occurrence scan. -/
theorem scan_length {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (xs : List (((e : Fin F)×Fin (arity e))×Placement)) :
    (scan owner dict a q target xs).value.length ≤ 2*xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have h:=one_length owner dict a q target x.1 x.2
    simp only [scan,List.length_append,List.length_cons]
    omega

/-- The frozen scan report pays every occurrence, append and endpoint header. -/
theorem scan_work {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (xs : List (((e : Fin F)×Fin (arity e))×Placement)) (K R G : ℕ)
    (hk : ∀x∈xs,x.2.source.length ≤ K) (hg : target.length ≤ G)
    (hr : ∀id,(stored dict.trie id).length ≤ R) :
    (scan owner dict a q target xs).work ≤ xs.length*(oneBudget a q K R G+8)+2 := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have hh:=one_work owner dict a q target x.1 x.2 K R G (hk x List.mem_cons_self) hg hr
    have hl:=one_length owner dict a q target x.1 x.2
    have ht:=ih (fun y hy=>hk y (List.mem_cons_of_mem x hy))
    simp only [scan,List.length_cons]
    nlinarith

/-- Endpoint payload bounds persist through every actual append in the scan. -/
theorem scan_payload {n F : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool)
    (xs : List (((e : Fin F)×Fin (arity e))×Placement)) (W : ℕ)
    (h : ∀x∈xs,x.2.packet.length ≤ W ∧ x.2.edge.length ≤ W ∧ x.2.slot.length ≤ a) :
    ∀e∈(scan owner dict a q target xs).value,
      e.packet.length ≤ W ∧ e.edge.length ≤ W ∧ e.slot.length ≤ a := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    intro e he
    change e∈(one owner dict a q target x.1 x.2).value++(scan owner dict a q target xs).value at he
    rcases List.mem_append.mp he with he|he
    · have hh:=h x List.mem_cons_self
      exact one_payload owner dict a q target x.1 x.2 W hh.1 hh.2.1 hh.2.2 e he
    · exact ih (fun y hy=>h y (List.mem_cons_of_mem x hy)) e he

/-- Literal filter traversal has no hidden constant-cost hash lookup. -/
theorem bucket_work {V : ℕ} (packet : List Bool) (es : List (Endpoint V)) (W : ℕ)
    (h : ∀e∈es,e.packet.length ≤ W) :
    (bucket packet es).work ≤ es.length*(6*W+9)+2 := by
  induction es with
  | nil => simp [bucket]
  | cons e es ih =>
    have hc:=equalBytes_work e.packet packet
    have hh:=h e List.mem_cons_self
    have ht:=ih (fun x hx=>h x (List.mem_cons_of_mem e hx))
    simp only [bucket,List.length_cons]
    nlinarith

/-- A literal bucket never creates an endpoint. -/
theorem bucket_length {V : ℕ} (packet : List Bool) (es : List (Endpoint V)) :
    (bucket packet es).value.length ≤ es.length := by
  induction es with
  | nil => simp [bucket]
  | cons e es ih =>
    simp only [bucket]
    split_ifs
    · simp only [List.length_cons];omega
    · simp only [List.length_cons];omega

/-- Every actual observed factor is paid, even when its bucket is empty. -/
theorem buckets_work {V : ℕ} (es : List (Endpoint V)) (packets : List (List Bool)) (W : ℕ)
    (h : ∀e∈es,e.packet.length ≤ W) :
    (buckets es packets).work ≤ packets.length*(es.length*(6*W+9)+6)+2 := by
  induction packets with
  | nil => simp [buckets]
  | cons p ps ih =>
    have hh:=bucket_work p es W h
    simp only [buckets,List.length_cons]
    nlinarith

/-- Cached factor flattening is bounded without a supplied partition/permutation. -/
theorem buckets_length {V : ℕ} (es : List (Endpoint V)) (packets : List (List Bool)) :
    (buckets es packets).value.flatten.length ≤ packets.length*es.length := by
  induction packets with
  | nil => simp [buckets]
  | cons p ps ih =>
    have hh:=bucket_length p es
    simp only [buckets,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeD1ChildMetadataPrimitives
