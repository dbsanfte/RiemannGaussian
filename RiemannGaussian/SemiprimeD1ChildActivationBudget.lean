/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalChildGraphBudget

/-! # Actual original-source activation byte reads and copies
Malformed branches are included. Original ID widths, counts and dictionary
payload bounds are derived from the acquired selector/bank, not supplied advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace RiemannGaussian.SemiprimeD1ChildActivationBudget
open SemiprimeD1ChildMetadataPrimitives SemiprimeD1ChildActivation
open SemiprimeD1OriginalChildGraphBudget SemiprimeMaterializedWords
open SemiprimeSourceHistogramTrie

/-- Original read/parse/physical comparison allowance for one selected byte ID. -/
def oneBudget (a q B R G : ℕ) : ℕ :=
  8*B+3*R+12+(a+1)*(6*R+8)+colourBudget q R G+5

/-- Literal single-row activation report, including parse rejection. -/
theorem readOne_work (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ)
    (target id : List Bool) (B R G : ℕ) (hid : id.length ≤ B) (hG : target.length ≤ G)
    (hrow : ∀key,(stored dict.trie key).length ≤ R) :
    (readOne dict a q target id).work ≤ oneBudget a q B R G := by
  let row:=SemiprimeSourceHistogramRows.readRow dict id
  let parsed:=SemiprimeD1PacketRows.parse a row.bits
  have hr : row.bits.length ≤ R := by
    simpa only [row,SemiprimeSourceHistogramRows.readRow,SemiprimeSourceHistogramTrie.lookup_bits] using hrow id
  have hc : row.clock ≤ 8*B+3*R+12 :=
    (SemiprimeSourceHistogramTrieBounds.lookup_clock dict.trie id R (hrow id)).trans (by omega)
  have hp : parsed.clock ≤ (a+1)*(6*R+8) :=
    (SemiprimeD1PacketRows.parse_clock a row.bits).trans (by gcongr)
  have hfields : ∀x∈parsed.fields,x.length ≤ R := fun x hx=>
    (SemiprimeD1PacketRows.parse_fields_bound a row.bits x hx).trans hr
  have htest:=colour_work target q parsed.fields R G hfields hG
  unfold readOne
  dsimp only
  split_ifs
  · change row.clock+parsed.clock+(SemiprimeD1ChildGraph.testColour target q parsed.fields).work+5 ≤ _
    unfold oneBudget
    omega
  · change row.clock+parsed.clock+3 ≤ _
    unfold oneBudget
    omega

/-- Every copied selected-ID byte and reversal cell is charged once. -/
theorem reverse_work (ids acc : List (List Bool)) (B : ℕ)
    (h : ∀id∈ids,id.length ≤ B) : (reverseFrom ids acc).work ≤ ids.length*(3*B+7)+2 := by
  induction ids generalizing acc with
  | nil => simp [reverseFrom]
  | cons id ids ih =>
    have hh:=h id List.mem_cons_self
    have ht:=ih ((SemiprimeSourceCompactBits.copy id).bits::acc) (fun x hx=>h x (List.mem_cons_of_mem id hx))
    simp only [reverseFrom,SemiprimeSourceCompactBits.copy_clock,List.length_cons]
    nlinarith

/-- Same-order activation scan retains every actual row predicate report. -/
theorem scan_clock (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ)
    (target : List Bool) (ids : List (List Bool)) (B R G : ℕ)
    (h : ∀id∈ids,id.length ≤ B) (hG : target.length ≤ G)
    (hrow : ∀key,(stored dict.trie key).length ≤ R) :
    (scan dict a q target ids).clock ≤ ids.length*(oneBudget a q B R G+4)+2 := by
  induction ids with
  | nil => simp [scan]
  | cons id ids ih =>
    have hh:=readOne_work dict a q target id B R G (h id List.mem_cons_self) hG hrow
    have ht:=ih (fun x hx=>h x (List.mem_cons_of_mem id hx))
    simp only [scan,List.length_cons]
    nlinarith

/-- Original selected byte-ID count includes every old vertex, even isolated ones. -/
theorem ids_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (source n F r a arity owner).padding.source.selection.ids.length=n+F :=
  SemiprimeD1IncidenceSearch.run_length n F r a arity owner

/-- Actual selected IDs belong to the acquired compact menu; no ID advice. -/
theorem ids_width (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    ∀id∈(source n F r a arity owner).padding.source.selection.ids,
      id.length ≤ Nat.clog 2 (r^a+1) := by
  intro id hid
  exact SemiprimeSourceCompactWordBank.ids_bounded r a id
    (SemiprimeD1IncidenceSearch.run_valid n F r a arity owner id hid)

/-- Fixed original-parameter overhead; no reacquired palette or truth table. -/
def overhead (n F r a : ℕ) : ℕ :=
  let B:=Nat.clog 2 (r^a+1)
  let R:=rowCap r a
  let G:=SemiprimeSourceHistogramPortKeys.keyWidth r
  SemiprimeSourceHistogramPortKeys.encodeBudget r+(n+F)*(3*B+7)+2+
    (n+F)*(oneBudget a a B R G+4)+2+(n+F)+8

/-- CLOSED original activation report retains its actual replay acquisition once. -/
theorem fromReplay_clock (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (q : Fin a) (g : Fin r) :
    (fromReplay (source n F r a arity owner) q g).clock ≤
      (source n F r a arity owner).state.clock+overhead n F r a := by
  let src:=source n F r a arity owner
  let target:=SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let ids:=reverseFrom src.padding.source.selection.ids []
  let dict:=src.padding.source.selection.cache.rows.source.dictionary
  let B:=Nat.clog 2 (r^a+1)
  have hi:=ids_width n F r a arity owner
  have hlen:=ids_length n F r a arity owner
  have hreverse:=reverse_work src.padding.source.selection.ids [] B hi
  rw [hlen] at hreverse
  have hids : ids.value=src.padding.source.selection.ids.reverse := by
    simp only [ids,reverseFrom_value,List.append_nil]
  have hscan:=scan_clock dict a q.val target.bits ids.value B (rowCap r a)
    (SemiprimeSourceHistogramPortKeys.keyWidth r) (by intro id hid;rw [hids,List.mem_reverse] at hid;exact hi id hid)
    (SemiprimeSourceHistogramPortKeys.encodeKey_length g.val r (by omega))
    (dictionary_width n F r a arity owner)
  have hidlen : ids.value.length=n+F := by rw [hids,List.length_reverse,hlen]
  rw [hidlen] at hscan
  have ht:=SemiprimeSourceHistogramPortKeys.encodeKey_clock g.val r (by omega)
  have hscan' : (scan dict a q.val target.bits ids.value).clock ≤
      (n+F)*(oneBudget a a B (rowCap r a) (SemiprimeSourceHistogramPortKeys.keyWidth r)+4)+2 := by
    refine hscan.trans ?_
    unfold oneBudget colourBudget
    gcongr
    exact Nat.le_of_lt q.isLt
  change src.state.clock+target.clock+ids.work+(scan dict a q.val target.bits ids.value).clock+
    src.padding.source.selection.ids.length+8 ≤ src.state.clock+overhead n F r a
  change ids.work ≤ _ at hreverse
  change target.clock ≤ _ at ht
  rw [hlen]
  change _ ≤ src.state.clock+(SemiprimeSourceHistogramPortKeys.encodeBudget r+
    (n+F)*(3*B+7)+2+(n+F)*(oneBudget a a B (rowCap r a)
      (SemiprimeSourceHistogramPortKeys.keyWidth r)+4)+2+(n+F)+8)
  omega

end RiemannGaussian.SemiprimeD1ChildActivationBudget
