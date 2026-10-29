/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildGraphInterface

/-! # Physical activation reads for every retained old vertex
The selected-ID prefix is physically copied into original vertex order. Every
old vertex, including isolated ones, receives an actual dictionary/row/colour
read. No tensor truth callback or semantic Word getter enters execution.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1ChildActivation
open SemiprimeMaterializedWords
open SemiprimeSourceCompactBits (Report)

/-- Reverse-copy actual selected ID payloads, paying each byte and list stage. -/
def reverseFrom : List (List Bool)→List (List Bool)→Run (List (List Bool))
  | [],acc => ⟨acc,2⟩
  | id::ids,acc =>
    let copied := SemiprimeSourceCompactBits.copy id
    let out := reverseFrom ids (copied.bits::acc)
    ⟨out.value,copied.clock+out.work+6⟩

/-- The physical copy changes no selected ID or its original vertex order. -/
theorem reverseFrom_value (ids acc : List (List Bool)) :
    (reverseFrom ids acc).value=ids.reverse++acc := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
    simp only [reverseFrom,ih,SemiprimeSourceCompactBits.copy_bits,List.reverse_cons,List.append_assoc,
      List.singleton_append]

/-- Read one old vertex's actual selected row, rejecting malformed row payloads. -/
def readOne (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ)
    (target id : List Bool) : Run Bool :=
  let row := SemiprimeSourceHistogramRows.readRow dict id
  let parsed := SemiprimeD1PacketRows.parse a row.bits
  if parsed.valid then
    let out := SemiprimeD1ChildGraph.testColour target q parsed.fields
    ⟨out.value,row.clock+parsed.clock+out.work+5⟩
  else ⟨false,row.clock+parsed.clock+3⟩

/-- Acquire all old-vertex activation bits in their original numeric order. -/
def scan (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ) (target : List Bool) :
    List (List Bool)→Report
  | [] => ⟨[],2⟩
  | id::ids =>
    let here := readOne dict a q target id
    let tail := scan dict a q target ids
    ⟨here.value::tail.bits,here.work+tail.clock+4⟩

/-- Exact one-read-per-ID semantics of the physical activation loop. -/
theorem scan_bits (dict : SemiprimeSourceHistogramRows.Dictionary) (a q : ℕ)
    (target : List Bool) (ids : List (List Bool)) :
    (scan dict a q target ids).bits=ids.map (fun id => (readOne dict a q target id).value) := by
  induction ids with
  | nil => rfl
  | cons id ids ih => simp only [scan,ih,List.map_cons]

/-- Reuse the retained selection/row cache; do not select or acquire a word bank again. -/
def fromReplay {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) : Report :=
  let target := SemiprimeSourceHistogramPortKeys.encodeKey g.val
  let ids := reverseFrom source.padding.source.selection.ids []
  let out := scan source.padding.source.selection.cache.rows.source.dictionary a q.val target.bits ids.value
  ⟨out.bits,source.state.clock+target.clock+ids.work+out.clock+source.padding.source.selection.ids.length+8⟩

/-- The actual activation data path is precisely the reverse-ID row read loop. -/
theorem fromReplay_bits {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    (fromReplay source q g).bits=source.padding.source.selection.ids.reverse.map
      (fun id => (readOne source.padding.source.selection.cache.rows.source.dictionary a q.val
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits id).value) := by
  simp only [fromReplay,scan_bits,reverseFrom_value,List.append_nil]

/-- Original-input convenience endpoint, without supplied selected IDs or masks. -/
def acquire (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) : Report :=
  fromReplay (SemiprimeD1PacketReplayOriginal.acquire n F r a inputArity inputOwner) q g

/-- All parent acquisition and actual activation reports remain retained. -/
theorem retains {n F a r : ℕ} {inputArity : Fin F→ℕ}
    (source : SemiprimeD1PacketReplayOriginal.Acquired n F a inputArity) (q : Fin a) (g : Fin r) :
    source.state.clock≤(fromReplay source q g).clock := by
  unfold fromReplay
  dsimp only
  omega

end RiemannGaussian.SemiprimeD1ChildActivation
