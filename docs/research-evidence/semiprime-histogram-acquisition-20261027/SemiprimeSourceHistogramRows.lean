/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramTrieStore
import RiemannGaussian.SemiprimeSourceHistogramKeyBits
import RiemannGaussian.SemiprimeSourceCompactWordBank

/-! # Acquired physical candidate-row dictionary
Every colour magnitude is physically trimmed and framed once. The dictionary
copies the actual encoded row at its acquired compact candidate ID. Native
persistent references and host list/control stages remain explicit boundaries.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramRows
open SemiprimeRationalBits SemiprimeBitArithmetic SemiprimeSourceHistogramTrie
open SemiprimeSourceCompactBits (Report)
/-- Actual acquired physical coordinate row. -/
abbrev Row := List RationalWord

/-- Proof-side byte layout of a physical row, without rational interpretation. -/
def layout : Row → List Bool
  | [] => []
  | x::xs => SemiprimeSourceHistogramKeyBits.frame
      (SemiprimeSourceCompactBits.trim x.numerator.magnitude).bits (layout xs)

/-- Acquire compact colour fields solely from actual numerator magnitudes. -/
def encodeRow : Row → Report
  | [] => ⟨[],1⟩
  | x::xs =>
    let tail := encodeRow xs
    let colour := SemiprimeSourceCompactBits.trim x.numerator.magnitude
    let joined := SemiprimeSourceHistogramKeyBits.pair colour.bits tail.bits
    ⟨joined.bits,tail.clock+colour.clock+joined.clock+6⟩

/-- Executed bytes equal the complete framed physical-row layout. -/
theorem encodeRow_bits (row : Row) : (encodeRow row).bits=layout row := by
  induction row with
  | nil => rfl
  | cons x xs ih => simp only [encodeRow,layout,SemiprimeSourceHistogramKeyBits.pair_bits,ih]

/-- Every original bounded magnitude gives a linear encoded-row payload bound. -/
theorem layout_length (row : Row) (B : ℕ)
    (hb : ∀ x ∈ row, x.numerator.magnitude.length ≤ B) :
    (layout row).length ≤ row.length*(2*B+1) := by
  induction row with
  | nil => simp [layout]
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    have hc := SemiprimeSourceCompactBits.trim_length x.numerator.magnitude
    simp only [layout,SemiprimeSourceHistogramKeyBits.frame_length,List.length_cons]
    nlinarith

/-- Actual trim, frame, list and cell work is linear in original row payload. -/
theorem encodeRow_clock (row : Row) (B : ℕ)
    (hb : ∀ x ∈ row, x.numerator.magnitude.length ≤ B) :
    (encodeRow row).clock ≤ row.length*(12*B+10)+1 := by
  induction row with
  | nil => simp [encodeRow]
  | cons x xs ih =>
    have hx := hb x (by simp)
    have ht := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    have hc := SemiprimeSourceCompactBits.trim_length x.numerator.magnitude
    simp only [encodeRow,SemiprimeSourceCompactBits.trim_clock,
      SemiprimeSourceHistogramKeyBits.pair_clock,List.length_cons]
    nlinarith

/-- Actual cached paired-list acquisition, including every emitted pair cell. -/
def zipRows : List (List Bool) → List Row → SemiprimeMaterializedWords.Run
    (List (List Bool × Row))
  | id::ids,row::rows =>
    let tail := zipRows ids rows
    ⟨(id,row)::tail.value,tail.work+4⟩
  | _,_ => ⟨[],1⟩

/-- No list-order or reindexing assumption hides in paired-list acquisition. -/
theorem zipRows_value (ids : List (List Bool)) (rows : List Row) :
    (zipRows ids rows).value=ids.zip rows := by
  induction ids generalizing rows with
  | nil => cases rows <;> rfl
  | cons id ids ih => cases rows with
    | nil => rfl
    | cons row rows => simp only [zipRows,List.zip_cons_cons,ih]

/-- The actual zip traversal pays once per emitted cell. -/
theorem zipRows_clock (ids : List (List Bool)) (rows : List Row) :
    (zipRows ids rows).work=4*(ids.zip rows).length+1 := by
  induction ids generalizing rows with
  | nil => cases rows <;> rfl
  | cons id ids ih => cases rows with
    | nil => rfl
    | cons row rows => simp only [zipRows,List.zip_cons_cons,List.length_cons,ih];omega

/-- Physical acquired row dictionary and retained construction report. -/
structure Dictionary where
  /-- Actual persistent Boolean-key dictionary. -/
  trie : Trie
  /-- All row encoding, insertion and original acquisition stages. -/
  clock : ℕ

/-- Every supplied pair is encoded once and inserted once, in literal order. -/
def build : List (List Bool × Row) → Dictionary
  | [] => ⟨.empty,1⟩
  | (id,row)::rest =>
    let tail := build rest
    let encoded := encodeRow row
    let out := SemiprimeSourceHistogramTrieStore.put tail.trie id encoded.bits
    ⟨out.trie,tail.clock+encoded.clock+out.clock+6⟩

/-- Actual bank dictionary construction retains its bank acquisition report. -/
def acquire (r Q : ℕ) : Dictionary :=
  let bank := SemiprimeSourceCompactWordBank.acquire r Q
  let paired := zipRows bank.ids bank.rows
  let out := build paired.value
  ⟨out.trie,bank.clock+paired.work+out.clock+4⟩

/-- Original bank and its actual row dictionary acquired in one shared scope. -/
structure Cached where
  /-- The same acquired original physical rows and candidate IDs. -/
  bank : SemiprimeSourceWordBank.Bank
  /-- Dictionary with original bank acquisition already included in its report. -/
  dictionary : Dictionary

/-- Acquire the bank once and retain it for candidate/prefix selection. -/
def acquireWithBank (r Q : ℕ) : Cached :=
  let bank := SemiprimeSourceCompactWordBank.acquire r Q
  let paired := zipRows bank.ids bank.rows
  let out := build paired.value
  ⟨bank,⟨out.trie,bank.clock+paired.work+out.clock+4⟩⟩

/-- Retaining the actual bank does not change dictionary data or its paid report. -/
theorem acquireWithBank_dictionary (r Q : ℕ) :
    (acquireWithBank r Q).dictionary=acquire r Q := rfl

/-- The retained candidate menu is the actual single acquired compact bank. -/
theorem acquireWithBank_bank (r Q : ℕ) :
    (acquireWithBank r Q).bank=SemiprimeSourceCompactWordBank.acquire r Q := rfl

/-- Read the physical selected payload by the actual trie path and copy. -/
def readRow (dict : Dictionary) (id : List Bool) : Report := lookup dict.trie id

/-- Literal first-match specification, used only to prove the constructed map. -/
def expected : List (List Bool × Row) → List Bool → List Bool
  | [],_ => []
  | (id,row)::rest,key => if key=id then layout row else expected rest key

/-- The actual insertion sequence gives exact literal first-match byte semantics. -/
theorem build_stored (pairs : List (List Bool × Row)) (key : List Bool) :
    stored (build pairs).trie key=expected pairs key := by
  induction pairs with
  | nil => simp [build,stored_empty,expected]
  | cons p ps ih =>
    rcases p with ⟨id,row⟩
    simp only [build,SemiprimeSourceHistogramTrieStore.put_stored,expected,encodeRow_bits,ih]

/-- No duplicated acquired ID can shadow another original row. -/
theorem expected_mem (pairs : List (List Bool × Row)) (id : List Bool) (row : Row)
    (hn : (pairs.map Prod.fst).Nodup) (hm : (id,row) ∈ pairs) :
    expected pairs id=layout row := by
  induction pairs with
  | nil => simp at hm
  | cons p ps ih =>
    rcases p with ⟨key,value⟩
    simp only [List.map_cons,List.nodup_cons] at hn
    rcases List.mem_cons.mp hm with h|h
    · cases h; simp only [expected,ite_true]
    · have hk : id≠key := by
        intro he
        apply hn.1
        exact List.mem_map.mpr ⟨(id,row),h,he⟩
      simp only [expected,hk,ite_false]
      exact ih hn.2 h

/-- Physical dictionary lookup for any actual original paired row. -/
theorem build_lookup (pairs : List (List Bool × Row)) (id : List Bool) (row : Row)
    (hn : (pairs.map Prod.fst).Nodup) (hm : (id,row) ∈ pairs) :
    (readRow (build pairs) id).bits=(encodeRow row).bits := by
  rw [readRow,lookup_bits,build_stored,expected_mem pairs id row hn hm,encodeRow_bits]

/-- Original acquired paired rows have distinct dictionary keys. -/
theorem original_nodup (r Q : ℕ) :
    (((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows).map Prod.fst).Nodup := by
  rw [List.map_fst_zip (SemiprimeSourceCompactWordBank.ids_length r Q).le]
  exact SemiprimeSourceCompactWordBank.ids_nodup r Q

/-- Each actual acquired ID is paired with its physically indexed original row. -/
theorem original_pair (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (id,(SemiprimeSourceWordBank.readRow
      (SemiprimeSourceCompactWordBank.acquire r Q) id).value) ∈
      (SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
        (SemiprimeSourceCompactWordBank.acquire r Q).rows := by
  obtain ⟨i,hil,he⟩ := List.mem_iff_getElem.mp hi
  have hv := congrArg (fun xs : List ℕ => xs[i]?)
    (SemiprimeSourceCompactWordBank.ids_values r Q)
  rw [List.getElem?_map,List.getElem?_eq_getElem hil,Option.map_some,he] at hv
  have hrange : i < (List.range (r^Q)).length := by
    simpa only [List.length_range,SemiprimeSourceCompactWordBank.ids_length,
      SemiprimeSourceCompactWordBank.acquire_length] using hil
  rw [List.getElem?_eq_getElem hrange,List.getElem_range,Option.some.injEq] at hv
  have hir : i < (SemiprimeSourceCompactWordBank.acquire r Q).rows.length := by
    rwa [← SemiprimeSourceCompactWordBank.ids_length r Q]
  have hiz : i < ((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows).length := by
    rw [List.length_zip]; exact lt_min hil hir
  have hm := List.getElem_mem hiz
  rw [List.getElem_zip,he] at hm
  simpa only [SemiprimeSourceWordBank.readRow_value,hv,
    List.getElem?_eq_getElem hir,Option.getD_some] using hm

/-- Actual original-input lookup equals the encoded actual physical bank row.
The old linear bank read appears ONLY in this semantic theorem. -/
theorem lookup_original (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (readRow (acquire r Q) id).bits =
      (encodeRow (SemiprimeSourceWordBank.readRow
        (SemiprimeSourceCompactWordBank.acquire r Q) id).value).bits := by
  change (readRow (build (zipRows _ _).value) id).bits = _
  rw [zipRows_value]
  exact build_lookup _ _ _ (original_nodup r Q) (original_pair r Q id hi)

end RiemannGaussian.SemiprimeSourceHistogramRows
