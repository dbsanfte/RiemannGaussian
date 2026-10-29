import RiemannGaussian.SemiprimeD1BoundaryRecordsSort

/-! # Exact sequential boundary lookup and literal local-table catalogues

The source remains the concrete monotone merge in BoundaryRecords. These
theorems justify its repeated-request cursor and byte-exact multiplication.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsLookup
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsOrder
open SemiprimeD1BoundaryRecordsSort
open SemiprimeD1JetAxes (Context)

/-- The serialized local table lists every false-first assignment and original payload. -/
theorem tableEntries_catalogue {n : ℕ} (table : SemiprimeD1TensorTables.Table n) :
    (tableEntries table).value = (assignments n).value.map (fun bits =>
      (⟨bits, (SemiprimeD1TensorTables.lookup table bits).words⟩ : Entry)) := by
  induction table with
  | leaf ws => simp [tableEntries, assignments, SemiprimeD1TensorTables.lookup,
      SemiprimeD1JetAxes.copyVector_value]
  | fork low high ihlow ihhigh =>
    simp [tableEntries, assignments, ihlow, ihhigh, List.map_append, List.map_map, Function.comp_def,
      SemiprimeD1TensorTables.lookup]

/-- The literal false-first tree serialization has nondecreasing exact keys. -/
theorem tableEntries_sorted {n : ℕ} (table : SemiprimeD1TensorTables.Table n) :
    (tableEntries table).value.Pairwise EntryLE := by
  induction table with
  | leaf ws => simp [tableEntries]
  | fork low high ihlow ihhigh =>
    simp only [tableEntries]
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      apply ihlow.imp
      intro a b hab
      simpa [EntryLE, KeyLE, compareKey] using hab
    · rw [List.pairwise_map]
      apply ihhigh.imp
      intro a b hab
      simpa [EntryLE, KeyLE, compareKey] using hab
    · intro a ha b hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
      simp [EntryLE, KeyLE, compareKey]

/-- Proof-side exact-key bytes of the actual first matching table entry. -/
def lookupWords (table : List Entry) (key : List Bool) : List (List Bool) :=
  ((table.find? (fun e => e.key == key)).map Entry.words).getD []

/-- Literal result of one request, including its saved route and whole product. -/
def applied (ctx : Context) (r : Entry) (table : List Entry) : Entry :=
  let req := Request.unpack r
  ⟨req.route, (SemiprimeD1JetRingBits.mul ctx req.words (lookupWords table r.key)).words⟩

/-- A table without a matching raw key supplies the same literal zero default. -/
theorem lookupWords_absent (table : List Entry) (key : List Bool)
    (h : ∀ e ∈ table, e.key ≠ key) : lookupWords table key = [] := by
  have hf : table.find? (fun e => e.key == key) = none := by
    apply List.find?_eq_none.mpr
    intro e he
    simpa only [beq_iff_eq] using h e he
  simp [lookupWords, hf]

/-- Removing a different first key does not change a requested payload. -/
theorem lookupWords_cons_ne (t : Entry) (table : List Entry) (key : List Bool)
    (h : t.key ≠ key) : lookupWords (t :: table) key = lookupWords table key := by
  simp [lookupWords, h]

/-- Every valid local address finds its exact original serialized entry. -/
theorem tableEntries_find {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (bits : List Bool) (hlen : bits.length = n) :
    (tableEntries table).value.find? (fun e => e.key == bits) =
      some (⟨bits, (SemiprimeD1TensorTables.lookup table bits).words⟩ : Entry) := by
  induction table generalizing bits with
  | leaf ws =>
    have he : bits = [] := List.eq_nil_of_length_eq_zero hlen
    subst bits
    simp [tableEntries, SemiprimeD1TensorTables.lookup, SemiprimeD1JetAxes.copyVector_value]
  | fork low high ihlow ihhigh =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have ht : bits.length = _ := Nat.succ.inj hlen
      cases bit
      ·
        simp [tableEntries, List.find?_append, List.find?_map, Function.comp_def,
          ihlow bits ht, SemiprimeD1TensorTables.lookup]
      · have hn : List.find? (fun _ : Entry => false) (tableEntries low).value = none := by
          apply List.find?_eq_none.mpr
          intro e _
          simp
        simp [tableEntries, List.find?_append, List.find?_map, Function.comp_def,
          ihhigh bits ht, SemiprimeD1TensorTables.lookup, hn]

/-- Local-table attachment reads original bytes, without an entry answer operand. -/
theorem tableEntries_lookup {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (bits : List Bool) (hlen : bits.length = n) :
    lookupWords (tableEntries table).value bits = (SemiprimeD1TensorTables.lookup table bits).words := by
  simp only [lookupWords, tableEntries_find table bits hlen, Option.map_some, Option.getD_some]

/-- The metadata search returns the actual first port ordinal, including EOF. -/
theorem findPort_value (p : ℕ) (ports : List ℕ) : (findPort p ports).value = ports.idxOf p := by
  induction ports with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : p = q <;> simp [findPort, h, eq_comm, ih]

/-- A paid bit read returns precisely the original selected Boolean/default. -/
theorem readBit_value (bits : List Bool) (n : ℕ) :
    (readBit bits n).value = (bits[n]?).getD false := by
  induction bits generalizing n with
  | nil => simp [readBit]
  | cons b bs ih => cases n <;> simp [readBit, ih]

/-- Address projection retains the cached target port order and literal defaults. -/
theorem project_value (bits : List Bool) (source target : List ℕ) :
    (project bits source target).value = target.map (fun p => (bits[source.idxOf p]?).getD false) := by
  induction target with
  | nil => rfl
  | cons p ps ih => simp [project, findPort_value, readBit_value, ih]

/-- Every projected address has exactly the target table's actual arity. -/
theorem project_length (bits : List Bool) (source target : List ℕ) :
    (project bits source target).value.length = target.length := by
  rw [project_value, List.length_map]

/-- A projected restriction reads the original assignment in target-port order. -/
theorem project_restriction (bits : ℕ → Bool) (source target : List ℕ)
    (h : ∀ p ∈ target, p ∈ source) :
    (project (source.map bits) source target).value = target.map bits := by
  rw [project_value]
  apply List.map_congr_left
  intro p hp
  have hi := List.idxOf_lt_length_of_mem (h p hp)
  rw [List.getElem?_map, List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getElem_idxOf hi]

/-- Strictly earlier keys cannot also follow the same key. -/
theorem lt_not_reverse_le (xs ys : List Bool) (h : (compareKey xs ys).value = Ordering.lt) :
    ¬ KeyLE ys xs := by
  intro hr
  have hf : KeyLE xs ys := by simp [KeyLE, h]
  have he := keyLE_antisymm xs ys hf hr
  have hc := (compareKey_eq xs ys).mpr he
  rw [h] at hc
  cases hc

/-- The actual forward cursor processes every request, retaining the table head
for repeated equal requests. Its budget counts requests plus table advances. -/
theorem lookupFuel_exact (ctx : Context) (fuel : ℕ) (rs table : List Entry)
    (hf : rs.length + table.length < fuel) (hr : rs.Pairwise EntryLE)
    (ht : table.Pairwise EntryLE) :
    (lookupFuel ctx fuel rs table).value = rs.map (fun r => applied ctx r table) := by
  induction fuel generalizing rs table with
  | zero => omega
  | succ fuel ih =>
    cases rs with
    | nil => simp [lookupFuel]
    | cons r rs =>
      have hr' := List.pairwise_cons.mp hr
      cases table with
      | nil =>
        have hb : rs.length + ([] : List Entry).length < fuel := by simp only [List.length_cons] at hf; omega
        simp only [lookupFuel, List.map_cons]
        rw [ih rs [] hb hr'.2 (by simp)]
        rfl
      | cons t ts =>
        have ht' := List.pairwise_cons.mp ht
        have hbr : rs.length + (t :: ts).length < fuel := by simp only [List.length_cons] at hf ⊢; omega
        have hbt : (r :: rs).length + ts.length < fuel := by simp only [List.length_cons] at hf ⊢; omega
        cases hc : (compareKey r.key t.key).value with
        | eq =>
          have he := (compareKey_eq r.key t.key).mp hc
          simp only [lookupFuel, hc, List.map_cons]
          rw [ih rs (t :: ts) hbr hr'.2 ht]
          simp [applied, lookupWords, he]
        | lt =>
          have hn : lookupWords (t :: ts) r.key = [] := by
            apply lookupWords_absent
            intro q hq he
            have hle : KeyLE t.key q.key := by
              rcases List.mem_cons.mp hq with rfl | hq
              · exact keyLE_refl _
              · exact ht'.1 q hq
            rw [he] at hle
            exact lt_not_reverse_le _ _ hc hle
          simp only [lookupFuel, hc, List.map_cons]
          rw [ih rs (t :: ts) hbr hr'.2 ht]
          simp [applied, hn]
        | gt =>
          have hn : ∀ q ∈ r :: rs, t.key ≠ q.key := by
            intro q hq he
            have hle : KeyLE r.key q.key := by
              rcases List.mem_cons.mp hq with rfl | hq
              · exact keyLE_refl _
              · exact hr'.1 q hq
            rw [← he] at hle
            exact hle hc
          simp only [lookupFuel, hc]
          rw [ih (r :: rs) ts hbt hr ht'.2]
          apply List.map_congr_left
          intro q hq
          simp only [applied, lookupWords_cons_ne t ts q.key (hn q hq)]

/-- Every request is physically formed from the source key and full accumulator. -/
theorem requests_value (source target : List ℕ) (acc : List Entry) :
    (requests source target acc).value = acc.map (fun e =>
      (Request.mk (project e.key source target).value e.key e.words).pack) := by
  induction acc with
  | nil => rfl
  | cons e es ih => simp only [requests, List.map_cons, ih]

/-- Two actual sorts and the forward join preserve every requested product.
This is a concrete record permutation, not a supplied entry evaluator. -/
theorem attach_perm (ctx : Context) (source target : List ℕ) (acc table : List Entry)
    (ht : table.Pairwise EntryLE) :
    (attach ctx source target acc table).value.Perm
      (acc.map (fun e => (⟨e.key, (SemiprimeD1JetRingBits.mul ctx e.words
        (lookupWords table (project e.key source target).value)).words⟩ : Entry))) := by
  let req := (requests source target acc).value
  have hlookup := lookupFuel_exact ctx ((sort req).value.length + table.length + 1)
    (sort req).value table (by omega) (sort_sorted req) ht
  change (sort (lookupFuel ctx ((sort req).value.length + table.length + 1)
    (sort req).value table).value).value.Perm _
  rw [hlookup]
  have hperm := (sort_perm ((sort req).value.map (fun r => applied ctx r table))).trans
    ((sort_perm req).map (fun r => applied ctx r table))
  have hreq : req.map (fun r => applied ctx r table) = acc.map (fun e =>
      (⟨e.key, (SemiprimeD1JetRingBits.mul ctx e.words
        (lookupWords table (project e.key source target).value)).words⟩ : Entry)) := by
    simp only [req, requests_value, List.map_map, Function.comp_def, applied,
      Request.pack, Request.unpack, List.headD_cons, List.tail_cons]
  exact hreq ▸ hperm

/-- The actual final address sort restores nondecreasing original assignment keys. -/
theorem attach_sorted (ctx : Context) (source target : List ℕ) (acc table : List Entry) :
    (attach ctx source target acc table).value.Pairwise EntryLE := by
  exact sort_sorted _

/-- Actual local-table attachment has exactly the old physical lookup payloads,
with one request per accumulator and no table-entry supplier. -/
theorem attach_vertex_perm (ctx : Context) (source : List ℕ)
    (v : SemiprimeD1LeafCounter.Vertex) (acc : List Entry) :
    (attach ctx source v.ports acc (tableEntries v.table).value).value.Perm
      (acc.map (fun e => (⟨e.key, (SemiprimeD1JetRingBits.mul ctx e.words
        (SemiprimeD1TensorTables.lookup v.table (project e.key source v.ports).value).words).words⟩ : Entry))) := by
  have h := attach_perm ctx source v.ports acc (tableEntries v.table).value (tableEntries_sorted v.table)
  simpa only [tableEntries_lookup v.table _ (project_length _ source v.ports)] using h

/-- No request or original assignment route is lost or duplicated by attachment. -/
theorem attach_keys_perm (ctx : Context) (source target : List ℕ) (acc table : List Entry)
    (ht : table.Pairwise EntryLE) :
    ((attach ctx source target acc table).value.map Entry.key).Perm (acc.map Entry.key) := by
  have h := (attach_perm ctx source target acc table ht).map Entry.key
  simpa only [List.map_map, Function.comp_def] using h

/-- Actual attachment length equals the number of acquired accumulator records. -/
theorem attach_length (ctx : Context) (source target : List ℕ) (acc table : List Entry)
    (ht : table.Pairwise EntryLE) : (attach ctx source target acc table).value.length = acc.length := by
  simpa only [List.length_map] using (attach_perm ctx source target acc table ht).length_eq

/-- Every joined payload is a complete canonical current jet, even for zero defaults. -/
theorem attach_good (ctx : Context) (source target : List ℕ) (acc table : List Entry)
    (ht : table.Pairwise EntryLE) :
    ∀ e ∈ (attach ctx source target acc table).value, SemiprimeD1TensorTables.GoodWords ctx e.words := by
  intro e he
  have hm := (attach_perm ctx source target acc table ht).mem_iff.mp he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hm
  exact SemiprimeD1LeafCounterBounds.mul_good ctx _ _

/-- Full local serialization retains every canonical original leaf payload. -/
theorem tableEntries_good (ctx : Context) {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (ht : SemiprimeD1TensorTables.Good ctx table) :
    ∀ e ∈ (tableEntries table).value, SemiprimeD1TensorTables.GoodWords ctx e.words := by
  intro e he
  rw [tableEntries_catalogue] at he
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp he
  exact SemiprimeD1TensorTables.lookup_good ctx table ht bits

end RiemannGaussian.SemiprimeD1BoundaryRecordsLookup
