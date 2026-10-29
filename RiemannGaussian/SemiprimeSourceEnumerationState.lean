/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerations

/-! # Actual source enumeration containers and coordinate-copy states
These invariants follow the literal paid list/copy constructors. Function-valued
words are related to their ACTUAL copied coordinate arrays, not supplied as
constant-cost functional oracles. Named payload/header counters are not a tape heap.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeSourceEnumerationState
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimePaidFiniteEnumerationLists

/-- Every actual collect call pays at least the produced list cells. -/
theorem collect_length_le_work {α β : Type*} (f : α → Run β) (xs : List α) :
    (collect f xs).value.length ≤ (collect f xs).work := by
  induction xs with
  | nil => simp [collect]
  | cons a xs ih => simp only [collect,List.length_cons];omega

/-- Actual callback reports pay a named payload count without a free callback. -/
theorem collect_work_ge_sum {α β : Type*} (f : α → Run β) (cells : α → ℕ) (xs : List α)
    (hf : ∀ a∈xs,cells a ≤ (f a).work) :
    (xs.map cells).sum ≤ (collect f xs).work := by
  induction xs with
  | nil => simp [collect]
  | cons a xs ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    simp only [collect,List.map_cons,List.sum_cons]
    omega

/-- Cartesian pair payload length is charged by the real append/collect reports. -/
theorem product_length_le_work {α β : Type*} (as : List α) (bs : List β) :
    (product as bs).value.length ≤ (product as bs).work := by
  induction as with
  | nil => simp [product]
  | cons a as ih => simp only [product,List.length_append];omega

/-- Flattening includes a literal append charge for every returned child-list cell. -/
theorem flat_length_le_work {α β : Type*} (f : α → Run (List β)) (as : List α) :
    (flat f as).value.length ≤ (flat f as).work := by
  induction as with
  | nil => simp [flat]
  | cons a as ih => simp only [flat,List.length_append];omega

/-- Both tag maps and their real append pay the original sum-list payload. -/
theorem sum_length_le_work {α β : Type*} (as : List α) (bs : List β) :
    (SemiprimePaidFiniteEnumerationLists.sum as bs).value.length ≤
      (SemiprimePaidFiniteEnumerationLists.sum as bs).work := by
  have hl := collect_length_le_work (fun a => (⟨Sum.inl a,1⟩ : Run (α⊕β))) as
  have hr := collect_length_le_work (fun b => (⟨Sum.inr b,1⟩ : Run (α⊕β))) bs
  simp only [SemiprimePaidFiniteEnumerationLists.sum,List.length_append]
  omega

section Words
variable {r q : ℕ} [NeZero r]

/-- The concrete array produced inside the ORIGINAL copyWord definition. -/
def copyCells (coordinates : List (Fin q)) (word : Word r q) : Array (Fin r) :=
  (collect (fun i => (⟨word i,2⟩ : Run (Fin r))) coordinates).value.toArray

/-- A copied word reads exactly the finite cells actually acquired by its copy loop. -/
theorem copyWord_lookup (coordinates : List (Fin q)) (word : Word r q) (i : Fin q) :
    (copyWord coordinates word).value i=((copyCells coordinates word)[i.val]?).getD 0 := rfl

omit [NeZero r] in
/-- Exact concrete copy-cache size, including noncanonical coordinate lists. -/
theorem copyCells_size (coordinates : List (Fin q)) (word : Word r q) :
    (copyCells coordinates word).size=coordinates.length := by simp [copyCells,collect_value]

omit [NeZero r] in
/-- Every actual copied coordinate has its original bounded colour ID. -/
theorem copyCells_colour_lt (coordinates : List (Fin q)) (word : Word r q)
    (i : ℕ) (hi : i<(copyCells coordinates word).size) :
    ((copyCells coordinates word)[i]).val<r := ((copyCells coordinates word)[i]).isLt

omit [NeZero r] in
/-- Every copy prefix has the literal number of acquired coordinate cells. -/
theorem copy_prefix_cells (coordinates : List (Fin q)) (word : Word r q) (k : ℕ) :
    (copyCells (coordinates.take k) word).size=min k coordinates.length := by
  rw [copyCells_size,List.length_take]

omit [NeZero r] in
/-- Every cached right-recursive collect suffix has its original remaining size. -/
theorem copy_suffix_cells (coordinates : List (Fin q)) (word : Word r q) (k : ℕ) :
    (copyCells (coordinates.drop k) word).size=coordinates.length-k := by
  rw [copyCells_size,List.length_drop]

/-- Literal copy report, not a coordinate oracle with an arbitrary attached cost. -/
theorem copyWord_work_exact (coordinates : List (Fin q)) (word : Word r q) :
    (copyWord coordinates word).work=5*coordinates.length+3 := by
  have h : ∀ xs : List (Fin q),(collect (fun i => (⟨word i,2⟩ : Run (Fin r))) xs).work=4*xs.length+1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp only [collect,List.length_cons,ih];omega
  simp only [copyWord,h,collect_value,List.length_map]
  omega

/-- Named coordinate/list payload and header allocations in one word copy.
This excludes interpreter register/tape metadata; it is not a whole-heap counter. -/
def copyAllocations (coordinates : List (Fin q)) : ℕ := 3*coordinates.length+3

/-- Two coordinate payloads (collect list and array), list spines and constant headers are paid. -/
theorem copy_allocations_le_work (coordinates : List (Fin q)) (word : Word r q) :
    copyAllocations coordinates ≤ (copyWord coordinates word).work := by
  rw [copyWord_work_exact]
  unfold copyAllocations
  omega

/-- Proof-side finite array backing, with no requested lookup answer as a premise. -/
def ArrayBacked (w : Word r q) : Prop :=
  ∃ cells : Array (Fin r),cells.size=q ∧ ∀ i,w i=(cells[i.val]?).getD 0

/-- The canonical actual copy has its own acquired array as backing data. -/
theorem copyWord_arrayBacked (word : Word r q) : ArrayBacked (copyWord (List.finRange q) word).value := by
  refine ⟨copyCells (List.finRange q) word,?_,?_⟩
  · simp [copyCells_size]
  · exact copyWord_lookup _ _

/-- The successor-stage output is LITERALLY a copy of one actual acquired head/tail pair. -/
theorem words_member_copy (r q : ℕ) [NeZero r] (w : Word r (q+1))
    (hw : w∈(words r (q+1)).value) :
    ∃ p∈(product (fin r).value (words r q).value).value,
      w=(copyWord (fin (q+1)).value (Fin.cons p.1 p.2)).value := by
  change w∈(collect (fun p => copyWord (fin (q+1)).value (Fin.cons p.1 p.2))
    (product (fin r).value (words r q).value).value).value at hw
  rw [collect_value] at hw
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hw
  exact ⟨p,hp,he.symm⟩

/-- Every generated word has a real finite backing array; zero width is explicit. -/
theorem words_arrayBacked (r q : ℕ) [NeZero r] (w : Word r q)
    (hw : w∈(words r q).value) : ArrayBacked w := by
  cases q with
  | zero => exact ⟨#[],rfl,fun i => Fin.elim0 i⟩
  | succ q =>
    obtain ⟨p,_,rfl⟩ := words_member_copy r q w hw
    simpa only [fin_value] using copyWord_arrayBacked (Fin.cons p.1 p.2)

/-- A generated prefix word has bounded original colours at every coordinate. -/
theorem words_colour_lt (r q : ℕ) (w : Word r q) (i : Fin q) : (w i).val<r :=
  (w i).isLt

/-- New named coordinate/list/header allocations in actual word-copy stages. -/
def wordCopyAllocations (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | q+1 => wordCopyAllocations r q+r^(q+1)*(3*(q+1)+3)

/-- Every actual copy allocation is retained by the ORIGINAL words report. -/
theorem wordCopyAllocations_le_work (r q : ℕ) [NeZero r] :
    wordCopyAllocations r q ≤ (words r q).work := by
  induction q with
  | zero => simp [wordCopyAllocations,words]
  | succ q ih =>
    have hc := collect_work_ge_sum
      (fun p : Fin r × Word r q => copyWord (fin (q+1)).value (Fin.cons p.1 p.2))
      (fun _ => 3*(q+1)+3) (product (fin r).value (words r q).value).value (by
        intro p _
        simpa only [fin_value,List.length_finRange,copyAllocations] using
          copy_allocations_le_work (fin (q+1)).value (Fin.cons p.1 p.2))
    have hlen : (product (fin r).value (words r q).value).value.length=r^(q+1) := by
      rw [product_value,fin_value]
      change ((List.finRange r) ×ˢ (words r q).value).length=r^(q+1)
      rw [List.length_product,List.length_finRange,words_length,pow_succ]
      exact Nat.mul_comm _ _
    simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id,hlen] at hc
    simp only [words,wordCopyAllocations]
    omega

/-- All generated stages fit the original alphabet and target coordinate envelope. -/
theorem wordCopyAllocations_bound (r q Q : ℕ) [NeZero r] (hq : q ≤ Q) :
    wordCopyAllocations r q ≤ Q*r^Q*(3*Q+3) := by
  have haux : ∀ k, k ≤ Q → wordCopyAllocations r k ≤ k*r^Q*(3*Q+3) := by
    intro k
    induction k with
    | zero => simp [wordCopyAllocations]
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hp := Nat.pow_le_pow_right (NeZero.pos r) hk
      have hstep : r^(k+1)*(3*(k+1)+3) ≤ r^Q*(3*Q+3) := by gcongr
      simp only [wordCopyAllocations]
      nlinarith
  exact (haux q hq).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hq))

end Words

open SemiprimePaidFiniteEnumerations

/-- The universal constructor shares its acquired word bank; both word references
are literal members of that bank, not arbitrary functional callbacks. -/
theorem universal_member_words (r Q : ℕ) [NeZero r]
    (u : UniversalType r Q 1) (hu : u∈(universal r Q).value) :
    u.head∈(words r Q).value ∧ u.slot 0∈(words r Q).value := by
  simp only [universal,collect_value,List.mem_map] at hu
  obtain ⟨p,hp,rfl⟩ := hu
  rcases p with ⟨ph,ps⟩
  rw [product_value] at hp
  change (ph,ps)∈((words r Q).value ×ˢ _) at hp
  rw [List.mem_product] at hp
  obtain ⟨hh,hs⟩ := hp
  simp only [List.mem_map] at hs
  obtain ⟨z,hz,hzout⟩ := hs
  rcases z with ⟨zh,zs⟩
  rw [product_value] at hz
  change (zh,zs)∈((words r Q).value ×ˢ _) at hz
  rw [List.mem_product] at hz
  have hslot : (Fin.cons zh zs : Fin 1 → Word r Q) 0=ps 0 := by
    exact congrFun hzout 0
  exact ⟨hh,by simpa only [equivProd,Equiv.coe_fn_symm_mk,Fin.cons_zero] using hslot ▸ hz.1⟩

/-- Both references in each actual universal descriptor retain actual coordinate arrays. -/
theorem universal_arrayBacked (r Q : ℕ) [NeZero r]
    (u : UniversalType r Q 1) (hu : u∈(universal r Q).value) :
    ArrayBacked u.head ∧ ArrayBacked (u.slot 0) := by
  obtain ⟨hh,hs⟩ := universal_member_words r Q u hu
  exact ⟨words_arrayBacked r Q _ hh,words_arrayBacked r Q _ hs⟩

/-- The actual indexed candidate menu, including its distinguished zero word,
has exactly L entries. This is separate from the U universal descriptors. -/
theorem indexed_word_length (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    let en := (indexed n F r Q arity).value
    (en.wordFirst::en.wordTail).length=r^Q := by
  let en := (indexed n F r Q arity).value
  let bank : FiniteEnumeration (Word r Q) :=
    ⟨en.wordFirst::en.wordTail,en.words_nodup,en.words_complete⟩
  exact bank.length_eq_card.trans (card_word r Q)

/-- Every actual nonzero candidate retains the copied bank's array backing;
the distinguished zero candidate is deliberately not asserted freshly copied. -/
theorem indexed_tail_arrayBacked (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (w : Word r Q) (hw : w∈(indexed n F r Q arity).value.wordTail) :
    ArrayBacked w := by
  change w∈(nonzeroWords (fin Q).value (words r Q).value).value at hw
  rw [fin_value,nonzeroWords_value] at hw
  exact words_arrayBacked r Q w (List.mem_filter.mp hw).1

/-- A conservative expanded coordinate/payload view of the actual indexed
containers. Universal head/slot references are expanded here; this is NOT a
claim that the shared constructor freshly allocates 2Q cells per descriptor. -/
def indexedPayload (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) : ℕ :=
  let en := (indexed n F r Q arity).value
  2*en.incidences.values.length+(2*Q+3)*en.types.values.length+
    4*en.terms.values.length+en.indices.values.length+
    (Q+3)*(words r Q).value.length+5

/-- Original dimensions exactly determine the finite descriptor/payload view. -/
theorem indexedPayload_eq (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    indexedPayload n F r Q arity =
      2*(∑ e,arity e)+(2*Q+3)*r^(2*Q)+4*((∑ e,arity e)^2+Q*n^2)+
        (n+F)+(Q+3)*r^Q+5 := by
  simp only [indexedPayload,indexed_incidence_length,indexed_universal_length,
    indexed_score_length,indexed_indices_length,words_length]

/-- Every index code in the actual variable/factor sum has its original finite range. -/
def indexCode {n F : ℕ} : Fin n ⊕ Fin F → ℕ
  | .inl v => v.val
  | .inr e => n+e.val

theorem indexCode_lt {n F : ℕ} (i : Fin n ⊕ Fin F) : indexCode i<n+F := by
  cases i with
  | inl v => simp only [indexCode]; omega
  | inr e => simp only [indexCode]; omega

/-- Actual incidence fields carry bounded original factor/port IDs. -/
theorem incidence_ids {F : ℕ} (arity : Fin F → ℕ)
    (i : (e : Fin F) × Fin (arity e)) :
    i.1.val<F ∧ i.2.val<∑ e,arity e := by
  refine ⟨i.1.isLt,lt_of_lt_of_le i.2.isLt ?_⟩
  exact Finset.single_le_sum (fun e _ => Nat.zero_le (arity e)) (Finset.mem_univ i.1)

/-- Every prefix and suffix of every actual acquired metadata list fits its
original full length, including empty lists and endpoints. -/
theorem indexed_prefix_suffix (n F r Q k : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    let en := (indexed n F r Q arity).value
    (en.incidences.values.take k).length≤∑ e,arity e ∧
    (en.incidences.values.drop k).length≤∑ e,arity e ∧
    (en.types.values.take k).length≤r^(2*Q) ∧
    (en.types.values.drop k).length≤r^(2*Q) ∧
    (en.terms.values.take k).length≤(∑ e,arity e)^2+Q*n^2 ∧
    (en.terms.values.drop k).length≤(∑ e,arity e)^2+Q*n^2 ∧
    (en.indices.values.take k).length≤n+F ∧
    (en.indices.values.drop k).length≤n+F := by
  dsimp only
  simp only [List.length_take,List.length_drop,indexed_incidence_length,
    indexed_universal_length,indexed_score_length,indexed_indices_length]
  omega

/-- The indexed acquisition really invokes TWO word producers: its explicit
candidate bank and the bank inside universal. Both copy ledgers are retained. -/
theorem indexed_retains_word_copies (n F r Q : ℕ) [NeZero r] (arity : Fin F → ℕ) :
    2*wordCopyAllocations r Q ≤ (indexed n F r Q arity).work := by
  have h := wordCopyAllocations_le_work r Q
  simp only [indexed,universal]
  omega

/-- Coordinate payload in each generated-prefix bank is bounded by the actual
word-copy ledger, including the length-zero singleton. -/
theorem generated_coordinate_cells_le_work (r q : ℕ) [NeZero r] :
    q*(words r q).value.length ≤ (words r q).work := by
  rw [words_length]
  have h := wordCopyAllocations_le_work r q
  cases q with
  | zero => omega
  | succ q =>
    simp only [wordCopyAllocations] at h
    nlinarith [Nat.zero_le (wordCopyAllocations r q),
      Nat.zero_le (r^(q+1))]

/-- Every generation prefix/suffix has at most the original Q*L coordinate view. -/
theorem generated_coordinate_prefix (r q Q k : ℕ) [NeZero r] (hq : q ≤ Q) :
    q*((words r q).value.take k).length ≤ Q*r^Q ∧
    q*((words r q).value.drop k).length ≤ Q*r^Q := by
  have hp := Nat.pow_le_pow_right (NeZero.pos r) hq
  have hl := words_length r q
  simp only [List.length_take,List.length_drop,hl]
  constructor <;> apply Nat.mul_le_mul hq <;> omega

end RiemannGaussian.SemiprimeSourceEnumerationState
