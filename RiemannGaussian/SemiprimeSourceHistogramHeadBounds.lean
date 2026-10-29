/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramHeadQueryBounds
import RiemannGaussian.SemiprimeSourceHistogramSquaresBounds

/-! # Actual original head-pass and histogram report bounds
All prefix payload, colour, key and counter widths follow from acquired original
input data and actual loop invariants. No callback/height/work answer is supplied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramHeadBounds
open SemiprimeBitArithmetic SemiprimeSourceHistogramHeadBits
open SemiprimeSourceCompactBits (Compact)
open SemiprimeSourceHistogramTrie (Trie)

/-- Every static vertex encoder and returned record cell is paid. -/
theorem verticesWith_work {n : ℕ} (is : List (Fin n)) :
    (verticesWith is).work ≤ is.length*(SemiprimeSourceHistogramPortKeys.encodeBudget n+5)+1 := by
  induction is with
  | nil => simp [verticesWith]
  | cons i is ih =>
    have he := SemiprimeSourceHistogramPortKeys.encodeKey_clock i.val n i.isLt.le
    simp only [verticesWith,vertex,List.length_cons]
    nlinarith

/-- Original finite-index generation is retained by the static cache endpoint. -/
theorem acquireVertices_work (n : ℕ) : (acquireVertices n).work ≤
    3*(n+1)^2+n*(SemiprimeSourceHistogramPortKeys.encodeBudget n+5)+4 := by
  have hi := SemiprimePaidFiniteEnumerationLists.fin_work n
  have hv := verticesWith_work (SemiprimePaidFiniteEnumerationLists.fin n).value
  rw [SemiprimePaidFiniteEnumerationLists.fin_value,List.length_finRange] at hv
  unfold acquireVertices
  dsimp only
  rw [SemiprimePaidFiniteEnumerationLists.fin_value]
  omega

/-- The original static list has exactly its supplied cardinality. -/
theorem verticesWith_length {n : ℕ} (is : List (Fin n)) :
    (verticesWith is).value.length=is.length := by rw [verticesWith_value,List.length_map]

/-- Static original variable keys have their original dimension-derived widths. -/
theorem verticesWith_width {n : ℕ} (is : List (Fin n)) :
    ∀ v∈(verticesWith is).value,v.key.length ≤ SemiprimeSourceHistogramPortKeys.keyWidth n := by
  intro v hv
  rw [verticesWith_value] at hv
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
  exact SemiprimeSourceHistogramPortKeys.encodeKey_length i.val n i.isLt.le

/-- Static source vertices preserve the original fixed-prefix interval filter exactly. -/
theorem original_fixed_count {n : ℕ} (cache : SemiprimeSourceHistogramRowKeys.QueryCache)
    (dict : Trie) (k s : ℕ) (is : List (Fin n)) :
    bitValue (produce cache dict k s (verticesWith is).value).fixed=
      (is.filter (fun v => !(SemiprimeSourceHistogramFeatureBits.active k s v.val))).length := by
  rw [produce_fixed,verticesWith_value,List.filter_map,List.length_map]
  rfl

/-- Static source vertices preserve the original free-prefix interval filter exactly. -/
theorem original_free_count {n : ℕ} (cache : SemiprimeSourceHistogramRowKeys.QueryCache)
    (dict : Trie) (k s : ℕ) (is : List (Fin n)) :
    bitValue (produce cache dict k s (verticesWith is).value).free=
      (is.filter (fun v => SemiprimeSourceHistogramFeatureBits.active k s v.val)).length := by
  rw [produce_free,verticesWith_value,List.filter_map,List.length_map]
  rfl

/-- The actual acquired fixed/free counters both fit their actual vertex-count cap. -/
theorem counter_lengths (cache : SemiprimeSourceHistogramRowKeys.QueryCache) (dict : Trie)
    (k s : ℕ) (vs : List Vertex) (N : ℕ) (hn : vs.length ≤ N) :
    (produce cache dict k s vs).fixed.length ≤ SemiprimeSourceHistogramTrieBounds.clockWidth N ∧
      (produce cache dict k s vs).free.length ≤ SemiprimeSourceHistogramTrieBounds.clockWidth N := by
  have hc := produce_compact cache dict k s vs
  have hp := Nat.le_pow_clog (by decide : 1 < (2:ℕ)) (N+2)
  constructor
  · apply SemiprimeSourceCompactBits.compact_length_of_lt _ hc.1
    rw [produce_fixed]
    have hf := List.length_filter_le (fun v : Vertex =>
      !(SemiprimeSourceHistogramFeatureBits.active k s v.code)) vs
    change _ < 2^Nat.clog 2 (N+2)
    omega
  · apply SemiprimeSourceCompactBits.compact_length_of_lt _ hc.2
    rw [produce_free]
    have hf := List.length_filter_le (fun v : Vertex =>
      SemiprimeSourceHistogramFeatureBits.active k s v.code) vs
    change _ < 2^Nat.clog 2 (N+2)
    omega

/-- Actual original prefix and coordinate cache give exactly Q keys per fixed query. -/
theorem original_row_length (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (key : List Bool) :
    (SemiprimeSourceHistogramRowKeys.readKeys
      (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).source.dictionary
      (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).coordinates
      (SemiprimeSourceHistogramTrie.stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie key)).keys.length=Q := by
  rw [SemiprimeSourceHistogramRowKeys.acquireCaches_dictionary,
    SemiprimeSourceHistogramRowKeys.acquireCaches_coordinates]
  exact SemiprimeSourceHistogramRowKeys.readKeys_length r Q _
    (SemiprimeSourceHistogramDictRefinement.stored_mem r Q fixed hf key)

/-- Original fixed-key stream has at most Q times the original vertex count. -/
theorem produce_length (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (vs : List Vertex) :
    (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).keys.length ≤ Q*vs.length := by
  induction vs with
  | nil => simp [produce]
  | cons v vs ih =>
    have hr := original_row_length r Q fixed hf v.key
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simp only [produce,ha,ite_true,List.length_cons]
      nlinarith
    · simp only [produce,ha,Bool.false_eq_true,ite_false,appendKeys_value,
        SemiprimeSourceHistogramTrie.lookup_bits,List.length_append,hr,List.length_cons]
      nlinarith

/-- Actual fixed-key width is logarithmic in original Q and r, from cached fields. -/
theorem produce_width (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (vs : List Vertex) :
    ∀ key∈(produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).keys,
      key.length ≤ SemiprimeSourceHistogramHeadQueryBounds.keyWidth r Q := by
  induction vs with
  | nil => simp [produce]
  | cons v vs ih =>
    have hrow := SemiprimeSourceHistogramHeadQueryBounds.readKeys_width r Q
      (SemiprimeSourceHistogramTrie.stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie v.key)
      (SemiprimeSourceHistogramDictRefinement.stored_mem r Q fixed hf v.key)
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simpa only [produce,ha,ite_true] using ih
    · intro key hk
      simp only [produce,ha,Bool.false_eq_true,ite_false,appendKeys_value,List.mem_append,
        SemiprimeSourceHistogramTrie.lookup_bits] at hk
      rcases hk with hk|hk
      · simpa only [SemiprimeSourceHistogramRowKeys.acquireCaches_dictionary,
          SemiprimeSourceHistogramRowKeys.acquireCaches_coordinates] using hrow key hk
      · exact ih key hk

/-- Uniform paid per-vertex stage; all dimensions are original or actual count caps. -/
def vertexStage (r Q V N : ℕ) : ℕ :=
  8*V+3*Nat.clog 2 (r^Q+1)+12+
    SemiprimeSourceHistogramHeadQueryBounds.rowQueryBudget r Q+3*Q+1+
    20*(SemiprimeSourceHistogramTrieBounds.clockWidth N+1)+10+20

/-- Actual head pass retains prefix read, one all-coordinate query, append and counters. -/
theorem produce_clock (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (vs : List Vertex) (V N : ℕ)
    (hv : ∀ v∈vs,v.key.length ≤ V) (hn : vs.length ≤ N) :
    (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).clock ≤
      vs.length*vertexStage r Q V N+1 := by
  induction vs with
  | nil => simp [produce]
  | cons v vs ih =>
    have htlen : vs.length ≤ N := by simp only [List.length_cons] at hn;omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) htlen
    have hc := counter_lengths (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs N htlen
    have hp := SemiprimeSourceHistogramTrieBounds.clockWidth_pos N
    have hif := SemiprimeSourceCompactBits.increment_clock
      (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
        (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).fixed _ hp hc.1
    have hia := SemiprimeSourceCompactBits.increment_clock
      (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
        (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).free _ hp hc.2
    have hkey := hv v (by simp)
    have hid := SemiprimeSourceHistogramDictRefinement.stored_mem r Q fixed hf v.key
    have hlookup := SemiprimeSourceHistogramTrieBounds.lookup_clock_of_count
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie v.key (r^Q)
      (SemiprimeSourceHistogramPrefix.stored_compact fixed)
      (SemiprimeSourceHistogramDictRefinement.count_cap r Q fixed hf v.key)
    have hrow := SemiprimeSourceHistogramHeadQueryBounds.readKeys_clock r Q _ hid
    have hrowlen := original_row_length r Q fixed hf v.key
    have happ := appendKeys_work
      (SemiprimeSourceHistogramRowKeys.readKeys
        (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).source.dictionary
        (SemiprimeSourceHistogramRowKeys.acquireCaches r Q).coordinates
        (SemiprimeSourceHistogramTrie.stored (SemiprimeSourceHistogramPrefix.acquire fixed).trie v.key)).keys
      (produce (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
        (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).keys
    rw [hrowlen] at happ
    by_cases ha : SemiprimeSourceHistogramFeatureBits.active k s v.code=true
    · simp only [produce,ha,ite_true,List.length_cons]
      unfold vertexStage at ht ⊢
      nlinarith
    · simp only [produce,ha,Bool.false_eq_true,ite_false,
        SemiprimeSourceHistogramTrie.lookup_bits,List.length_cons]
      simp only [SemiprimeSourceHistogramRowKeys.acquireCaches_dictionary,
        SemiprimeSourceHistogramRowKeys.acquireCaches_coordinates] at happ ⊢
      unfold vertexStage at ht ⊢
      nlinarith

/-- Complete actual head query plus sparse histogram report, with no quadratic pair loop. -/
def budget (r Q V N : ℕ) : ℕ := N*vertexStage r Q V N+1+
  SemiprimeSourceHistogramSquaresBounds.budget
    (SemiprimeSourceHistogramHeadQueryBounds.keyWidth r Q) (Q*N)+3

/-- Original acquired prefix and key cache discharge all dynamic histogram costs. -/
theorem acquire_clock (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (vs : List Vertex) (V N : ℕ)
    (hv : ∀ v∈vs,v.key.length ≤ V) (hn : vs.length ≤ N) :
    (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s vs).clock ≤ budget r Q V N := by
  have hp := produce_clock r Q fixed hf k s vs V N hv hn
  have hk := produce_width r Q fixed hf k s vs
  have hs := SemiprimeSourceHistogramSquaresBounds.acquire_clock _ _ hk
  have hl := produce_length r Q fixed hf k s vs
  have hm := SemiprimeSourceHistogramSquaresBounds.budget_mono (le_refl
    (SemiprimeSourceHistogramHeadQueryBounds.keyWidth r Q))
    (hl.trans (Nat.mul_le_mul_left Q hn))
  unfold acquire budget
  dsimp only
  nlinarith

/-- Original cached finite vertices discharge the final key and counter caps;
no supplied dynamic output, callback-clock or representation advice remains. -/
theorem acquire_static_clock {n : ℕ} (r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (k s : ℕ) (is : List (Fin n)) :
    (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s (verticesWith is).value).clock ≤
      budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) is.length := by
  apply acquire_clock r Q fixed hf k s _ _ _ (verticesWith_width is)
  exact (verticesWith_length is).le

/-- Fully original finite-range static cache specialization, with every actual
original vertex included exactly once in its published order. -/
theorem acquire_original_clock (n r Q : ℕ) [NeZero r] (fixed : List (List Bool))
    (hf : ∀ id∈fixed,id∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (k s : ℕ) :
    (acquire (SemiprimeSourceHistogramRowKeys.acquireCaches r Q)
      (SemiprimeSourceHistogramPrefix.acquire fixed).trie k s (acquireVertices n).value).clock ≤
      budget r Q (SemiprimeSourceHistogramPortKeys.keyWidth n) n := by
  have he : (acquireVertices n).value=(verticesWith (List.finRange n)).value := by
    rw [acquireVertices_value,verticesWith_value]
  rw [he]
  simpa only [List.length_finRange] using acquire_static_clock r Q fixed hf k s (List.finRange n)

end RiemannGaussian.SemiprimeSourceHistogramHeadBounds
