import RiemannGaussian.SemiprimeD1BoundaryLeafCorrectness
import RiemannGaussian.SemiprimeD1BoundaryLeafCanonical

/-! Concrete sorted shape and exact scalar extraction of boundary records. -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsShape
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsOrder
open SemiprimeD1BoundaryRecordsSort
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1JetAxes (Context)

theorem group_key_mem (ctx : Context) : (es : List Entry) → (e : Entry) →
    e ∈ (group ctx es).value → e.key ∈ es.map Entry.key
  | [],e,h => by simp [group] at h
  | [a],e,h => by
    have he : e = a := by simpa [group] using h
    simp [he]
  | a::b::rest,e,h => by
    by_cases hc : (compareKey a.key b.key).value = .eq
    · have he := (compareKey_eq _ _).mp hc
      simp only [group, hc, beq_self_eq_true, ite_true] at h
      have hh := group_key_mem ctx _ e h
      simpa only [List.map_cons, List.mem_cons] using
        (show e.key = a.key ∨ e.key = b.key ∨ e.key ∈ rest.map Entry.key from by
          simpa only [List.map_cons, List.mem_cons, he, or_self_left] using hh)
    · have hb : ((compareKey a.key b.key).value == .eq) = false := by simp [hc]
      simp only [group, hb, Bool.false_eq_true, ite_false, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (group_key_mem ctx _ e h)
termination_by es _ _ => es.length

theorem group_sorted (ctx : Context) : (es : List Entry) → es.Pairwise EntryLE →
    (group ctx es).value.Pairwise EntryLE
  | [],_ => by simp [group]
  | [a],_ => by simp [group]
  | a::b::rest,h => by
    have ha := List.pairwise_cons.mp h
    have hb := List.pairwise_cons.mp ha.2
    by_cases hc : (compareKey a.key b.key).value = .eq
    · have he := (compareKey_eq _ _).mp hc
      simp only [group, hc, beq_self_eq_true, ite_true]
      apply group_sorted ctx
      apply List.pairwise_cons.mpr
      exact ⟨fun e hmem => ha.1 e (List.mem_cons_of_mem b hmem), hb.2⟩
    · have hcmp : ((compareKey a.key b.key).value == .eq) = false := by simp [hc]
      simp only [group, hcmp, Bool.false_eq_true, ite_false]
      apply List.pairwise_cons.mpr
      refine ⟨?_,group_sorted ctx _ ha.2⟩
      intro e he
      obtain ⟨q,hq,hkey⟩ := List.mem_map.mp (group_key_mem ctx _ e he)
      change KeyLE a.key e.key
      rw [← hkey]
      exact ha.1 q hq
termination_by es _ => es.length

theorem contract_sorted (ctx : Context) (source target : List Nat) (es : List Entry) :
    (contract ctx source target es).value.Pairwise EntryLE :=
  group_sorted ctx _ (sort_sorted _)

theorem group_unique (ctx : Context) : (es : List Entry) → es.Pairwise EntryLE →
    (group ctx es).value.Pairwise (fun a b => a.key ≠ b.key)
  | [],_ => by simp [group]
  | [a],_ => by simp [group]
  | a::b::rest,h => by
    have ha := List.pairwise_cons.mp h
    have hb := List.pairwise_cons.mp ha.2
    by_cases hc : (compareKey a.key b.key).value = .eq
    · simp only [group, hc, beq_self_eq_true, ite_true]
      apply group_unique ctx
      exact List.pairwise_cons.mpr
        ⟨fun e he => ha.1 e (List.mem_cons_of_mem b he),hb.2⟩
    · have hcmp : ((compareKey a.key b.key).value == .eq) = false := by simp [hc]
      simp only [group, hcmp, Bool.false_eq_true, ite_false]
      apply List.pairwise_cons.mpr
      refine ⟨?_,group_unique ctx _ ha.2⟩
      intro e he hae
      obtain ⟨q,hq,hkey⟩ := List.mem_map.mp (group_key_mem ctx _ e he)
      have hba : KeyLE b.key a.key := by
        rw [hae, ←hkey]
        rcases List.mem_cons.mp hq with rfl | hq
        · exact keyLE_refl _
        · exact hb.1 q hq
      exact hc ((compareKey_eq _ _).mpr
        (keyLE_antisymm _ _ (ha.1 b List.mem_cons_self) hba))
termination_by es _ => es.length

theorem contract_unique (ctx : Context) (source target : List Nat) (es : List Entry) :
    (contract ctx source target es).value.Pairwise (fun a b => a.key ≠ b.key) :=
  group_unique ctx _ (sort_sorted _)

theorem contract_key_length (ctx : Context) (source target : List Nat) (es : List Entry)
    (e : Entry) (he : e ∈ (contract ctx source target es).value) : e.key.length = target.length := by
  have hk := group_key_mem ctx _ e he
  obtain ⟨q,hq,hkey⟩ := List.mem_map.mp hk
  have hq' := (sort_perm (rekey source target es).value).mem_iff.mp hq
  rw [SemiprimeD1BoundaryLeafCorrectness.rekey_value] at hq'
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hq'
  rw [←hkey]
  exact SemiprimeD1BoundaryRecordsLookup.project_length _ _ _

theorem weighted_eq_lookup (ctx : Context) (es : List Entry)
    (hu : es.Pairwise (fun a b => a.key ≠ b.key)) (key : List Bool) :
    weighted ctx es key = SemiprimeD1JetInterpretation.interpret ctx
      (SemiprimeD1BoundaryRecordsLookup.lookupWords es key) := by
  induction es with
  | nil => simp [weighted, SemiprimeD1BoundaryRecordsLookup.lookupWords,
      SemiprimeD1JetInterpretation.interpret, SemiprimeD1JetRingBits.coefficient,
      SemiprimeD1JetOperations.basis_zero, SemiprimeBitArithmetic.bitValue]
  | cons e es ih =>
    have hh := List.pairwise_cons.mp hu
    by_cases he : e.key = key
    · have hz : weighted ctx es key = 0 := by
        unfold weighted
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
        simp only [ite_eq_right_iff]
        intro hqkey
        exact False.elim (hh.1 q hq (he.trans hqkey.symm))
      change (if e.key = key then SemiprimeD1JetInterpretation.interpret ctx e.words else 0) +
        weighted ctx es key = _
      rw [hz]
      simp [SemiprimeD1BoundaryRecordsLookup.lookupWords, he]
    · rw [SemiprimeD1BoundaryRecordsLookup.lookupWords_cons_ne e es key he]
      simpa [weighted, he] using ih hh.2

theorem weighted_eq_head (ctx : Context) (es : List Entry)
    (hu : es.Pairwise (fun a b => a.key ≠ b.key)) (hn : es ≠ [])
    (hk : ∀ e ∈ es, e.key = []) :
    weighted ctx es [] = SemiprimeD1JetInterpretation.interpret ctx
      (es.headD ⟨[],[]⟩).words := by
  rw [weighted_eq_lookup ctx es hu []]
  cases es with
  | nil => exact False.elim (hn rfl)
  | cons e es =>
    have he := hk e List.mem_cons_self
    simp [SemiprimeD1BoundaryRecordsLookup.lookupWords,he]

open SemiprimeD1BoundaryLeaf

theorem bucket_sorted (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph)
    (vs : List Vertex) (colours : List Nat) (c : Nat) :
    (bucket ctx g vs colours c).value.entries.Pairwise EntryLE :=
  contract_sorted ctx _ _ _

theorem bucket_unique (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph)
    (vs : List Vertex) (colours : List Nat) (c : Nat) :
    (bucket ctx g vs colours c).value.entries.Pairwise (fun a b => a.key ≠ b.key) :=
  contract_unique ctx _ _ _

theorem merge_sorted (ctx : Context) (left right : Tensor) :
    (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries.Pairwise EntryLE :=
  contract_sorted ctx _ _ _

theorem merge_unique (ctx : Context) (left right : Tensor) :
    (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries.Pairwise
      (fun a b => a.key ≠ b.key) := contract_unique ctx _ _ _

theorem mergeAll_sorted (ctx : Context) (first : Tensor) (rest : List Tensor)
    (h : first.entries.Pairwise EntryLE) :
    (mergeAll ctx first rest).value.entries.Pairwise EntryLE := by
  induction rest generalizing first with
  | nil => exact h
  | cons t ts ih => exact ih _ (merge_sorted ctx first t)

theorem mergeAll_unique (ctx : Context) (first : Tensor) (rest : List Tensor)
    (h : first.entries.Pairwise (fun a b => a.key ≠ b.key)) :
    (mergeAll ctx first rest).value.entries.Pairwise (fun a b => a.key ≠ b.key) := by
  induction rest generalizing first with
  | nil => exact h
  | cons t ts ih => exact ih _ (merge_unique ctx first t)

theorem bucket_key_length (ctx : Context) (g : SemiprimeD1BoundaryPlan.Graph)
    (vs : List Vertex) (colours : List Nat) (c : Nat) (e : Entry)
    (he : e ∈ (bucket ctx g vs colours c).value.entries) :
    e.key.length = (bucket ctx g vs colours c).value.ports.length :=
  contract_key_length ctx _ _ _ e he

theorem merge_key_length (ctx : Context) (left right : Tensor) (e : Entry)
    (he : e ∈ (SemiprimeD1BoundaryLeaf.merge ctx left right).value.entries) :
    e.key.length = (SemiprimeD1BoundaryLeaf.merge ctx left right).value.ports.length :=
  contract_key_length ctx _ _ _ e he

theorem mergeAll_key_length (ctx : Context) (first : Tensor) (rest : List Tensor)
    (h : ∀ e ∈ first.entries, e.key.length = first.ports.length) :
    ∀ e ∈ (mergeAll ctx first rest).value.entries,
      e.key.length = (mergeAll ctx first rest).value.ports.length := by
  induction rest generalizing first with
  | nil => exact h
  | cons t ts ih => exact ih _ (merge_key_length ctx first t)

/-- The actually acquired tensor has sorted unique full-length addresses. -/
theorem acquire_shape (ctx : Context) (net : Network) :
    (acquire ctx net).tensor.entries.Pairwise EntryLE ∧
    (acquire ctx net).tensor.entries.Pairwise (fun a b => a.key ≠ b.key) ∧
    ∀ e ∈ (acquire ctx net).tensor.entries,
      e.key.length = (acquire ctx net).tensor.ports.length := by
  let g := SemiprimeD1BoundaryPlan.graph net
  let vs := SemiprimeD1TensorNetwork.vertices net
  let plan := SemiprimeD1BoundaryPlan.acquire g
  let bs := (List.range plan.k).map (bucket ctx g vs plan.colours)
  have hbs : bs ≠ [] := SemiprimeD1BoundaryLeafCanonical.buckets_nonempty ctx net
  have hh := SemiprimeD1BoundaryLeafCanonical.headD_member bs ⟨⟨[],[]⟩,1⟩ hbs
  obtain ⟨c,_,hc⟩ := List.mem_map.mp hh
  have hs : (bs.headD ⟨⟨[],[]⟩,1⟩).value.entries.Pairwise EntryLE := by
    rw [←hc]
    exact bucket_sorted ctx g vs plan.colours c
  have hu : (bs.headD ⟨⟨[],[]⟩,1⟩).value.entries.Pairwise (fun a b => a.key ≠ b.key) := by
    rw [←hc]
    exact bucket_unique ctx g vs plan.colours c
  have hk : ∀ e ∈ (bs.headD ⟨⟨[],[]⟩,1⟩).value.entries,
      e.key.length = (bs.headD ⟨⟨[],[]⟩,1⟩).value.ports.length := by
    rw [←hc]
    exact bucket_key_length ctx g vs plan.colours c
  exact ⟨mergeAll_sorted ctx _ _ hs,mergeAll_unique ctx _ _ hu,
    mergeAll_key_length ctx _ _ hk⟩

theorem run_interpret_scalar (ctx : Context) (net : Network)
    (hports : (acquire ctx net).tensor.ports = []) :
    SemiprimeD1JetInterpretation.interpret ctx (run ctx net).words =
      weighted ctx (acquire ctx net).tensor.entries [] := by
  have hs := acquire_shape ctx net
  have ht := SemiprimeD1BoundaryLeafCanonical.acquire_tensor ctx net
  change SemiprimeD1JetInterpretation.interpret ctx (acquire ctx net).result.words = _
  rw [SemiprimeD1BoundaryLeafCanonical.acquire_words]
  symm
  apply weighted_eq_head ctx _ hs.2.1 ht.2
  intro e he
  apply List.eq_nil_of_length_eq_zero
  simpa only [hports, List.length_nil] using hs.2.2 e he

end RiemannGaussian.SemiprimeD1BoundaryRecordsShape
