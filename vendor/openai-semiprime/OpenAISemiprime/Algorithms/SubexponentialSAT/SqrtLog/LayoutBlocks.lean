import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutHeadPullback
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutIndexed
import OpenAISemiprime.Algorithms.SubexponentialSAT.BlockPacking

namespace OAI.Algorithms

/-! Assemble complete copies of an actual universal block, with singleton
constraints on uncovered incidences. The scalar ring is arbitrary. -/
namespace SubexponentialSAT.SqrtLog.LayoutBlocks

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {U I F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

noncomputable def assembledRow (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) : I → I → Polynomial O :=
  Function.extend P.embed
    (fun z => row (P.blockEmbedding z.1) (rows z.2))
    (fun i v => Polynomial.C (if v = i then 1 else 0))

omit [DecidableEq U] [Fintype I] in
@[simp] theorem assembledRow_apply (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) (j : Fin b) (u : U) :
    assembledRow P rows (P.embed (j,u)) = row (P.blockEmbedding j) (rows u) :=
  P.embed.injective.extend_apply _ _ (j,u)

omit [DecidableEq U] [Fintype I] in
@[simp] theorem assembledRow_outside (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) (i : I) (hi : i ∉ Set.range P.embed) :
    assembledRow P rows i = (fun v => Polynomial.C (if v = i then 1 else 0)) :=
  Function.extend_apply' _ _ i hi

def copyHead
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (label : I → U) (t : Fin Q) (i : I) : G := C.head t (label i)

abbrev RowIndex
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :=
  (Fin b × Fin (C.rowCount t g)) ⊕
    {v : {i : I // copyHead C label t i = g} // v.val ∉ Set.range P.embed}

def embedHead
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) (j : Fin b) :
    {u : U // C.head t u = g} → {i : I // copyHead C label t i = g} :=
  fun u => ⟨P.embed (j,u.val), by simpa [copyHead, P.type_eq] using u.property⟩

noncomputable def constraints
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :
    RowIndex C P t g → {i : I // copyHead C label t i = g} → ℤ
  | Sum.inl jk => row (embedHead C P t g jk.1) (C.constraints t g jk.2)
  | Sum.inr v => Pi.single v.val 1

noncomputable def data
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t) :
    Layout.Data (O := O) (G := G) (id : I → I) factor Q R := by
  classical
  let head := copyHead C label
  let J := RowIndex C P
  let embedHead := embedHead C P
  let constraints := constraints C P
  refine Layout.ofIndexed C.node C.units head color (assembledRow P C.row) ?_ ?_
    J constraints ?_
  · intro i v
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      rw [assembledRow_apply]
      apply row_origin (P.blockEmbedding j) (C.row u) u
      intro w
      simpa [Pi.single_apply, eq_comm] using C.row_origin u w
    · by_cases hv : v = i <;> simp [assembledRow_outside P C.row i hi, hv]
  · intro i v
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      rw [assembledRow_apply]
      exact row_degree _ _ R (C.row_degree u) v
    · by_cases hv : v = i <;> simp [assembledRow_outside P C.row i hi, hv]
  · intro t i g hg z hz
    by_cases hi : i ∈ Set.range P.embed
    · obtain ⟨⟨j,u⟩, rfl⟩ := hi
      have htype : label (P.embed (j,u)) = u := P.type_eq j u
      have hgc : g ≠ C.color u t := by
        intro heq
        apply hg
        rw [← hcolor (P.embed (j,u)) t, htype]
        exact heq
      have hc : ∀ a, signature (C.constraints t g)
          (duplicate (embedHead t g j) z) a = 0 := by
        intro a
        have hh := hz (Sum.inl (j,a))
        change value (row (embedHead t g j) (C.constraints t g a)) z = 0 at hh
        rw [value_pullback] at hh
        exact hh
      have hh := C.locality t u g hgc (duplicate (embedHead t g j) z) hc
      change value (fun v : {i : I // head t i = g} =>
        (assembledRow P C.row (P.embed (j,u)) v.val).eval (C.node t)) z = 0
      rw [assembledRow_apply]
      simp_rw [row_eval]
      have he (a : U) : C.head t a = head t (P.blockEmbedding j a) := by
        change C.head t a = C.head t (label (P.embed (j, a)))
        rw [P.type_eq]
      have hr (v : {i : I // head t i = g}) :
          row (P.blockEmbedding j) (fun a => (C.row u a).eval (C.node t)) v.val =
            row (embedHead t g j)
              (fun a : {a : U // C.head t a = g} => (C.row u a.val).eval (C.node t)) v := by
        exact LayoutHeadPullback.row_restrict (P.blockEmbedding j)
          (C.head t) (head t) he g _ v
      simp_rw [hr]
      rw [value_pullback]
      exact hh
    · change (∑ v : {i : I // head t i = g},
        (assembledRow P C.row i v.val).eval (C.node t) * (z v : O)) = 0
      rw [assembledRow_outside P C.row i hi]
      by_cases hig : head t i = g
      · let v : {i : I // head t i = g} := ⟨i,hig⟩
        have hzv : z v = 0 := by
          have hh := hz (Sum.inr ⟨v,hi⟩)
          simpa [constraints, LayoutBlocks.constraints, signature, Pi.single_apply] using hh
        have hs : (∑ a : {i : I // head t i = g},
            (if a.val = i then (1 : O) else 0) * (z a : O)) = (z v : O) := by
          have he (a : {i : I // head t i = g}) : (a.val = i) ↔ a = v := by
            exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
          simp_rw [he]
          simp
        simp only [Polynomial.eval_C, hs, hzv, Int.cast_zero]
      · apply Finset.sum_eq_zero
        intro v _
        have hv : v.val ≠ i := by
          intro h
          exact hig (h ▸ v.property)
        simp [hv]

end SubexponentialSAT.SqrtLog.LayoutBlocks

end OAI.Algorithms
