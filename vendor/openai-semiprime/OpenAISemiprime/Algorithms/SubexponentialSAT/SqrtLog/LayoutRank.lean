import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRowSelection

namespace OAI.Algorithms

/-! Rational row-space bounds for literal integer constraint families. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module LayoutPullback LayoutExactBuckets LayoutRowSelection

variable {J I V : Type*} [Fintype J] [Fintype I] [Fintype V]

def rowSpace (C : J → V → ℤ) : Submodule ℚ (V → ℚ) :=
  Submodule.span ℚ (Set.range (rationalRows C))

noncomputable def rowRank (C : J → V → ℤ) : ℕ := finrank ℚ (rowSpace C)

omit [Fintype V] in
theorem rowRank_le_card (C : J → V → ℤ) : rowRank C ≤ Fintype.card J :=
  finrank_range_le_card (rationalRows C)

theorem rowRank_eq_matrix_rank (C : J → V → ℤ) :
    rowRank C = Matrix.rank (rationalRows C : Matrix J V ℚ) := by
  unfold rowRank rowSpace
  exact (Matrix.rank_eq_finrank_span_row (rationalRows C : Matrix J V ℚ)).symm

variable [DecidableEq V]

def rowLinear (owner : I → V) : (I → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun := row owner
  map_add' a b := by
    funext v
    simp only [row, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' c a := by
    funext v
    simp only [row, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

omit [Fintype J] in
omit [Fintype V] in
theorem rowSpace_pullback (owner : I → V) (C : J → I → ℤ) :
    rowSpace (pulledConstraints owner C) = (rowSpace C).map (rowLinear owner) := by
  rw [rowSpace, rowSpace, LinearMap.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℚ)
  apply congrArg Set.range
  funext j v
  exact row_map (Int.castRingHom ℚ) owner (C j) v

omit [Fintype J] in
omit [Fintype V] in
/-- Literal incidence pullback never increases rational constraint rank. -/
theorem rowRank_pullback_le (owner : I → V) (C : J → I → ℤ) :
    rowRank (pulledConstraints owner C) ≤ rowRank C := by
  unfold rowRank
  rw [rowSpace_pullback]
  exact Submodule.finrank_map_le _ _

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowSpace (fun k => C (e k)) = rowSpace C := by
  unfold rowSpace
  congr 1
  exact he.range_comp (rationalRows C)

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowRank_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowRank (fun k => C (e k)) = rowRank C := by
  unfold rowRank
  rw [rowSpace_reindex C e he]

omit [DecidableEq V] in
theorem finrank_biSup_le {K : Type*} (s : Finset K)
    (W : K → Submodule ℚ (V → ℚ)) :
    finrank ℚ (⨆ k ∈ s, W k : Submodule ℚ (V → ℚ)) ≤ ∑ k ∈ s, finrank ℚ (W k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hk]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

omit [DecidableEq V] in
theorem finrank_iSup_le {K : Type*} [Fintype K]
    (W : K → Submodule ℚ (V → ℚ)) :
    finrank ℚ (⨆ k, W k : Submodule ℚ (V → ℚ)) ≤ ∑ k, finrank ℚ (W k) := by
  have he : (⨆ k ∈ (Finset.univ : Finset K), W k) = ⨆ k, W k := by
    apply le_antisymm
    · exact iSup_le (fun k => iSup_le (fun _ => le_iSup W k))
    · exact iSup_le (fun k => le_iSup_of_le k
        (le_iSup_of_le (Finset.mem_univ k) le_rfl))
  have h := finrank_biSup_le (Finset.univ : Finset K) W
  rw [he] at h
  exact h

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_product {K : Type*} [Fintype K] (C : K → J → V → ℤ) :
    rowSpace (fun p : K × J => C p.1 p.2) = ⨆ k, rowSpace (C k) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨k,j⟩, rfl⟩
    exact (le_iSup (fun k => rowSpace (C k)) k)
      (Submodule.subset_span ⟨j, rfl⟩)
  · apply iSup_le
    intro k
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨(k,j), rfl⟩

omit [Fintype J] in
omit [DecidableEq V] in
theorem rowRank_product_le {K : Type*} [Fintype K] (C : K → J → V → ℤ) :
    rowRank (fun p : K × J => C p.1 p.2) ≤ ∑ k, rowRank (C k) := by
  unfold rowRank
  rw [rowSpace_product]
  exact finrank_iSup_le _

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_sum {K : Type*} [Fintype K] (C : J → V → ℤ) (D : K → V → ℤ) :
    rowSpace (Sum.elim C D) = rowSpace C ⊔ rowSpace D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    cases j with
    | inl j =>
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)
    | inr k =>
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  · apply sup_le
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨Sum.inl j, rfl⟩
    · apply Submodule.span_mono
      rintro _ ⟨k, rfl⟩
      exact ⟨Sum.inr k, rfl⟩

omit [Fintype J] [DecidableEq V] in
theorem rowRank_sum_le {K : Type*} [Fintype K] (C : J → V → ℤ) (D : K → V → ℤ) :
    rowRank (Sum.elim C D) ≤ rowRank C + rowRank D := by
  unfold rowRank
  rw [rowSpace_sum]
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

omit [Fintype J] in
/-- Any number of embedded block row families, plus arbitrary leftover rows. -/
theorem blocks_and_leftovers_rank_le {K L : Type*} [Fintype K] [Fintype L]
    (owner : K → I → V) (C : J → I → ℤ) (D : L → V → ℤ) :
    rowRank (Sum.elim (fun p : K × J => row (owner p.1) (C p.2)) D) ≤
      Fintype.card K * rowRank C + Fintype.card L := by
  apply (rowRank_sum_le _ _).trans
  apply Nat.add_le_add _ (rowRank_le_card D)
  calc
    _ ≤ ∑ k, rowRank (pulledConstraints (owner k) C) := rowRank_product_le _
    _ ≤ ∑ _k : K, rowRank C := Finset.sum_le_sum (fun k _ => rowRank_pullback_le (owner k) C)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
