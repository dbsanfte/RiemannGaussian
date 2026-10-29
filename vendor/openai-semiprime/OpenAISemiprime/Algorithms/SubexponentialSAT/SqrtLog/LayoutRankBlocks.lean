import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankCounts

namespace OAI.Algorithms

/-! Rank accumulation for the concrete complete-block layout and its pullback. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LayoutPullback LayoutExactBuckets

variable {U I V F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

omit [Fintype G] in
theorem block_constraints_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :
    rowRank (LayoutBlocks.constraints C P t g) ≤ b * rowRank (C.constraints t g) +
      Fintype.card {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
        v.val ∉ Set.range P.embed} := by
  have he : LayoutBlocks.constraints C P t g =
      Sum.elim (fun p => row (LayoutBlocks.embedHead C P t g p.1) (C.constraints t g p.2))
        (fun v => Pi.single v.val (1 : ℤ)) := by
    funext j
    cases j <;> rfl
  rw [he]
  simpa only [Fintype.card_fin] using blocks_and_leftovers_rank_le (LayoutBlocks.embedHead C P t g)
    (C.constraints t g)
    (fun v : {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
      v.val ∉ Set.range P.embed} => Pi.single v.val (1 : ℤ))

theorem blocks_total_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) :
    (∑ g, (rowRank (LayoutBlocks.constraints C P t g) : ℚ)) ≤
      (b : ℚ) * ∑ g, (rowRank (C.constraints t g) : ℚ) + P.leftovers.card := by
  calc
    _ ≤ ∑ g, ((b : ℚ) * rowRank (C.constraints t g) +
        Fintype.card {v : {i : I // LayoutBlocks.copyHead C label t i = g} //
          v.val ∉ Set.range P.embed}) := by
      apply Finset.sum_le_sum
      intro g _
      exact_mod_cast block_constraints_rank_le C P t g
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      exact_mod_cast sum_card_uncovered_heads P (LayoutBlocks.copyHead C label t)

omit [Fintype G] in
theorem blocks_data_rank_eq
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (t : Fin Q) (g : G) :
    rowRank ((LayoutBlocks.data C P factor color hcolor).constraints t g) =
      rowRank (LayoutBlocks.constraints C P t g) := by
  change rowRank (fun j => LayoutBlocks.constraints C P t g
    ((Fintype.equivFin (LayoutBlocks.RowIndex C P t g)).symm j)) = _
  exact rowRank_reindex _ _ (Equiv.surjective _)

theorem blocks_data_total_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (t : Fin Q) (ε : ℚ) (hε : 0 ≤ ε)
    (hbase : (∑ g, (rowRank (C.constraints t g) : ℚ)) ≤ ε * Fintype.card U)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card U : ℚ)) :
    (∑ g, (rowRank ((LayoutBlocks.data C P factor color hcolor).constraints t g) : ℚ)) ≤
      2 * ε * Fintype.card I := by
  simp_rw [blocks_data_rank_eq]
  calc
    _ ≤ (b : ℚ) * ∑ g, (rowRank (C.constraints t g) : ℚ) + P.leftovers.card :=
      blocks_total_rank_le C P t
    _ ≤ (b : ℚ) * (ε * Fintype.card U) + P.leftovers.card := by gcongr
    _ ≤ _ := block_budget_le P ε hε hcover

omit [Fintype G] in
theorem head_pullback_rank_le (owner : I → V) (factor : I → F)
    (head : Fin Q → V → G)
    (C : Layout.Data (O := O) (G := G) (id : I → I) factor Q R)
    (hhead : ∀ t i, C.head t i = head t (owner i)) (t : Fin Q) (g : G) :
    rowRank ((LayoutHeadPullback.pullback owner factor head C hhead).constraints t g) ≤
      rowRank (C.constraints t g) :=
  rowRank_pullback_le _ _

theorem head_pullback_total_rank_le (owner : I → V) (factor : I → F)
    (head : Fin Q → V → G)
    (C : Layout.Data (O := O) (G := G) (id : I → I) factor Q R)
    (hhead : ∀ t i, C.head t i = head t (owner i)) (t : Fin Q) :
    (∑ g, (rowRank ((LayoutHeadPullback.pullback owner factor head C hhead).constraints t g) : ℚ)) ≤
      ∑ g, (rowRank (C.constraints t g) : ℚ) := by
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast head_pullback_rank_le owner factor head C hhead t g

theorem pulled_blocks_total_rank_le
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (owner : I → V) (head : Fin Q → V → G)
    (hhead : ∀ t i, (LayoutBlocks.data C P factor color hcolor).head t i = head t (owner i))
    (t : Fin Q) (ε : ℚ) (hε : 0 ≤ ε)
    (hbase : (∑ g, (rowRank (C.constraints t g) : ℚ)) ≤ ε * Fintype.card U)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card U : ℚ)) :
    (∑ g, (rowRank ((LayoutHeadPullback.pullback owner factor head
      (LayoutBlocks.data C P factor color hcolor) hhead).constraints t g) : ℚ)) ≤
        2 * ε * Fintype.card I := by
  exact (head_pullback_total_rank_le owner factor head _ hhead t).trans
    (blocks_data_total_rank_le C P factor color hcolor t ε hε hbase hcover)

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
