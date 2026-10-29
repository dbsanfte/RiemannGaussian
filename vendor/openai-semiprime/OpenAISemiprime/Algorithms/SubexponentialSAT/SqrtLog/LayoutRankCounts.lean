import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes

namespace OAI.Algorithms

/-! Disjoint head counts and the single total uncovered-coordinate budget. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

variable {I U G : Type*} [Fintype I] [Fintype U] [Fintype G]
variable [DecidableEq I] [DecidableEq G]

omit [DecidableEq I] in
theorem sum_card_heads (head : I → G) :
    (∑ g, Fintype.card {i : I // head i = g}) = Fintype.card I := by
  simpa using Fintype.sum_fiberwise head (fun _ : I => (1 : ℕ))

omit [DecidableEq I] in
theorem sum_card_restricted_heads (head : I → G) (p : I → Prop) [DecidablePred p] :
    (∑ g, Fintype.card {v : {i : I // head i = g} // p v.val}) =
      Fintype.card {i : I // p i} := by
  have he (g : G) :
      Fintype.card {v : {i : I // head i = g} // p v.val} =
        Fintype.card {v : {i : I // p i} // head v.val = g} := by
    apply Fintype.card_congr
    exact {
      toFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp_rw [he]
  exact sum_card_heads (fun v : {i : I // p i} => head v.val)

variable {b : ℕ} {label : I → U}

theorem card_uncovered_eq (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) :
    Fintype.card {i : I // i ∉ Set.range P.embed} = P.leftovers.card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp [SubexponentialSAT.BlockPacking.CompleteBlocks.leftovers,
    SubexponentialSAT.BlockPacking.CompleteBlocks.covered, Set.mem_range]

theorem uncovered_add_blocks (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) :
    Fintype.card {i : I // i ∉ Set.range P.embed} + b * Fintype.card U =
      Fintype.card I := by
  rw [card_uncovered_eq]
  simpa using P.card_leftovers_add_covered

theorem sum_card_uncovered_heads (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (head : I → G) :
    (∑ g, Fintype.card {v : {i : I // head i = g} // v.val ∉ Set.range P.embed}) =
      P.leftovers.card := by
  classical
  exact (sum_card_restricted_heads head (fun i => i ∉ Set.range P.embed)).trans
    (card_uncovered_eq P)

/-- Complete joint fibers occupy disjoint subsets of the universal heads.
There is a single ambient block cardinality, not one per color. -/
theorem sum_card_joint_le {r Q Δ : ℕ} (t : Fin Q) (i : Fin Δ) :
    (∑ g : Fin r, Fintype.card (Joint t g i)) ≤
      Fintype.card (UniversalType r Q Δ) := by
  calc
    _ ≤ ∑ g : Fin r, Fintype.card (Side (Δ := Δ) t g) :=
      Finset.sum_le_sum (fun g _ => card_joint_le_side t g i)
    _ = _ := sum_card_heads (fun u : UniversalType r Q Δ => u.head t)

/-- Coverage pays for leftover coordinates once in the total rank sum. -/
theorem block_budget_le (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hcover : (1 - ε) * (Fintype.card I : ℚ) ≤ b * (Fintype.card U : ℚ)) :
    (b : ℚ) * (ε * Fintype.card U) + P.leftovers.card ≤
      2 * ε * Fintype.card I := by
  have hsum : (P.leftovers.card : ℚ) + (b : ℚ) * Fintype.card U = Fintype.card I := by
    have h : P.leftovers.card + b * Fintype.card U = Fintype.card I := by
      simpa using P.card_leftovers_add_covered
    exact_mod_cast h
  have hpacked : (b : ℚ) * Fintype.card U ≤ Fintype.card I := by
    have hnonneg : (0 : ℚ) ≤ P.leftovers.card := by positivity
    linarith
  have hfirst : (b : ℚ) * (ε * Fintype.card U) ≤ ε * Fintype.card I := by
    nlinarith [mul_le_mul_of_nonneg_left hpacked hε]
  have hleft : (P.leftovers.card : ℚ) ≤ ε * Fintype.card I := by linarith
  linarith

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
