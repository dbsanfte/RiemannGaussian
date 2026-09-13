/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedRangeTree

/-!
# Integer endpoints for cached continuous range queries

A common positive denominator permits all query comparisons to use
integers. A one-time structural comparison transports the already proved
rational range table to this representation. Query results remain valid
throughout closed real intervals.
-/

namespace RiemannGaussian.CertifiedIntegerRangeTree

/-- A cached interval tree with integer cut coordinates. -/
inductive Tree (α : Type*) where
  | leaf (bound : α)
  | node (bound : α) (cut : ℤ) (left right : Tree α)

/-- The cached lower bound at the root. -/
def Tree.lower {α : Type*} : Tree α → α
  | .leaf b => b
  | .node b _ _ _ => b

/-- Real interpretation of a common-denominator coordinate. -/
noncomputable def coordinate (D : ℕ) (n : ℤ) : ℝ := (n : ℝ) / D

/-- Real coordinate order is exactly integer order for a positive denominator. -/
theorem coordinate_le {D : ℕ} (hD : 0 < D) (a b : ℤ) :
    coordinate D a ≤ coordinate D b ↔ a ≤ b := by
  unfold coordinate
  rw [div_le_div_iff_of_pos_right (by exact_mod_cast hD : (0 : ℝ) < D)]
  exact Int.cast_le

/-- Continuous meaning of all cached bounds in an integer tree. -/
def Valid {α β : Type*} [LE β] (D : ℕ) (coeBound : α → β) (f : ℝ → β) :
    Tree α → ℤ → ℤ → Prop
  | .leaf b, l, r => ∀ x ∈ Set.Icc (coordinate D l) (coordinate D r), coeBound b ≤ f x
  | .node b m left right, l, r =>
    (∀ x ∈ Set.Icc (coordinate D l) (coordinate D r), coeBound b ≤ f x) ∧
      Valid D coeBound f left l m ∧ Valid D coeBound f right m r

/-- Any valid tree supplies its root bound on the full closed interval. -/
theorem Valid.lower {α β : Type*} [LE β] {D : ℕ} {coeBound : α → β} {f : ℝ → β}
    {tree : Tree α} {l r : ℤ} (h : Valid D coeBound f tree l r)
    {x : ℝ} (hx : x ∈ Set.Icc (coordinate D l) (coordinate D r)) :
    coeBound tree.lower ≤ f x := by
  cases tree with
  | leaf b => exact h x hx
  | node b m left right => exact h.1 x hx

/-- Check exact bounds and scaled cuts against an already certified
rational tree. Leaf witnesses have already been checked upstream. -/
def agrees {α ω : Type*} [DecidableEq α] (D : ℕ) :
    Tree α → CertifiedRangeTree.Tree α ω → Bool
  | .leaf b, .leaf c _ => decide (b = c)
  | .node b m left right, .node c q oldLeft oldRight =>
    decide (b = c) && decide ((m : ℚ) / D = q) &&
      agrees D left oldLeft && agrees D right oldRight
  | _, _ => false

/-- A successful one-time structural comparison transports every
continuous bound to integer endpoints. -/
theorem agrees_sound {α β ω : Type*} [DecidableEq α] [LE β]
    (D : ℕ) (coeBound : α → β) (f : ℝ → β)
    (tree : Tree α) (old : CertifiedRangeTree.Tree α ω) {l r : ℤ}
    (hmatch : agrees D tree old = true)
    (hold : CertifiedRangeTree.Valid coeBound f (fun _ => True) old
      ((l : ℚ) / D) ((r : ℚ) / D)) : Valid D coeBound f tree l r := by
  induction tree generalizing old l r with
  | leaf b =>
    cases old with
    | leaf c w =>
      simp only [agrees, decide_eq_true_eq] at hmatch
      subst c
      intro x hx
      apply hold x trivial
      simpa only [coordinate, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hx
    | node c q left right => simp only [agrees, Bool.false_eq_true] at hmatch
  | node b m left right ihl ihr =>
    cases old with
    | leaf c w => simp only [agrees, Bool.false_eq_true] at hmatch
    | node c q oldLeft oldRight =>
      simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at hmatch
      obtain ⟨⟨⟨rfl, hq⟩, hl⟩, hr⟩ := hmatch
      subst q
      refine ⟨?_, ihl _ hl hold.2.1, ihr _ hr hold.2.2⟩
      intro x hx
      apply hold.1 x trivial
      simpa only [coordinate, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hx

/-- Integer range queries descend only at the requested interval endpoints. -/
def query {α : Type*} [SemilatticeInf α] (tree : Tree α) (l r a b : ℤ) : α :=
  match tree with
  | .leaf v => v
  | .node v m left right =>
    if a ≤ l ∧ r ≤ b then v else
    if b ≤ m then query left l m a b else
    if m ≤ a then query right m r a b else
      query left l m a b ⊓ query right m r a b

/-- Integer-only queries preserve continuous real bounds on the full
intersection of the queried and stored intervals. -/
theorem query_sound {α β : Type*} [SemilatticeInf α] [Preorder β]
    {D : ℕ} (hD : 0 < D) (coeBound : α → β) (hmono : Monotone coeBound)
    {f : ℝ → β} (tree : Tree α) {l r a b : ℤ}
    (h : Valid D coeBound f tree l r) {x : ℝ}
    (hx : x ∈ Set.Icc (coordinate D l) (coordinate D r))
    (hq : x ∈ Set.Icc (coordinate D a) (coordinate D b)) :
    coeBound (query tree l r a b) ≤ f x := by
  induction tree generalizing l r with
  | leaf v => exact h x hx
  | node v m left right ihl ihr =>
    change coeBound (if a ≤ l ∧ r ≤ b then v else
      if b ≤ m then query left l m a b else
      if m ≤ a then query right m r a b else
        query left l m a b ⊓ query right m r a b) ≤ f x
    split_ifs with hcover hleft hright
    · exact h.1 x hx
    · exact ihl h.2.1 ⟨hx.1, hq.2.trans ((coordinate_le hD b m).mpr hleft)⟩
    · exact ihr h.2.2 ⟨((coordinate_le hD m a).mpr hright).trans hq.1, hx.2⟩
    · rcases le_total x (coordinate D m) with hxm | hmx
      · exact (hmono inf_le_left).trans (ihl h.2.1 ⟨hx.1, hxm⟩)
      · exact (hmono inf_le_right).trans (ihr h.2.2 ⟨hmx, hx.2⟩)

end RiemannGaussian.CertifiedIntegerRangeTree
