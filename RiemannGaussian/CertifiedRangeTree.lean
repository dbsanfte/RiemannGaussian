/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!+# Cached continuous bounds with logarithmic range queries

Each leaf certifies a complete real interval. Internal nodes retain a
checked common lower bound for their children. Queries reuse these cached
bounds and descend only at the requested interval's endpoints. A product
order permits one tree to carry both value and curvature bounds.
-/

namespace RiemannGaussian.CertifiedRangeTree

/-- A continuous interval tree with a cached bound at every node. -/
inductive Tree (α ω : Type*) where
  | leaf (bound : α) (witness : ω)
  | node (bound : α) (cut : ℚ) (left right : Tree α ω)

/-- The cached common lower bound at the root of a tree. -/
def Tree.lower {α ω : Type*} : Tree α ω → α
  | .leaf b _ => b
  | .node b _ _ _ => b

/-- Check every continuous leaf and the ordering of every cached bound. -/
def check {α ω : Type*} [LE α] [DecidableLE α]
    (leafCheck : ℚ → ℚ → α → ω → Bool) : Tree α ω → ℚ → ℚ → Bool
  | .leaf b w, l, r => leafCheck l r b w
  | .node b m left right, l, r =>
    decide (b ≤ left.lower) && decide (b ≤ right.lower) &&
      check leafCheck left l m && check leafCheck right m r

/-- All nodes carry valid continuous bounds, with the designated analytic
domain retained at every leaf and every cached interval. -/
def Valid {α β ω : Type*} [LE β] (coeBound : α → β)
    (f : ℝ → β) (P : ℝ → Prop) : Tree α ω → ℚ → ℚ → Prop
  | .leaf b _, l, r => ∀ x, P x → x ∈ Set.Icc (l : ℝ) r → coeBound b ≤ f x
  | .node b m left right, l, r =>
    (∀ x, P x → x ∈ Set.Icc (l : ℝ) r → coeBound b ≤ f x) ∧
      Valid coeBound f P left l m ∧ Valid coeBound f P right m r

/-- A valid node supplies its cached bound on the full closed interval. -/
theorem Valid.lower {α β ω : Type*} [LE β] {coeBound : α → β}
    {f : ℝ → β} {P : ℝ → Prop} {tree : Tree α ω} {l r : ℚ}
    (h : Valid coeBound f P tree l r) {x : ℝ}
    (hp : P x) (hx : x ∈ Set.Icc (l : ℝ) r) : coeBound tree.lower ≤ f x := by
  cases tree with
  | leaf b w => exact h x hp hx
  | node b m left right => exact h.1 x hp hx

/-- Exact cache comparisons and a sound leaf checker establish continuous
validity throughout the complete tree. -/
theorem check_sound {α β ω : Type*} [Preorder α] [DecidableLE α] [Preorder β]
    (coeBound : α → β) (hmono : Monotone coeBound) (f : ℝ → β) (P : ℝ → Prop)
    (leafCheck : ℚ → ℚ → α → ω → Bool)
    (hleaf : ∀ l r b w, leafCheck l r b w = true →
      ∀ x, P x → x ∈ Set.Icc (l : ℝ) r → coeBound b ≤ f x)
    (tree : Tree α ω) {l r : ℚ} (h : check leafCheck tree l r = true) :
    Valid coeBound f P tree l r := by
  induction tree generalizing l r with
  | leaf b w => exact hleaf l r b w h
  | node b m left right ihl ihr =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := ihl h.1.2
    have hr := ihr h.2
    refine ⟨?_, hl, hr⟩
    intro x hp hx
    rcases le_total x (m : ℝ) with hxm | hmx
    · exact (hmono h.1.1.1).trans (hl.lower hp ⟨hx.1, hxm⟩)
    · exact (hmono h.1.1.2).trans (hr.lower hp ⟨hmx, hx.2⟩)

/-- Query a subinterval, reusing every completely covered cached node.
Only the paths to the query endpoints require further descent. -/
def query {α ω : Type*} [SemilatticeInf α] (tree : Tree α ω)
    (l r a b : ℚ) : α :=
  if a ≤ l ∧ r ≤ b then tree.lower else
    match tree with
    | .leaf v _ => v
    | .node _ m left right =>
      if b ≤ m then query left l m a b else
      if m ≤ a then query right m r a b else
        query left l m a b ⊓ query right m r a b

/-- Every successful table proof supports arbitrary closed-interval
queries; endpoint equality cannot leave a gap between children. -/
theorem query_sound {α β ω : Type*} [SemilatticeInf α] [Preorder β]
    (coeBound : α → β) (hmono : Monotone coeBound)
    {f : ℝ → β} {P : ℝ → Prop} (tree : Tree α ω) {l r a b : ℚ}
    (h : Valid coeBound f P tree l r) {x : ℝ} (hp : P x)
    (hx : x ∈ Set.Icc (l : ℝ) r) (hq : x ∈ Set.Icc (a : ℝ) b) :
    coeBound (query tree l r a b) ≤ f x := by
  induction tree generalizing l r with
  | leaf v w =>
    simpa only [query, Tree.lower, ite_self] using h x hp hx
  | node v m left right ihl ihr =>
    rw [query]
    split_ifs with hcover hleft hright
    · exact h.lower hp hx
    · have hm : x ≤ (m : ℝ) := hq.2.trans (by exact_mod_cast hleft)
      exact ihl h.2.1 ⟨hx.1, hm⟩
    · have hm : (m : ℝ) ≤ x := (by exact_mod_cast hright : (m : ℝ) ≤ a).trans hq.1
      exact ihr h.2.2 ⟨hm, hx.2⟩
    · rcases le_total x (m : ℝ) with hxm | hmx
      · exact (hmono inf_le_left).trans (ihl h.2.1 ⟨hx.1, hxm⟩)
      · exact (hmono inf_le_right).trans (ihr h.2.2 ⟨hmx, hx.2⟩)

end RiemannGaussian.CertifiedRangeTree
