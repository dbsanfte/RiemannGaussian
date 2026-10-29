/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPotential

/-! # Ordered overlap counting for literal endpoint occurrences
Parallel occurrences retain separate list positions throughout these bounds.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryOverlap
open SemiprimeD1BoundaryPlan

/-- Two original occurrences share an endpoint. -/
def touches (e f : Nat × Nat) : Bool :=
  (f.1 == e.1 || f.2 == e.1) || (f.1 == e.2 || f.2 == e.2)

/-- The maximum fold retains its initial lower bound. -/
theorem le_foldl_max (xs : List Nat) (a : Nat) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact (Nat.le_max_left a x).trans (ih (max a x))

/-- Each literal list member is bounded by its computed maximum fold. -/
theorem member_le_foldl_max (xs : List Nat) (a x : Nat) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y xs ih =>
    rcases List.mem_cons.mp hx with rfl | hh
    · exact (Nat.le_max_right a x).trans (le_foldl_max xs (max a x))
    · exact ih (max a y) hh

/-- Every valid endpoint degree is bounded by the executed maximum degree. -/
theorem degree_le_maxDegree (g : Graph) (v : Nat) (hv : v < g.vertices) :
    degree g v ≤ maxDegree g := by
  apply member_le_foldl_max
  exact List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩

/-- A union-filter count is bounded by the two individual occurrence counts. -/
theorem filter_or_length_le {α : Type} (xs : List α) (p q : α → Bool) :
    (xs.filter (fun x => p x || q x)).length ≤ (xs.filter p).length + (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] at * <;> omega

/-- All occurrences sharing either endpoint are counted by the endpoint degrees. -/
theorem touching_length_le_degrees (g : Graph) (e : Nat × Nat) :
    (g.edges.filter (touches e)).length ≤ degree g e.1 + degree g e.2 := by
  exact filter_or_length_le g.edges _ _

/-- One edge has at most twice the executed maximum degree many overlaps. -/
theorem touching_length_le (g : Graph) (e : Nat × Nat)
    (he : e ∈ g.edges) (hg : SemiprimeD1BoundaryPotential.Valid g) :
    (g.edges.filter (touches e)).length ≤ 2 * maxDegree g := by
  have h := hg e he
  have h1 := degree_le_maxDegree g e.1 h.1
  have h2 := degree_le_maxDegree g e.2 h.2.1
  have h3 := touching_length_le_degrees g e
  omega

/-- Sum of uniformly bounded original occurrence values. -/
theorem sum_map_le {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (hf : ∀ x ∈ xs, f x ≤ b) : (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h1 := hf x (by simp)
    have h2 := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    omega

/-- The number of ordered overlapping occurrence pairs is at most `2*M*Delta`. -/
theorem ordered_overlaps_le (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g) :
    ((g.edges.flatMap (fun e => g.edges.map (fun f => (e, f)))).filter
      (fun ef => touches ef.1 ef.2)).length ≤ 2 * g.edges.length * maxDegree g := by
  have he : ((g.edges.flatMap (fun e => g.edges.map (fun f => (e, f)))).filter
      (fun ef => touches ef.1 ef.2)).length =
      (g.edges.map (fun e => (g.edges.filter (touches e)).length)).sum := by
    simp [List.filter_flatMap, List.filter_map, List.length_flatMap, Function.comp_def]
  rw [he]
  have hh := sum_map_le g.edges (fun e => (g.edges.filter (touches e)).length)
    (2 * maxDegree g) (fun e he => touching_length_le g e he hg)
  nlinarith

end RiemannGaussian.SemiprimeD1BoundaryOverlap
