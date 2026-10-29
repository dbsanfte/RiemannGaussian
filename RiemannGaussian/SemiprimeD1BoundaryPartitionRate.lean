/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryOverlap

/-! # Numeric guarantees for the actual finite colour-count search -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryPartitionRate
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryOverlap

/-- A maximum fold is bounded by a common upper bound on every input. -/
theorem foldl_max_le (xs : List Nat) (a b : Nat) (ha : a ≤ b)
    (hx : ∀ x ∈ xs, x ≤ b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih
    · exact max_le ha (hx x (by simp))
    · intro y hy
      exact hx y (by simp [hy])

/-- The actual maximum incidence degree never exceeds the occurrence count. -/
theorem maxDegree_le_edges (g : Graph) : maxDegree g ≤ g.edges.length := by
  apply foldl_max_le _ 0 _ (Nat.zero_le _)
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact List.length_filter_le _ _

/-- A valid nonempty graph has a genuinely positive executed maximum degree. -/
theorem maxDegree_pos (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : 0 < maxDegree g := by
  cases heq : g.edges with
  | nil => simp [heq] at hm
  | cons e es =>
    have he : e ∈ g.edges := by simp [heq]
    have hv := (hg e he).1
    have hmemb : e ∈ g.edges.filter (fun f => f.1 == e.1 || f.2 == e.1) := by
      simp [he]
    have hd : 0 < degree g e.1 := by
      apply List.length_pos_iff.mpr
      intro hh
      rw [hh] at hmemb
      simp at hmemb
    exact hd.trans_le (degree_le_maxDegree g e.1 hv)

/-- The literal bounded search menu, exposed only for its proof. -/
def menu (g : Graph) : List Nat := (List.range (g.edges.length + 1)).map (fun i => i + 2)

/-- The last menu candidate always passes when the graph has positive degree. -/
theorem last_passes (g : Graph) (hd : 0 < maxDegree g) :
    g.edges.length ≤ (g.edges.length + 2)^3 * maxDegree g := by
  have hb : g.edges.length ≤ (g.edges.length + 2)^3 :=
    (by omega : g.edges.length ≤ g.edges.length + 2).trans (le_self_pow₀ (by omega) (by decide))
  have hp : (g.edges.length + 2)^3 ≤ (g.edges.length + 2)^3 * maxDegree g := by
    nlinarith
  exact hb.trans hp

/-- A valid nonempty graph never takes the search's default branch. -/
theorem chooseK_found (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) :
    (menu g).find? (fun k => g.edges.length ≤ k^3 * maxDegree g) = some (chooseK g) := by
  have hd := maxDegree_pos g hg hm
  have hlast : g.edges.length + 2 ∈ menu g :=
    List.mem_map.mpr ⟨g.edges.length, List.mem_range.mpr (by omega), rfl⟩
  cases hh : (menu g).find? (fun k => g.edges.length ≤ k^3 * maxDegree g) with
  | none =>
    have hf := List.find?_eq_none.mp hh (g.edges.length + 2) hlast
    have ht := last_passes g hd
    simp [ht] at hf
  | some k =>
    have hk : chooseK g = k := by
      change ((menu g).find? (fun k => g.edges.length ≤ k^3 * maxDegree g)).getD 2 = k
      rw [hh]
      rfl
    simp only [hk]

/-- The returned actual colour count satisfies its literal integer cube test. -/
theorem chooseK_sufficient (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) : g.edges.length ≤ (chooseK g)^3 * maxDegree g := by
  have h := List.find?_some (chooseK_found g hg hm)
  exact of_decide_eq_true h

/-- The first successful value in an ascending list is at most any passing member. -/
theorem find_le_of_pairwise (xs : List Nat) (p : Nat → Bool) (a b : Nat)
    (hs : xs.Pairwise (· ≤ ·)) (ha : xs.find? p = some a)
    (hb : b ∈ xs) (hp : p b = true) : a ≤ b := by
  induction xs with
  | nil => simp at hb
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases hx : p x = true
    · have he : a = x := by simpa [hx] using ha.symm
      subst a
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact hhead b hb
    · have hpx : p x = false := Bool.eq_false_iff.mpr hx
      have hfind : xs.find? p = some a := by simpa [hpx] using ha
      have hmem : b ∈ xs := by
        rcases List.mem_cons.mp hb with he | hh
        · subst b; rw [hpx] at hp; contradiction
        · exact hh
      exact ih htail hfind hmem

/-- Actual first-success acquisition is bounded by every sufficient menu candidate. -/
theorem chooseK_le_candidate (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) (t : Nat) (ht : 2 ≤ t) (htop : t ≤ g.edges.length + 2)
    (hpass : g.edges.length ≤ t^3 * maxDegree g) : chooseK g ≤ t := by
  apply find_le_of_pairwise (menu g) _ _ t
  · exact List.pairwise_le_range.map (fun i => i + 2) (fun a b hab => by omega)
  · exact chooseK_found g hg hm
  · exact List.mem_map.mpr ⟨t - 2, List.mem_range.mpr (by omega), by omega⟩
  · exact decide_eq_true hpass

/-- Beyond the minimum menu size, the immediately preceding cube test failed. -/
theorem chooseK_previous_fails (g : Graph) (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hm : 0 < g.edges.length) (hk : 2 < chooseK g) :
    (chooseK g - 1)^3 * maxDegree g < g.edges.length := by
  have htop := (SemiprimeD1BoundaryChoice.chooseK_bounds g).2
  by_contra hn
  have hp : g.edges.length ≤ (chooseK g - 1)^3 * maxDegree g := by omega
  have hh := chooseK_le_candidate g hg hm (chooseK g - 1) (by omega) (by omega) hp
  omega

end RiemannGaussian.SemiprimeD1BoundaryPartitionRate
