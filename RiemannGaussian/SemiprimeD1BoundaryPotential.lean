/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryChoice

/-! # Literal conditional-potential identities
The integer potential is evaluated from the original endpoint occurrences.
These identities concern the executable expression, including every diagonal
and parallel occurrence; no supplied numerical load matrix is introduced.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false

namespace RiemannGaussian.SemiprimeD1BoundaryPotential
open SemiprimeD1BoundaryPlan

/-- Endpoint well-formedness needed by the local probability calculation. -/
def Valid (g : Graph) : Prop :=
  ∀ e ∈ g.edges, e.1 < g.vertices ∧ e.2 < g.vertices ∧ e.1 ≠ e.2

/-- Every acquired incidence has one left and one disjoint right endpoint. -/
theorem graph_valid (net : SemiprimeD1TensorNetwork.Network) : Valid (graph net) := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hl := (SemiprimeD1TensorNetwork.owner net.rows i).isLt
  have hr := i.1.isLt
  have hv : (graph net).vertices = net.leftCount + net.rows.length := by
    simp [graph, SemiprimeD1TensorNetwork.vertices]
  rw [hv]
  constructor
  · omega
  constructor <;> omega

/-- A fully fixed local factor has no remaining endpoint colours to enumerate. -/
theorem unknown_nil (fixed : List Nat) (es : List (Nat × Nat))
    (hf : ∀ e ∈ es, e.1 < fixed.length ∧ e.2 < fixed.length) :
    (endpoints es).filter (fun v => !(v < fixed.length)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv
  have hm : v ∈ es.flatMap (fun e => [e.1, e.2]) := List.mem_eraseDups.mp hv
  obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hm
  have hh := hf e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> simp_all

/-- Exact completion of a local one/two-edge conditional expectation. -/
theorem localExpectation_fixed (scale k : Nat) (fixed : List Nat) (load : Load)
    (es : List (Nat × Nat))
    (hf : ∀ e ∈ es, e.1 < fixed.length ∧ e.2 < fixed.length) :
    (localExpectation scale k fixed load es).value =
      if es.all (fun e => indicator load (fixed.getD e.1 0) (fixed.getD e.2 0))
      then k ^ scale else 0 := by
  have hu := unknown_nil fixed es hf
  have ha : es.all (fun e => indicator load (readColour fixed [] [] e.1)
      (readColour fixed [] [] e.2)) =
      es.all (fun e => indicator load (fixed.getD e.1 0) (fixed.getD e.2 0)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor <;> intro h e he
    · simpa only [readColour, ite_eq_left (hf e he).1, ite_eq_left (hf e he).2] using h e he
    · simpa only [readColour, ite_eq_left (hf e he).1, ite_eq_left (hf e he).2] using h e he
  simp only [localExpectation, hu, List.length_nil, colourWords, List.filter_cons,
    List.filter_nil, ha]
  split <;> simp_all

/-- Integer indicator of the actual fully fixed edge event. -/
def atom (load : Load) (fixed : List Nat) (e : Nat × Nat) : Int :=
  if indicator load (fixed.getD e.1 0) (fixed.getD e.2 0) then 1 else 0

/-- The measured load is the sum of its exact occurrence indicators. -/
theorem loadValue_sum (g : Graph) (fixed : List Nat) (load : Load) :
    (loadValue g fixed load : Int) = (g.edges.map (atom load fixed)).sum := by
  obtain ⟨vertices, es⟩ := g
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [loadValue, List.filter_cons, List.map_cons, List.sum_cons, atom] at *
    split_ifs <;> simp_all [Int.add_comm]

/-- A fixed single-edge expectation is exactly its integer event times the scale. -/
theorem single_fixed (k : Nat) (fixed : List Nat) (load : Load) (e : Nat × Nat)
    (he : e.1 < fixed.length ∧ e.2 < fixed.length) :
    ((localExpectation 2 k fixed load [e]).value : Int) =
      (k : Int)^2 * atom load fixed e := by
  rw [localExpectation_fixed 2 k fixed load [e] (by simpa only [List.mem_singleton] using
    (show ∀ x, x = e → x.1 < fixed.length ∧ x.2 < fixed.length from fun x hx => hx ▸ he))]
  simp only [List.all_cons, List.all_nil, Bool.and_true, atom]
  split_ifs <;> simp_all

/-- A fixed ordered pair retains both original events, including the diagonal. -/
theorem pair_fixed (k : Nat) (fixed : List Nat) (load : Load) (e f : Nat × Nat)
    (he : e.1 < fixed.length ∧ e.2 < fixed.length)
    (hf : f.1 < fixed.length ∧ f.2 < fixed.length) :
    ((localExpectation 4 k fixed load [e, f]).value : Int) =
      (k : Int)^4 * atom load fixed e * atom load fixed f := by
  rw [localExpectation_fixed 4 k fixed load [e, f] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact he
    · exact hf)]
  simp only [List.all_cons, List.all_nil, Bool.and_true, atom]
  split_ifs <;> simp_all

/-- One load's executed quadratic expression after every endpoint is fixed. -/
theorem load_square (g : Graph) (k : Nat) (fixed : List Nat) (load : Load)
    (hf : ∀ e ∈ g.edges, e.1 < fixed.length ∧ e.2 < fixed.length) :
    (((g.edges.flatMap (fun e => g.edges.map (fun f =>
      (localExpectation 4 k fixed load [e, f]).value))).sum : Nat) : Int) -
      2 * (meanNumerator g.edges.length k load : Int) *
        ((g.edges.map (fun e => (localExpectation 2 k fixed load [e]).value)).sum : Nat) +
      (meanNumerator g.edges.length k load : Int)^2 =
    ((k : Int)^2 * (loadValue g fixed load : Int) -
      (meanNumerator g.edges.length k load : Int))^2 := by
  have hs : (((g.edges.map (fun e =>
      (localExpectation 2 k fixed load [e]).value)).sum : Nat) : Int) =
      (k : Int)^2 * (loadValue g fixed load : Int) := by
    rw [Nat.cast_list_sum, List.map_map, loadValue_sum]
    have he : g.edges.map (fun e => ((localExpectation 2 k fixed load [e]).value : Int)) =
        g.edges.map (fun e => (k : Int)^2 * atom load fixed e) := by
      apply List.map_congr_left
      intro e he
      exact single_fixed k fixed load e (hf e he)
    change (g.edges.map (fun e => ((localExpectation 2 k fixed load [e]).value : Int))).sum = _
    rw [he, List.sum_map_mul_left]
  have hp : (((g.edges.flatMap (fun e => g.edges.map (fun f =>
      (localExpectation 4 k fixed load [e, f]).value))).sum : Nat) : Int) =
      (k : Int)^4 * (loadValue g fixed load : Int)^2 := by
    rw [Nat.cast_list_sum, List.map_flatMap, loadValue_sum]
    have he : g.edges.flatMap (fun e => (g.edges.map (fun f =>
        (localExpectation 4 k fixed load [e, f]).value)).map (fun x : Nat => (x : Int))) =
        g.edges.flatMap (fun e => g.edges.map (fun f =>
          (k : Int)^4 * atom load fixed e * atom load fixed f)) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro e he
      rw [List.map_map]
      apply List.map_congr_left
      intro f hh
      exact pair_fixed k fixed load e f (hf e he) (hf f hh)
    rw [he]
    change ((g.edges.map (fun e => g.edges.map (fun f =>
      (k : Int)^4 * atom load fixed e * atom load fixed f))).flatten).sum = _
    rw [List.sum_flatten]
    simp only [List.map_map, Function.comp_def, List.sum_map_mul_left, List.sum_map_mul_right]
    ring
  rw [hs, hp]
  ring

/-- At completion the literal scaled potential is a sum of nonnegative squares. -/
theorem potential_fixed (g : Graph) (k : Nat) (fixed : List Nat)
    (hf : ∀ e ∈ g.edges, e.1 < fixed.length ∧ e.2 < fixed.length) :
    (potential g k fixed).value = ((loads k).map (fun load =>
      ((k : Int)^2 * (loadValue g fixed load : Int) -
        (meanNumerator g.edges.length k load : Int))^2)).sum := by
  unfold potential
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro load _
  simpa only [Nat.cast_list_sum, List.map_flatMap, List.map_map, Function.comp_def] using
    load_square g k fixed load hf

end RiemannGaussian.SemiprimeD1BoundaryPotential
