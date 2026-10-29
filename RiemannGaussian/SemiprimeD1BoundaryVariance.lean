/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryInitialVariance
import RiemannGaussian.SemiprimeD1BoundaryOverlap

/-! # Covariance accounting for original ordered edge occurrences -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BoundaryVariance
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryInitialVariance
open SemiprimeD1BoundaryOverlap SemiprimeD1BoundaryConditionalAverage

/-- Original ordered edge pairs, including every diagonal and parallel position. -/
def pairs (g : Graph) : List ((Nat × Nat) × (Nat × Nat)) :=
  g.edges.flatMap (fun e => g.edges.map (fun f => (e, f)))

/-- Exact scaled covariance numerator for one ordered occurrence pair. -/
def covariance (k : Nat) (load : Load) (ef : (Nat × Nat) × (Nat × Nat)) : Int :=
  ((localExpectation 4 k [] load [ef.1, ef.2]).value : Int) - (eventCount k load : Int)^2

/-- Membership in the ordered occurrence list retains both actual edge witnesses. -/
theorem pairs_mem (g : Graph) (ef : (Nat × Nat) × (Nat × Nat))
    (h : ef ∈ pairs g) : ef.1 ∈ g.edges ∧ ef.2 ∈ g.edges := by
  obtain ⟨e, he, hh⟩ := List.mem_flatMap.mp h
  obtain ⟨f, hf, hpair⟩ := List.mem_map.mp hh
  cases hpair
  exact ⟨he, hf⟩

/-- Disjoint original occurrences have exactly zero covariance. -/
theorem covariance_zero (g : Graph) (k : Nat) (load : Load)
    (ef : (Nat × Nat) × (Nat × Nat)) (hm : ef ∈ pairs g)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (ht : touches ef.1 ef.2 = false) :
    covariance k load ef = 0 := by
  obtain ⟨he, hf⟩ := pairs_mem g ef hm
  have hae : ef.1.1 ≠ ef.2.1 := by intro h; simp [touches, h] at ht
  have haf : ef.1.1 ≠ ef.2.2 := by intro h; simp [touches, h] at ht
  have hbe : ef.1.2 ≠ ef.2.1 := by intro h; simp [touches, h] at ht
  have hbf : ef.1.2 ≠ ef.2.2 := by intro h; simp [touches, h] at ht
  unfold covariance
  rw [pair_initial_disjoint k ef.1.1 ef.1.2 ef.2.1 ef.2.2 load
    (hg _ he).2.2 hae haf hbe hbf (hg _ hf).2.2]
  push_cast
  ring

/-- Each actual pair contributes at most one quarter-scale when it overlaps. -/
theorem covariance_le_touch (g : Graph) (k : Nat) (load : Load)
    (ef : (Nat × Nat) × (Nat × Nat)) (hm : ef ∈ pairs g)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hk : 0 < k) :
    4 * covariance k load ef ≤ if touches ef.1 ef.2 then (k : Int)^4 else 0 := by
  cases ht : touches ef.1 ef.2 with
  | false => rw [covariance_zero g k load ef hm hg ht]; simp
  | true =>
    obtain ⟨he, hf⟩ := pairs_mem g ef hm
    exact covariance_quarter g k load ef.1 ef.2 hk he hf hg

/-- Pointwise comparison of two integer occurrence sums. -/
theorem sum_map_le_sum {α : Type} (xs : List α) (f h : α → Int)
    (hle : ∀ x ∈ xs, f x ≤ h x) : (xs.map f).sum ≤ (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h1 := hle x (by simp)
    have h2 := ih (fun y hy => hle y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The exact covariance sum is bounded by the literal overlap-pair count. -/
theorem covariance_sum_le (g : Graph) (k : Nat) (load : Load)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hk : 0 < k) :
    4 * ((pairs g).map (covariance k load)).sum ≤
      (2 * g.edges.length * maxDegree g : Nat) * (k : Int)^4 := by
  have hh := sum_map_le_sum (pairs g) (fun ef => 4 * covariance k load ef)
    (fun ef => if touches ef.1 ef.2 then (k : Int)^4 else 0)
    (fun ef hm => covariance_le_touch g k load ef hm hg hk)
  rw [List.sum_map_mul_left] at hh
  have he {α : Type} (xs : List α) (p : α → Bool) (w : Int) :
      ((xs.map (fun x => if p x then w else 0)).sum) = ((xs.filter p).length : Int) * w := by
    induction xs with
    | nil => simp
    | cons x xs ih => cases hp : p x <;> simp [hp, ih, add_mul, add_comm]
  rw [he] at hh
  have hb := ordered_overlaps_le g hg
  change ((pairs g).filter (fun ef => touches ef.1 ef.2)).length ≤ _ at hb
  have hbc : (((pairs g).filter (fun ef => touches ef.1 ef.2)).length : Int) ≤
      (2 * g.edges.length * maxDegree g : Nat) := by exact_mod_cast hb
  exact hh.trans (mul_le_mul_of_nonneg_right hbc (by positivity))

/-- Integer subtraction distributes over the complete original occurrence list. -/
theorem sum_map_sub_int {α : Type} (xs : List α) (f h : α → Int) :
    (xs.map (fun x => f x - h x)).sum = (xs.map f).sum - (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Ordered covariance subtraction removes precisely the squared full mean. -/
theorem covariance_sum_eq (g : Graph) (k : Nat) (load : Load) :
    ((pairs g).map (covariance k load)).sum =
      (((g.edges.flatMap (fun e => g.edges.map (fun f =>
        (localExpectation 4 k [] load [e, f]).value))).sum : Nat) : Int) -
      (g.edges.length : Int)^2 * (eventCount k load : Int)^2 := by
  change ((pairs g).map (fun ef => ((localExpectation 4 k [] load [ef.1, ef.2]).value : Int) -
    (eventCount k load : Int)^2)).sum = _
  rw [sum_map_sub_int]
  have hl : (pairs g).length = g.edges.length * g.edges.length := by
    simp [pairs, List.length_flatMap]
  have hc : ((pairs g).map (fun _ => (eventCount k load : Int)^2)).sum =
      (g.edges.length : Int)^2 * (eventCount k load : Int)^2 := by
    simp [hl, pow_two]
  rw [hc]
  congr 1
  simp [pairs, Nat.cast_list_sum, List.map_flatMap, List.map_map, Function.comp_def]

/-- Every original nonloop single term has the same exact initial count. -/
theorem single_sum_eq (g : Graph) (k : Nat) (load : Load)
    (hg : SemiprimeD1BoundaryPotential.Valid g) :
    (((g.edges.map (fun e => (localExpectation 2 k [] load [e]).value)).sum : Nat) : Int) =
      (g.edges.length : Int) * (eventCount k load : Int) := by
  have he : g.edges.map (fun e => (localExpectation 2 k [] load [e]).value) =
      g.edges.map (fun _ => eventCount k load) := by
    apply List.map_congr_left
    intro e he
    exact single_initial k e.1 e.2 load (hg e he).2.2
  rw [he]
  simp

/-- One executed initial quadratic load is its exact ordered covariance sum. -/
theorem initial_load_covariances (g : Graph) (k : Nat) (load : Load)
    (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hmean : meanNumerator g.edges.length k load = g.edges.length * eventCount k load) :
    (((g.edges.flatMap (fun e => g.edges.map (fun f =>
      (localExpectation 4 k [] load [e, f]).value))).sum : Nat) : Int) -
      2 * (meanNumerator g.edges.length k load : Int) *
        ((g.edges.map (fun e => (localExpectation 2 k [] load [e]).value)).sum : Nat) +
      (meanNumerator g.edges.length k load : Int)^2 =
      ((pairs g).map (covariance k load)).sum := by
  rw [covariance_sum_eq, single_sum_eq g k load hg, hmean]
  push_cast
  ring

/-- The actual executed initial potential is the sum of its load covariances. -/
theorem initial_potential_covariances (g : Graph) (k : Nat)
    (hg : SemiprimeD1BoundaryPotential.Valid g)
    (hmean : ∀ load ∈ loads k,
      meanNumerator g.edges.length k load = g.edges.length * eventCount k load) :
    (potential g k []).value =
      ((loads k).map (fun load => ((pairs g).map (covariance k load)).sum)).sum := by
  unfold potential
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro load hl
  simpa only [Nat.cast_list_sum, List.map_flatMap, List.map_map, Function.comp_def] using
    initial_load_covariances g k load hg (hmean load hl)

/-- Exact initial variance bound after the actual load means have been identified. -/
theorem initial_potential_bound (g : Graph) (k : Nat)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hk : 0 < k)
    (hmean : ∀ load ∈ loads k,
      meanNumerator g.edges.length k load = g.edges.length * eventCount k load) :
    4 * (potential g k []).value ≤
      ((loads k).length : Int) * ((2 * g.edges.length * maxDegree g : Nat) : Int) *
        (k : Int)^4 := by
  rw [initial_potential_covariances g k hg hmean, ← List.sum_map_mul_left]
  have hh := sum_map_le_sum (loads k)
    (fun load => 4 * ((pairs g).map (covariance k load)).sum)
    (fun _ => ((2 * g.edges.length * maxDegree g : Nat) : Int) * (k : Int)^4)
    (fun load _ => covariance_sum_le g k load hg hk)
  simpa only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_assoc] using hh

/-- The executed menu contains exactly the prescribed bucket and merge loads. -/
theorem loads_length (k : Nat) : (loads k).length = 2 * k - 1 := by
  simp only [loads, List.length_append, List.length_map, List.length_range]
  omega

/-- Real-valued form of the exact initial variance bound for width arithmetic. -/
theorem initial_potential_real_bound (g : Graph) (k : Nat)
    (hg : SemiprimeD1BoundaryPotential.Valid g) (hk : 0 < k)
    (hmean : ∀ load ∈ loads k,
      meanNumerator g.edges.length k load = g.edges.length * eventCount k load) :
    ((potential g k []).value : Real) ≤
      (k : Real)^4 * ((2 * k - 1 : Nat) : Real) *
        (g.edges.length : Real) * (maxDegree g : Real) / 2 := by
  have hi := initial_potential_bound g k hg hk hmean
  rw [loads_length] at hi
  have hr : 4 * ((potential g k []).value : Real) ≤
      ((2 * k - 1 : Nat) : Real) *
        (2 * (g.edges.length : Real) * (maxDegree g : Real)) * (k : Real)^4 := by
    exact_mod_cast hi
  nlinarith

end RiemannGaussian.SemiprimeD1BoundaryVariance
