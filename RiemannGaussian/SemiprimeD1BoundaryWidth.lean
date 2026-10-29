/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryConditionalAverage
import RiemannGaussian.SemiprimeD1BoundaryMergeMean
import RiemannGaussian.SemiprimeD1BoundaryLeafLoad
import Mathlib.Analysis.Real.Sqrt

/-! # Width consequences of the literal acquired quadratic potential

The deterministic averaging identity is discharged from the actual local loops.
The initial-variance estimate is a separate arithmetic obligation: the final
lemma below states its exact interface rather than assuming a good partition.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryWidth
open SemiprimeD1BoundaryPlan SemiprimeD1BoundaryPotential

/-- Every completed load square is bounded by the complete original potential. -/
theorem acquired_square_le (g : Graph) (hg : Valid g) (load : Load)
    (hl : load ∈ loads (acquire g).k) :
    (((acquire g).k : Int)^2 * (loadValue g (acquire g).colours load : Int) -
      (meanNumerator g.edges.length (acquire g).k load : Int))^2 ≤
      (potential g (acquire g).k []).value := by
  have hf : ∀ e ∈ g.edges, e.1 < (acquire g).colours.length ∧
      e.2 < (acquire g).colours.length := by
    intro e he
    rw [SemiprimeD1BoundaryChoice.acquire_length]
    exact ⟨(hg e he).1, (hg e he).2.1⟩
  apply le_trans _ (SemiprimeD1BoundaryConditionalAverage.acquire_potential_le g)
  rw [potential_fixed g (acquire g).k (acquire g).colours hf]
  apply List.single_le_sum
  · intro x hx
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg _
  · exact List.mem_map.mpr ⟨load, hl, rfl⟩

/-- All literal unconditional load means fit the same common upper bound. -/
theorem mean_bound (m k : Nat) (hk : 2 ≤ k) (load : Load) (hl : load ∈ loads k) :
    (meanNumerator m k load : Real) ≤ ((k : Real)^2 / 2 + k) * m := by
  rcases List.mem_append.mp hl with hb | hm
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    have hs : (1 : Nat) ≤ 2 * k := by omega
    have he : ((2 * k - 1 : Nat) : Real) = 2 * k - 1 := by
      rw [Nat.cast_sub hs]
      push_cast
      rfl
    have hp : 2 * (k : Real) - 1 ≤ (k : Real)^2 / 2 + k := by
      nlinarith [sq_nonneg ((k : Real) - 1)]
    simp only [meanNumerator, Nat.cast_mul, he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg m)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hir := List.mem_range.mp hi
    let j := i + 2
    have hj : 2 ≤ j ∧ j ≤ k := by dsimp only [j]; omega
    have hkj : 1 ≤ k + 1 - j := by omega
    have hmul : 1 ≤ j * (k + 1 - j) := by nlinarith
    have ha : ((k + 1 - j : Nat) : Real) = (k : Real) + 1 - j := by
      rw [Nat.cast_sub (by omega : j ≤ k + 1)]
      push_cast
      rfl
    have hb : ((j * (k + 1 - j) - 1 : Nat) : Real) =
        (j : Real) * ((k : Real) + 1 - j) - 1 := by
      rw [Nat.cast_sub hmul, Nat.cast_mul, ha]
      norm_num
    have hp : 2 * ((j : Real) * ((k : Real) + 1 - j) - 1) ≤
        (k : Real)^2 / 2 + k := by
      nlinarith [sq_nonneg (2 * (j : Real) - (k : Real) - 1)]
    change (meanNumerator m k (.merge j) : Real) ≤ _
    simp only [meanNumerator, Nat.cast_mul, Nat.cast_ofNat, hb]
    nlinarith only [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg m)]

/-- A real maximum bound propagates through the exact measured-list fold. -/
theorem fold_max_le (xs : List Nat) (initial : Nat) (B : Real)
    (hi : (initial : Real) ≤ B) (hx : ∀ x ∈ xs, (x : Real) ≤ B) :
    ((xs.foldl max initial : Nat) : Real) ≤ B := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons x xs ih =>
    apply ih
    · rcases le_total initial x with h | h
      · rw [max_eq_right h]
        exact hx x List.mem_cons_self
      · rw [max_eq_left h]
        exact hi
    · intro y hy
      exact hx y (List.mem_cons_of_mem _ hy)

/-- Exact acquisition width from its initial variance bound. This internal
arithmetic interface will be discharged by the occurrence-covariance theorem. -/
theorem acquired_width_of_initial (g : Graph) (hg : Valid g) (B : Real) (hB : 0 ≤ B)
    (hinit : ((potential g (acquire g).k []).value : Real) ≤
      ((acquire g).k : Real)^4 * B) :
    ((acquire g).width : Real) ≤
      (1 / 2 + 1 / ((acquire g).k : Real)) * g.edges.length + Real.sqrt B := by
  let k := (acquire g).k
  have hk : 2 ≤ k := (SemiprimeD1BoundaryChoice.chooseK_bounds g).1
  have hkpos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hk2 : (0 : Real) < (k : Real)^2 := by positivity
  have hroot := Real.sq_sqrt hB
  have each : ∀ load ∈ loads k,
      (loadValue g (acquire g).colours load : Real) ≤
        (1 / 2 + 1 / (k : Real)) * g.edges.length + Real.sqrt B := by
    intro load hl
    have hs : ((k : Real)^2 * (loadValue g (acquire g).colours load : Real) -
        (meanNumerator g.edges.length k load : Real))^2 ≤ (k : Real)^4 * B := by
      have hi := acquired_square_le g hg load hl
      have hic : ((k : Real)^2 * (loadValue g (acquire g).colours load : Real) -
          (meanNumerator g.edges.length k load : Real))^2 ≤
          ((potential g k []).value : Real) := by exact_mod_cast hi
      exact hic.trans hinit
    have hs' : ((k : Real)^2 * (loadValue g (acquire g).colours load : Real) -
        (meanNumerator g.edges.length k load : Real))^2 ≤
        ((k : Real)^2 * Real.sqrt B)^2 := by
      apply hs.trans_eq
      rw [mul_pow, hroot]
      ring
    have hu := le_of_sq_le_sq hs' (show (0 : Real) ≤ (k : Real)^2 * Real.sqrt B by positivity)
    have hm := mean_bound g.edges.length k hk load hl
    have hclear :
        (k : Real)^2 * ((1 / 2 + 1 / (k : Real)) * g.edges.length + Real.sqrt B) =
        ((k : Real)^2 / 2 + k) * g.edges.length + (k : Real)^2 * Real.sqrt B := by
      field_simp
    apply (mul_le_mul_iff_right₀ hk2).mp
    rw [hclear]
    linarith
  change ((((loads k).map (loadValue g (acquire g).colours)).foldl max 0 : Nat) : Real) ≤ _
  apply fold_max_le _ 0 _
  · norm_num only [Nat.cast_zero]
    positivity
  · intro x hx
    obtain ⟨load, hl, rfl⟩ := List.mem_map.mp hx
    exact each load hl

/-- Closed simultaneous width bound for the partition acquired by the actual code.
No good-colouring, averaging, covariance or mean premise remains. -/
theorem acquired_width (g : Graph) (hg : Valid g) :
    ((acquire g).width : Real) ≤
      (1 / 2 + 1 / ((acquire g).k : Real)) * g.edges.length +
        Real.sqrt (((2 * (acquire g).k - 1 : Nat) : Real) *
          g.edges.length * maxDegree g / 2) := by
  apply acquired_width_of_initial g hg
  · positivity
  · have h := SemiprimeD1BoundaryMergeMean.initial_bound g (acquire g).k hg
      (SemiprimeD1BoundaryChoice.chooseK_bounds g).1
    convert h using 1
    ring

/-- The complete concrete leaf's assignment dimensions satisfy the same closed bound. -/
theorem leaf_width (ctx : SemiprimeD1JetAxes.Context) (net : SemiprimeD1TensorNetwork.Network)
    (hw : SemiprimeD1TensorNetwork.WellFormed net) :
    (SemiprimeD1BoundaryLeafReport.width ctx net : Real) ≤
      (1 / 2 + 1 / ((acquire (graph net)).k : Real)) * (graph net).edges.length +
        Real.sqrt (((2 * (acquire (graph net)).k - 1 : Nat) : Real) *
          (graph net).edges.length * maxDegree (graph net) / 2) := by
  have h := SemiprimeD1BoundaryLeafLoad.width_le_plan ctx net hw
  have hc : (SemiprimeD1BoundaryLeafReport.width ctx net : Real) ≤
      ((acquire (graph net)).width : Real) := by exact_mod_cast h
  exact hc.trans (acquired_width (graph net) (graph_valid net))

end RiemannGaussian.SemiprimeD1BoundaryWidth
