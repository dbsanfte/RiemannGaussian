/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorPhaseGrid
import Mathlib.Data.List.Chain

/-!
# A sequential checker for the trigonometric table

The certificate stores integer coordinates. Checking adjacent entries takes
one sequential pass; indexed access is used only in the soundness theorem.
The checker never evaluates a trigonometric function.
-/

namespace RiemannGaussian.MontgomeryTaylorPhaseGrid

/-- Integer coordinate and residual obligations for one rotation. -/
def validStep (a b : ℤ × ℤ) : Prop :=
  |a.1| + |a.2| ≤ 2 * (scale : ℤ) ∧
  |(scale : ℤ) * b.1 - (baseCos * a.1 - baseSin * a.2)| ≤ scale ∧
  |(scale : ℤ) * b.2 - (baseSin * a.1 + baseCos * a.2)| ≤ scale

/-- Executable integer checks for one adjacent pair. -/
def checkStep (a b : ℤ × ℤ) : Bool :=
  decide (|a.1| + |a.2| ≤ 2 * (scale : ℤ)) &&
  decide (|(scale : ℤ) * b.1 - (baseCos * a.1 - baseSin * a.2)| ≤ scale) &&
  decide (|(scale : ℤ) * b.2 - (baseSin * a.1 + baseCos * a.2)| ≤ scale)

/-- Primitive list recursion checks a chain from its preceding entry.
Using the primitive recursor avoids recomputing course-of-values data. -/
def checkFrom (a : ℤ × ℤ) (v : List (ℤ × ℤ)) : Bool :=
  List.rec (motive := fun _ => (ℤ × ℤ) → Bool) (fun _ => true)
    (fun b _ cont prev => checkStep prev b && cont b) v a

/-- Boolean checks for all consecutive pairs, without repeated indexing. -/
def checkEdges : List (ℤ × ℤ) → Bool
  | [] => true
  | a :: rest => checkFrom a rest

private theorem checkStep_iff (a b : ℤ × ℤ) : checkStep a b = true ↔ validStep a b := by
  simp only [checkStep, validStep, Bool.and_eq_true, decide_eq_true_eq]
  tauto

private theorem checkFrom_iff (a : ℤ × ℤ) (v : List (ℤ × ℤ)) :
    checkFrom a v = true ↔ List.IsChain validStep (a :: v) := by
  induction v generalizing a with
  | nil => simp [checkFrom]
  | cons b rest ih =>
    rw [show checkFrom a (b :: rest) = (checkStep a b && checkFrom b rest) from rfl]
    rw [Bool.and_eq_true, checkStep_iff, ih, List.isChain_cons_cons]

/-- The executable adjacency checker proves the mathematical chain. -/
theorem checkEdges_iff (v : List (ℤ × ℤ)) :
    checkEdges v = true ↔ v.IsChain validStep := by
  cases v with
  | nil => simp [checkEdges]
  | cons a rest => exact checkFrom_iff a rest

/-- Independently checked data chunks compose after checking the single
seam between them. This keeps the kernel's individual computations small. -/
theorem checkEdges_append {v w : List (ℤ × ℤ)}
    (hv : checkEdges v = true) (hw : checkEdges w = true)
    (hseam : checkStep (v.getLast?.getD (0, 0)) (w.head?.getD (0, 0)) = true) :
    checkEdges (v ++ w) = true := by
  apply (checkEdges_iff _).mpr
  apply ((checkEdges_iff v).mp hv).append ((checkEdges_iff w).mp hw)
  intro a ha b hb
  have ha' : v.getLast? = some a := ha
  have hb' : w.head? = some b := hb
  rw [ha', hb'] at hseam
  exact (checkStep_iff a b).mp hseam

/-- A successful sequential check encloses every table entry around the
exact sine and cosine. The displayed error grows only linearly in the index. -/
theorem table_error (v : List (ℤ × ℤ))
    (hstart : v[0]?.getD (0, 0) = ((scale : ℤ), 0))
    (hcheck : checkEdges v = true) {n : ℕ} (hn : n < v.length) :
    |((v[n]?.getD (0, 0)).1 : ℝ) / scale -
        Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 6 * n / (scale : ℝ) ∧
      |((v[n]?.getD (0, 0)).2 : ℝ) / scale -
        Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 6 * n / (scale : ℝ) := by
  have hchain := (checkEdges_iff v).mp hcheck
  have hstep (i : ℕ) (hi : i < v.length - 1) :
      validStep (v[i]?.getD (0, 0)) (v[i + 1]?.getD (0, 0)) := by
    have hi' : i + 1 < v.length := by omega
    simpa only [List.getElem?_eq_getElem (by omega : i < v.length),
      List.getElem?_eq_getElem hi', Option.getD_some] using
        (List.isChain_iff_getElem.mp hchain i hi')
  exact grid_error_of_integer_checks
    (fun i => (v[i]?.getD (0, 0)).1) (fun i => (v[i]?.getD (0, 0)).2)
    (congrArg Prod.fst hstart) (congrArg Prod.snd hstart)
    (fun i hi => (hstep i hi).1) (fun i hi => (hstep i hi).2.1)
    (fun i hi => (hstep i hi).2.2) (by omega : n ≤ v.length - 1)

/-- One checked period controls the entire unbounded phase grid, with a
uniform error independent of the number of completed rotations. -/
theorem periodic_table_error (v : List (ℤ × ℤ))
    (hstart : v[0]?.getD (0, 0) = ((scale : ℤ), 0))
    (hcheck : checkEdges v = true) (hsize : 16000 ≤ v.length) (n : ℕ) :
    |((v[n % 16000]?.getD (0, 0)).1 : ℝ) / scale -
        Real.cos ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000 ∧
      |((v[n % 16000]?.getD (0, 0)).2 : ℝ) / scale -
        Real.sin ((n : ℝ) * (Real.pi / 8000))| ≤ 1 / 10000000000000 := by
  have hn := Nat.mod_lt n (by decide : 0 < 16000)
  have h := table_error v hstart hcheck (lt_of_lt_of_le hn hsize)
  have hnat : ((n % 16000 : ℕ) : ℝ) + 16000 * ((n / 16000 : ℕ) : ℝ) = n := by
    exact_mod_cast Nat.mod_add_div n 16000
  have hang : (n : ℝ) * (Real.pi / 8000) =
      ((n % 16000 : ℕ) : ℝ) * (Real.pi / 8000) +
        ((n / 16000 : ℕ) : ℝ) * (2 * Real.pi) := by
    calc
      _ = (((n % 16000 : ℕ) : ℝ) + 16000 * ((n / 16000 : ℕ) : ℝ)) *
          (Real.pi / 8000) := by rw [hnat]
      _ = _ := by ring
  rw [hang, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  have hnR : ((n % 16000 : ℕ) : ℝ) ≤ 16000 := by exact_mod_cast hn.le
  have hb : (6 : ℝ) * (n % 16000 : ℕ) / scale ≤ 1 / 10000000000000 := by
    norm_num only [scale, Nat.cast_ofNat]
    linarith
  exact ⟨h.1.trans hb, h.2.trans hb⟩

end RiemannGaussian.MontgomeryTaylorPhaseGrid
