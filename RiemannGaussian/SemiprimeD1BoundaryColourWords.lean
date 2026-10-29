/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryPlan

/-! # Exact arbitrary-coordinate marginal of the executed colour enumerator

Only this proof rearranges finite sums. Runtime continues to enumerate the
at-most-four endpoint colours used by each actual potential term.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryColourWords
open SemiprimeD1BoundaryPlan

/-- Every executed local sample has precisely the advertised length. -/
theorem member_length (k n : Nat) (sample : List Nat) (h : sample ∈ colourWords k n) :
    sample.length = n := by
  induction n generalizing sample with
  | zero =>
    have he : sample = [] := List.mem_singleton.mp h
    simp only [he, List.length_nil]
  | succ n ih =>
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
    obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hc
    simp only [List.length_cons, ih tail ht]

/-- Swapping two finite sums retains all original occurrences and multiplicities. -/
theorem sum_swap (xs ys : List Nat) (f : Nat → Nat → Nat) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.sum_map_add, ih]

/-- Fixing any local coordinate partitions the literal executed success count.
The deleted coordinate is reinserted without changing any other sample position. -/
theorem successes_insert (k n j : Nat) (p : List Nat → Bool) (hj : j ≤ n) :
    ((List.range k).map (fun c => ((colourWords k n).filter (fun sample =>
      p (sample.take j ++ [c] ++ sample.drop j))).length)).sum =
      ((colourWords k (n + 1)).filter p).length := by
  induction j generalizing n p with
  | zero =>
    simp [colourWords, List.filter_flatMap, List.filter_map, List.length_flatMap, Function.comp_def]
  | succ j ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hjn : j ≤ n := by omega
      have hsplit (c : Nat) :
          ((colourWords k (n + 1)).filter (fun sample =>
            p (sample.take (j + 1) ++ [c] ++ sample.drop (j + 1)))).length =
          ((List.range k).map (fun a => ((colourWords k n).filter (fun sample =>
            p (a :: (sample.take j ++ [c] ++ sample.drop j)))).length)).sum := by
        simp [colourWords, List.filter_flatMap, List.filter_map, List.length_flatMap, Function.comp_def]
      simp_rw [hsplit]
      rw [sum_swap]
      have hinner :
          (List.range k).map (fun a => ((List.range k).map (fun c =>
            ((colourWords k n).filter (fun sample =>
              p (a :: (sample.take j ++ [c] ++ sample.drop j)))).length)).sum) =
          (List.range k).map (fun a => ((colourWords k (n + 1)).filter
            (fun sample => p (a :: sample))).length) := by
        apply List.map_congr_left
        intro a _
        exact ih n (fun sample => p (a :: sample)) hjn
      rw [hinner]
      simp [colourWords, List.filter_flatMap, List.filter_map, List.length_flatMap, Function.comp_def]

end RiemannGaussian.SemiprimeD1BoundaryColourWords
