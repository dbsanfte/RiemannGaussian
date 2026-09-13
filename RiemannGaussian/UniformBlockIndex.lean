/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.List.Flatten
import Mathlib.Tactic

/-!
# Indexed access to uniformly sized data blocks

Two short lookups recover exactly the same entry as one lookup in the full
flattened table. The identity lets numerical checkers retain a proved table
while avoiding a linear scan through all preceding blocks for each query.
-/

namespace RiemannGaussian.UniformBlockIndex

/-- Lookup at an explicit block and within-block index. -/
theorem getElem?_flatten_mul_add {α : Type*} (blocks : List (List α)) {k : ℕ}
    (hlen : ∀ b ∈ blocks, b.length = k) (m n : ℕ) (hn : n < k) :
    blocks.flatten[m * k + n]? = (blocks[m]?.getD [])[n]? := by
  induction blocks generalizing m with
  | nil => simp
  | cons b rest ih =>
    have hb : b.length = k := hlen b (by simp)
    have hr : ∀ a ∈ rest, a.length = k := fun a ha => hlen a (by simp [ha])
    cases m with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons,
        List.getElem?_cons_zero, Option.getD_some]
      exact List.getElem?_append_left (by omega)
    | succ m =>
      simp only [List.flatten_cons, List.getElem?_cons_succ]
      rw [List.getElem?_append_right (by rw [hb, Nat.add_mul, Nat.one_mul]; omega)]
      have hi : (m + 1) * k + n - b.length = m * k + n := by
        rw [hb, Nat.add_mul, Nat.one_mul]
        omega
      rw [hi]
      exact ih hr m

/-- Quotient and remainder indexing agrees with the full flattened table. -/
theorem getElem?_flatten {α : Type*} (blocks : List (List α)) {k : ℕ}
    (hk : 0 < k) (hlen : ∀ b ∈ blocks, b.length = k) (n : ℕ) :
    blocks.flatten[n]? = (blocks[n / k]?.getD [])[n % k]? := by
  have h := getElem?_flatten_mul_add blocks hlen (n / k) (n % k) (Nat.mod_lt n hk)
  have hi : n / k * k + n % k = n := by
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n k
  rwa [hi] at h

end RiemannGaussian.UniformBlockIndex
