/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteOriginal

/-! # Zero-aware rational dyadic error ideals
Numeric padicValRat(0)=0, so positive-precision zero errors must be included
explicitly. These scalar closure lemmas feed the actual D.5 array recurrence.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1DyadicBounds
open scoped BigOperators

/-- Zero-aware membership in the rational dyadic fractional ideal2^e Z_(2). -/
def AtLeast (e : ℤ) (q : ℚ) : Prop := q=0 ∨ e≤padicValRat 2 q

/-- Zero errors satisfy every requested precision, including positive precision. -/
theorem zero (e : ℤ) : AtLeast e 0 := Or.inl rfl

/-- A weaker exponent bound follows without nonzero advice. -/
theorem mono {e f : ℤ} {q : ℚ} (h : AtLeast f q) (hef : e≤f) : AtLeast e q := by
  rcases h with h0|hv
  · exact Or.inl h0
  · exact Or.inr (hef.trans hv)

/-- Finite-precision fractional ideals are closed under addition. -/
theorem add {e : ℤ} {q r : ℚ} (hq : AtLeast e q) (hr : AtLeast e r) : AtLeast e (q+r) := by
  rcases hq with hq0|hqv
  · simpa only [hq0,zero_add] using hr
  rcases hr with hr0|hrv
  · rw [hr0,add_zero]
    exact Or.inr hqv
  by_cases hs : q+r=0
  · exact Or.inl hs
  · exact Or.inr ((le_min hqv hrv).trans (padicValRat.min_le_padicValRat_add hs))

/-- Negation preserves every zero-aware dyadic bound. -/
theorem neg {e : ℤ} {q : ℚ} (hq : AtLeast e q) : AtLeast e (-q) := by
  rcases hq with h0|hv
  · exact Or.inl (by rw [h0,neg_zero])
  · exact Or.inr (by simpa only [padicValRat.neg] using hv)

/-- Multiplication adds dyadic error exponents; zero factors need no valuation premise. -/
theorem mul {e f : ℤ} {q r : ℚ} (hq : AtLeast e q) (hr : AtLeast f r) : AtLeast (e+f) (q*r) := by
  by_cases hq0 : q=0
  · exact Or.inl (by rw [hq0,zero_mul])
  by_cases hr0 : r=0
  · exact Or.inl (by rw [hr0,mul_zero])
  have hqv := hq.resolve_left hq0
  have hrv := hr.resolve_left hr0
  exact Or.inr (by rw [padicValRat.mul hq0 hr0];omega)

/-- All actual integer scalars are dyadically integral, including zero. -/
theorem integer (z : ℤ) : AtLeast 0 (z:ℚ) := by
  exact Or.inr (by rw [SemiprimeD1JetRecoveryGrid.int_valuation];positivity)

/-- Actual scalar1 is integral. -/
theorem one : AtLeast 0 1 := by simpa only [Int.cast_one] using integer 1

/-- Products retain the sum of the actual scalar exponents. -/
theorem pow {e : ℤ} {q : ℚ} (hq : AtLeast e q) (n : ℕ) : AtLeast ((n:ℤ)*e) (q^n) := by
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul] using one
  | succ n ih =>
    have hm := mul ih hq
    simpa only [pow_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hm

/-- Every actual finite sum retains a common zero-aware precision, without a loss
for its number of summands. -/
theorem sum {ι : Type*} (s : Finset ι) (f : ι→ℚ) (e : ℤ)
    (hf : ∀i∈s,AtLeast e (f i)) : AtLeast e (∑i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero e
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add (hf a (by simp)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

end RiemannGaussian.SemiprimeD1DyadicBounds
