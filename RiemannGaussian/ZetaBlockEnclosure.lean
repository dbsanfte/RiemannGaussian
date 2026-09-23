/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockMoments

/-!
# Checked interval arithmetic for the shared block polynomial

Coefficient tables and geometric moments are evaluated once and reused.
All enclosures are justified for the literal finite expressions. The
resonant fallback sums the original polynomial block directly.
-/

namespace RiemannGaussian.ZetaBlockEnclosure
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaBlockTaylor ZetaBlockMoments

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Outward-rounded finite sum. -/
def sumBox (prec : ℤ) (B : ℕ → Box) : ℕ → Box
  | 0 => rat prec 0
  | n + 1 => add prec (sumBox prec B n) (B n)

theorem mem_sumBox {prec : ℤ} (hp : prec ≤ 0) {f : ℕ → ℂ} {B : ℕ → Box}
    (n : ℕ) (h : ∀ j < n, Mem (f j) (B j)) :
    Mem (∑ j ∈ Finset.range n, f j) (sumBox prec B n) := by
  induction n with
  | zero => simpa only [Finset.sum_range_zero, sumBox, Rat.cast_zero] using mem_rat hp 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact mem_add (ih (fun j hj => h j (by omega))) (h n (by omega)) prec

/-- Repeated squaring for a nonnegative integer power. -/
def powerBox (prec : ℤ) (B : Box) (n : ℕ) : Box :=
  if n = 0 then rat prec 1 else
    let P := powerBox prec B (n / 2)
    let Q := mul prec P P
    if n % 2 = 0 then Q else mul prec Q B
termination_by n
decreasing_by omega

theorem mem_powerBox {prec : ℤ} (hp : prec ≤ 0) {z : ℂ} {B : Box}
    (hz : Mem z B) (n : ℕ) : Mem (z ^ n) (powerBox prec B n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [powerBox]
    split_ifs with hn he
    · subst n; simpa only [pow_zero, Rat.cast_one] using mem_rat hp 1
    · have hh := mem_mul (ih (n / 2) (by omega)) (ih (n / 2) (by omega)) prec
      convert hh using 1
      rw [← pow_add, show n / 2 + n / 2 = n by omega]
    · have hh := mem_mul (mem_mul (ih (n / 2) (by omega)) (ih (n / 2) (by omega)) prec) hz prec
      convert hh using 1
      rw [← pow_add, ← pow_succ, show n / 2 + n / 2 + 1 = n by omega]

/-- Rounded coefficient recurrence; it retains both signed coordinates. -/
def coefficientPairBox (prec : ℤ) (A : Box) : ℕ → Box × Box
  | 0 => (rat prec 1, rat prec 0)
  | j + 1 =>
      let C := coefficientPairBox prec A j
      (C.2, mul prec
        (add prec (mul prec (mul prec A (rat prec (1 / 90000))) C.1)
          (neg (mul prec (rat prec ((j + 1 : ℚ) / 300)) C.2)))
        (rat prec (1 / (j + 2 : ℚ))))

theorem mem_coefficientPairBox {prec : ℤ} (hp : prec ≤ 0) {s : ℂ} {A : Box}
    (hs : Mem s A) (j : ℕ) :
    Mem (coefficientPair s j).1 (coefficientPairBox prec A j).1 ∧
      Mem (coefficientPair s j).2 (coefficientPairBox prec A j).2 := by
  induction j with
  | zero => exact ⟨by simpa [coefficientPair, coefficientPairBox] using mem_rat hp 1,
      by simpa [coefficientPair, coefficientPairBox] using mem_rat hp 0⟩
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have hh := mem_mul
      (mem_add (mem_mul (mem_mul hs (mem_rat hp (1 / 90000)) prec) ih.1 prec)
        (mem_neg (mem_mul (mem_rat hp ((j + 1 : ℚ) / 300)) ih.2 prec)) prec)
      (mem_rat hp (1 / (j + 2 : ℚ))) prec
    simpa only [coefficientPairBox, coefficientPair, Rat.cast_div, Rat.cast_one, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_one, sub_eq_add_neg,
      div_eq_mul_inv, Rat.cast_inv, Rat.cast_mul, mul_one, one_mul] using hh

/-- A materialized table, shared by every block of a sample. -/
def coefficients (prec : ℤ) (A : Box) : Array Box :=
  Array.ofFn (fun j : Fin 19 => (coefficientPairBox prec A j).1)

/-- Read a stored enclosure, with a zero box outside the table's proven range. -/
def lookup (prec : ℤ) (C : Array Box) (j : ℕ) : Box := C.getD j (rat prec 0)

theorem mem_coefficients {prec : ℤ} (hp : prec ≤ 0) {s : ℂ} {A : Box}
    (hs : Mem s A) {j : ℕ} (hj : j < 19) :
    Mem (coefficient s j) (lookup prec (coefficients prec A) j) := by
  simpa [lookup, coefficients, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj,
    coefficient] using (mem_coefficientPairBox hp hs j).1

/-- Horner evaluation with an explicit initial coefficient index. -/
def horner (prec : ℤ) (C : ℕ → Box) (X : Box) : ℕ → ℕ → Box
  | 0, j => C j
  | m + 1, j => add prec (C j) (mul prec X (horner prec C X m (j + 1)))

theorem mem_horner {prec : ℤ} (_hp : prec ≤ 0) {c : ℕ → ℂ} {C : ℕ → Box}
    {x : ℂ} {X : Box} (hx : Mem x X) (m j : ℕ)
    (hc : ∀ i ≤ m, Mem (c (j + i)) (C (j + i))) :
    Mem (∑ i ∈ Finset.range (m + 1), c (j + i) * x ^ i) (horner prec C X m j) := by
  induction m generalizing j with
  | zero => simpa [horner] using hc 0 (by omega)
  | succ m ih =>
    have hh := mem_add (by simpa using hc 0 (by omega))
      (mem_mul hx (ih (j + 1) (fun i hi => by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc (i + 1) (by omega))) prec) prec
    convert! hh using 1
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one, Nat.add_zero, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show j + (i + 1) = j + 1 + i by omega, pow_succ]
    ring

/-- A direct block sum, with the current geometric power threaded through. -/
def directState (prec : ℤ) (C : ℕ → Box) (Q : Box) (h : ℚ) : ℕ → Box × Box
  | 0 => (rat prec 1, rat prec 0)
  | K + 1 =>
      let S := directState prec C Q h K
      (mul prec S.1 Q,
        add prec S.2 (mul prec S.1 (horner prec C (rat prec ((K : ℚ) * h)) 18 0)))

theorem mem_directState {prec : ℤ} (hp : prec ≤ 0) {s q : ℂ} {C : ℕ → Box} {Q : Box}
    (hq : Mem q Q) (hc : ∀ j < 19, Mem (coefficient s j) (C j)) (h : ℚ) (K : ℕ) :
    Mem (q ^ K) (directState prec C Q h K).1 ∧
      Mem (∑ k ∈ Finset.range K, q ^ k * polynomial s 18 ((k : ℂ) * h))
        (directState prec C Q h K).2 := by
  induction K with
  | zero => exact ⟨by simpa [directState] using mem_rat hp 1,
      by simpa [directState] using mem_rat hp 0⟩
  | succ K ih =>
    have hx := mem_rat hp ((K : ℚ) * h)
    simp only [Rat.cast_mul, Rat.cast_natCast] at hx
    have hpv := mem_horner hp (c := coefficient s) (C := C) hx 18 0
      (fun j hj => by simpa only [Nat.zero_add] using hc j (by omega))
    simp only [Nat.zero_add] at hpv
    constructor
    · change Mem (q ^ (K + 1)) (mul prec (directState prec C Q h K).1 Q)
      rw [pow_succ]
      exact mem_mul ih.1 hq prec
    · change Mem _ (add prec (directState prec C Q h K).2
        (mul prec (directState prec C Q h K).1 (horner prec C (rat prec ((K : ℚ) * h)) 18 0)))
      rw [Finset.sum_range_succ]
      exact mem_add ih.2 (mem_mul ih.1 hpv prec) prec


/-- Successive geometric moments, storing each computed value for reuse. -/
def momentTable (prec : ℤ) (QK D : Box) (h : ℚ) (K : ℕ) : ℕ → Array Box
  | 0 => #[]
  | j + 1 =>
      let T := momentTable prec QK D h K j
      let M := mul prec
        (add prec
          (add prec (mul prec QK (rat prec ((((K : ℚ) - 1) * h) ^ j)))
            (sumBox prec (fun l => mul prec (rat prec ((j.choose l : ℚ) * (-h) ^ (j - l))) (lookup prec T l)) j))
          (rat prec (-((-h) ^ j)))) D
      T.push M

@[simp] theorem size_momentTable (prec : ℤ) (QK D : Box) (h : ℚ) (K m : ℕ) :
    (momentTable prec QK D h K m).size = m := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [momentTable, Array.size_push] using congrArg Nat.succ ih

theorem mem_momentTable {prec : ℤ} (hp : prec ≤ 0) {q : ℂ} (hq : q ≠ 1)
    {QK D : Box} {K : ℕ} (hQK : Mem (q ^ K) QK) (hD : Mem ((q - 1)⁻¹) D)
    (h : ℚ) (m : ℕ) : ∀ j < m, Mem (moment q (h : ℂ) K j) (lookup prec (momentTable prec QK D h K m) j) := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    by_cases hje : j = m
    · subst j
      have hsum := mem_sumBox hp m (fun l hl =>
        mem_mul (mem_rat hp ((m.choose l : ℚ) * (-h) ^ (m - l))) (ih l hl) prec)
      have hh := mem_mul (mem_add
        (mem_add (mem_mul hQK (mem_rat hp ((((K : ℚ) - 1) * h) ^ m)) prec) hsum prec)
        (mem_rat hp (-((-h) ^ m))) prec) hD prec
      rw [moment_eq_div hq]
      simpa only [lookup, Array.getD_eq_getD_getElem?, momentTable, Array.getElem?_push,
        size_momentTable, lt_self_iff_false, ↓reduceIte, Option.getD_some, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_pow, Rat.cast_neg, Rat.cast_add, sub_eq_add_neg, div_eq_mul_inv] using hh
    · have hjm : j < m := by omega
      simpa only [lookup, Array.getD_eq_getD_getElem?, momentTable, Array.getElem?_push,
        size_momentTable, if_neg hje] using ih j hjm

/-- Use compressed moments when the reciprocal enclosure is reasonably small;
otherwise use the exact direct polynomial sum. The threshold affects speed
and conditioning only, not soundness. -/
def polynomialBlock (cfg : DyadicConfig) (C : ℕ → Box) (Q : Box) (h : ℚ) (K : ℕ) : Box :=
  if K ≤ 18 then (directState cfg.precision C Q h K).2 else
    match inv cfg (add cfg.precision Q (rat cfg.precision (-1))) with
    | .error _ => (directState cfg.precision C Q h K).2
    | .ok D =>
        if max |D.re.lo.toRat| |D.re.hi.toRat| + max |D.im.lo.toRat| |D.im.hi.toRat| > 8 then
          (directState cfg.precision C Q h K).2
        else
          let T := momentTable cfg.precision (powerBox cfg.precision Q K) D h K 19
          sumBox cfg.precision (fun j => mul cfg.precision (C j) (lookup cfg.precision T j)) 19

theorem mem_polynomialBlock {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s q : ℂ} (hq : q ≠ 1) {C : ℕ → Box} {Q : Box} (hQ : Mem q Q)
    (hc : ∀ j < 19, Mem (coefficient s j) (C j)) (h : ℚ) (K : ℕ) :
    Mem (∑ k ∈ Finset.range K, q ^ k * polynomial s 18 ((k : ℂ) * h))
      (polynomialBlock cfg C Q h K) := by
  unfold polynomialBlock
  split_ifs with hK
  · exact (mem_directState hp hQ hc h K).2
  · cases hD : inv cfg (add cfg.precision Q (rat cfg.precision (-1))) with
    | error err => exact (mem_directState hp hQ hc h K).2
    | ok D =>
      dsimp only
      split_ifs
      · exact (mem_directState hp hQ hc h K).2
      · rw [sum_polynomial_eq_moments]
        apply mem_sumBox hp 19
        intro j hj
        apply mem_mul (hc j hj)
        apply mem_momentTable hp hq (mem_powerBox hp hQ K) _ h 19 j hj
        apply mem_inv hp _ hD
        simpa only [Rat.cast_neg, Rat.cast_one, sub_eq_add_neg] using
          mem_add hQ (mem_rat hp (-1)) cfg.precision

end RiemannGaussian.ZetaBlockEnclosure
