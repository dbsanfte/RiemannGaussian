/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatch
import RiemannGaussian.ZetaBlockEnclosure

/-!
# Sound enclosures for reusable block amplitudes

Materialized arrays share the center moments across nearby sample heights.
Short or poorly conditioned blocks use literal finite sums. Periodically
reset phase powers by repeated squaring to avoid interval wrapping from
an arbitrarily long succession of rectangular multiplications.
-/

namespace RiemannGaussian.ZetaBlockBatchEnclosure
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaBlockEnclosure
open ZetaBlockTaylor ZetaBlockMoments

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Rounded binomial coefficient recurrence at the actual complex shift. -/
def shiftCoefficient (prec : ℤ) (D : Box) : ℕ → Box
  | 0 => rat prec 1
  | j + 1 => mul prec
      (mul prec (add prec D (rat prec j)) (rat prec (-1 / (300 * (j + 1)))))
      (shiftCoefficient prec D j)

theorem mem_shiftCoefficient {prec : ℤ} (hp : prec ≤ 0) {d : ℂ} {D : Box}
    (hd : Mem d D) (j : ℕ) :
    Mem (ZetaBlockShift.coefficient d j) (shiftCoefficient prec D j) := by
  induction j with
  | zero => simpa [shiftCoefficient] using mem_rat hp 1
  | succ j ih =>
    have hh := mem_mul (mem_mul (mem_add hd (mem_rat hp j) prec)
      (mem_rat hp (-1 / (300 * (j + 1)))) prec) ih prec
    convert! hh using 1
    simp only [ZetaBlockShift.coefficient, Rat.cast_div, Rat.cast_neg, Rat.cast_one,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
    ring

/-- All thirteen shift coefficients are shared by every block at that height. -/
def shiftCoefficients (prec : ℤ) (D : Box) : Array Box :=
  Array.ofFn (fun j : Fin 13 => shiftCoefficient prec D j)

theorem mem_shiftCoefficients {prec : ℤ} (hp : prec ≤ 0) {d : ℂ} {D : Box}
    (hd : Mem d D) {j : ℕ} (hj : j < 13) :
    Mem (ZetaBlockShift.coefficient d j) (lookup prec (shiftCoefficients prec D) j) := by
  simpa [lookup, shiftCoefficients, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj,
    rat] using mem_shiftCoefficient hp hd j

/-- Compute powers successively, storing each for reuse in the direct fallback. -/
def powerState (prec : ℤ) (X : Box) : ℕ → Box × Array Box
  | 0 => (rat prec 1, #[])
  | m + 1 =>
      let S := powerState prec X m
      (mul prec S.1 X, S.2.push S.1)

@[simp] theorem size_powerState (prec : ℤ) (X : Box) (m : ℕ) :
    (powerState prec X m).2.size = m := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [powerState, Array.size_push] using congrArg Nat.succ ih

theorem mem_powerState {prec : ℤ} (hp : prec ≤ 0) {x : ℂ} {X : Box}
    (hx : Mem x X) (m : ℕ) :
    Mem (x ^ m) (powerState prec X m).1 ∧
      ∀ j < m, Mem (x ^ j) (lookup prec (powerState prec X m).2 j) := by
  induction m with
  | zero => exact ⟨by simpa [powerState] using mem_rat hp 1, by intro j hj; omega⟩
  | succ m ih =>
    constructor
    · simpa only [powerState, pow_succ] using mem_mul ih.1 hx prec
    · intro j hj
      by_cases hje : j = m
      · subst j
        simpa only [powerState, lookup, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          size_powerState, ↓reduceIte, Option.getD_some] using ih.1
      · simpa only [powerState, lookup, Array.getD_eq_getD_getElem?, Array.getElem?_push,
          size_powerState, if_neg hje] using ih.2 j (by omega)

/-- Direct fallback retains the current geometric power and thirteen weighted sums. -/
def directState (prec : ℤ) (C : ℕ → Box) (Q : Box) (h : ℚ) : ℕ → Box × Array Box
  | 0 => (rat prec 1, Array.replicate 13 (rat prec 0))
  | K + 1 =>
      let S := directState prec C Q h K
      let X := rat prec ((K : ℚ) * h)
      let W := mul prec S.1 (horner prec C X 18 0)
      let Xs := (powerState prec X 13).2
      (mul prec S.1 Q, Array.ofFn (fun j : Fin 13 =>
        add prec (lookup prec S.2 j) (mul prec W (lookup prec Xs j))))

@[simp] theorem size_directState (prec : ℤ) (C : ℕ → Box) (Q : Box) (h : ℚ) (K : ℕ) :
    (directState prec C Q h K).2.size = 13 := by
  cases K <;> simp only [directState, Array.size_replicate, Array.size_ofFn]

theorem mem_directState {prec : ℤ} (hp : prec ≤ 0) {s q : ℂ} {C : ℕ → Box} {Q : Box}
    (hq : Mem q Q) (hc : ∀ j < 19, Mem (coefficient s j) (C j)) (h : ℚ) (K : ℕ) :
    Mem (q ^ K) (directState prec C Q h K).1 ∧ ∀ j < 13,
      Mem (∑ k ∈ Finset.range K, q ^ k * polynomial s 18 ((k : ℂ) * h) * ((k : ℂ) * h) ^ j)
        (lookup prec (directState prec C Q h K).2 j) := by
  induction K with
  | zero =>
    constructor
    · simpa [directState] using mem_rat hp 1
    · intro j hj
      simpa [directState, lookup, Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hj, rat]
        using mem_rat hp 0
  | succ K ih =>
    have hx := mem_rat hp ((K : ℚ) * h)
    simp only [Rat.cast_mul, Rat.cast_natCast] at hx
    have hpoly := mem_horner hp (c := coefficient s) (C := C) hx 18 0
      (fun j hj => by simpa only [Nat.zero_add] using hc j (by omega))
    simp only [Nat.zero_add] at hpoly
    constructor
    · simpa only [directState, pow_succ] using mem_mul ih.1 hq prec
    · intro j hj
      have hh := mem_add (ih.2 j hj)
        (mem_mul (mem_mul ih.1 hpoly prec) ((mem_powerState hp hx 13).2 j hj) prec) prec
      rw [Finset.sum_range_succ]
      simpa only [directState, lookup, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj,
        ↓reduceDIte, Option.getD_some, polynomial] using hh

/-- Use thirty-one compressed moments when safely conditioned, else sum directly. -/
def amplitudeTable (cfg : DyadicConfig) (C : ℕ → Box) (Q : Box) (h : ℚ) (K : ℕ) : Array Box :=
  if K ≤ 30 then (directState cfg.precision C Q h K).2 else
    match inv cfg (add cfg.precision Q (rat cfg.precision (-1))) with
    | .error _ => (directState cfg.precision C Q h K).2
    | .ok D =>
        if max |D.re.lo.toRat| |D.re.hi.toRat| + max |D.im.lo.toRat| |D.im.hi.toRat| > 8 then
          (directState cfg.precision C Q h K).2
        else
          let T := momentTable cfg.precision (powerBox cfg.precision Q K) D h K 31
          Array.ofFn (fun j : Fin 13 => sumBox cfg.precision
            (fun i => mul cfg.precision (C i) (lookup cfg.precision T (i + j))) 19)

@[simp] theorem size_amplitudeTable (cfg : DyadicConfig) (C : ℕ → Box) (Q : Box) (h : ℚ) (K : ℕ) :
    (amplitudeTable cfg C Q h K).size = 13 := by
  unfold amplitudeTable
  split_ifs
  · exact size_directState _ _ _ _ _
  · split
    · exact size_directState _ _ _ _ _
    · split_ifs
      · exact size_directState _ _ _ _ _
      · exact Array.size_ofFn

theorem mem_amplitudeTable {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s q : ℂ} (hq : q ≠ 1) {C : ℕ → Box} {Q : Box} (hQ : Mem q Q)
    (hc : ∀ j < 19, Mem (coefficient s j) (C j)) (h : ℚ) (K : ℕ) {j : ℕ} (hj : j < 13) :
    Mem (∑ k ∈ Finset.range K, q ^ k * polynomial s 18 ((k : ℂ) * h) * ((k : ℂ) * h) ^ j)
      (lookup cfg.precision (amplitudeTable cfg C Q h K) j) := by
  unfold amplitudeTable
  split_ifs with hK
  · exact (mem_directState hp hQ hc h K).2 j hj
  · cases hD : inv cfg (add cfg.precision Q (rat cfg.precision (-1))) with
    | error err => exact (mem_directState hp hQ hc h K).2 j hj
    | ok D =>
      dsimp only
      split_ifs
      · exact (mem_directState hp hQ hc h K).2 j hj
      · have hDm : Mem ((q - 1)⁻¹) D := mem_inv hp
          (by simpa only [Rat.cast_neg, Rat.cast_one, sub_eq_add_neg] using
            mem_add hQ (mem_rat hp (-1)) cfg.precision) hD
        rw [ZetaBlockBatch.weighted_sum_eq_moments]
        simp only [lookup, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj,
          ↓reduceDIte, Option.getD_some]
        apply mem_sumBox hp 19
        intro i hi
        apply mem_mul (hc i hi)
        have hm := mem_momentTable hp hq (mem_powerBox hp hQ K) hDm h 31 (i + j) (by omega)
        simpa only [lookup, Array.getD_eq_getD_getElem?] using hm

/-- Reanchor each eighth sample; intermediate steps use one multiplication. -/
def phaseAt (prec : ℤ) (P Q : Box) : ℕ → Box
  | 0 => P
  | j + 1 =>
      if j % 8 = 7 then mul prec P (powerBox prec Q (j + 1))
      else mul prec (phaseAt prec P Q j) Q

/-- Every phase reset and every incremental step encloses the same exact power. -/
theorem mem_phaseAt {prec : ℤ} (hp : prec ≤ 0) {p q : ℂ} {P Q : Box}
    (hP : Mem p P) (hQ : Mem q Q) (j : ℕ) : Mem (p * q ^ j) (phaseAt prec P Q j) := by
  induction j with
  | zero => simpa [phaseAt] using hP
  | succ j ih =>
    rw [phaseAt]
    split_ifs
    · exact mem_mul hP (mem_powerBox hp hQ (j + 1)) prec
    · simpa only [pow_succ, mul_assoc] using mem_mul ih hQ prec

end RiemannGaussian.ZetaBlockBatchEnclosure
