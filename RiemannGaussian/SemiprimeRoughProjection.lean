/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeOrderSeparation
import RiemannGaussian.SemiprimeLongPeriodExtraction
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Partial rough-order extraction and cheap recurrence maps

A public quadratic exponent product can remove one component of a
two-factor residual local order. The remaining component is inside the
existing square-sized linear closure cover. Coverage is proved for the
explicit small-polynomial-root class, not for every semiprime.

The split-colour characters justify native scalar powering. An indexed
Dickson recurrence generates large exponents without constructing them.
Imaginary orientation and derivative root stripping retain separating
signals that a globally shared reciprocal trace would otherwise hide.

This side-investigation algebra is checked in the ordinary library; numerical probes remain optional.
It proves the algebra and stated-class coverage, not the entire Python
implementation or a universal one-sixth bit-complexity theorem.
-/

namespace RiemannGaussian.SemiprimeRoughProjection

open SemiprimeOrderSeparation SemiprimeLongPeriodExtraction

/-- Four public quadratic values, with signs removed only from exponents. -/
def quadraticProjectionTerm (i : ℕ) : ℕ :=
  (i^2+1) * ((i : ℤ)^2-2).natAbs * ((i : ℤ)^2-3).natAbs *
    ((i : ℤ)^2-5).natAbs

/-- Common exponent formed from the entire public quadratic candidate list. -/
def quadraticProjector (B : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 B, quadraticProjectionTerm i

theorem quadratic_plus_one_dvd_term (i : ℕ) : i^2+1 ∣ quadraticProjectionTerm i := by
  exact ⟨((i : ℤ)^2-2).natAbs * ((i : ℤ)^2-3).natAbs *
    ((i : ℤ)^2-5).natAbs, by simp [quadraticProjectionTerm, mul_assoc]⟩

theorem small_root_dvd_projector {B i r : ℕ} (hi : 1 ≤ i) (hiB : i ≤ B)
    (hroot : r ∣ i^2+1) : r ∣ quadraticProjector B := by
  exact (hroot.trans (quadratic_plus_one_dvd_term i)).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hi, hiB⟩))

theorem quadratic_projection_term_le {B i : ℕ} (hi : i ≤ B) :
    quadraticProjectionTerm i ≤ (B^2+5)^4 := by
  have hpow : i^2 ≤ B^2 := Nat.pow_le_pow_left hi 2
  have h2 : ((i : ℤ)^2-2).natAbs ≤ i^2+2 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 2
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  have h3 : ((i : ℤ)^2-3).natAbs ≤ i^2+3 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 3
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  have h5 : ((i : ℤ)^2-5).natAbs ≤ i^2+5 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 5
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  calc
    quadraticProjectionTerm i ≤ (B^2+5)*(B^2+5)*(B^2+5)*(B^2+5) := by
      dsimp [quadraticProjectionTerm]
      gcongr <;> omega
    _ = (B^2+5)^4 := by ring

/-- The exponent has O(B log B) bits, rather than an uncharged B²-sized
collection of pair differences. The logarithmic interpretation is external;
this theorem bounds the exact integer product. -/
theorem quadratic_projector_le (B : ℕ) :
    quadraticProjector B ≤ (B^2+5)^(4*B) := by
  calc
    quadraticProjector B ≤ ∏ _i ∈ Finset.Icc 1 B, (B^2+5)^4 := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun _ hi =>
        quadratic_projection_term_le (Finset.mem_Icc.mp hi).2
    _ = (B^2+5)^(4*B) := by simp [pow_mul]

theorem quadratic_leaves_pos (i : ℕ) :
    0 < ((i : ℤ)^2-2).natAbs ∧ 0 < ((i : ℤ)^2-3).natAbs ∧
      0 < ((i : ℤ)^2-5).natAbs := by
  by_cases hi : i ≤ 2
  · interval_cases i <;> norm_num
  · have hz : (3 : ℤ) ≤ i := by exact_mod_cast (show 3 ≤ i by omega)
    refine ⟨Int.natAbs_pos.mpr ?_, Int.natAbs_pos.mpr ?_, Int.natAbs_pos.mpr ?_⟩ <;>
      intro he <;> nlinarith

/-- This projection genuinely targets two-factor orders, not arbitrary
long prime orders: none of its quadratic leaves contains such a prime. -/
theorem prime_above_quadratic_bound_coprime {B p : ℕ} (hp : p.Prime)
    (hpB : B^2+5 < p) : p.Coprime (quadraticProjector B) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro i hi
  have hiB := (Finset.mem_Icc.mp hi).2
  have hpow : i^2 ≤ B^2 := Nat.pow_le_pow_left hiB 2
  have hpos := quadratic_leaves_pos i
  have h2 : ((i : ℤ)^2-2).natAbs ≤ i^2+2 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 2
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  have h3 : ((i : ℤ)^2-3).natAbs ≤ i^2+3 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 3
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  have h5 : ((i : ℤ)^2-5).natAbs ≤ i^2+5 := by
    have h := Int.natAbs_sub_le ((i : ℤ)^2) 5
    rw [← Nat.cast_pow, Int.natAbs_natCast] at h
    exact h
  have hc1 : p.Coprime (i^2+1) := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hc2 : p.Coprime ((i : ℤ)^2-2).natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hpos.1 (by omega))
  have hc3 : p.Coprime ((i : ℤ)^2-3).natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hpos.2.1 (by omega))
  have hc5 : p.Coprime ((i : ℤ)^2-5).natAbs := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hpos.2.2 (by omega))
  exact (hc1.mul_right hc2).mul_right hc3 |>.mul_right hc5

theorem long_prime_order_survives_quadratic_projection {G : Type*} [Group G]
    (a : G) {B p : ℕ} (hp : p.Prime) (hpB : B^2+5 < p) (ha : orderOf a = p) :
    orderOf (a^(quadraticProjector B)) = p := by
  have hcop : (orderOf a).Coprime (quadraticProjector B) := by
    rw [ha]
    exact prime_above_quadratic_bound_coprime hp hpB
  exact hcop.orderOf_pow.trans ha

/-- Four public cubic values for the explicit long-prime-root class. -/
def cubicProjectionTerm (i : ℕ) : ℕ :=
  ((i : ℤ)^3-2).natAbs * ((i : ℤ)^3-3).natAbs *
    ((i : ℤ)^3-5).natAbs * ((i : ℤ)^3+2).natAbs

/-- Common exponent formed from the public cubic candidate list. -/
def cubicProjector (B : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 B, cubicProjectionTerm i

theorem small_cubic_root_dvd_projector {B i r : ℕ} (hi : 1 ≤ i) (hiB : i ≤ B)
    (hroot : r ∣ ((i : ℤ)^3-2).natAbs) : r ∣ cubicProjector B := by
  have hterm : ((i : ℤ)^3-2).natAbs ∣ cubicProjectionTerm i := by
    exact ⟨((i : ℤ)^3-3).natAbs * ((i : ℤ)^3-5).natAbs *
      ((i : ℤ)^3+2).natAbs, by simp [cubicProjectionTerm, mul_assoc]⟩
  exact (hroot.trans hterm).trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hi, hiB⟩))

/-- A genuinely long prime period can close at one-sixth-sized public
construction cost on the explicit cubic-root class. The root condition
is not asserted for arbitrary primes. -/
theorem cubic_root_closes {G : Type*} [Group G] (a : G) {B i r : ℕ}
    (hi : 1 ≤ i) (hiB : i ≤ B) (hroot : r ∣ ((i : ℤ)^3-2).natAbs)
    (ha : orderOf a ∣ r) : a^(cubicProjector B) = 1 := by
  exact orderOf_dvd_iff_pow_eq_one.mp
    (ha.trans (small_cubic_root_dvd_projector hi hiB hroot))

/-- A cubic leaf can contain at most one coprime period larger than B².
Increasing the degree extends a success class but does not cover every
prime in the cubic-sized interval. -/
theorem cubic_leaf_not_divisible_by_two_long_orders {B a b e : ℕ} (hB : 2 ≤ B)
    (ha : B^2+1 ≤ a) (hb : B^2+1 ≤ b) (hc : a.Coprime b)
    (he : 0 < e) (heB : e ≤ B^3+5) (hae : a ∣ e) : ¬b ∣ e := by
  intro hbe
  have hmul := Nat.le_of_dvd he (hc.mul_dvd_of_dvd_of_dvd hae hbe)
  have hmin := Nat.mul_le_mul ha hb
  have hsq : B ≤ B^2 := by nlinarith
  have hquart : B^3 ≤ B^4 := by
    calc
      B^3 = B^2*B := by ring
      _ ≤ B^2*B^2 := Nat.mul_le_mul_left _ hsq
      _ = B^4 := by ring
  nlinarith

/-- Closing one order component is enough; the full product order need
not close. The lemma also covers a repeated rough prime. -/
theorem partial_projection_order_dvd {G : Type*} [Group G] (a : G)
    {r t M : ℕ} (hr : 0 < r) (ha : orderOf a ∣ r*t) (hM : r ∣ M) :
    orderOf (a^M) ∣ t := by
  have h := order_pow_dvd_quotient a ha (dvd_mul_right r t) hM
  simpa [Nat.mul_div_cancel_left _ hr] using h

/-- Explicit coverage of the small-root two-rough-factor population.
If the other leg is already closed, the projection GCD is the extraction;
this theorem handles the surviving nontrivial other leg. -/
theorem quadratic_partial_separating_witness {G H : Type*}
    [Group G] [Group H] [Finite G] (a : G) (b : H)
    {B r t i : ℕ} (hB : 2 ≤ B) (hr : B+1 ≤ r) (ht : B+1 ≤ t)
    (hsize : r*t ≤ B^3+1) (ha : orderOf a ∣ r*t)
    (hc : (orderOf a).Coprime (orderOf b))
    (hi : 1 ≤ i) (hiB : i ≤ B) (hroot : r ∣ i^2+1)
    (hb : b^(quadraticProjector B) ≠ 1) :
    ∃ d : ℕ, 0 < d ∧ d ≤ B^2 ∧
      (a^(quadraticProjector B))^d = 1 ∧
      (b^(quadraticProjector B))^d ≠ 1 := by
  have hrpos : 0 < r := by omega
  have hM := small_root_dvd_projector hi hiB hroot
  have horder := partial_projection_order_dvd a hrpos ha hM
  have hbound := (two_rough_factors_lt_square hB hr ht hsize).2
  have htle : 0 < t := by omega
  have hordle : orderOf (a^(quadraticProjector B)) ≤ B^2 :=
    (Nat.le_of_dvd htle horder).trans hbound.le
  have hcop := hc.of_dvd (orderOf_pow_dvd (quadraticProjector B))
    (orderOf_pow_dvd (quadraticProjector B))
  exact bounded_separating_witness _ _ hcop (orderOf_pos _) hordle
    (fun h => hb (orderOf_eq_one_iff.mp h))

/-- The witness is a collision in the literal B-by-B linear point cover.
The search enumerates public indices, not the unknown residual order. -/
theorem partial_witness_in_linear_cover {G H : Type*} [Group G] [Group H]
    {a : G} {b : H} {B d : ℕ} (hB : 0 < B) (hd : 0 < d) (hdB : d ≤ B^2)
    (ha : a^d = 1) (hb : b^d ≠ 1) :
    ∃ j i : ℕ, 1 ≤ j ∧ j ≤ B ∧ i < B ∧ a^(B*j) = a^i ∧ b^(B*j) ≠ b^i := by
  obtain ⟨j, i, hj, hjB, hiB, he⟩ := geometric_order_cover hB hd
    (by simpa [pow_two] using hdB)
  refine ⟨j, i, hj, hjB, hiB, ?_, ?_⟩
  · rw [← he, pow_add, ha, one_mul]
  · intro h
    rw [← he, pow_add] at h
    exact hb (mul_right_cancel (show b^d*b^i = 1*b^i by simpa using h))

/-- A positive quadratic leaf cannot simultaneously close two coprime
rough orders. Balanced prefix descent can therefore separate a shared
full-product annihilation under these conditions. -/
theorem small_leaf_not_divisible_by_both {B a b e : ℕ} (hB : 3 ≤ B)
    (ha : B+1 ≤ a) (hb : B+1 ≤ b) (hc : a.Coprime b)
    (he : 0 < e) (heB : e ≤ B^2+5) (hae : a ∣ e) : ¬b ∣ e := by
  intro hbe
  have hmul := Nat.le_of_dvd he (hc.mul_dvd_of_dvd_of_dvd hae hbe)
  have hmin := Nat.mul_le_mul ha hb
  nlinarith

/-- The original linear trace cover cannot reach a sufficiently long
period. This audit includes both equal and inverse channels. -/
theorem long_order_outside_linear_cover {B d i j : ℕ}
    (_hB : 0 < B) (hi : i < B) (hj : 0 < j) (hjB : j ≤ B)
    (hd : B^2+B < d) : ¬d ∣ B*j-i ∧ ¬d ∣ B*j+i := by
  have hlo : B ≤ B*j := by nlinarith
  have hhi : B*j ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul_left B hjB
  constructor
  · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- The positive split character over any commutative coefficient ring. -/
def splitPlus {R : Type*} [CommRing R] : QuadraticAlgebra R 1 0 →+* R where
  toFun x := x.re+x.im
  map_one' := by change (1 : R)+0 = 1; exact add_zero _
  map_zero' := by simp
  map_mul' x y := by simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]; ring
  map_add' x y := by simp; ring

/-- The negative split character over any commutative coefficient ring. -/
def splitMinus {R : Type*} [CommRing R] : QuadraticAlgebra R 1 0 →+* R where
  toFun x := x.re-x.im
  map_one' := by change (1 : R)-0 = 1; exact sub_zero _
  map_zero' := by simp
  map_mul' x y := by simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]; ring
  map_add' x y := by simp; ring

theorem split_characters_inverse {R : Type*} [CommRing R]
    (x : QuadraticAlgebra R 1 0) (hx : QuadraticAlgebra.norm x = 1) :
    splitPlus x * splitMinus x = 1 := by
  change (x.re+x.im)*(x.re-x.im) = 1
  simp only [QuadraticAlgebra.norm_def, one_mul, zero_mul, add_zero] at hx
  linear_combination hx

/-- Native modular powering through a split character recovers both
coordinates exactly over a composite ring. Inverses are explicit premises;
there is no field assumption or silent nonunit division. -/
theorem split_power_recovery {R : Type*} [CommRing R]
    (x : QuadraticAlgebra R 1 0) (hx : QuadraticAlgebra.norm x = 1)
    (m : ℕ) (v vi half : R) (hv : (splitPlus x)^m = v)
    (hvi : v*vi = 1) (hhalf : 2*half = 1) :
    (x^m).re = (v+vi)*half ∧ (x^m).im = (v-vi)*half := by
  have hplus : (x^m).re+(x^m).im = v := by
    simpa [splitPlus] using (splitPlus.map_pow x m).trans hv
  have hnorm : QuadraticAlgebra.norm (x^m) = 1 := by rw [map_pow, hx, one_pow]
  have hinv := split_characters_inverse (x^m) hnorm
  change ((x^m).re+(x^m).im)*((x^m).re-(x^m).im) = 1 at hinv
  rw [hplus] at hinv
  have hminus : (x^m).re-(x^m).im = vi := by
    have hh := congrArg (fun z => vi*z) hinv
    simpa [← mul_assoc, mul_comm vi v, hvi] using hh
  constructor
  · linear_combination -(x^m).re*hhalf + half*(hplus+hminus)
  · linear_combination -(x^m).im*hhalf + half*(hplus-hminus)

/-- Integer Dickson/Lucas exponent sequence at one fixed seed. -/
def lucasExponent (seed : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => seed
  | n+2 => seed*lucasExponent seed (n+1)-lucasExponent seed n

/-- Generate exponentiated Lucas values without materializing the exponents. -/
def recurrenceOrbit {G : Type*} [Group G] (a : G) (seed : ℤ) : ℕ → G
  | 0 => a^2
  | 1 => a^seed
  | n+2 => (recurrenceOrbit a seed (n+1))^seed * (recurrenceOrbit a seed n)⁻¹

/-- Increasing polynomial index is cheap at a fixed seed: the recurrence
uses one fixed-seed power and one multiplication per new point. -/
theorem recurrenceOrbit_eq {G : Type*} [Group G] (a : G) (seed : ℤ) :
    ∀ n, recurrenceOrbit a seed n = a^(lucasExponent seed n)
  | 0 => by simp [recurrenceOrbit, lucasExponent]
  | 1 => by simp [recurrenceOrbit, lucasExponent]
  | n+2 => by
    rw [recurrenceOrbit, recurrenceOrbit_eq a seed (n+1), recurrenceOrbit_eq a seed n,
      lucasExponent, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    ring

theorem lucasExponent_eq_dickson (seed : ℤ) :
    ∀ n, lucasExponent seed n = (Polynomial.dickson 1 (1 : ℤ) n).eval seed
  | 0 => by norm_num [lucasExponent]
  | 1 => by simp [lucasExponent]
  | n+2 => by
    simp [lucasExponent, lucasExponent_eq_dickson seed (n+1), lucasExponent_eq_dickson seed n,
      Polynomial.dickson_add_two]

/-- A particularly tempting pair of seeds gives globally coherent aliases,
not a separating hidden-period signal. -/
theorem seed_three_seven_global_alias {G : Type*} [Group G] (a : G) (n : ℕ) :
    recurrenceOrbit a 7 n = recurrenceOrbit a 3 (2*n) := by
  rw [recurrenceOrbit_eq, recurrenceOrbit_eq, lucasExponent_eq_dickson,
    lucasExponent_eq_dickson]
  congr 1
  simpa [Nat.mul_comm, Polynomial.dickson_two, Polynomial.dickson_zero]
    using dickson_nested_fold n 2 (3 : ℤ)

/-- Collision polynomial on globally distinct scalar traces. -/
noncomputable def collisionPolynomial {R : Type*} [CommRing R] (S : Finset R) : Polynomial R :=
  ∏ x ∈ S, (Polynomial.X-Polynomial.C x)

/-- Deflate a globally coherent trace root before extracting another local
collision. The derivative preserves the entire remaining product exactly,
over composite coefficient rings as well as fields. -/
theorem derivative_strips_shared_root {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) {t : R} (ht : t ∈ S) :
    (collisionPolynomial S).derivative.eval t = ∏ x ∈ S.erase t, (t-x) := by
  have hsplit : collisionPolynomial S =
      (Polynomial.X-Polynomial.C t)*collisionPolynomial (S.erase t) := by
    exact (Finset.mul_prod_erase S (fun x => Polynomial.X-Polynomial.C x) ht).symm
  rw [hsplit, Polynomial.derivative_mul]
  simp [collisionPolynomial, Polynomial.eval_prod]

/-- Whole-modulus trace equality can retain a separating imaginary signal. -/
theorem imaginary_orientation_control :
    (((10 : ZMod 35)-(10 : ZMod 35)).val.gcd 35 = 35) ∧
    (((27 : ZMod 35)-(22 : ZMod 35)).val.gcd 35 = 5) := by
  norm_num [ZMod.val_natCast, ZMod.val_ofNat]

theorem rough_square_control :
    393757207*590636903 = (232567537276409921 : ℕ) ∧
    8101 = 90^2+1 ∧ 8101^2 > (785 : ℕ)^2+785 := by norm_num

end RiemannGaussian.SemiprimeRoughProjection
