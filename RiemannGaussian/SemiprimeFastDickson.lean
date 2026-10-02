/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLongPeriodExtraction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Cheap high-degree folds and their exact collision limitation

Binary doubling evaluates a Dickson fold without expanding its polynomial.
A degree coprime to the relevant trace-lift exponent preserves collisions.
In particular, degree p*q cannot create collisions in the smaller prime
field. These are exact algebraic statements, not a universal factoring
algorithm or a proof of its bit complexity. This optional side module is
checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeFastDickson

open SemiprimeLongPeriodExtraction

/-- The even binary update, over a commutative ring including Z/NZ. -/
theorem dickson_double_eval {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    (Polynomial.dickson 1 (1 : R) (2*k)).eval x =
      ((Polynomial.dickson 1 (1 : R) k).eval x)^2-2 := by
  rw [Polynomial.dickson_one_one_mul, Polynomial.eval_comp]
  simp
  ring

/-- The odd update uses the two adjacent values and the original x. -/
theorem dickson_double_add_one_eval {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    (Polynomial.dickson 1 (1 : R) (2*k+1)).eval x =
      (Polynomial.dickson 1 (1 : R) k).eval x *
        (Polynomial.dickson 1 (1 : R) (k+1)).eval x-x := by
  have h := congrArg (fun P : Polynomial R => P.eval x)
    (Polynomial.Chebyshev.C_mul_C R (k : ℤ) ((k+1 : ℕ) : ℤ))
  have ha : (k : ℤ)+((k+1 : ℕ) : ℤ) = ((2*k+1 : ℕ) : ℤ) := by omega
  have hs : (k : ℤ)-((k+1 : ℕ) : ℤ) = -1 := by omega
  rw [ha, hs, Polynomial.Chebyshev.C_neg_one] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    ← Polynomial.dickson_one_one_eq_chebyshev_C] at h
  linear_combination -h

/-- Little-endian degree bits; no polynomial coefficient list is built. -/
def degreeOfBits : List Bool → ℕ
  | [] => 0
  | bit :: tail => 2*degreeOfBits tail + if bit then 1 else 0

/-- The exact binary circuit, valid over composite rings as well. -/
def dicksonOfBits {R : Type*} [CommRing R] (x : R) : List Bool → R × R
  | [] => (2, x)
  | bit :: tail =>
    let pair := dicksonOfBits x tail
    if bit then (pair.1*pair.2-x, pair.2^2-2)
    else (pair.1^2-2, pair.1*pair.2-x)

/-- Both outputs of the small binary circuit are genuine Dickson values. -/
theorem dicksonOfBits_correct {R : Type*} [CommRing R] (x : R) (bits : List Bool) :
    dicksonOfBits x bits =
      ((Polynomial.dickson 1 (1 : R) (degreeOfBits bits)).eval x,
       (Polynomial.dickson 1 (1 : R) (degreeOfBits bits+1)).eval x) := by
  induction bits with
  | nil => simp [dicksonOfBits, degreeOfBits]; ring
  | cons bit tail ih =>
    cases bit <;> simp only [dicksonOfBits, ih, degreeOfBits,
      Bool.false_eq_true, if_false, if_true, add_zero]
    · apply Prod.ext
      · exact (dickson_double_eval x _).symm
      · exact (dickson_double_add_one_eval x _).symm
    · apply Prod.ext
      · exact (dickson_double_add_one_eval x _).symm
      · convert (dickson_double_eval x (degreeOfBits tail+1)).symm using 1
        congr 1

private theorem pow_eq_one_of_coprime {F : Type*} [Field F]
    {x : F} {M d : ℕ} (hM : x^M = 1) (hd : x^d = 1)
    (hc : M.Coprime d) : x = 1 := by
  have ho : orderOf x ∣ 1 := by
    have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hM)
      (orderOf_dvd_of_pow_eq_one hd)
    simpa [hc.gcd_eq_one] using hh
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one ho)

/-- Large formal degree alone supplies no folding gain on these lifts. -/
theorem dickson_collision_iff_of_coprime {F : Type*} [Field F]
    {x y : F} {M d : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxM : x^M = 1) (hyM : y^M = 1) (hc : M.Coprime d) :
    (Polynomial.dickson 1 (1 : F) d).eval (x+x⁻¹) =
      (Polynomial.dickson 1 (1 : F) d).eval (y+y⁻¹) ↔
    x+x⁻¹ = y+y⁻¹ := by
  rw [dickson_collision_lift hx hy, reciprocal_trace_eq_iff hx hy]
  constructor
  · rintro (hr | hp)
    · left
      have hm : (x/y)^M = 1 := by rw [div_pow, hxM, hyM, div_one]
      exact (div_eq_one_iff_eq hy).mp (pow_eq_one_of_coprime hm hr hc)
    · right
      have hm : (x*y)^M = 1 := by rw [mul_pow, hxM, hyM, mul_one]
      exact pow_eq_one_of_coprime hm hp hc
  · rintro (rfl | hp)
    · left
      simp [hx]
    · right
      simp [hp]

private theorem pow_eq_one_gcd_iff {F : Type*} [Field F]
    {x : F} {M d : ℕ} (hM : x^M = 1) : x^d = 1 ↔ x^(M.gcd d) = 1 := by
  constructor
  · intro hd
    exact orderOf_dvd_iff_pow_eq_one.mp
      (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hM) (orderOf_dvd_of_pow_eq_one hd))
  · intro hg
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one hg).trans (Nat.gcd_dvd_right M d))

/-- Exact fibre compression: only the degree's GCD with the lift period
matters, even if the original degree has many more bits. -/
theorem dickson_collision_gcd {F : Type*} [Field F]
    {x y : F} {M : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxM : x^M = 1) (hyM : y^M = 1) (d : ℕ) :
    (Polynomial.dickson 1 (1 : F) d).eval (x+x⁻¹) =
      (Polynomial.dickson 1 (1 : F) d).eval (y+y⁻¹) ↔
    (Polynomial.dickson 1 (1 : F) (M.gcd d)).eval (x+x⁻¹) =
      (Polynomial.dickson 1 (1 : F) (M.gcd d)).eval (y+y⁻¹) := by
  rw [dickson_collision_lift hx hy, dickson_collision_lift hx hy]
  have hdiv : (x/y)^M = 1 := by rw [div_pow, hxM, hyM, div_one]
  have hmul : (x*y)^M = 1 := by rw [mul_pow, hxM, hyM, mul_one]
  rw [pow_eq_one_gcd_iff hdiv, pow_eq_one_gcd_iff hmul]

private theorem exists_reciprocal_lift {F : Type*} [Field F] [IsAlgClosed F]
    (x : F) : ∃ a : F, a ≠ 0 ∧ a+a⁻¹ = x := by
  let P : Polynomial F := Polynomial.X^2-Polynomial.C x*Polynomial.X+1
  have hdeg : P.degree ≠ 0 := by
    have hd : P.natDegree = 2 := by dsimp [P]; compute_degree!
    intro he
    have hn : P.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some he
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P hdeg
  have he : a^2-x*a+1 = 0 := by simpa [P, Polynomial.IsRoot] using ha
  have hne : a ≠ 0 := by intro h; simp [h] at he
  refine ⟨a, hne, ?_⟩
  apply (mul_left_inj' hne).mp
  field_simp
  linear_combination he

private theorem reciprocal_lift_period {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (f : ZMod p →+* F)
    {a : F} (ha : a ≠ 0) (x : ZMod p) (ht : a+a⁻¹ = f x) :
    a^(p^2-1) = 1 := by
  have hf : (a+a⁻¹)^p = a+a⁻¹ := by
    rw [ht, ← map_pow, ZMod.pow_card]
  have htr : a^p+(a^p)⁻¹ = a+a⁻¹ := by
    simpa only [add_pow_char, inv_pow] using hf
  have hsplit := (reciprocal_trace_eq_iff (pow_ne_zero p ha) ha).mp htr
  have hpp : a^(p^2) = a := by
    rw [pow_two, pow_mul]
    rcases hsplit with he | he
    · rw [he, he]
    · have he' : a^p = a⁻¹ := by
        exact (mul_eq_one_iff_eq_inv₀ ha).mp he
      rw [he', inv_pow, he', inv_inv]
  have hp : 1 ≤ p^2 := by have := (Fact.out : p.Prime).two_le; nlinarith
  have hh : a^(p^2-1)*a = a := by
    rw [← pow_succ, Nat.sub_add_cancel hp, hpp]
  exact (mul_left_inj' ha).mp (by simpa using hh)

private theorem map_dickson_eval {F K : Type*} [CommRing F] [CommRing K]
    (f : F →+* K) (x : F) (d : ℕ) :
    f ((Polynomial.dickson 1 (1 : F) d).eval x) =
      (Polynomial.dickson 1 (1 : K) d).eval (f x) := by
  have hm : (Polynomial.dickson 1 (1 : F) d).map f =
      Polynomial.dickson 1 (1 : K) d := by
    simpa using Polynomial.map_dickson (k := 1) (a := (1 : F)) f d
  rw [← hm, Polynomial.eval_map_apply]

/-- Every prime-field collision partition equals the much smaller
degree GCD partition. The hidden GCD is explanatory, not a public oracle. -/
theorem dickson_prime_field_collision_gcd {p : ℕ} [Fact p.Prime]
    (x y : ZMod p) (d : ℕ) :
    (Polynomial.dickson 1 (1 : ZMod p) d).eval x =
      (Polynomial.dickson 1 (1 : ZMod p) d).eval y ↔
    (Polynomial.dickson 1 (1 : ZMod p) ((p^2-1).gcd d)).eval x =
      (Polynomial.dickson 1 (1 : ZMod p) ((p^2-1).gcd d)).eval y := by
  let F := AlgebraicClosure (ZMod p)
  let f : ZMod p →+* F := algebraMap (ZMod p) F
  obtain ⟨a, ha, hat⟩ := exists_reciprocal_lift (f x)
  obtain ⟨b, hb, hbt⟩ := exists_reciprocal_lift (f y)
  have hh := dickson_collision_gcd ha hb
    (reciprocal_lift_period f ha x hat) (reciprocal_lift_period f hb y hbt) d
  rw [hat, hbt, ← map_dickson_eval, ← map_dickson_eval,
    ← map_dickson_eval, ← map_dickson_eval] at hh
  simpa only [(RingHom.injective f).eq_iff] using hh

/-- Full prime-field injectivity, with its exact group-period condition. -/
theorem dickson_injective_prime_field {p d : ℕ} [Fact p.Prime]
    (hc : (p^2-1).Coprime d) :
    Function.Injective (fun x : ZMod p =>
      (Polynomial.dickson 1 (1 : ZMod p) d).eval x) := by
  let F := AlgebraicClosure (ZMod p)
  let f : ZMod p →+* F := algebraMap (ZMod p) F
  intro x y hxy
  obtain ⟨a, ha, hat⟩ := exists_reciprocal_lift (f x)
  obtain ⟨b, hb, hbt⟩ := exists_reciprocal_lift (f y)
  have hfx : (Polynomial.dickson 1 (1 : F) d).eval (f x) =
      (Polynomial.dickson 1 (1 : F) d).eval (f y) := by
    have hh := congrArg f hxy
    have hm : (Polynomial.dickson 1 (1 : ZMod p) d).map f =
        Polynomial.dickson 1 (1 : F) d := by
      simpa using Polynomial.map_dickson (k := 1) (a := (1 : ZMod p)) f d
    rw [← hm, Polynomial.eval_map_apply, Polynomial.eval_map_apply]
    exact hh
  rw [← hat, ← hbt] at hfx
  have ht := (dickson_collision_iff_of_coprime ha hb
    (reciprocal_lift_period f ha x hat) (reciprocal_lift_period f hb y hbt) hc).mp hfx
  rw [hat, hbt] at ht
  exact (RingHom.injective f) ht

/-- For ordered odd primes, N is coprime to the smaller trace exponent. -/
theorem semiprime_degree_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpodd : 2 < p) (hpq : p < q) : (p^2-1).Coprime (p*q) := by
  have hp1 : (p^2-1).Coprime p := by
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hs : p^2-1+1 = p^2 := Nat.sub_add_cancel (by nlinarith)
    have hd' : p ∣ p^2-1+1 := by rw [hs]; exact dvd_pow_self p (by decide)
    have hone : p ∣ 1 := (Nat.dvd_add_iff_right hd).mpr hd'
    exact hp.not_dvd_one hone
  have hqp : p+1 < q := by
    have hpo := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
    have hqo := hq.mod_two_eq_one_iff_ne_two.mpr (by omega)
    omega
  have he : p^2-1 = (p-1)*(p+1) := by
    have hs : p^2-1+1 = p^2 := Nat.sub_add_cancel (by nlinarith)
    have hs' : p-1+1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hq1 : (p^2-1).Coprime q := (hq.coprime_iff_not_dvd.mpr (by
    rw [he]
    intro hd
    rcases hq.dvd_mul.mp hd with h | h
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) h
    · exact (Nat.not_dvd_of_pos_of_lt (by omega) hqp) h)).symm
  exact Nat.coprime_mul_iff_right.mpr ⟨hp1, hq1⟩

/-- The proposed cheap degree-N map cannot reveal a new smaller-prime
collision for ANY ordered odd semiprime, not merely the tested samples. -/
theorem semiprime_degree_no_new_smaller_collision {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : 2 < p) (hpq : p < q)
    (x y : ZMod p) :
    (Polynomial.dickson 1 (1 : ZMod p) (p*q)).eval x =
      (Polynomial.dickson 1 (1 : ZMod p) (p*q)).eval y ↔ x = y := by
  have : Fact p.Prime := ⟨hp⟩
  exact (dickson_injective_prime_field (semiprime_degree_coprime hp hq hpodd hpq)).eq_iff

/-- The concrete B-by-B integer cover still misses the smaller prime
when it exceeds B²; evaluating degree N adds no longer-period access. -/
theorem semiprime_degree_short_grid_no_collision {p q B i j : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : 2 < p) (hpq : p < q)
    (hsize : B^2 < p) (hi : i < B) (hj : 1 ≤ j) (hjB : j ≤ B) :
    (Polynomial.dickson 1 (1 : ZMod p) (p*q)).eval (i : ZMod p) ≠
      (Polynomial.dickson 1 (1 : ZMod p) (p*q)).eval ((B*j : ℕ) : ZMod p) := by
  intro he
  have hv := congrArg ZMod.val
    ((semiprime_degree_no_new_smaller_collision hp hq hpodd hpq _ _).mp he)
  have hB : 0 < B := by omega
  have hip : i < p := by nlinarith
  have hjp : B*j < p := by nlinarith
  simp only [ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp] at hv
  nlinarith

/-- Finite GCD replay for a nearby-degree recovery missed by the direct
linear, degree-six, and degree-twenty-four batches. Polynomial evaluation
and universal coverage remain distinct from this divisor certificate. -/
theorem fresh_nearby_degree_signal :
    Nat.gcd 171033372116459 95291626633620 = 12108181 ∧
      (1 : ℕ) < 12108181 ∧ 12108181 < 171033372116459 ∧
      12108181 ∣ (171033372116459 : ℕ) := by
  norm_num

end RiemannGaussian.SemiprimeFastDickson
