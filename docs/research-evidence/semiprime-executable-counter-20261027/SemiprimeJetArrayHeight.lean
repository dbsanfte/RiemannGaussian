/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetArray
import Mathlib.Data.Rat.Lemmas

/-!
# Denominator and numerator bounds for cached normalized inverse jets

The coefficient at index k has a representation with denominator d^k when the
normalized input has common denominator d. Thus exponentially many formal
inverse terms do not create exponentially many unrelated denominators.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeJetArrayHeight
open scoped BigOperators
open RiemannGaussian.SemiprimeJetRecurrence
open RiemannGaussian.SemiprimeJetArray

/-- A common integer denominator and a literal numerator bound. -/
def Representation (q : ℚ) (d B : ℕ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / (d : ℚ) ∧ z.natAbs ≤ B

theorem representation_mono {q : ℚ} {d B C : ℕ} (h : Representation q d B) (hBC : B ≤ C) :
    Representation q d C := by
  obtain ⟨z, hz, hb⟩ := h
  exact ⟨z, hz, hb.trans hBC⟩

theorem representation_add {q r : ℚ} {d B C : ℕ}
    (hq : Representation q d B) (hr : Representation r d C) : Representation (q+r) d (B+C) := by
  obtain ⟨z, hz, hb⟩ := hq
  obtain ⟨w, hw, hc⟩ := hr
  refine ⟨z+w, ?_, (Int.natAbs_add_le z w).trans (Nat.add_le_add hb hc)⟩
  simp only [hz, hw, Int.cast_add, add_div]

theorem representation_mul {q r : ℚ} {d e B C : ℕ}
    (hq : Representation q d B) (hr : Representation r e C) : Representation (q*r) (d*e) (B*C) := by
  obtain ⟨z, hz, hb⟩ := hq
  obtain ⟨w, hw, hc⟩ := hr
  refine ⟨z*w, ?_, ?_⟩
  · simp only [hz, hw, Int.cast_mul, Nat.cast_mul, div_mul_div_comm]
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hb hc

/-- Finite accumulation adds numerators over one denominator. -/
theorem representation_sum {I : Type*} (s : Finset I) (q : I → ℚ) (d B : ℕ)
    (h : ∀ i ∈ s, Representation (q i) d B) : Representation (∑ i ∈ s, q i) d (s.card*B) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    have ha := representation_add (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    convert ha using 1; ring

/-- Reducing a fraction cannot increase either of its integer magnitudes. -/
theorem representation_reduced_bound {q : ℚ} {d B : ℕ}
    (hd : 0 < d) (h : Representation q d B) : q.den ≤ d ∧ q.num.natAbs ≤ B := by
  obtain ⟨z, hz, hB⟩ := h
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  obtain ⟨c, hn, hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den z hdZ
  have heq : (z : ℚ) / ((d : ℤ) : ℚ) = q := by simpa only [Int.cast_natCast] using hz.symm
  rw [heq] at hn hden
  have hc : c ≠ 0 := by intro hc; simp [hc] at hden; omega
  have hcabs : 1 ≤ c.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc)
  have hnabs := congrArg Int.natAbs hn
  have hdabs := congrArg Int.natAbs hden
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnabs hdabs
  constructor
  · nlinarith
  · have hsmall : q.num.natAbs ≤ z.natAbs := by
      calc
        _ = 1 * q.num.natAbs := by simp
        _ ≤ c.natAbs * q.num.natAbs := Nat.mul_le_mul_right _ hcabs
        _ = _ := hnabs.symm
    exact hsmall.trans hB

/-- A polynomial-bit envelope; the extra one keeps the base positive at width zero. -/
def inverseBase (J d B : ℕ) : ℕ := J * (d+B+1) + 1

private theorem scaled_product (d : ℕ) (hd : 0 < d) (x y : ℤ) (n i : ℕ) (hi : i ≤ n) :
    ((x : ℚ) / d) * ((y : ℚ) / (d : ℚ)^(n-i)) =
      ((x * y * (d : ℤ)^i : ℤ) : ℚ) / (d : ℚ)^(n+1) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hp : (d : ℚ)^(n+1) = (d : ℚ) * (d : ℚ)^(n-i) * (d : ℚ)^i := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi, pow_succ]
    ring
  push_cast
  rw [hp]
  field_simp

/-- Literal coefficients of the normalized inverse have a shared power
denominator and polynomial description length in J and the input bit heights. -/
theorem inverseCoeff_representation (a : ℕ → ℚ) (d B J : ℕ) (hd : 0 < d)
    (ha0 : a 0 = 1) (ha : ∀ i < J, Representation (a i) d B) :
    ∀ k < J, Representation (inverseCoeff a k) (d^k) ((inverseBase J d B)^k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero =>
      refine ⟨1, ?_, by simp⟩
      simp [inverseCoeff, ha0]
    | succ n =>
      classical
      let A : Fin (n+1) → ℤ := fun i => Classical.choose (ha (i.val+1) (by omega))
      let C : Fin (n+1) → ℤ := fun i => Classical.choose (ih (n-i.val) (by omega) (by omega))
      have hA (i : Fin (n+1)) : a (i.val+1) = (A i : ℚ) / d ∧ (A i).natAbs ≤ B :=
        Classical.choose_spec (ha (i.val+1) (by omega))
      have hC (i : Fin (n+1)) :
          inverseCoeff a (n-i.val) = (C i : ℚ) / ((d^(n-i.val) : ℕ) : ℚ) ∧
            (C i).natAbs ≤ inverseBase J d B ^ (n-i.val) :=
        Classical.choose_spec (ih (n-i.val) (by omega) (by omega))
      let z : ℤ := -(∑ i : Fin (n+1), A i * C i * (d : ℤ)^i.val)
      refine ⟨z, ?_, ?_⟩
      · rw [inverseCoeff, ha0, inv_one, neg_one_mul]
        rw [← Fin.sum_univ_eq_sum_range]
        have hsum : (∑ i : Fin (n+1), a (i.val+1) * inverseCoeff a (n-i.val)) =
            (∑ i : Fin (n+1), (A i * C i * (d : ℤ)^i.val : ℤ)) / (d : ℚ)^(n+1) := by
          rw [Int.cast_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          rw [(hA i).1, (hC i).1]
          simp only [Nat.cast_pow]
          exact scaled_product d hd _ _ n i.val (by omega)
        rw [hsum]
        simp only [z, Int.cast_neg, Int.cast_sum, Nat.cast_pow, neg_div]
      · have hJ : 1 ≤ J := by omega
        have hdH : d ≤ inverseBase J d B := by unfold inverseBase; nlinarith
        have hJB : (n+1)*B ≤ inverseBase J d B := by unfold inverseBase; nlinarith
        have hterm (i : Fin (n+1)) :
            (A i * C i * (d : ℤ)^i.val).natAbs ≤ B * inverseBase J d B ^ n := by
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
          calc
            _ ≤ B * inverseBase J d B ^ (n-i.val) * inverseBase J d B ^ i.val := by
              gcongr
              · exact (hA i).2
              · exact (hC i).2
            _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
        have habs : |z| ≤ ((n+1 : ℕ) : ℤ) * (B : ℤ) * (inverseBase J d B : ℤ)^n := by
          dsimp [z]
          rw [abs_neg]
          calc
            _ ≤ ∑ i : Fin (n+1), |A i * C i * (d : ℤ)^i.val| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin (n+1), ((B * inverseBase J d B ^ n : ℕ) : ℤ) := by
              apply Finset.sum_le_sum
              intro i _
              have ht : ((A i * C i * (d : ℤ)^i.val).natAbs : ℤ) ≤
                  ((B * inverseBase J d B ^ n : ℕ) : ℤ) := by exact_mod_cast hterm i
              simpa only [Int.natCast_natAbs] using ht
            _ = _ := by simp; ring
        have hnat : z.natAbs ≤ (n+1) * B * inverseBase J d B ^ n := by
          have ht : (z.natAbs : ℤ) ≤ ((n+1) * B * inverseBase J d B ^ n : ℕ) := by
            simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using habs
          exact_mod_cast ht
        exact hnat.trans (by simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (inverseBase J d B ^ n) hJB)

/-- The actual cached arrays inherit the denominator/numerator bound; the
proof does not run the uncached recurrence to produce their values. -/
theorem cached_inverse_heights (a : Array ℚ) (d B J : ℕ) (hd : 0 < d)
    (ha0 : coefficient a 0 = 1) (ha : ∀ i < J, Representation (coefficient a i) d B)
    (k : ℕ) (hk : k < J) :
    (coefficient (inverse a J).coefficients k).den ≤ d^k ∧
      (coefficient (inverse a J).coefficients k).num.natAbs ≤ inverseBase J d B ^ k := by
  rw [inverse_coefficient a J k hk]
  exact representation_reduced_bound (pow_pos hd _)
    (inverseCoeff_representation (coefficient a) d B J hd ha0 ha k hk)

/-- Partial multiply-add accumulators use the same power denominator as the
completed recurrence coefficient. This includes every loop prefix. -/
theorem dotPrefix_representation (a b : Array ℚ) (d B H n len : ℕ) (hd : 0 < d)
    (hdH : d ≤ H) (hlen : len ≤ n+1)
    (ha : ∀ i < len, Representation (coefficient a (i+1)) d B)
    (hb : ∀ i < len, Representation (coefficient b (n-i)) (d^(n-i)) (H^(n-i))) :
    Representation (dotPrefix a b n len).value (d^(n+1)) (len * B * H^n) := by
  classical
  let A : Fin len → ℤ := fun i => Classical.choose (ha i.val i.isLt)
  let C : Fin len → ℤ := fun i => Classical.choose (hb i.val i.isLt)
  have hA (i : Fin len) : coefficient a (i.val+1) = (A i : ℚ) / d ∧ (A i).natAbs ≤ B :=
    Classical.choose_spec (ha i.val i.isLt)
  have hC (i : Fin len) : coefficient b (n-i.val) = (C i : ℚ) / ((d^(n-i.val) : ℕ) : ℚ) ∧
      (C i).natAbs ≤ H^(n-i.val) := Classical.choose_spec (hb i.val i.isLt)
  refine ⟨∑ i : Fin len, A i * C i * (d : ℤ)^i.val, ?_, ?_⟩
  · rw [dotPrefix_value, ← Fin.sum_univ_eq_sum_range, Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hA i).1, (hC i).1]
    simp only [Nat.cast_pow]
    exact scaled_product d hd (A i) (C i) n i.val (by omega)
  · have hterm (i : Fin len) :
        (A i * C i * (d : ℤ)^i.val).natAbs ≤ B * H^n := by
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      calc
        _ ≤ B * H^(n-i.val) * H^i.val := by
          gcongr
          · exact (hA i).2
          · exact (hC i).2
        _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
    have habs : |∑ i : Fin len, A i * C i * (d : ℤ)^i.val| ≤ ((len * B * H^n : ℕ) : ℤ) := by
      calc
        _ ≤ ∑ i : Fin len, |A i * C i * (d : ℤ)^i.val| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin len, ((B * H^n : ℕ) : ℤ) := by
          apply Finset.sum_le_sum
          intro i _
          have ht : ((A i * C i * (d : ℤ)^i.val).natAbs : ℤ) ≤ ((B * H^n : ℕ) : ℤ) := by
            exact_mod_cast hterm i
          simpa only [Int.natCast_natAbs] using ht
        _ = _ := by simp; ring
    rw [← Int.natCast_natAbs] at habs
    exact_mod_cast habs

/-- Every partial accumulator actually used by the cached normalized inverse
has polynomial-size numerator and denominator representations. -/
theorem cached_dotPrefix_heights (a : Array ℚ) (d B J n len : ℕ) (hd : 0 < d)
    (ha0 : coefficient a 0 = 1) (ha : ∀ i < J, Representation (coefficient a i) d B)
    (hn : n+1 < J) (hlen : len ≤ n+1) :
    (dotPrefix a (inverse a (n+1)).coefficients n len).value.den ≤ d^(n+1) ∧
      (dotPrefix a (inverse a (n+1)).coefficients n len).value.num.natAbs ≤
        inverseBase J d B ^ (n+1) := by
  have hdH : d ≤ inverseBase J d B := by unfold inverseBase; nlinarith
  have h := dotPrefix_representation a (inverse a (n+1)).coefficients
    d B (inverseBase J d B) n len hd hdH hlen
    (fun i hi => ha (i+1) (by omega)) (by
      intro i hi
      rw [inverse_coefficient a (n+1) (n-i) (by omega)]
      exact inverseCoeff_representation (coefficient a) d B J hd ha0 ha (n-i) (by omega))
  have hr := representation_reduced_bound (pow_pos hd _) h
  refine ⟨hr.1, hr.2.trans ?_⟩
  have hb : len * B ≤ inverseBase J d B := by unfold inverseBase; nlinarith
  simpa only [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (inverseBase J d B ^ n) hb

/-- Convert a literal power-height bound into an explicit binary length bound. -/
theorem clog_succ_le_of_le_pow {x C k : ℕ} (hx : x ≤ C^k) :
    Nat.clog 2 (x+1) ≤ k * Nat.clog 2 (C+1) + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  have hC : C ≤ 2 ^ Nat.clog 2 (C+1) :=
    (Nat.le_succ C).trans (Nat.le_pow_clog (by decide) (C+1))
  have hp : x ≤ 2^(k * Nat.clog 2 (C+1)) := by
    calc
      _ ≤ C^k := hx
      _ ≤ (2^Nat.clog 2 (C+1))^k := Nat.pow_le_pow_left hC k
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hpos : 1 ≤ 2^(k * Nat.clog 2 (C+1)) := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ]
  omega

/-- Both integer fields of every stored inverse rational have explicit
polynomial binary lengths, rather than an uncharged rational unit cost. -/
theorem cached_inverse_bit_lengths (a : Array ℚ) (d B J : ℕ) (hd : 0 < d)
    (ha0 : coefficient a 0 = 1) (ha : ∀ i < J, Representation (coefficient a i) d B)
    (k : ℕ) (hk : k < J) :
    Nat.clog 2 ((coefficient (inverse a J).coefficients k).den + 1) ≤
        k * Nat.clog 2 (d+1) + 1 ∧
      Nat.clog 2 ((coefficient (inverse a J).coefficients k).num.natAbs + 1) ≤
        k * Nat.clog 2 (inverseBase J d B + 1) + 1 := by
  have h := cached_inverse_heights a d B J hd ha0 ha k hk
  exact ⟨clog_succ_le_of_le_pow h.1, clog_succ_le_of_le_pow h.2⟩

/-- One common denominator suffices for the entire stored inverse array. -/
theorem cached_inverse_common_representation (a : Array ℚ) (d B J : ℕ) (hd : 0 < d)
    (ha0 : coefficient a 0 = 1) (ha : ∀ i < J, Representation (coefficient a i) d B)
    (k : ℕ) (hk : k < J) :
    Representation (coefficient (inverse a J).coefficients k) (d^J) (inverseBase J d B ^ J) := by
  rw [inverse_coefficient a J k hk]
  obtain ⟨z, hz, hb⟩ := inverseCoeff_representation (coefficient a) d B J hd ha0 ha k hk
  refine ⟨z * (d : ℤ)^(J-k), ?_, ?_⟩
  · rw [hz]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hp : (d : ℚ)^J = (d : ℚ)^k * (d : ℚ)^(J-k) := by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hk)]
    push_cast
    rw [hp]
    field_simp
  · have hdH : d ≤ inverseBase J d B := by unfold inverseBase; nlinarith
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    calc
      _ ≤ inverseBase J d B ^ k * inverseBase J d B ^ (J-k) := by gcongr
      _ = _ := by rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hk)]

/-- Actual truncated-convolution output retains one product denominator. -/
theorem multiply_representation (a b : Array ℚ) (d e B C J : ℕ)
    (ha : ∀ i < J, Representation (coefficient a i) d B)
    (hb : ∀ i < J, Representation (coefficient b i) e C) (k : ℕ) (hk : k < J) :
    Representation (coefficient (multiply a b J).coefficients k) (d*e) (J*B*C) := by
  rw [multiply_coefficient a b J k hk]
  have h := representation_sum (Finset.range (k+1))
    (fun i => coefficient a i * coefficient b (k-i)) (d*e) (B*C) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact representation_mul (ha i (by omega)) (hb (k-i) (by omega)))
  apply representation_mono h
  simp only [Finset.card_range]
  calc
    _ ≤ J * (B*C) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

/-- Denominators and numerators of the executed Hermite quotient arrays,
including the multiplication after inversion, have explicit finite bounds. -/
theorem quotient_heights (H L : Array ℚ) (dH dL BH BL J : ℕ)
    (hdH : 0 < dH) (hdL : 0 < dL) (hL0 : coefficient L 0 = 1)
    (hH : ∀ i < J, Representation (coefficient H i) dH BH)
    (hL : ∀ i < J, Representation (coefficient L i) dL BL) (k : ℕ) (hk : k < J) :
    (coefficient (quotient H L J).coefficients k).den ≤ dH * dL^J ∧
      (coefficient (quotient H L J).coefficients k).num.natAbs ≤
        J * BH * inverseBase J dL BL ^ J := by
  change (coefficient (multiply H (inverse L J).coefficients J).coefficients k).den ≤ _ ∧ _
  apply representation_reduced_bound (Nat.mul_pos hdH (pow_pos hdL _))
  exact multiply_representation H (inverse L J).coefficients dH (dL^J) BH
    (inverseBase J dL BL ^ J) J hH
    (fun i hi => cached_inverse_common_representation L dL BL J hdL hL0 hL i hi) k hk

#print axioms cached_inverse_heights
#print axioms cached_dotPrefix_heights
#print axioms cached_inverse_bit_lengths
#print axioms quotient_heights
end RiemannGaussian.SemiprimeJetArrayHeight
