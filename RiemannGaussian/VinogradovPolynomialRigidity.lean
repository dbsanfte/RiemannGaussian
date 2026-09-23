/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovAffineMoment
import RiemannGaussian.VinogradovAnisotropicCongruence
import Mathlib.Algebra.Regular.Basic

/-!
# Polynomial systems retain complete moment and prime-power fibres

Triangular polynomial systems with regular leading coefficients carry
exactly the same weighted collision equations as the complete power sums.
This includes quotient rings with zero divisors: regularity, rather than
an unjustified integral-domain instance, is required there. The actual
integer moment and nonsingular prime-power fibre bounds follow from the
existing monomial theorems, without an extra coefficient-dependent loss.

This is an algebraic counting ingredient for the polynomial-system
conditioning in Ford (2002), Section 3. It is not the moment-order-raising
inequality, which still requires conditioning and differencing estimates.
-/

namespace RiemannGaussian.VinogradovPolynomialRigidity
noncomputable section
open scoped BigOperators
open Polynomial VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPowerSumRigidity VinogradovPrimePowerRigidity

/-- The positive degrees are triangular and their diagonal coefficients
can be cancelled. This formulation also applies modulo a prime power. -/
def RegularTriangular {R : Type*} [CommRing R] {k : ℕ}
    (F : Fin k → R[X]) : Prop :=
  ∀ j, (F j).natDegree ≤ j.val + 1 ∧ IsLeftRegular ((F j).coeff (j.val + 1))

/-- Expand a weighted polynomial moment before cancelling any lower degree. -/
theorem weighted_evaluation {R ι : Type*} [CommRing R] [Fintype ι]
    (f : R[X]) {n : ℕ} (hf : f.natDegree ≤ n) (c x : ι → R) :
    (∑ i, c i * f.eval (x i)) =
      ∑ j ∈ Finset.range (n + 1), f.coeff j * ∑ i, c i * x i ^ j := by
  simp_rw [Polynomial.eval_eq_sum_range' (by omega : f.natDegree < n + 1),
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Preserve every weight, sign and lower-degree equation under triangular
polynomial replacement. The constant term cancels because both sides use
the same weights, including in quotient rings. -/
theorem weighted_equations_iff {R ι : Type*} [CommRing R] [Fintype ι]
    {k : ℕ} (F : Fin k → R[X]) (hF : RegularTriangular F) (c x y : ι → R) :
    (∀ j, (∑ i, c i * (F j).eval (x i)) = ∑ i, c i * (F j).eval (y i)) ↔
      ∀ n, 1 ≤ n → n ≤ k → (∑ i, c i * x i ^ n) = ∑ i, c i * y i ^ n := by
  constructor
  · intro h n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hnk
      let j : Fin k := ⟨n - 1, by omega⟩
      have hj : j.val + 1 = n := by dsimp [j]; omega
      have hd : (F j).natDegree ≤ n := by simpa only [hj] using (hF j).1
      have he := h j
      rw [weighted_evaluation _ hd, weighted_evaluation _ hd,
        Finset.sum_range_succ, Finset.sum_range_succ] at he
      have hl : (∑ a ∈ Finset.range n, (F j).coeff a * ∑ i, c i * x i ^ a) =
          ∑ a ∈ Finset.range n, (F j).coeff a * ∑ i, c i * y i ^ a := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ha0 : a = 0
        · simp [ha0]
        · rw [ih a (Finset.mem_range.mp ha) (by omega) ((Nat.le_of_lt (Finset.mem_range.mp ha)).trans hnk)]
      rw [hl] at he
      have hr : IsLeftRegular ((F j).coeff n) := by simpa only [hj] using (hF j).2
      exact hr (add_left_cancel he)
  · intro h j
    rw [weighted_evaluation _ (hF j).1, weighted_evaluation _ (hF j).1]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    · rw [h a (by omega) (by have := Finset.mem_range.mp ha; omega)]

/-- The full polynomial frequency of an integer or residue class. -/
def polynomialFrequency {R : Type*} [CommRing R] {k : ℕ}
    (F : Fin k → R[X]) (x : R) : Fin k → R := fun j => (F j).eval x

/-- Complete polynomial and power-sum collisions coincide exactly. -/
theorem frequency_collision_iff {R ι : Type*} [CommRing R] [Fintype ι]
    {k : ℕ} (F : Fin k → R[X]) (hF : RegularTriangular F) (x y : ι → R) :
    (∑ i, polynomialFrequency F (x i)) = (∑ i, polynomialFrequency F (y i)) ↔
      (∀ n, 1 ≤ n → n ≤ k → (∑ i, x i ^ n) = ∑ i, y i ^ n) := by
  have h := weighted_equations_iff F hF (fun _ => 1) x y
  simpa only [one_mul, funext_iff, Finset.sum_apply, polynomialFrequency] using h

/-- The literal torus moment is unchanged by an arbitrary triangular
integer polynomial system. No coefficient-size cost is introduced. -/
theorem moment_eq_monomial {ι : Type*} [Fintype ι] {k : ℕ}
    (F : Fin k → ℤ[X]) (hF : RegularTriangular F) (r : ℕ) (v : ι → ℤ) :
    moment r (fun i => polynomialFrequency F (v i)) =
      moment r (fun i => integerFrequency k (v i)) := by
  classical
  rw [moment_eq_collisionCount, moment_eq_collisionCount]
  congr 1
  unfold collisionCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    frequency_collision_iff F hF,
    VinogradovAffineMoment.frequency_sum_eq_iff]

/-- All tuple orders receive the existing unconditional elementary
bound, uniformly in the coefficients of the original polynomial system. -/
theorem polynomial_moment_le {ι : Type*} [Fintype ι] {k : ℕ}
    (F : Fin k → ℤ[X]) (hF : RegularTriangular F) (r : ℕ)
    (v : ι → ℤ) (hv : Function.Injective v) :
    moment r (fun i => polynomialFrequency F (v i)) ≤
      (Fintype.card ι : ℝ) ^ (2 * r - min r k) * (min r k).factorial := by
  rw [moment_eq_monomial F hF]
  exact integer_moment_le_all r k v hv

/-- Mapping an integer system to a residue ring retains triangularity
provided its actual leading coefficients are units in that ring. -/
theorem regularTriangular_map {R S : Type*} [CommRing R] [CommRing S] {k : ℕ}
    (F : Fin k → R[X]) (f : R →+* S)
    (hdeg : ∀ j, (F j).natDegree ≤ j.val + 1)
    (hunit : ∀ j, IsUnit (f ((F j).coeff (j.val + 1)))) :
    RegularTriangular (fun j => (F j).map f) := by
  intro j
  refine ⟨(Polynomial.natDegree_map_le).trans (hdeg j), ?_⟩
  rw [Polynomial.coeff_map]
  exact (hunit j).isRegular.left

/-- An arbitrary prescribed complete polynomial target costs at most
`k!` nonsingular ordered tuples at every prime-power precision. The
unit condition is explicit, so primes dividing a leading coefficient
cannot silently enter this bound. -/
theorem nonsingular_polynomial_fibre_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (F : Fin k → (ZMod (p ^ n))[X]) (hF : RegularTriangular F)
    (target : Fin k → ZMod (p ^ n)) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      (∑ j, polynomialFrequency F ((u j).val : ZMod (p ^ n))) = target)).card ≤
      k.factorial := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)) ∧
    (∑ j, polynomialFrequency F ((u j).val : ZMod (p ^ n))) = target)
  change S.card ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨v, hv⟩ := hS
    obtain ⟨_, hvF⟩ := (Finset.mem_filter.mp hv).2
    apply le_trans (Finset.card_le_card ?_)
      (nonsingular_fibre_le_factorial hkp (residuePowerSums v))
    intro u hu
    obtain ⟨huprime, huF⟩ := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, huprime, ?_⟩
    have he := (frequency_collision_iff F hF
      (fun j => ((u j).val : ZMod (p ^ n)))
      (fun j => ((v j).val : ZMod (p ^ n)))).mp (huF.trans hvF.symm)
    funext j
    exact he (j.val + 1) (by omega) (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Correlated sets of complete polynomial targets pay only their
actual cardinality, rather than the product of coordinate supports. -/
theorem nonsingular_polynomial_preimage_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (F : Fin k → (ZMod (p ^ n))[X]) (hF : RegularTriangular F)
    (T : Finset (Fin k → ZMod (p ^ n))) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      (∑ j, polynomialFrequency F ((u j).val : ZMod (p ^ n))) ∈ T)).card ≤
      T.card * k.factorial := by
  classical
  let S := Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
    Function.Injective (fun j => ((u j).val : ZMod p)))
  have he : (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      (∑ j, polynomialFrequency F ((u j).val : ZMod (p ^ n))) ∈ T)) =
      S.filter (fun u => (∑ j, polynomialFrequency F ((u j).val : ZMod (p ^ n))) ∈ T) := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, ← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _ ∈ T, k.factorial := by
      apply Finset.sum_le_sum
      intro target htarget
      simpa only [S, Finset.filter_filter] using nonsingular_polynomial_fibre_le hkp F hF target
    _ = _ := by simp

/-- Different precisions in the polynomial equations pay exactly the
sum of the missing precision digits. The original polynomial equations
are retained until the complete-target fibre estimate is applied. -/
theorem polynomial_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (F : Fin k → (ZMod (p ^ n))[X]) (hF : RegularTriangular F)
    (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, (F i).eval ((u j).val : ZMod (p ^ n))).val % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * k.factorial := by
  classical
  let T (i : Fin k) := Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e i = a i)
  have hb := nonsingular_polynomial_preimage_le hkp F hF (Fintype.piFinset T)
  simp only [Fintype.mem_piFinset, Fintype.card_piFinset, Finset.sum_apply,
    polynomialFrequency, T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply hb.trans
  apply Nat.mul_le_mul_right
  calc
    (∏ i, (T i).card) ≤ ∏ i, p ^ (n - e i) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      exact VinogradovAnisotropicCongruence.prime_power_class_card_le (p := p) (he i) (a i)
    _ = p ^ (∑ i, (n - e i)) := Finset.prod_pow_eq_pow_sum _ _ _

end
end RiemannGaussian.VinogradovPolynomialRigidity
