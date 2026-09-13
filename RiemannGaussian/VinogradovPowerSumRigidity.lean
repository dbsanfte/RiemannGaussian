/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovShiftedMoment
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.List.Permutation

/-!
# Power-sum rigidity before estimating Vinogradov collisions

Newton's identities retain every degree of the joint power-sum system.
The first `r` powers determine the complete multiset of an `r`-tuple,
including repeated entries. This is the classical diagonal range of the
moment problem; estimates beyond that range need additional mathematics.
-/

namespace RiemannGaussian.VinogradovPowerSumRigidity
noncomputable section
open MeasureTheory UnitAddTorus VinogradovMeanValue
open scoped BigOperators

/-- Match the normalized Haar measure used by the exact moment identity. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle Haar measure in the moment is a probability measure. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The full monomial vector of an arbitrary integer, retaining each degree. -/
def integerFrequency (k : ℕ) (n : ℤ) : Fin k → ℤ := fun j => n ^ (j.val + 1)

private theorem interval_frequency_eq (k N : ℕ) :
    (fun n : Fin N => integerFrequency k ((n.val : ℤ) + 1)) =
      (fun n : Fin N => monomialFrequency k (n.val + 1)) := by
  funext n j
  simp only [integerFrequency, monomialFrequency, Nat.cast_add, Nat.cast_one]

private theorem evaluated_newton {r : ℕ} (f : Fin r → ℤ) (n : ℕ) :
    (n : ℤ) * (Finset.univ.val.map f).esymm n = (-1) ^ (n + 1) *
      ∑ a ∈ Finset.antidiagonal n with a.1 < n,
        (-1) ^ a.1 * (Finset.univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f)
    (MvPolynomial.mul_esymm_eq_sum (Fin r) ℤ n)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum,
    MvPolynomial.aeval_X] using h

/-- Equality of the first power sums forces equality of all elementary
symmetric coefficients up to the same degree. Multiplicity is retained. -/
theorem esymm_eq_of_power_sums {r d : ℕ} (f g : Fin r → ℤ)
    (h : ∀ n, 1 ≤ n → n ≤ d → (∑ i, f i ^ n) = ∑ i, g i ^ n) :
    ∀ n, n ≤ d → (Finset.univ.val.map f).esymm n =
      (Finset.univ.val.map g).esymm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n = 0
    · subst n
      simp [Multiset.esymm]
    apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn0)
    rw [evaluated_newton, evaluated_newton]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨ha, hal⟩ := Finset.mem_filter.mp ha
    have has := Finset.mem_antidiagonal.mp ha
    rw [ih a.1 hal (by omega), h a.2 (by omega) (by omega)]

/-- The first `r` power sums determine an entire integer `r`-tuple as a
multiset. Repeated values are counted, not reduced to distinct support. -/
theorem multiset_eq_of_power_sums {r : ℕ} (f g : Fin r → ℤ)
    (h : ∀ n, 1 ≤ n → n ≤ r → (∑ i, f i ^ n) = ∑ i, g i ^ n) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have he := esymm_eq_of_power_sums f g h
  have hp : ((Finset.univ.val.map f).map (fun t => Polynomial.X - Polynomial.C t)).prod =
      ((Finset.univ.val.map g).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map]
    apply Finset.sum_congr rfl
    intro n hn
    rw [he n (by simpa using Finset.mem_range.mp hn)]
  have hr := congrArg Polynomial.roots hp
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hr

/-- In the diagonal range, equality of the complete monomial tuple
frequencies forces equality of the original tuple multisets. -/
theorem tuple_multiset_eq {r k : ℕ} {ι : Type*} (hrk : r ≤ k)
    (f : ι → ℤ) (hf : Function.Injective f) (x y : Fin r → ι)
    (h : (∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i))) :
    Finset.univ.val.map x = Finset.univ.val.map y := by
  apply Multiset.map_injective hf
  simp only [Multiset.map_map]
  apply multiset_eq_of_power_sums
  intro n hn hnr
  have hn1 : n - 1 + 1 = n := by omega
  have he := congrFun h ⟨n - 1, by omega⟩
  simpa only [Finset.sum_apply, integerFrequency, hn1, Function.comp_apply] using he

/-- The collision condition in this range is exactly a permutation,
including every repeated entry and every ordered tuple. -/
theorem collision_iff_perm {r k : ℕ} {ι : Type*} (hrk : r ≤ k)
    (f : ι → ℤ) (hf : Function.Injective f) (x y : Fin r → ι) :
    ((∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i))) ↔
      List.Perm (List.ofFn x) (List.ofFn y) := by
  constructor
  · intro h
    have he := tuple_multiset_eq hrk f hf x y h
    simpa only [Fin.univ_val_map, Multiset.coe_eq_coe] using he
  · intro h
    have he := (h.map (fun a : ι => integerFrequency k (f a))).sum_eq
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using he

/-- At most `r!` ordered tuples share a given complete frequency vector
when the retained polynomial degree is at least `r`. -/
theorem collision_fibre_le_factorial {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) (x : Fin r → ι) :
    (Finset.univ.filter (fun y : Fin r → ι =>
      (∑ i, integerFrequency k (f (x i))) =
        ∑ i, integerFrequency k (f (y i)))).card ≤ r.factorial := by
  classical
  let S := Finset.univ.filter (fun y : Fin r → ι =>
    (∑ i, integerFrequency k (f (x i))) =
      ∑ i, integerFrequency k (f (y i)))
  have hsub : S.image List.ofFn ⊆ (List.ofFn x).permutations.toFinset := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl
    rw [List.mem_toFinset, List.mem_permutations]
    exact ((collision_iff_perm hrk f hf x y).mp (Finset.mem_filter.mp hy).2).symm
  calc
    S.card = (S.image List.ofFn).card :=
      (Finset.card_image_of_injective S List.ofFn_injective).symm
    _ ≤ (List.ofFn x).permutations.toFinset.card := Finset.card_le_card hsub
    _ ≤ (List.ofFn x).permutations.length := List.toFinset_card_le _
    _ = r.factorial := by rw [List.length_permutations, List.length_ofFn]

/-- The complete Vinogradov collision count has the diagonal-range bound,
uniformly in interval length and in every polynomial degree at least `r`. -/
theorem collisionCount_le {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) :
    collisionCount r (fun i => integerFrequency k (f i)) ≤
      Fintype.card ι ^ r * r.factorial := by
  classical
  unfold VinogradovMeanValue.collisionCount
  rw [Finset.card_filter, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x : Fin r → ι, r.factorial := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [Finset.card_filter] using collision_fibre_le_factorial hrk f hf x
    _ = _ := by simp

/-- An unconditional high-moment estimate in the entire diagonal range.
The quantitative mean-value problem for `r > k` remains separate. -/
theorem integer_moment_le {r k : ℕ} {ι : Type*} [Fintype ι]
    (hrk : r ≤ k) (f : ι → ℤ) (hf : Function.Injective f) :
    moment r (fun i => integerFrequency k (f i)) ≤
      (Fintype.card ι : ℝ) ^ r * r.factorial := by
  rw [moment_eq_collisionCount]
  exact_mod_cast collisionCount_le hrk f hf

/-- The diagonal bound applies to the literal Vinogradov interval integral. -/
theorem meanValue_le {r k N : ℕ} (hrk : r ≤ k) :
    meanValue r k N ≤ (N : ℝ) ^ r * r.factorial := by
  have hf : Function.Injective (fun n : Fin N => (n.val : ℤ) + 1) := by
    intro m n h
    apply Fin.ext
    dsimp only at h
    omega
  have h := integer_moment_le hrk _ hf
  rw [interval_frequency_eq] at h
  unfold meanValue
  simpa only [Fintype.card_fin] using h

/-- A lower even moment controls every higher one after paying the
pointwise cardinality bound only for the extra powers. -/
theorem moment_le_of_order_le {d ι : Type*} [Fintype d] [Fintype ι]
    {r s : ℕ} (hrs : r ≤ s) (v : ι → d → ℤ) :
    moment s v ≤ (Fintype.card ι : ℝ) ^ (2 * (s - r)) * moment r v := by
  classical
  have hi (n : ℕ) : Integrable (fun θ : UnitAddTorus d =>
      ‖∑ i, mFourier (v i) θ‖ ^ (2 * n)) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  unfold moment
  rw [← integral_const_mul]
  apply integral_mono (hi s) ((hi r).const_mul _)
  intro θ
  dsimp only
  have hn : ‖∑ i, mFourier (v i) θ‖ ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, ‖mFourier (v i) θ‖ := norm_sum_le _ _
      _ = _ := by simp only [VinogradovShiftedMoment.norm_mFourier_apply,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [show 2 * s = 2 * (s - r) + 2 * r by omega, pow_add]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hn _) (pow_nonneg (norm_nonneg _) _)

/-- An elementary all-order estimate using the full diagonal range as
its base. This saves `min(r,k)` powers over the trivial tuple count;
the stronger Vinogradov estimate still requires further arithmetic. -/
theorem integer_moment_le_all {ι : Type*} [Fintype ι] (r k : ℕ)
    (f : ι → ℤ) (hf : Function.Injective f) :
    moment r (fun i => integerFrequency k (f i)) ≤
      (Fintype.card ι : ℝ) ^ (2 * r - min r k) * (min r k).factorial := by
  have h := moment_le_of_order_le (Nat.min_le_left r k)
    (fun i => integerFrequency k (f i))
  calc
    _ ≤ (Fintype.card ι : ℝ) ^ (2 * (r - min r k)) *
        moment (min r k) (fun i => integerFrequency k (f i)) := h
    _ ≤ (Fintype.card ι : ℝ) ^ (2 * (r - min r k)) *
        ((Fintype.card ι : ℝ) ^ min r k * (min r k).factorial) :=
      mul_le_mul_of_nonneg_left (integer_moment_le (Nat.min_le_right r k) f hf) (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- Every literal Vinogradov interval moment inherits the explicit
all-order bound, with no condition on interval length or degree. -/
theorem meanValue_le_all (r k N : ℕ) :
    meanValue r k N ≤ (N : ℝ) ^ (2 * r - min r k) * (min r k).factorial := by
  have hf : Function.Injective (fun n : Fin N => (n.val : ℤ) + 1) := by
    intro m n h
    apply Fin.ext
    dsimp only at h
    omega
  have h := integer_moment_le_all r k _ hf
  rw [interval_frequency_eq] at h
  unfold meanValue
  simpa only [Fintype.card_fin] using h

/-- Any finite set of integer shifts has the same cardinality-based
moment bound; no interval shape or distribution hypothesis is needed. -/
theorem finite_monomial_moment_le (r k : ℕ) (B : Finset ℕ) :
    moment r (fun b : B => monomialFrequency k b.val) ≤
      (B.card : ℝ) ^ (2 * r - min r k) * (min r k).factorial := by
  have hf : Function.Injective (fun b : B => (b.val : ℤ)) := by
    intro b c h
    apply Subtype.ext
    dsimp only at h
    exact_mod_cast h
  have h := integer_moment_le_all r k _ hf
  unfold integerFrequency at h
  unfold monomialFrequency
  simpa only [Fintype.card_coe] using h

end
end RiemannGaussian.VinogradovPowerSumRigidity
