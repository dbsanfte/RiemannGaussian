/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FinitePrimePatternSieve
import RiemannGaussian.ZetaMoebiusResonanceDecay

/-!
# Prime-square intersections with their full common-prime correction

Intersecting a squarefree prime factor with selected prime squares
retains each shared prime at exponent two. The exact weight factors
before summation. All square overlaps have a uniform finite budget past
real part one half, including when the selected-prime families overlap.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The literal intersection of the first-power primes in `W` with
the second-power primes in `V`, retaining every shared prime once at
the larger exponent. -/
def primeSquareIntersection (W V : Finset ℕ) : ℕ :=
  (∏ p ∈ W \ V, p) * (∏ p ∈ V, p) ^ 2

/-- Products of disjoint finite prime families are coprime. -/
theorem coprime_prod_primes_of_disjoint (W V : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hV : ∀ p ∈ V, p.Prime) (hdis : Disjoint W V) :
    (∏ p ∈ W, p).Coprime (∏ p ∈ V, p) := by
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Nat.coprime_primes (hW p hp) (hV q hq)).mpr
    (fun he ↦ (Finset.disjoint_left.mp hdis hp) (he ▸ hq))

/-- The square of a product of distinct primes divides an integer
exactly when each selected prime square divides it. -/
theorem prod_primes_sq_dvd_iff (V : Finset ℕ) (hV : ∀ p ∈ V, p.Prime) (n : ℕ) :
    (∏ p ∈ V, p) ^ 2 ∣ n ↔ ∀ p ∈ V, p ^ 2 ∣ n := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert p V hp ih =>
    have hprime := hV p (Finset.mem_insert_self _ _)
    have hrest (q : ℕ) (hq : q ∈ V) := hV q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ V, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (fun he ↦ hp (he ▸ hq))
    rw [Finset.prod_insert hp, mul_pow]
    constructor
    · intro h q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (Nat.dvd_mul_right _ _).trans h
      · exact (ih hrest).mp ((Nat.dvd_mul_left _ _).trans h) q hq
    · intro h
      exact ((hcop.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd
        (h p (Finset.mem_insert_self _ _))
        ((ih hrest).mpr (fun q hq ↦ h q (Finset.mem_insert_of_mem hq)))

/-- Every actual square intersection is positive. -/
theorem primeSquareIntersection_pos (W V : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hV : ∀ p ∈ V, p.Prime) :
    0 < primeSquareIntersection W V := by
  unfold primeSquareIntersection
  exact Nat.mul_pos (Finset.prod_pos (fun p hp ↦ (hW p (Finset.mem_sdiff.mp hp).1).pos))
    (pow_pos (Finset.prod_pos (fun p hp ↦ (hV p hp).pos)) _)

/-- The explicit intersection factor agrees with both original
divisibility conditions, including the zero physical index. -/
theorem primeSquareIntersection_dvd_iff (W V : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hV : ∀ p ∈ V, p.Prime) (n : ℕ) :
    primeSquareIntersection W V ∣ n ↔
      (∏ p ∈ W, p) ∣ n ∧ (∏ p ∈ V, p) ^ 2 ∣ n := by
  constructor
  · intro h
    have h1 : (∏ p ∈ W \ V, p) ∣ n := (Nat.dvd_mul_right _ _).trans h
    have h2 : (∏ p ∈ V, p) ^ 2 ∣ n := (Nat.dvd_mul_left _ _).trans h
    refine ⟨(prod_primes_dvd_iff W hW n).mpr (fun p hp ↦ ?_), h2⟩
    by_cases hpV : p ∈ V
    · exact (Finset.dvd_prod_of_mem id hpV).trans
        ((dvd_pow_self _ (by norm_num : 2 ≠ 0)).trans h2)
    · exact (Finset.dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hp, hpV⟩)).trans h1
  · rintro ⟨h1, h2⟩
    have hd : (∏ p ∈ W \ V, p) ∣ n :=
      (Finset.prod_dvd_prod_of_subset (W \ V) W id Finset.sdiff_subset).trans h1
    exact ((coprime_prod_primes_of_disjoint (W \ V) V
      (fun p hp ↦ hW p (Finset.mem_sdiff.mp hp).1) hV Finset.sdiff_disjoint).pow_right 2).mul_dvd_of_dvd_of_dvd hd h2

private theorem expWeight_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (σ : ℝ) :
    zetaPrimeExpWeight σ (a * b) = zetaPrimeExpWeight σ a * zetaPrimeExpWeight σ b := by
  unfold zetaPrimeExpWeight
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'), ← Real.exp_add]
  congr 1
  ring

/-- Positive finite products retain the exact multiplicative
exponential weight, before any overlap estimate. -/
theorem zetaPrimeExpWeight_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) (σ : ℝ) :
    zetaPrimeExpWeight σ (∏ p ∈ S, p) = ∏ p ∈ S, zetaPrimeExpWeight σ p := by
  induction S using Finset.induction_on with
  | empty => simp [zetaPrimeExpWeight]
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, expWeight_mul (hS p (Finset.mem_insert_self _ _))
      (Finset.prod_pos (fun q hq ↦ hS q (Finset.mem_insert_of_mem hq))),
      ih (fun q hq ↦ hS q (Finset.mem_insert_of_mem hq)), Finset.prod_insert hp]

private theorem square_weight (σ : ℝ) (n : ℕ) :
    zetaPrimeExpWeight σ (n ^ 2) = zetaPrimeExpWeight σ n ^ 2 := by
  unfold zetaPrimeExpWeight
  rw [Nat.cast_pow, Real.log_pow, ← Real.exp_nat_mul]
  congr 1
  ring

private theorem product_overlap (W V : Finset ℕ) (w : ℕ → ℝ) :
    (∏ p ∈ W \ V, w p) * (∏ p ∈ V, w p) ^ 2 =
      (∏ p ∈ W, w p) * ∏ p ∈ V, (if p ∈ W then w p else w p ^ 2) := by
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter,
    Finset.prod_pow]
  rw [← Finset.prod_inter_mul_prod_sdiff W V w, ← Finset.prod_inter_mul_prod_sdiff V W w,
    Finset.inter_comm V W]
  ring

/-- The exact intersection weight retains every shared prime:
its extra factor is first-power, while each new square costs second-power. -/
theorem zetaPrimeExpWeight_primeSquareIntersection (W V : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hV : ∀ p ∈ V, p.Prime) (σ : ℝ) :
    zetaPrimeExpWeight σ (primeSquareIntersection W V) =
      (∏ p ∈ W, zetaPrimeExpWeight σ p) *
        ∏ p ∈ V, (if p ∈ W then zetaPrimeExpWeight σ p else zetaPrimeExpWeight σ p ^ 2) := by
  rw [primeSquareIntersection, expWeight_mul
    (Finset.prod_pos (fun p hp ↦ (hW p (Finset.mem_sdiff.mp hp).1).pos))
    (pow_pos (Finset.prod_pos (fun p hp ↦ (hV p hp).pos)) _), square_weight,
    zetaPrimeExpWeight_prod _ (fun p hp ↦ (hW p (Finset.mem_sdiff.mp hp).1).pos),
    zetaPrimeExpWeight_prod _ (fun p hp ↦ (hV p hp).pos)]
  exact product_overlap W V _

/-- The full square-overlap mass has one exact product formula for
every finite selected square family, with no disjointness hypothesis. -/
theorem sum_primeSquareIntersection_weight (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (σ : ℝ) :
    (∑ V ∈ Q.powerset, zetaPrimeExpWeight σ (primeSquareIntersection W V)) =
      (∏ p ∈ W, zetaPrimeExpWeight σ p) *
        ∏ p ∈ Q, (1 + if p ∈ W then zetaPrimeExpWeight σ p else zetaPrimeExpWeight σ p ^ 2) := by
  rw [Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  exact zetaPrimeExpWeight_primeSquareIntersection W V hW
    (fun p hp ↦ hQ p (Finset.mem_powerset.mp hV hp)) σ

/-- The fixed square-divisor weight mass. It is finite strictly past
real part one half and independent of every finite selected family. -/
def primeSquareWeightMass (σ : ℝ) : ℝ :=
  ∑' n, zetaPrimeExpWeight σ n ^ 2

/-- All square-divisor weights are genuinely summable past one half. -/
theorem summable_primeSquareWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n ↦ zetaPrimeExpWeight σ n ^ 2) := by
  apply (summable_zetaPrimeExpWeight (show 1 < 2 * σ by linarith)).congr
  intro n
  unfold zetaPrimeExpWeight
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The full square weight mass is nonnegative. -/
theorem primeSquareWeightMass_nonneg (σ : ℝ) : 0 ≤ primeSquareWeightMass σ :=
  tsum_nonneg (fun _ ↦ sq_nonneg _)

/-- Every finite selection of squares fits the same total mass. -/
theorem sum_primeSquareWeight_le (Q : Finset ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑ p ∈ Q, zetaPrimeExpWeight σ p ^ 2) ≤ primeSquareWeightMass σ :=
  (summable_primeSquareWeight hσ).sum_le_tsum Q (fun _ _ ↦ sq_nonneg _)

/-- The complete square-subset product has a constant bound that does
not depend on the largest selected prime or the number of selected primes. -/
theorem prod_one_add_primeSquareWeight_le (Q : Finset ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∏ p ∈ Q, (1 + zetaPrimeExpWeight σ p ^ 2)) ≤ Real.exp (primeSquareWeightMass σ) := by
  calc
    _ ≤ ∏ p ∈ Q, Real.exp (zetaPrimeExpWeight σ p ^ 2) := Finset.prod_le_prod
      (fun p _ ↦ by positivity)
      (fun p _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (zetaPrimeExpWeight σ p ^ 2))
    _ = Real.exp (∑ p ∈ Q, zetaPrimeExpWeight σ p ^ 2) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (sum_primeSquareWeight_le Q hσ)

/-- The common-prime correction is retained in the first-power
factor, while every selected square is paid by one fixed convergent mass. -/
theorem sum_primeSquareIntersection_weight_le (W Q : Finset ℕ)
    (hW : ∀ p ∈ W, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑ V ∈ Q.powerset, zetaPrimeExpWeight σ (primeSquareIntersection W V)) ≤
      Real.exp (primeSquareWeightMass σ) *
        ∏ p ∈ W, (zetaPrimeExpWeight σ p * (1 + zetaPrimeExpWeight σ p)) := by
  let w := zetaPrimeExpWeight σ
  have hw (p : ℕ) : 0 ≤ w p := (Real.exp_pos _).le
  have hprod : (∏ p ∈ Q, (1 + if p ∈ W then w p else w p ^ 2)) ≤
      (∏ p ∈ W, (1 + w p)) * Real.exp (primeSquareWeightMass σ) := by
    calc
      _ ≤ ∏ p ∈ Q, ((if p ∈ W then 1 + w p else 1) * (1 + w p ^ 2)) := by
        apply Finset.prod_le_prod
        · intro p _
          split_ifs <;> nlinarith [hw p, sq_nonneg (w p)]
        · intro p _
          by_cases hp : p ∈ W <;> simp only [hp, if_true, if_false]
          · nlinarith [hw p, sq_nonneg (w p), mul_nonneg (hw p) (sq_nonneg (w p))]
          · simp
      _ = (∏ p ∈ Q ∩ W, (1 + w p)) * ∏ p ∈ Q, (1 + w p ^ 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_mem]
      _ ≤ (∏ p ∈ W, (1 + w p)) * Real.exp (primeSquareWeightMass σ) := mul_le_mul
        (Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ ↦ by linarith [hw p]) (fun p _ _ ↦ by linarith [hw p]))
        (prod_one_add_primeSquareWeight_le Q hσ)
        (Finset.prod_nonneg (fun p _ ↦ by positivity)) (Finset.prod_nonneg (fun p _ ↦ by linarith [hw p]))
  rw [sum_primeSquareIntersection_weight W Q hW hQ]
  exact (mul_le_mul_of_nonneg_left hprod (Finset.prod_nonneg (fun p _ ↦ hw p))).trans_eq (by
    rw [Finset.prod_mul_distrib]
    ring)

/-- The first-power intersection cost after every selected square
overlap has been summed, keeping the extra shared-prime correction. -/
def primeSquareCorrectedWeight (σ : ℝ) (p : ℕ) : ℝ :=
  zetaPrimeExpWeight σ p * (1 + zetaPrimeExpWeight σ p)

/-- All corrected first-power weights are nonnegative. -/
theorem primeSquareCorrectedWeight_nonneg (σ : ℝ) (p : ℕ) :
    0 ≤ primeSquareCorrectedWeight σ p := by
  unfold primeSquareCorrectedWeight zetaPrimeExpWeight
  positivity

/-- The full signed prime-pattern family has a product majorant for
every nonnegative multiplicative prime weight. The exact pattern identity
is kept separately from this companion estimate. -/
theorem sum_prime_patterns_product_le (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) :
    (∑ T ∈ S.powerset.filter (fun T ↦ 2 ≤ T.card), ∑ U ∈ (S \ T).powerset,
      ∏ p ∈ T ∪ U, w p) ≤ ∏ p ∈ S, (1 + 2 * w p) := by
  have he (T : Finset ℕ) (hT : T ∈ S.powerset) :
      (∑ U ∈ (S \ T).powerset, ∏ p ∈ T ∪ U, w p) =
        (∏ p ∈ T, w p) * ∏ p ∈ S \ T, (1 + w p) := by
    rw [Finset.prod_one_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.prod_union
    exact Finset.disjoint_left.mpr (fun p hpT hpU ↦
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hpU)).2 hpT)
  calc
    _ ≤ ∑ T ∈ S.powerset, ∑ U ∈ (S \ T).powerset, ∏ p ∈ T ∪ U, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun T _ _ ↦ Finset.sum_nonneg (fun U _ ↦ Finset.prod_nonneg (fun p _ ↦ hw p)))
    _ = ∑ T ∈ S.powerset, (∏ p ∈ T, w p) * ∏ p ∈ S \ T, (1 + w p) := Finset.sum_congr rfl he
    _ = ∏ p ∈ S, (w p + (1 + w p)) := (Finset.prod_add _ _ _).symm
    _ = _ := Finset.prod_congr rfl (fun _ _ ↦ by ring)

/-- Summing all corrected prime-pattern intersections still has the
same square-root cutoff exponent, with a fixed constant paying every
square overlap. No upper bound on the selected squares is required. -/
theorem prod_one_add_primeSquareCorrectedWeight_le (S : Finset ℕ) (R : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ R) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∏ p ∈ S, (1 + 2 * primeSquareCorrectedWeight σ p)) ≤
      Real.exp (2 * primeSquareWeightMass σ) * Real.exp (4 * Real.sqrt R) := by
  have hfirst : (∑ p ∈ S, zetaPrimeExpWeight σ p) ≤ 2 * Real.sqrt R := by
    calc
      _ ≤ ∑ p ∈ S, 1 / Real.sqrt p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [norm_zetaPrimeFeature, Complex.ofReal_re] using
          norm_zetaPrimeFeature_le_inv_sqrt (s := (σ : ℂ)) hσ.le (hS p hp).1.pos
      _ ≤ ∑ p ∈ Finset.Icc 1 R, 1 / Real.sqrt p :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp ↦ Finset.mem_Icc.mpr ⟨(hS p hp).1.pos, (hS p hp).2⟩)
          (fun p _ _ ↦ by positivity)
      _ ≤ _ := sum_inv_sqrt_Icc_le R
  have hsum : (∑ p ∈ S, primeSquareCorrectedWeight σ p) ≤
      2 * Real.sqrt R + primeSquareWeightMass σ := by
    have he : (∑ p ∈ S, primeSquareCorrectedWeight σ p) =
        (∑ p ∈ S, zetaPrimeExpWeight σ p) + ∑ p ∈ S, zetaPrimeExpWeight σ p ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      unfold primeSquareCorrectedWeight
      ring
    rw [he]
    exact add_le_add hfirst (sum_primeSquareWeight_le S hσ)
  calc
    _ ≤ ∏ p ∈ S, Real.exp (2 * primeSquareCorrectedWeight σ p) := Finset.prod_le_prod
      (fun p _ ↦ by linarith [primeSquareCorrectedWeight_nonneg σ p])
      (fun p _ ↦ by simpa only [add_comm] using Real.add_one_le_exp (2 * primeSquareCorrectedWeight σ p))
    _ = Real.exp (2 * ∑ p ∈ S, primeSquareCorrectedWeight σ p) := by rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * primeSquareWeightMass σ + 4 * Real.sqrt R) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_add _ _

end
end RiemannGaussian
