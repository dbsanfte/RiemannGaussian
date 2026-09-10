/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughSquarefreePrimeBalance

/-!
# Prime incidences inside the actual rough squarefree carrier

Marking one prime retains the original squarefree restriction, excluded
small primes, divisor cutoff, and complex kernel. Its exact completion
has every signed intersection and precisely one ordinary-prime correction.
Summing the norms of these complete marked series controls all bounded
complex prime weights at once. Multiple incidences are retained: this is
not an estimate for the union of the marked divisibility conditions.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.RoughPrimeIncidence
noncomputable section

/-- The original rough squarefree composite coefficient, marked by
one prime-divisibility condition. -/
def fibreCoefficient (D : ℕ) (S : Finset ℕ) (a n : ℕ) : ℂ :=
  if a ∣ n then zetaRoughSquarefreeCoefficient D S n else 0

/-- The full complex series for one marked prime, with the original
roughness and squarefree restrictions still present. -/
def fibre (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) (a : ℕ) : ℂ :=
  ∑' n, fibreCoefficient D S a n * zetaPrimeFilterKernel p N s n

/-- The linear incidence weight counts every selected prime dividing
an integer, retaining its supplied complex weight and every overlap. -/
def weight (T : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ T, if a ∣ n then w a else 0

/-- Every marked original series is genuinely summable in the
absolute Dirichlet half-plane. -/
theorem summable_fibre (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (a : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ fibreCoefficient D S a n * zetaPrimeFilterKernel p N s n) := by
  have h := (summable_zetaRoughSquarefreeFilter p D N hD S hS hs).indicator {n | a ∣ n}
  apply h.congr
  intro n
  by_cases hn : a ∣ n <;> simp [Set.indicator, fibreCoefficient, hn]

private theorem marked_prefix_eq (D : ℕ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b.Prime) {a : ℕ} (ha : a.Prime) (n : ℕ) :
    (if a ∣ n then zetaRoughSquarefreePrefixCoefficient D S n else 0) =
      ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixCoefficient D (insert a W) n := by
  have he (W : Finset ℕ) (hW : W ∈ S.powerset) :
      zetaSquarefreeDivisibilityPrefixCoefficient D (insert a W) n =
        if a ∣ n then zetaSquarefreeDivisibilityPrefixCoefficient D W n else 0 := by
    have hWp : ∀ b ∈ W, b.Prime := fun b hb ↦ hS b (Finset.mem_powerset.mp hW hb)
    have hi : ∀ b ∈ insert a W, b.Prime := by
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact hWp b hb
    rw [zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D (insert a W) n,
      zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D W n]
    simp only [prod_primes_dvd_iff _ hi, prod_primes_dvd_iff _ hWp,
      Finset.forall_mem_insert]
    by_cases han : a ∣ n <;> simp [han]
  have hsum := Finset.sum_congr rfl (fun W hW ↦
    congrArg (fun z : ℂ ↦ (-1 : ℂ) ^ W.card * z) (he W hW))
  rw [hsum]
  by_cases han : a ∣ n
  · simp only [han, if_true]
    exact zetaRoughSquarefreePrefixCoefficient_eq_subsets D S hS n
  · simp [han]

/-- The exact marked carrier includes all signed squarefree
intersections and one explicit ordinary-prime correction. -/
theorem fibreCoefficient_eq (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b.Prime) {a : ℕ} (ha : a.Prime) (haS : a ∉ S) (n : ℕ) :
    fibreCoefficient D S a n =
      (∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixCoefficient D (insert a W) n) +
      if n = a then (Real.log a : ℂ) else 0 := by
  have hp : (if a ∣ n then zetaRoughPrimeCoefficient S n else 0) =
      if n = a then (Real.log a : ℂ) else 0 := by
    by_cases hn : n = a
    · subst n
      simp [zetaRoughPrimeCoefficient, ha, haS]
    · have hno : ¬(a ∣ n ∧ n.Prime) := by
        rintro ⟨hd, hprime⟩
        exact hn ((Nat.prime_dvd_prime_iff_eq ha hprime).mp hd).symm
      by_cases hd : a ∣ n
      · have hnp : ¬n.Prime := fun h ↦ hno ⟨hd, h⟩
        simp [hd, hn, zetaRoughPrimeCoefficient, hnp]
      · simp [hd, hn]
  rw [← marked_prefix_eq D S hS ha n, ← hp]
  unfold fibreCoefficient
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS n]
  split_ifs <;> simp

/-- The exact finite signed completion sums to the genuine marked
arithmetic series; no unproved interchange or omitted prime term is used. -/
theorem hasSum_fibre (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ b ∈ S, b.Prime) {a : ℕ} (ha : a.Prime) (haS : a ∉ S)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ fibreCoefficient D S a n * zetaPrimeFilterKernel p N s n)
      ((∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixFilter p D (insert a W) N s) +
        (Real.log a : ℂ) * zetaPrimeFilterKernel p N s a) := by
  have h := hasSum_sum (s := S.powerset) (fun W hW ↦
    (summable_zetaSquarefreeDivisibilityPrefixFilter p D N (insert a W)
      (by
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ha
        · exact hS b (Finset.mem_powerset.mp hW hb)) hs).hasSum.mul_left ((-1 : ℂ) ^ W.card))
  have hp : HasSum (fun n ↦ if n = a then
      (Real.log a : ℂ) * zetaPrimeFilterKernel p N s a else 0)
      ((Real.log a : ℂ) * zetaPrimeFilterKernel p N s a) := hasSum_ite_eq a _
  apply (h.add hp).congr_fun
  intro n
  rw [fibreCoefficient_eq D hD S hS ha haS n, add_mul, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun W _ ↦ by ring)
  · by_cases hn : n = a <;> simp [hn]

/-- Finite complex prime families act on the original arithmetic
series through the exact incidence weight, including multiple marks. -/
theorem hasSum_weight (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (T : Finset ℕ) (w : ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ weight T w n * zetaRoughSquarefreeCoefficient D S n *
      zetaPrimeFilterKernel p N s n) (∑ a ∈ T, w a * fibre p D S N s a) := by
  have h := hasSum_sum (s := T) (fun a _ ↦
    (summable_fibre p D N hD S hS a hs).hasSum.mul_left (w a))
  apply h.congr_fun
  intro n
  simp only [weight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hn : a ∣ n <;> simp [fibreCoefficient, hn, mul_assoc]

/-- A marked prime has a decaying multiplicative weight in the
complete prefix bound. Its exact ordinary-prime correction is kept separately. -/
theorem exists_fibre_bound (y : ℝ) (hy : 1 < |y|) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ) (a : ℕ),
      1 ≤ D → (∀ b ∈ S, b.Prime ∧ b ≤ R) → a.Prime → a ∉ S →
      ‖fibre p D S N (3 / 2 + I * y) a‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) *
          primeSquareCorrectedWeight (zetaSquareSieveExponent r) a +
        Real.log a * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) a‖ := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  let w := primeSquareCorrectedWeight τ
  refine ⟨C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p D N R S a hD hS ha haS
  let A := C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw : ∀ b, 0 ≤ w b := primeSquareCorrectedWeight_nonneg τ
  rw [fibre, (hasSum_fibre p D N hD S (fun b hb ↦ (hS b hb).1) ha haS
    (by norm_num)).tsum_eq]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ W ∈ S.powerset, A * (w a * ∏ b ∈ W, w b) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro W hW
      have haW : a ∉ W := fun h ↦ haS (Finset.mem_powerset.mp hW h)
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      have h := hb p D N (insert a W) (by
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ha
        · exact (hS b (Finset.mem_powerset.mp hW hb)).1)
      simpa only [Finset.prod_insert haW] using h
    _ = (A * w a) * ∏ b ∈ S, (1 + w b) := by
      rw [Finset.prod_one_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun W _ ↦ by ring)
    _ ≤ (A * w a) * ∏ b ∈ S, (1 + 2 * w b) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun b _ ↦ by linarith [hw b])
        (fun b _ ↦ by linarith [hw b])) (mul_nonneg hA (hw a))
    _ ≤ (A * w a) *
        (Real.exp (2 * primeSquareWeightMass τ) * Real.exp (4 * Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left
        (prod_one_add_primeSquareCorrectedWeight_le S R hS (zetaSquareSieveExponent_gt_half hr1))
        (mul_nonneg hA (hw a))
    _ = _ := by dsimp [A, w, τ]; ring

private theorem sum_expWeight_le_sqrt (T : Finset ℕ) (X : ℕ)
    (hT : ∀ a ∈ T, a.Prime ∧ a ≤ X) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (∑ a ∈ T, zetaPrimeExpWeight σ a) ≤ 2 * Real.sqrt X := by
  calc
    _ ≤ ∑ a ∈ T, 1 / Real.sqrt a := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [norm_zetaPrimeFeature, Complex.ofReal_re] using
        norm_zetaPrimeFeature_le_inv_sqrt (s := (σ : ℂ)) hσ (hT a ha).1.pos
    _ ≤ ∑ a ∈ Finset.Icc 1 X, 1 / Real.sqrt a :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha ↦ Finset.mem_Icc.mpr ⟨(hT a ha).1.pos, (hT a ha).2⟩)
        (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_inv_sqrt_Icc_le X

private theorem sum_correctedWeight_le_sqrt (T : Finset ℕ) (X : ℕ)
    (hT : ∀ a ∈ T, a.Prime ∧ a ≤ X) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑ a ∈ T, primeSquareCorrectedWeight σ a) ≤ 4 * Real.sqrt X := by
  calc
    _ ≤ ∑ a ∈ T, 2 * zetaPrimeExpWeight σ a := by
      apply Finset.sum_le_sum
      intro a _
      have hw : zetaPrimeExpWeight σ a ≤ 1 := Real.exp_le_one_iff.mpr
        (by nlinarith [mul_nonneg (show 0 ≤ σ by linarith) (Real.log_natCast_nonneg a)])
      unfold primeSquareCorrectedWeight
      have hw0 : 0 ≤ zetaPrimeExpWeight σ a := (Real.exp_pos _).le
      nlinarith
    _ = 2 * ∑ a ∈ T, zetaPrimeExpWeight σ a := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by linarith [sum_expWeight_le_sqrt T X hT hσ.le]

/-- The full absolute mass of a finite ordinary-prime correction
has a square-root cutoff bound with one logarithmic factor. -/
theorem sum_primeKernel_norm_le (p : Polynomial ℂ) (N X : ℕ) (T : Finset ℕ)
    (hT : ∀ a ∈ T, a.Prime ∧ a ≤ X) (y : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑ a ∈ T, Real.log a * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) a‖) ≤
      2 * Real.sqrt X * Real.log X * r⁻¹ ^ N *
        ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ a ∈ T, (Real.log X * B) * zetaPrimeExpWeight (3 / 2 - r) a := by
      apply Finset.sum_le_sum
      intro a ha
      have hk : ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) a‖ ≤
          r⁻¹ ^ N * zetaPrimeExpWeight (3 / 2 - r) a *
            ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
        simpa only [show (3 / 2 + I * (y : ℂ)).re = 3 / 2 by simp, zetaPrimeExpWeight] using
          norm_zetaPrimeFilterKernel_le_tilt p N (3 / 2 + I * y)
            (show (1 : ℝ) ≤ a by exact_mod_cast (hT a ha).1.pos) hr
      have hl : Real.log a ≤ Real.log X := Real.log_le_log
        (by exact_mod_cast (hT a ha).1.pos) (by exact_mod_cast (hT a ha).2)
      calc
        _ ≤ Real.log X * (r⁻¹ ^ N * zetaPrimeExpWeight (3 / 2 - r) a *
            ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := mul_le_mul hl hk (norm_nonneg _)
          (Real.log_natCast_nonneg X)
        _ = _ := by dsimp [B]; ring
    _ = (Real.log X * B) * ∑ a ∈ T, zetaPrimeExpWeight (3 / 2 - r) a :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (Real.log X * B) * (2 * Real.sqrt X) := mul_le_mul_of_nonneg_left
      (sum_expWeight_le_sqrt T X hT (by linarith))
      (mul_nonneg (Real.log_natCast_nonneg X) hB)
    _ = _ := by dsimp [B]; ring

/-- The total variation of the marked complex responses has only a
square-root cost in the new prime cutoff. The original small-prime sieve
and all repeated marks remain explicit. -/
theorem exists_sum_norm_fibre_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R X : ℕ) (S T : Finset ℕ),
      1 ≤ D → (∀ b ∈ S, b.Prime ∧ b ≤ R) →
      (∀ a ∈ T, a.Prime ∧ a ≤ X ∧ a ∉ S) →
      (∑ a ∈ T, ‖fibre p D S N (3 / 2 + I * y) a‖) ≤
        C * D * Real.exp (4 * Real.sqrt R) * Real.sqrt X * (1 + Real.log X) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_fibre_bound y hy hr hr1
  refine ⟨4 * C + 2, by positivity, ?_⟩
  intro p D N R X S T hD hS hT
  let E : ℝ := D * Real.exp (4 * Real.sqrt R)
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
    (Real.one_le_exp_iff.mpr (by positivity))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT' : ∀ a ∈ T, a.Prime ∧ a ≤ X := fun a ha ↦ ⟨(hT a ha).1, (hT a ha).2.1⟩
  have hsum := Finset.sum_le_sum (fun a ha ↦
    hb p D N R S a hD hS (hT a ha).1 (hT a ha).2.2)
  calc
    _ ≤ (C * E * B) * ∑ a ∈ T, primeSquareCorrectedWeight (zetaSquareSieveExponent r) a +
        ∑ a ∈ T, Real.log a * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) a‖ := by
      apply hsum.trans_eq
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      dsimp only [E, B]
      ring
    _ ≤ (C * E * B) * (4 * Real.sqrt X) +
        2 * Real.sqrt X * Real.log X * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := add_le_add
      (mul_le_mul_of_nonneg_left
        (sum_correctedWeight_le_sqrt T X hT' (zetaSquareSieveExponent_gt_half hr1))
        (by positivity)) (sum_primeKernel_norm_le p N X T hT' y hr hr1)
    _ = (4 * C * E + 2 * Real.log X) * Real.sqrt X * B := by dsimp [B]; ring
    _ ≤ ((4 * C + 2) * E * (1 + Real.log X)) * Real.sqrt X * B := by
      have hl := Real.log_natCast_nonneg X
      have hLE : Real.log X ≤ E * Real.log X := by nlinarith
      have hCE : 0 ≤ C * E := mul_nonneg hC.le (by linarith)
      have hstep : 4 * C * E + 2 * Real.log X ≤ (4 * C + 2) * E * (1 + Real.log X) := by
        nlinarith [mul_nonneg hCE hl]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg X)) hB
    _ = _ := by dsimp [E, B]; ring

/-- A radius strictly above the eighth-root growth cost of all
marked primes through the fourth power of the original divisor cutoff. -/
def radius (rho : NontrivialZetaZero) : ℝ :=
  (1 + zetaMoebiusCubicRate (3 / 2 - rho.1.re)) / 2

/-- The selected radius remains inside the square-summable analytic
domain and strictly exceeds the full incidence growth cost. -/
theorem radius_bounds (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    0 < radius rho ∧ radius rho < 1 ∧ zetaMoebiusCubicRate (3 / 2 - rho.1.re) < radius rho := by
  have h0 := zetaMoebiusCubicRate_pos (u := 3 / 2 - rho.1.re)
    (by linarith [NontrivialZetaZero.re_lt_one rho])
  have h1 := zetaMoebiusCubicRate_lt_one (u := 3 / 2 - rho.1.re) (by linarith)
  unfold radius
  constructor
  · positivity
  · constructor <;> linarith

/-- The geometric base after source normalization and all marked
prime, square-overlap and finite-prime correction costs. -/
def rate (rho : NontrivialZetaZero) : ℝ :=
  zetaMoebiusCubicRate (3 / 2 - rho.1.re) / radius rho

/-- The entire incidence allowance has a strict geometric saving
for every hypothetical zero right of the critical line. -/
theorem rate_bounds (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    0 < rate rho ∧ rate rho < 1 := by
  obtain ⟨hr, _, hb⟩ := radius_bounds rho hrho
  exact ⟨div_pos (zetaMoebiusCubicRate_pos
    (by linarith [NontrivialZetaZero.re_lt_one rho])) hr, (div_lt_one hr).mpr hb⟩

/-- Keeping the exact factor four in the original quadratic sieve
cost saves a square root of the head-growth allowance. -/
theorem exp_sqrt_cutoff_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) ≤
      Real.sqrt (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) ^ N := by
  let c := zetaRightHalfPrimePatternSlope rho
  let q := zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)
  have hc : 0 < c := zetaRightHalfPrimePatternSlope_pos rho hrho
  have hq : 0 < q := (one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)).trans' zero_lt_one
  have hf : (⌊c * (N : ℝ)⌋₊ : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hs : Real.sqrt (zetaRightHalfPrimePatternCutoff rho N) = (⌊c * (N : ℝ)⌋₊ : ℝ) := by
    simp [zetaRightHalfPrimePatternCutoff, c]
  rw [hs]
  calc
    _ ≤ Real.exp (4 * (c * (N : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp ((N : ℝ) * Real.log (Real.sqrt q)) := by
      rw [Real.log_sqrt hq.le]
      congr 1
      dsimp [c, zetaRightHalfPrimePatternSlope, q]
      ring
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (Real.sqrt_pos.mpr hq)]

/-- The marked arithmetic response at the exact original cutoffs,
pole-isolating polynomial, ordinate, and source normalization. -/
def actualFibre (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N a : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    fibre (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) a

/-- All marked-prime responses through `D_N^4` have independently
vanishing total variation. The constant and bound are uniform over every
selected finite prime family at each moment order. -/
theorem exists_actual_sum_norm_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : Finset ℕ),
      (∀ a ∈ T, a.Prime ∧
        a ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
        a ∉ zetaRightHalfPrimePatternPrimes rho N) →
      (∑ a ∈ T, ‖actualFibre rho hrho N a‖) ≤ C * (1 + (N : ℝ)) * rate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := radius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq1 : 1 < q := one_lt_zetaMoebiusHeadGrowth hu hu1
  have hq : 0 < q := zero_lt_one.trans hq1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hrate : 0 ≤ rate rho := (rate_bounds rho hrho).1.le
  obtain ⟨hr, hr1, _⟩ := radius_bounds rho hrho
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_fibre_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + 4 * Real.log q) + 1, by positivity, ?_⟩
  intro N T hT
  let D := zetaMoebiusGeometricCutoff q N
  have hDpos : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have he := exp_sqrt_cutoff_bound rho hrho N
  have hsqrt : Real.sqrt ((D ^ 4 : ℕ) : ℝ) = (D : ℝ) ^ 2 := by
    rw [Nat.cast_pow, show (D : ℝ) ^ 4 = ((D : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg (D : ℝ))]
  have hlog : Real.log ((D ^ 4 : ℕ) : ℝ) ≤ 4 * (N : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow] at h
    norm_num
    linarith
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N) (D ^ 4)
    (zetaRightHalfPrimePatternPrimes rho N) T hDpos (zetaRightHalfPrimePatternPrimes_eligible rho N) hT
  have hnorm : ‖(3 / 2 - rho.1.re : ℝ)‖ = u := Real.norm_of_nonneg hu.le
  simp only [actualFibre, norm_mul, norm_pow, Complex.norm_real, hnorm]
  rw [← Finset.mul_sum]
  calc
    _ ≤ u ^ (N + 1) * (C * D * Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) *
        Real.sqrt ((D ^ 4 : ℕ) : ℝ) * (1 + Real.log ((D ^ 4 : ℕ) : ℝ)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * (Real.sqrt q) ^ N * (q ^ N) ^ 2 *
        (1 + 4 * (N : ℝ) * Real.log q) * r⁻¹ ^ N * B) := by
      rw [hsqrt]
      gcongr
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) *
        ((u * Real.sqrt q * q ^ 3) / r) ^ N := by
      rw [div_pow, mul_pow, mul_pow, pow_succ,
        show (q ^ 3) ^ N = (q ^ N) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) * rate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
      rfl
    _ ≤ (C * u * B) * ((1 + 4 * Real.log q) * (1 + (N : ℝ))) * rate rho ^ N := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ _ := by
      have h0 : 0 ≤ (1 + (N : ℝ)) * rate rho ^ N := by positivity
      calc
        _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * rate rho ^ N) := by ring
        _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * rate rho ^ N) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
        _ = _ := by ring

/-- The uniform total-variation allowance tends to zero, including
its linear factor in the moment order. -/
theorem tendsto_allowance (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + (N : ℝ)) * rate rho ^ N) atTop (𝓝 0) := by
  obtain ⟨h0, h1⟩ := rate_bounds rho hrho
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  have hn := tendsto_self_mul_const_pow_of_lt_one h0.le h1
  convert (hp.add hn).const_mul C using 1
  · funext N
    ring
  · simp

/-- Every moving eligible prime family has vanishing total variation
of its source-normalized marked arithmetic responses. -/
theorem tendsto_actual_sum_norm (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ)
    (hT : ∀ᶠ N in atTop, ∀ a ∈ T N, a.Prime ∧
      a ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      a ∉ zetaRightHalfPrimePatternPrimes rho N) :
    Tendsto (fun N ↦ ∑ a ∈ T N, ‖actualFibre rho hrho N a‖) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actual_sum_norm_bound rho hrho
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ Finset.sum_nonneg (fun a _ ↦ norm_nonneg _)))
    (hT.mono (fun N h ↦ hb N (T N) h)) (tendsto_allowance rho hrho C)

/-- Arbitrary moving complex prime weights of norm at most one have
vanishing response, uniformly over the entire enlarged prime range. -/
theorem tendsto_actual_weighted_fibres (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hT : ∀ᶠ N in atTop, ∀ a ∈ T N, a.Prime ∧
      a ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      a ∉ zetaRightHalfPrimePatternPrimes rho N)
    (hw : ∀ᶠ N in atTop, ∀ a ∈ T N, ‖w N a‖ ≤ 1) :
    Tendsto (fun N ↦ ∑ a ∈ T N, w N a * actualFibre rho hrho N a) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_actual_sum_norm rho hrho T hT)
  filter_upwards [hw] with N hN
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun a ha ↦ by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hN a ha) (norm_nonneg _))

/-- The all-family decay theorem is about the literal incidence-
weighted rough squarefree series, with its original divisor cutoff,
complex phase and every prime overlap retained. -/
theorem tendsto_actual_incidence (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hT : ∀ᶠ N in atTop, ∀ a ∈ T N, a.Prime ∧
      a ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      a ∉ zetaRightHalfPrimePatternPrimes rho N)
    (hw : ∀ᶠ N in atTop, ∀ a ∈ T N, ‖w N a‖ ≤ 1) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      weight (T N) (w N) n *
        zetaRoughSquarefreeCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_actual_weighted_fibres rho hrho T w hT hw).congr'
  filter_upwards [] with N
  rw [(hasSum_weight _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (T N) (w N)
      (by norm_num)).tsum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ ↦ by unfold actualFibre; ring)

end
end RiemannGaussian.RoughPrimeIncidence
