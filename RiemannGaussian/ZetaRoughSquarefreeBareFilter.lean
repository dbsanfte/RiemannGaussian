/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughDivisorIncidence

/-!
# Removing a logarithm without losing the squarefree arithmetic phase

Dividing each polynomial coefficient by its shifted moment order removes
one logarithm exactly. The cutoff-one squarefree prefix therefore controls
the bare squarefree series, including every selected divisibility mark.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughSquarefreeBare
noncomputable section

/-- The exact coefficient division needed to remove one logarithm
while lowering the factorial moment order by one. -/
def dividedPolynomial (p : Polynomial ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ p.support, Polynomial.monomial k (p.coeff k / (N + k + 1 : ℕ))

/-- Coefficient division retains every original complex phase. -/
theorem dividedPolynomial_coeff (p : Polynomial ℂ) (N k : ℕ) :
    (dividedPolynomial p N).coeff k = p.coeff k / (N + k + 1 : ℕ) := by
  classical
  simp only [dividedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [hbk]
  · intro hk
    simp [Polynomial.notMem_support_iff.mp hk]

/-- The shifted positive denominators neither add nor remove support. -/
theorem dividedPolynomial_support (p : Polynomial ℂ) (N : ℕ) :
    (dividedPolynomial p N).support = p.support := by
  ext k
  simp only [Polynomial.mem_support_iff, dividedPolynomial_coeff, ne_eq, div_eq_zero_iff]
  have h : ((N + k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show N + k + 1 ≠ 0 by omega)
  simp only [h, or_false]

/-- Multiplication by the literal logarithm restores the original
kernel exactly, with no estimate or phase projection. -/
theorem log_mul_kernel (p : Polynomial ℂ) (N : ℕ) (s : ℂ) (x : ℝ) :
    (Real.log x : ℂ) * zetaPrimeFilterKernel (dividedPolynomial p N) N s x =
      zetaPrimeFilterKernel p (N + 1) s x := by
  unfold zetaPrimeFilterKernel zetaFactorialPolynomial Polynomial.sum
  rw [dividedPolynomial_support, ← mul_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rw [dividedPolynomial_coeff, show N + 1 + k = N + k + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, pow_succ]
  ring

/-- Removing one logarithm never enlarges the coefficient envelope. -/
theorem dividedPolynomial_envelope_le (p : Polynomial ℂ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ k ∈ (dividedPolynomial p N).support,
      ‖(dividedPolynomial p N).coeff k‖ * r ^ k) ≤
        ∑ k ∈ p.support, ‖p.coeff k‖ * r ^ k := by
  rw [dividedPolynomial_support]
  apply Finset.sum_le_sum
  intro k _
  rw [dividedPolynomial_coeff, norm_div, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr k)
  apply div_le_self (norm_nonneg _)
  exact_mod_cast (show 1 ≤ N + k + 1 by omega)

/-- The bare marked squarefree coefficient, with the complete
small-prime exclusion retained. Ordinary primes have not been removed. -/
def coefficient (S : Finset ℕ) (P n : ℕ) : ℂ :=
  if Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ P ∣ n then 1 else 0

/-- The complete arithmetic series for a bare marked squarefree kernel. -/
def response (p : Polynomial ℂ) (S : Finset ℕ) (P N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, coefficient S P n * zetaPrimeFilterKernel p N s n

private theorem bare_eq_prefix (p : Polynomial ℂ) (N : ℕ) (W : Finset ℕ)
    (s : ℂ) (n : ℕ) :
    (if Squarefree n ∧ (∏ a ∈ W, a) ∣ n then (1 : ℂ) else 0) *
        zetaPrimeFilterKernel p (N + 1) s n =
      -(zetaSquarefreeDivisibilityPrefixCoefficient 1 W n *
        zetaPrimeFilterKernel (dividedPolynomial p N) N s n) := by
  by_cases hsf : Squarefree n <;> by_cases hd : (∏ a ∈ W, a) ∣ n
  · simp only [hsf, hd, and_self, if_true, one_mul,
      zetaSquarefreeDivisibilityPrefixCoefficient]
    simp only [zetaDivisibilityPrefixCoefficient, Finset.Icc_self,
      Finset.sum_singleton, zetaMultipleLogCoefficient, one_dvd, hd, and_self,
      if_true, Nat.div_one, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, one_smul, Pi.neg_apply, neg_mul, neg_neg]
    exact (log_mul_kernel p N s n).symm
  all_goals simp [zetaSquarefreeDivisibilityPrefixCoefficient, hsf,
    zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, hd]

/-- Every roughness intersection is retained in the marked bare
coefficient, before the infinite arithmetic sum is taken. -/
theorem coefficient_eq_subsets (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {P : ℕ} (hP : Squarefree P) (n : ℕ) :
    coefficient S P n = ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
      (if Squarefree n ∧ (∏ a ∈ P.primeFactors ∪ W, a) ∣ n then 1 else 0) := by
  have he (W : Finset ℕ) (hW : W ∈ S.powerset) :
      (∏ a ∈ P.primeFactors ∪ W, a) ∣ n ↔ P ∣ n ∧ (∏ a ∈ W, a) ∣ n := by
    have hp : ∀ a ∈ P.primeFactors, a.Prime := fun _ ha ↦ Nat.prime_of_mem_primeFactors ha
    have hw : ∀ a ∈ W, a.Prime := fun a ha ↦ hS a (Finset.mem_powerset.mp hW ha)
    rw [prod_primes_dvd_iff _ (by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hp a ha
      · exact hw a ha)]
    simp only [Finset.forall_mem_union]
    rw [← prod_primes_dvd_iff _ hp, ← prod_primes_dvd_iff _ hw,
      Nat.prod_primeFactors_of_squarefree hP]
  have h := primeAvoidance_eq_signed_subsets S hS
    (fun m ↦ if Squarefree m ∧ P ∣ m then (1 : ℂ) else 0) n
  have ht : (∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
      (if Squarefree n ∧ (∏ a ∈ P.primeFactors ∪ W, a) ∣ n then 1 else 0)) =
      ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        (if (∏ a ∈ W, a) ∣ n then (if Squarefree n ∧ P ∣ n then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro W hW
    simp only [he W hW]
    by_cases hn : Squarefree n <;> by_cases hd : P ∣ n <;>
      by_cases hw : (∏ a ∈ W, a) ∣ n <;> simp [hn, hd, hw]
  rw [ht, h]
  by_cases hn : Squarefree n <;> by_cases hd : P ∣ n <;>
    by_cases hs : ∃ a ∈ S, a ∣ n <;> simp [coefficient, hn, hd, hs]

/-- The bare response is a genuine convergent series of the exact
lowered cutoff-one prefix, with all signed intersections preserved. -/
theorem hasSum_response (p : Polynomial ℂ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient S P n * zetaPrimeFilterKernel p (N + 1) s n)
      (∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        (-zetaSquarefreeDivisibilityPrefixFilter (dividedPolynomial p N) 1
          (P.primeFactors ∪ W) N s)) := by
  have h := hasSum_sum (s := S.powerset) (fun W hW ↦
    (summable_zetaSquarefreeDivisibilityPrefixFilter (dividedPolynomial p N) 1 N
      (P.primeFactors ∪ W) (by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Nat.prime_of_mem_primeFactors ha
        · exact hS a (Finset.mem_powerset.mp hW ha)) hs).hasSum.neg.mul_left ((-1 : ℂ) ^ W.card))
  apply h.congr_fun
  intro n
  rw [coefficient_eq_subsets S hS hP n, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro W _
  rw [mul_assoc, bare_eq_prefix]

/-- The complete marked bare arithmetic series is summable for every
natural mark, including the zero and nonsquarefree cases. -/
theorem summable_response (p : Polynomial ℂ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (P N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ coefficient S P n * zetaPrimeFilterKernel p (N + 1) s n) := by
  by_cases hP : Squarefree P
  · exact (hasSum_response p S hS hP N hs).summable
  · have hz (n : ℕ) : coefficient S P n = 0 := by
      have h : ¬(Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ P ∣ n) :=
        fun h ↦ hP (h.1.squarefree_of_dvd h.2.2)
      simp only [coefficient, if_neg h]
    simp [hz]

/-- Every marked bare response has an independent bound uniform in
the mark. The small-prime sieve and complete complex kernel remain present. -/
theorem exists_response_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N R : ℕ) (S : Finset ℕ) (P : ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖response p S P (N + 1) (3 / 2 + I * y)‖ ≤
        C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  let w := primeSquareCorrectedWeight τ
  refine ⟨4 * C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p N R S P hS
  have hnonneg : 0 ≤ (4 * C * Real.exp (2 * primeSquareWeightMass τ)) *
      Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
        (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by positivity
  by_cases hgood : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · obtain ⟨hP, hPS⟩ := hgood
    let A := C * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hw : ∀ a, 0 ≤ w a := primeSquareCorrectedWeight_nonneg τ
    have hmass : lcmSqrtFactorMass P ≤ 4 := by
      simpa using sqrt_mul_lcmSqrtFactorMass_le_four (D := 1)
        (Nat.pos_of_ne_zero hP.ne_zero) (by have := Nat.pos_of_ne_zero hP.ne_zero; omega)
    rw [response, (hasSum_response p S (fun a ha ↦ (hS a ha).1) hP N (by norm_num)).tsum_eq]
    calc
      _ ≤ ∑ W ∈ S.powerset, A * (4 * ∏ a ∈ W, w a) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro W hW
        have hdis : Disjoint P.primeFactors W := Finset.disjoint_left.mpr
          (fun a haP haW ↦ hPS a haP (Finset.mem_powerset.mp hW haW))
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_neg]
        have h := hb (dividedPolynomial p N) 1 N (P.primeFactors ∪ W) (by
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact Nat.prime_of_mem_primeFactors ha
          · exact (hS a (Finset.mem_powerset.mp hW ha)).1)
        simp only [Nat.cast_one, mul_one] at h
        rw [Finset.prod_union hdis] at h
        apply h.trans
        have he := dividedPolynomial_envelope_le p N (inv_nonneg.mpr hr.le)
        have hf := (RoughDivisorIncidence.prod_correctedWeight_le_lcmSqrtFactorMass hP
          (zetaSquareSieveExponent_gt_half hr1).le).trans hmass
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left he (by positivity))
          (mul_le_mul_of_nonneg_right hf (Finset.prod_nonneg (fun a _ ↦ hw a)))
          (mul_nonneg (Finset.prod_nonneg (fun a _ ↦ hw a))
            (Finset.prod_nonneg (fun a _ ↦ hw a))) hA
      _ = (A * 4) * ∏ a ∈ S, (1 + w a) := by
        rw [Finset.prod_one_add, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun W _ ↦ by ring)
      _ ≤ (A * 4) * ∏ a ∈ S, (1 + 2 * w a) := mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun a _ ↦ by linarith [hw a])
          (fun a _ ↦ by linarith [hw a])) (by positivity)
      _ ≤ (A * 4) * (Real.exp (2 * primeSquareWeightMass τ) * Real.exp (4 * Real.sqrt R)) :=
        mul_le_mul_of_nonneg_left
          (prod_one_add_primeSquareCorrectedWeight_le S R hS (zetaSquareSieveExponent_gt_half hr1))
          (by positivity)
      _ = _ := by dsimp [A]; ring
  · have hz (n : ℕ) : coefficient S P n = 0 := by
      have h : ¬(Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ P ∣ n) := by
        rintro ⟨hsf, hs, hd⟩
        apply hgood
        exact ⟨hsf.squarefree_of_dvd hd, fun a ha haS ↦
          hs ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hd⟩⟩
      simp only [coefficient, if_neg h]
    simpa [response, hz] using hnonneg

end
end RiemannGaussian.RoughSquarefreeBare
