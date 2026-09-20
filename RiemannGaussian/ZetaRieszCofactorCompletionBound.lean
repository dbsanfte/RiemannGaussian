/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHarmonicWindow
import RiemannGaussian.ZetaSquarefreeEulerQuadraticSieveDecay
import RiemannGaussian.ZetaSquarefreeRieszCompletion
import RiemannGaussian.NatDivisorSquareDirichlet
import RiemannGaussian.ZetaPrimeClearedHeat

/-!
# Completing the joint wing while retaining cofactor size

A radius-three-quarters Euler estimate keeps the divisor mark decay.
It pays every shifted Riesz cutoff in the complete coprime squarefree
series, uniformly in the distinguished prime and moment order.
The original unpaid orders and physical prime family have geometric
source-scale decay after this completion. Its arithmetic corrections
are proved and retained in the subsequent modules.
-/

namespace RiemannGaussian.ZetaRieszJointCofactor
noncomputable section
open Complex Filter Topology
open scoped Classical BigOperators ArithmeticFunction.Moebius

private theorem local_weight_le {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    {p : ℕ} (hp : p.Prime) :
    zetaPrimeExpWeight σ p ≤ 1 / Real.sqrt p := by
  simpa only [norm_zetaPrimeFeature, Complex.ofReal_re, zetaPrimeExpWeight] using
    (norm_zetaPrimeFeature_le_inv_sqrt (s := (σ : ℂ)) hσ hp.pos)

private theorem inverse_le_four {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    {p : ℕ} (hp : p.Prime) :
    0 ≤ (1 - zetaPrimeExpWeight σ p)⁻¹ ∧
      (1 - zetaPrimeExpWeight σ p)⁻¹ ≤ 4 := by
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt p := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)).mpr
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hsp : 0 < Real.sqrt (p : ℝ) := by linarith
  have hw : zetaPrimeExpWeight σ p ≤ 3 / 4 :=
    (local_weight_le hσ hp).trans ((div_le_iff₀ hsp).mpr (by linarith))
  have hd : 0 < 1 - zetaPrimeExpWeight σ p := by linarith
  refine ⟨(inv_pos.mpr hd).le, ?_⟩
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hd).mpr (by linarith)

private theorem inverse_le_two {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) :
    (1 - zetaPrimeExpWeight σ p)⁻¹ ≤ 2 := by
  have hs : (2 : ℝ) ≤ Real.sqrt p := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)).mpr
    exact_mod_cast hp4
  have hsp : 0 < Real.sqrt (p : ℝ) := by linarith
  have hw : zetaPrimeExpWeight σ p ≤ 1 / 2 :=
    (local_weight_le hσ hp).trans ((div_le_iff₀ hsp).mpr (by linarith))
  have hd : 0 < 1 - zetaPrimeExpWeight σ p := by linarith
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hd).mpr (by linarith)

/-- Every reciprocal local factor keeps at most one divisor-count cost, uniformly on
real edges at least one half. -/
theorem inverse_product_bound {σ : ℝ} (hσ : 1 / 2 ≤ σ) (P : ℕ) :
    (∏ a ∈ P.primeFactors, (1 - zetaPrimeExpWeight σ a)⁻¹) ≤
      16 * (2 : ℝ) ^ P.primeFactors.card := by
  have hc : (P.primeFactors.filter (fun a => a < 4)).card ≤ 4 := by
    apply le_trans (Finset.card_le_card (t := Finset.range 4) ?_) (by simp)
    intro a ha
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  calc
    _ ≤ ∏ a ∈ P.primeFactors, (2 : ℝ) * (if a < 4 then 2 else 1) := by
      apply Finset.prod_le_prod
        (fun a ha => (inverse_le_four hσ (Nat.prime_of_mem_primeFactors ha)).1)
      intro a ha
      split_ifs with h
      · norm_num only [show (2 : ℝ) * 2 = 4 by norm_num]
        exact (inverse_le_four hσ (Nat.prime_of_mem_primeFactors ha)).2
      · simpa using inverse_le_two hσ (Nat.prime_of_mem_primeFactors ha) (by omega)
    _ = (2 : ℝ) ^ P.primeFactors.card *
        2 ^ (P.primeFactors.filter (fun a => a < 4)).card := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite]
      simp
    _ ≤ (2 : ℝ) ^ P.primeFactors.card * 2 ^ 4 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (by positivity)
    _ = _ := by ring

-- Retains the mark-size decay lost by the older uniform-mark estimate.
/-- Excluding one prime retains the mark-size decay and a single divisor count,
uniformly in both the prime and squarefree mark. -/
theorem singleton_budget_bound {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    {p d : ℕ} (hp : p.Prime) (hd : Squarefree d) (hpd : ¬p ∣ d) :
    squarefreeEulerBudget σ {p} d ≤
      64 * (d.divisors.card : ℝ) * zetaPrimeExpWeight σ d := by
  have hdis : Disjoint ({p} : Finset ℕ) d.primeFactors := by
    simp only [Finset.disjoint_singleton_left]
    exact fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  rw [squarefreeEulerBudget, Finset.prod_union hdis, Finset.prod_singleton]
  have h := mul_le_mul (inverse_le_four hσ hp).2 (inverse_product_bound hσ d)
    (Finset.prod_nonneg (fun a ha =>
      (inverse_le_four hσ (Nat.prime_of_mem_primeFactors ha)).1)) (by norm_num : (0 : ℝ) ≤ 4)
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ zetaPrimeExpWeight σ d from (Real.exp_pos _).le)
  rw [RoughCoprimeFactor.card_divisors_eq hd]
  nlinarith [hmul]


-- A complete prefix is paid at exponent 13/50 rather than at exponent 1.
/-- The entire growing marked Riesz prefix costs at most a constant times T
exp(13T/50). The constant is a proved convergent divisor-square series. -/
theorem weighted_mark_sum_bound {T : ℝ} (hT : 0 ≤ T)
    (D : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hD : ∀ d ∈ D, Squarefree d ∧ ¬p ∣ d) :
    (∑ d ∈ D, max 0 (T - Real.log d) * squarefreeEulerBudget (3 / 4) {p} d) ≤
      64 * T * Real.exp ((13 / 50 : ℝ) * T) * divisorSquareDirichletMass (101 / 100) := by
  have hterm (d : ℕ) (hd : d ∈ D) :
      max 0 (T - Real.log d) * squarefreeEulerBudget (3 / 4) {p} d ≤
        (64 * T * Real.exp ((13 / 50 : ℝ) * T)) *
          ((d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-(101 / 100 : ℝ))) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (hD d hd).1.ne_zero
    have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
    by_cases hdt : Real.log (d : ℝ) ≤ T
    · rw [max_eq_right (sub_nonneg.mpr hdt)]
      have hb := singleton_budget_bound (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
        hp (hD d hd).1 (hD d hd).2
      have hcard : (d.divisors.card : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by
        have hpos : 1 ≤ d.divisors.card := Finset.one_le_card.mpr
          ⟨1, Nat.one_mem_divisors.mpr (hD d hd).1.ne_zero⟩
        have hpos' : (1 : ℝ) ≤ d.divisors.card := by exact_mod_cast hpos
        nlinarith
      have he : zetaPrimeExpWeight (3 / 4) d ≤
          Real.exp ((13 / 50 : ℝ) * T) * (d : ℝ) ^ (-(101 / 100 : ℝ)) := by
        rw [zetaPrimeExpWeight, Real.rpow_def_of_pos hd0, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      calc
        _ ≤ T * (64 * (d.divisors.card : ℝ) * zetaPrimeExpWeight (3 / 4) d) :=
          mul_le_mul (by linarith) hb
            ((norm_nonneg (squarefreeEulerMultiplier {p} d (3 / 4))).trans
              (norm_squarefreeEulerMultiplier_le {p} (by simpa) d (by norm_num) (by norm_num)))
            hT
        _ ≤ T * (64 * (d.divisors.card : ℝ) ^ 2 *
            (Real.exp ((13 / 50 : ℝ) * T) * (d : ℝ) ^ (-(101 / 100 : ℝ)))) := by
          gcongr
          exact (Real.exp_pos _).le
        _ = _ := by ring
    · rw [max_eq_left (by linarith), zero_mul]
      positivity
  calc
    _ ≤ ∑ d ∈ D, (64 * T * Real.exp ((13 / 50 : ℝ) * T)) *
        ((d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-(101 / 100 : ℝ))) :=
      Finset.sum_le_sum hterm
    _ = (64 * T * Real.exp ((13 / 50 : ℝ) * T)) *
        ∑ d ∈ D, (d.divisors.card : ℝ) ^ 2 * (d : ℝ) ^ (-(101 / 100 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_card_divisors_sq_mul_rpow_neg (by norm_num : (1 : ℝ) < 101 / 100)).sum_le_tsum D
        (fun d _ => by positivity)) (by positivity)


/-- The complete squarefree Riesz coefficient with the distinguished prime excluded.
The unit and prime terms are included. -/
def cofactorCoefficient (p : ℕ) (T : ℝ) (n : ℕ) : ℂ :=
  if Squarefree n ∧ ¬p ∣ n then (VaughanLogAverage.riesz T n : ℂ) else 0

/-- The actual coprime cofactor coefficient is an exact finite sum of Euler marks at
one common physical cutoff. -/
theorem cofactorCoefficient_eq_marks (p : ℕ) (T : ℝ) {D : ℕ}
    (hD : T ≤ Real.log (D + 1 : ℕ)) (n : ℕ) :
    cofactorCoefficient p T n =
      ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ ¬p ∣ d),
        (((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ) *
          RoughSquarefreeBare.coefficient {p} d n := by
  rw [Finset.sum_filter]
  by_cases hn : Squarefree n ∧ ¬p ∣ n
  · rw [cofactorCoefficient, if_pos hn,
      ZetaSquarefreeRieszCompletion.riesz_eq_finite_divisor_cutoff T hD hn.1.ne_zero,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ n
    · have hsd := hn.1.squarefree_of_dvd hd
      have hpd : ¬p ∣ d := fun h => hn.2 (h.trans hd)
      simp [RoughSquarefreeBare.coefficient, hn.1, hn.2, hd, hsd, hpd]
    · simp [RoughSquarefreeBare.coefficient, hd]
  · simp [cofactorCoefficient, RoughSquarefreeBare.coefficient, ← and_assoc, hn]

/-- The complete complex factorial moment of the coprime squarefree Riesz
coefficients. -/
def cofactorResponse (p : ℕ) (T : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n, cofactorCoefficient p T n * zetaPrimeFilterKernel 1 k s n

/-- The cofactor series converges genuinely in the Euler half-plane and equals the
exact finite marked response. -/
theorem hasSum_cofactorResponse {p : ℕ} (hp : p.Prime) (T : ℝ) {D : ℕ}
    (hD : T ≤ Real.log (D + 1 : ℕ)) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => cofactorCoefficient p T n * zetaPrimeFilterKernel 1 k s n)
      (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ ¬p ∣ d),
        (((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ) *
          RoughSquarefreeBare.response 1 {p} d k s) := by
  have h := hasSum_sum
    (s := (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ ¬p ∣ d)) (fun d hd =>
      ((hasSum_markedSquarefreeEuler_filter {p} (by simpa)
        (Finset.mem_filter.mp hd).2.1 (by
          intro a ha ham
          have hap : a = p := Finset.mem_singleton.mp ham
          exact (Finset.mem_filter.mp hd).2.2 (hap ▸ Nat.dvd_of_mem_primeFactors ha))
        1 k hs).summable.hasSum).mul_left
          ((((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ)))
  apply h.congr_fun
  intro n
  rw [cofactorCoefficient_eq_marks p T hD n, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun d _ => by ring)

-- One constant for all distinguished primes, all nonnegative shifted
-- cutoffs and all orders. This is a complete arithmetic cofactor sum.
/-- A fixed eligible height supplies one constant for all primes, cutoffs and
orders. Mark-size decay pays the entire growing prefix. -/
theorem exists_cofactor_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ), p.Prime → ∀ (T : ℝ), 0 ≤ T → ∀ k : ℕ,
      ‖cofactorResponse p T k (3 / 2 + I * y)‖ ≤
        C * T * Real.exp ((13 / 50 : ℝ) * T) * (4 / 3 : ℝ) ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_squarefreeEuler_variable_radius_bound y hy
  let B := divisorSquareDirichletMass (101 / 100)
  have hB : 0 ≤ B := divisorSquareDirichletMass_nonneg _
  refine ⟨64 * C * (B + 1), by positivity, ?_⟩
  intro p hp T hT k
  let D := ⌈Real.exp T⌉₊
  let A := (Finset.Icc 1 D).filter (fun d => Squarefree d ∧ ¬p ∣ d)
  have hD : T ≤ Real.log (D + 1 : ℕ) := by
    have h := Nat.le_ceil (Real.exp T)
    have hcast : Real.exp T ≤ (D + 1 : ℕ) := by dsimp [D]; push_cast; linarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos T) hcast
  have he := (hasSum_cofactorResponse hp T hD k (by norm_num :
    (1 : ℝ) < (3 / 2 + I * (y : ℂ)).re)).tsum_eq
  change cofactorResponse p T k (3 / 2 + I * y) = _ at he
  rw [he]
  have hterm (d : ℕ) (hd : d ∈ A) :
      ‖((((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ) *
        RoughSquarefreeBare.response 1 {p} d k (3 / 2 + I * y))‖ ≤
          (C * (4 / 3 : ℝ) ^ k) *
            (max 0 (T - Real.log d) * squarefreeEulerBudget (3 / 4) {p} d) := by
    have hvalid := (Finset.mem_filter.mp hd).2
    have hbound := hb (3 / 4) (by norm_num)
      (by linarith [(squarefreeEulerRadius_bounds hy).1]) {p} (by simpa) d hvalid.1
      (by intro a ha ham; exact hvalid.2 ((Finset.mem_singleton.mp ham) ▸ Nat.dvd_of_mem_primeFactors ha))
      1 k
    have hsupp : (1 : Polynomial ℂ).support = {0} := by
      simpa using (Polynomial.support_C (one_ne_zero : (1 : ℂ) ≠ 0))
    norm_num [hsupp] at hbound
    have hw : ‖(((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ)‖ ≤
        max 0 (T - Real.log d) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (le_max_left 0 (T - Real.log d))]
      have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      simpa using mul_le_mul_of_nonneg_right hm (le_max_left 0 _)
    rw [norm_mul]
    exact (mul_le_mul hw hbound (norm_nonneg _) (le_max_left 0 _)).trans_eq (by ring)
  calc
    _ ≤ ∑ d ∈ A, ‖((((μ d : ℝ) * max 0 (T - Real.log d) : ℝ) : ℂ) *
        RoughSquarefreeBare.response 1 {p} d k (3 / 2 + I * y))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ A, (C * (4 / 3 : ℝ) ^ k) *
        (max 0 (T - Real.log d) * squarefreeEulerBudget (3 / 4) {p} d) :=
      Finset.sum_le_sum hterm
    _ = (C * (4 / 3 : ℝ) ^ k) * ∑ d ∈ A,
        max 0 (T - Real.log d) * squarefreeEulerBudget (3 / 4) {p} d := by rw [Finset.mul_sum]
    _ ≤ (C * (4 / 3 : ℝ) ^ k) *
        (64 * T * Real.exp ((13 / 50 : ℝ) * T) * B) :=
      mul_le_mul_of_nonneg_left (weighted_mark_sum_bound hT A hp
        (fun d hd => (Finset.mem_filter.mp hd).2)) (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (show B ≤ B + 1 by linarith)
        (show 0 ≤ 64 * C * T * Real.exp ((13 / 50 : ℝ) * T) * (4 / 3 : ℝ) ^ k by positivity)
      nlinarith only [h]


/-- A finite distinguished-prime family coupled to every coprime squarefree cofactor
at the shifted cutoff. -/
def jointBlock (A : Finset ℕ) (L y : ℝ) (k l : ℕ) : ℂ :=
  ∑ p ∈ A, zetaPrimeLogKernel l (3 / 2 + I * y) p *
    cofactorResponse p (L - Real.log p) k (3 / 2 + I * y)

/-- The complete joint block has a common norm bound for all physical prime
selections and complementary orders at a fixed eligible height. -/
theorem exists_jointBlock_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ) (L : ℝ), 0 ≤ L →
      (∀ p ∈ A, p.Prime ∧ Real.log p ≤ L) → ∀ k l : ℕ,
        ‖jointBlock A L y k l‖ ≤
          C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l) := by
  obtain ⟨C, hC, hb⟩ := exists_cofactor_bound y hy
  let Z := ∑' n, zetaPrimeExpWeight (101 / 100) n
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨C * (Z + 1), by positivity, ?_⟩
  intro A L hL hA k l
  have ht (p : ℕ) (hp : p ∈ A) :
      ‖zetaPrimeLogKernel l (3 / 2 + I * y) p *
        cofactorResponse p (L - Real.log p) k (3 / 2 + I * y)‖ ≤
          (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l)) *
            zetaPrimeExpWeight (101 / 100) p := by
    have hpL := (hA p hp).2
    have hlog := Real.log_natCast_nonneg p
    have hc := hb p (hA p hp).1 (L - Real.log p) (sub_nonneg.mpr hpL) k
    have hk := norm_zetaPrimeLogKernel_le l (3 / 2 + I * (y : ℂ)) p
      (q := 3 / 4) (by norm_num)
    norm_num at hk
    have hk' : ‖zetaPrimeLogKernel l (3 / 2 + I * y) p‖ ≤
        (4 / 3 : ℝ) ^ l * zetaPrimeExpWeight (3 / 4) p := hk
    have hw0 : 0 ≤ zetaPrimeExpWeight (3 / 4) p := (Real.exp_pos _).le
    rw [norm_mul]
    calc
      _ ≤ ((4 / 3 : ℝ) ^ l * zetaPrimeExpWeight (3 / 4) p) *
          (C * (L - Real.log p) * Real.exp ((13 / 50 : ℝ) * (L - Real.log p)) * (4 / 3 : ℝ) ^ k) :=
        mul_le_mul hk' hc (norm_nonneg _) (by positivity)
      _ ≤ ((4 / 3 : ℝ) ^ l * zetaPrimeExpWeight (3 / 4) p) *
          (C * L * Real.exp ((13 / 50 : ℝ) * (L - Real.log p)) * (4 / 3 : ℝ) ^ k) := by
        have hw : 0 ≤ zetaPrimeExpWeight (3 / 4) p := (Real.exp_pos _).le
        gcongr
        linarith
      _ = _ := by
        have hex : zetaPrimeExpWeight (3 / 4) p *
            Real.exp ((13 / 50 : ℝ) * (L - Real.log p)) =
              Real.exp ((13 / 50 : ℝ) * L) * zetaPrimeExpWeight (101 / 100) p := by
          unfold zetaPrimeExpWeight
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [pow_add]
        linear_combination (C * L * (4 / 3 : ℝ) ^ l * (4 / 3 : ℝ) ^ k) * hex
  calc
    _ ≤ ∑ p ∈ A, ‖zetaPrimeLogKernel l (3 / 2 + I * y) p *
        cofactorResponse p (L - Real.log p) k (3 / 2 + I * y)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ A,
        (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l)) *
          zetaPrimeExpWeight (101 / 100) p := Finset.sum_le_sum ht
    _ = (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l)) *
        ∑ p ∈ A, zetaPrimeExpWeight (101 / 100) p := by rw [Finset.mul_sum]
    _ ≤ (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l)) * Z :=
      mul_le_mul_of_nonneg_left
        ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 101 / 100)).sum_le_tsum A
          (fun _ _ => (Real.exp_pos _).le)) (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (show Z ≤ Z + 1 by linarith)
        (show 0 ≤ C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (k + l) by positivity)
      nlinarith only [h]

/-- The restored cofactor allowance decays at source scale throughout the original
harmonic radius interval. -/
theorem joint_source_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) (N : ℕ)
    (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ N * (4 / 3 : ℝ) ^ N * Real.exp ((13 / 50 : ℝ) * L) ≤
      Real.exp (-(N : ℝ) / 64) := by
  have hlu : Real.log u ≤ -(2 / 3 : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hu huh
  have hlog : Real.log (4 / 3 : ℝ) ≤ 36 / 125 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  have hpow (x : ℝ) (hx : 0 < x) : x ^ N = Real.exp ((N : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow u hu, hpow (4 / 3) (by norm_num), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) N)
  have h2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]


-- This completion retains the actual physical primes and unpaid wing
-- orders, but contains all squarefree coprime cofactors. Transferring
-- the carrier's other masks still requires their explicit corrections.
/-- The completion uses the original unpaid orders and intermediate primes, but all
squarefree coprime cofactors. Its corrections remain explicit below. -/
def completedWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      jointBlock (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k)

/-- The normalized completed wing is bounded by C(N+1)^2 exp(-(N+1)/64), with one
constant across the radius interval at a fixed eligible height. -/
theorem exists_completedWing_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ), 1 / 2 ≤ u → u ≤ Real.exp (-(2 / 3 : ℝ)) →
      ∀ (N : ℕ), 2 ≤ N →
        ‖(u : ℂ) ^ (N + 1) * completedWing u y N‖ ≤
          C * (N + 1 : ℝ) ^ 2 * Real.exp (-(N + 1 : ℝ) / 64) := by
  obtain ⟨C, hC, hb⟩ := exists_jointBlock_bound y hy
  refine ⟨2 * C, by positivity, ?_⟩
  intro u hu huh N hN
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszWingHighOrders.unpaidOrders N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hu0 : 0 < u := by linarith
  have hA : ∀ p ∈ A, p.Prime ∧ Real.log p ≤ L := by
    intro p hp
    obtain ⟨hprime, _, hpX⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp
    exact ⟨hprime, (Real.log_lt_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hpX)).le⟩
  have hkM (k : ℕ) (hk : k ∈ S) : k ≤ N + 1 :=
    (ZetaRieszReflectedCompletion.lowerWing_bounds
      (ZetaRieszWingHighOrders.unpaidOrders_support hk).1).2.2
  have hcard : (S.card : ℝ) ≤ 2 * (N + 1 : ℝ) := by
    have hs : S ⊆ Finset.range (N + 2) := by
      intro k hk
      exact Finset.mem_range.mpr (by have := hkM k hk; omega)
    have hc' : S.card ≤ N + 2 := by simpa using Finset.card_le_card hs
    have hc : (S.card : ℝ) ≤ N + 2 := by exact_mod_cast hc'
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hLL : L ≤ (139 / 100 : ℝ) * (N + 1) := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hl : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    have h' := h.trans (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg (α := ℝ) N))
    dsimp only [L]
    linarith
  have hrate := joint_source_scalar hu0 huh (N + 1) (by exact_mod_cast hLL)
  norm_num only [Nat.cast_add, Nat.cast_one] at hrate
  have hbound : ‖∑ k ∈ S, jointBlock A L y k (N + 1 - k)‖ ≤
      (S.card : ℝ) * (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (N + 1)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ S, C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (N + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.add_sub_of_le (hkM k hk)] using hb A L hL.le hA k (N + 1 - k)
      _ = _ := by simp
  change ‖(u : ℂ) ^ (N + 1) *
    (((N + 1 : ℕ) : ℂ) / (L : ℂ) * ∑ k ∈ S, jointBlock A L y k (N + 1 - k))‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_natCast,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hu0.le,
    Real.norm_of_nonneg hL.le]
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ u ^ (N + 1) * (((N + 1 : ℝ) / L) *
        ((S.card : ℝ) * (C * L * Real.exp ((13 / 50 : ℝ) * L) * (4 / 3 : ℝ) ^ (N + 1)))) := by
      gcongr
    _ = C * (N + 1 : ℝ) * S.card *
        (u ^ (N + 1) * (4 / 3 : ℝ) ^ (N + 1) * Real.exp ((13 / 50 : ℝ) * L)) := by
      field_simp
    _ ≤ C * (N + 1 : ℝ) * (2 * (N + 1 : ℝ)) * Real.exp (-(N + 1 : ℝ) / 64) := by
      gcongr
    _ = _ := by ring


/-- The whole completed wing vanishes independently of hypothetical zeros on the
original harmonic radius interval. -/
theorem tendsto_completedWing (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u ≤ Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * completedWing u y N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_completedWing_bound y hy
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1 / 64 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 64 : ℝ) < 0))).const_mul C
  simp only [mul_zero] at h
  apply squeeze_zero_norm' (a := fun N : ℕ => C * ((N + 1 : ℝ) ^ 2 *
    Real.exp (-(1 / 64 : ℝ)) ^ N)) _ h
  filter_upwards [eventually_ge_atTop 2] with N hN
  apply (hb u hu huh N hN).trans
  have he : Real.exp (-(N + 1 : ℝ) / 64) ≤ Real.exp (-(1 / 64 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ C * (N + 1 : ℝ) ^ 2 by positivity)]

end
end RiemannGaussian.ZetaRieszJointCofactor
