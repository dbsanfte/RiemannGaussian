/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughMoebiusHyperbola
import RiemannGaussian.ZetaArithmeticQuadraticSmallProduct

/-!
# Independent small-prime logarithmic decay and a large-prime source

The squared Mobius mask keeps every ordered divisor intersection. Its
complete small-prime logarithmic part has an independent cubic-cost
bound and decays at the original zero-source normalization. Subtracting
that exact response leaves the large-prime logarithmic weight, which
vanishes on integers all of whose prime factors are at most D_N. Every
remaining coefficient has a prime and cofactor both beyond D_N.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughPrimeLog
noncomputable section
open RoughMoebiusIncidence

/-- The complete logarithm of the prime factors through the cutoff. -/
def smallLog (D n : ℕ) : ℂ :=
  ∑ a ∈ zetaSquarePrimesThrough D, if a ∣ n then (Real.log a : ℂ) else 0

/-- The squared-mask contribution of all small-prime logarithms. -/
def smallCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  RoughSquarefreeBare.coefficient S 1 n * mask D n ^ 2 * smallLog D n

/-- Every prime mark and ordered divisor intersection is retained. -/
theorem smallCoefficient_eq_lcm_sum (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    smallCoefficient D S n =
      ∑ a ∈ zetaSquarePrimesThrough D, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((μ d : ℂ) * (μ e : ℂ) * (Real.log a : ℂ)) *
          RoughSquarefreeBare.coefficient S (Nat.lcm a (Nat.lcm d e)) n := by
  unfold smallCoefficient smallLog
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_two, mask]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hsf : Squarefree n <;> by_cases hs : ∃ b ∈ S, b ∣ n <;>
    by_cases ha : a ∣ n <;> by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
      simp [RoughSquarefreeBare.coefficient, Nat.lcm_dvd_iff, hsf, hs, ha, hd, he]
  all_goals ring_nf
  all_goals simp

/-- The complete small-prime logarithmic response keeps the original kernel. -/
def smallResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, smallCoefficient D S n * zetaPrimeFilterKernel p N s n

/-- The full marked expansion is an equality of convergent series. -/
theorem hasSum_smallResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ smallCoefficient D S n * zetaPrimeFilterKernel p (N + 1) s n)
      (∑ a ∈ zetaSquarePrimesThrough D, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((μ d : ℂ) * (μ e : ℂ) * (Real.log a : ℂ)) *
          RoughSquarefreeBare.response p S (Nat.lcm a (Nat.lcm d e)) (N + 1) s) := by
  have h := hasSum_sum (s := zetaSquarePrimesThrough D) (fun a _ ↦
    hasSum_sum (s := Finset.Icc 1 D) (fun d _ ↦
      hasSum_sum (s := Finset.Icc 1 D) (fun e _ ↦
        (RoughSquarefreeBare.summable_response p S hS (Nat.lcm a (Nat.lcm d e)) N hs).hasSum.mul_left
          ((μ d : ℂ) * (μ e : ℂ) * (Real.log a : ℂ)))))
  apply h.congr_fun
  intro n
  rw [smallCoefficient_eq_lcm_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

private theorem norm_moebius_le_one (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- The entire logarithmic deletion has an independent cubic divisor cost.
The estimate includes every prime and every lcm cross term. -/
theorem exists_smallResponse_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖smallResponse p D S (N + 1) (3 / 2 + I * y)‖ ≤
        C * D ^ 3 * Real.log D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by
  obtain ⟨C, hC, hb⟩ := RoughSquarefreeBare.exists_response_bound y hy hr hr1
  refine ⟨C, hC, ?_⟩
  intro p D N R S hS
  let A := C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
    (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcard : (zetaSquarePrimesThrough D).card ≤ D := by
    simpa [RoughPrimeIncidence.cutoffPrimes] using RoughPrimeIncidence.card_cutoffPrimes_le D ∅
  rw [smallResponse, (hasSum_smallResponse p D S (fun a ha ↦ (hS a ha).1) N (by norm_num)).tsum_eq]
  calc
    _ ≤ ∑ _a ∈ zetaSquarePrimesThrough D, ∑ _d ∈ Finset.Icc 1 D,
        ∑ _e ∈ Finset.Icc 1 D, Real.log D * A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
      have haspec := (Finset.mem_filter.mp ha).1
      have hlog : Real.log a ≤ Real.log D := Real.log_le_log
        (by exact_mod_cast (Finset.mem_Icc.mp haspec).1)
        (by exact_mod_cast (Finset.mem_Icc.mp haspec).2)
      have hm : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ ≤ 1 := by
        simpa using mul_le_mul (norm_moebius_le_one d) (norm_moebius_le_one e)
          (norm_nonneg _) (by norm_num)
      have hc : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * Real.log a ≤ Real.log D :=
        (mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg a)).trans
          (by simpa using hlog)
      exact mul_le_mul hc (hb p N R S (Nat.lcm a (Nat.lcm d e)) hS)
        (norm_nonneg _) (Real.log_natCast_nonneg D)
    _ = (zetaSquarePrimesThrough D).card * ((D : ℝ) ^ 2 * Real.log D * A) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    _ ≤ (D : ℝ) * ((D : ℝ) ^ 2 * Real.log D * A) := by gcongr
    _ = _ := by dsimp [A]; ring

/-- The original zero-adapted normalization of all small-prime logarithms. -/
def actualSmallResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    smallResponse (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The full small-prime logarithmic contribution has a geometrically vanishing
allowance at the literal zero-source normalization. This estimate uses
the independent marked-series bound, not the source limit. -/
theorem exists_actualSmall_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖actualSmallResponse rho hrho N‖ ≤ C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := RoughPrimeIncidence.radius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq1 : 1 < q := one_lt_zetaMoebiusHeadGrowth hu hu1
  have hq : 0 < q := zero_lt_one.trans hq1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hrate : 0 ≤ RoughPrimeIncidence.rate rho := (RoughPrimeIncidence.rate_bounds rho hrho).1.le
  obtain ⟨hr, hr1, _⟩ := RoughPrimeIncidence.radius_bounds rho hrho
  have hri : 1 ≤ r⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hr).mpr (by simpa using hr1.le)
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_smallResponse_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + 4 * Real.log q) + 1, by positivity, ?_⟩
  intro N hN
  let D := zetaMoebiusGeometricCutoff q N
  have hDpos : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have he := RoughPrimeIncidence.exp_sqrt_cutoff_bound rho hrho N
  have hlog : Real.log D ≤ 1 + 4 * (N : ℝ) * Real.log q := by
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow] at h
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hD3 : (D : ℝ) ^ 3 ≤ q ^ N * (q ^ N) ^ 2 := by
    calc
      (D : ℝ) ^ 3 ≤ (q ^ N) ^ 3 := pow_le_pow_left₀ (by positivity) hD 3
      _ = _ := by ring
  have hpred : N - 1 + 1 = N := by omega
  have hbN := hb p D (N - 1) (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [hpred] at hbN
  have hpow : r⁻¹ ^ (N - 1) ≤ r⁻¹ ^ N := pow_le_pow_right₀ hri (by omega)
  rw [actualSmallResponse, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D ^ 3 * Real.log D *
        Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ (N - 1) * B) :=
      mul_le_mul_of_nonneg_left hbN (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N * (q ^ N) ^ 2) *
        (1 + 4 * (N : ℝ) * Real.log q) * (Real.sqrt q) ^ N * r⁻¹ ^ N * B) := by
      gcongr
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) *
        ((u * Real.sqrt q * q ^ 3) / r) ^ N := by
      rw [div_pow, mul_pow, mul_pow, pow_succ,
        show (q ^ 3) ^ N = (q ^ N) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) * RoughPrimeIncidence.rate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
      rfl
    _ ≤ (C * u * B) * ((1 + 4 * Real.log q) * (1 + (N : ℝ))) * RoughPrimeIncidence.rate rho ^ N := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ _ := by
      have h0 : 0 ≤ (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by positivity
      calc
        _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) := by ring
        _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
        _ = _ := by ring

/-- The complete small-prime logarithmic response tends to zero in
complex norm at the original normalization, with no missing premise. -/
theorem tendsto_actualSmallResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualSmallResponse rho hrho) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actualSmall_bound rho hrho
  exact squeeze_zero_norm' ((eventually_ge_atTop 1).mono (fun N hN ↦ hb N hN))
    (RoughPrimeIncidence.tendsto_allowance rho hrho C)



/-- The low-prime logarithm is an exact prime-factor prefix. -/
theorem smallLog_eq_primeFactors (D : ℕ) {n : ℕ} (hn : n ≠ 0) :
    smallLog D n = ∑ a ∈ n.primeFactors.filter (fun a ↦ a ≤ D), (Real.log a : ℂ) := by
  unfold smallLog
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [zetaSquarePrimesThrough, Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨⟨_, haD⟩, ha⟩, han⟩
    exact ⟨⟨ha, han, hn⟩, haD⟩
  · rintro ⟨⟨ha, han, _⟩, haD⟩
    exact ⟨⟨⟨ha.pos, haD⟩, ha⟩, han⟩

/-- The logarithmic weight of all prime factors strictly beyond the cutoff. -/
def largeLog (D n : ℕ) : ℂ :=
  ∑ a ∈ n.primeFactors.filter (fun a ↦ D < a), (Real.log a : ℂ)

/-- Squarefreeness turns the complete prime-factor logarithm into log n. -/
theorem smallLog_add_largeLog (D : ℕ) {n : ℕ} (hn : Squarefree n) :
    smallLog D n + largeLog D n = (Real.log n : ℂ) := by
  have hprod := congrArg (fun a : ℕ ↦ Real.log a) (Nat.prod_primeFactors_of_squarefree hn)
  rw [Nat.cast_prod, Real.log_prod (fun a ha ↦ by
    exact_mod_cast (Nat.prime_of_mem_primeFactors ha).ne_zero)] at hprod
  rw [smallLog_eq_primeFactors D hn.ne_zero, largeLog]
  have h := Finset.sum_filter_add_sum_filter_not n.primeFactors (fun a ↦ a ≤ D)
    (fun a ↦ (Real.log a : ℂ))
  simp only [not_le] at h
  rw [h]
  exact_mod_cast hprod

/-- No ordinary-prime term is introduced by logarithmic deletion. -/
theorem smallCoefficient_prime (D : ℕ) (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    smallCoefficient D S p = 0 := by
  by_cases h : p ≤ D
  · simp [smallCoefficient, mask_eq_unit hp.pos h, hp.ne_one]
  · have hz : smallLog D p = 0 := by
      rw [smallLog_eq_primeFactors D hp.ne_zero, hp.primeFactors]
      have he : ({p} : Finset ℕ).filter (fun a ↦ a ≤ D) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a ha
        have he := Finset.mem_singleton.mp ha
        simpa only [he] using h
      rw [he]
      simp
    simp [smallCoefficient, hz]

/-- The exact remaining coefficient retains only large-prime logarithms
on the original rough squarefree composite support. -/
def coefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ ¬n.Prime then
    mask D n ^ 2 * largeLog D n else 0

/-- The full square source splits into the independently controlled
small-prime logarithms and the exact large-prime carrier. -/
theorem coefficient_eq_square_sub_small (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    coefficient D S n = RoughMoebiusMixed.squareCoefficient D S n - smallCoefficient D S n := by
  by_cases hp : n.Prime
  · simp [coefficient, hp, smallCoefficient_prime D S hp,
      RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight]
  by_cases hsf : Squarefree n
  · by_cases hs : ∃ a ∈ S, a ∣ n
    · simp [coefficient, smallCoefficient, RoughSquarefreeBare.coefficient,
        RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight, hs]
    · simp only [coefficient, smallCoefficient, RoughSquarefreeBare.coefficient,
        RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight,
        hsf, hs, hp, not_false_eq_true, true_and, one_dvd, ite_true, one_mul]
      rw [← smallLog_add_largeLog D hsf]
      ring
  · simp [coefficient, smallCoefficient, RoughSquarefreeBare.coefficient,
      RoughMoebiusMixed.squareCoefficient, zetaRoughSquarefreeCompositeLogWeight, hsf]

/-- Every integer with no prime divisor beyond the cutoff has zero
remaining coefficient, without estimating its original separate sum. -/
theorem coefficient_eq_zero_of_smooth (D : ℕ) (S : Finset ℕ) {n : ℕ}
    (hn : ∀ a ∈ n.primeFactors, a ≤ D) : coefficient D S n = 0 := by
  have he : n.primeFactors.filter (fun a ↦ D < a) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    exact not_lt_of_ge (hn a ha)
  simp [coefficient, largeLog, he]

/-- Any surviving integer has a genuine prime factor beyond the cutoff. -/
theorem exists_large_prime_of_coefficient_ne_zero (D : ℕ) (S : Finset ℕ) {n : ℕ}
    (hn : coefficient D S n ≠ 0) : ∃ a ∈ n.primeFactors, D < a := by
  by_contra h
  push Not at h
  exact hn (coefficient_eq_zero_of_smooth D S h)

/-- The genuine arithmetic response of the remaining large-prime weight. -/
def response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, coefficient D S n * zetaPrimeFilterKernel p N s n

/-- The infinite source partition is justified by genuine convergence. -/
theorem hasSum_response (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient D S n * zetaPrimeFilterKernel p (N + 1) s n)
      (RoughMoebiusMixed.squareResponse p D S (N + 1) s - smallResponse p D S (N + 1) s) := by
  have hq := (RoughMoebiusMixed.hasSum_squareResponse p D hD S hS N hs).summable.hasSum
  have he := (hasSum_smallResponse p D S hS N hs).summable.hasSum
  apply (hq.sub he).congr_fun
  intro n
  rw [coefficient_eq_square_sub_small, sub_mul]

/-- The remaining series at the unchanged zero-source normalization. -/
def actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    response (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- At each positive order the source partition retains both exact terms. -/
theorem actualResponse_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {N : ℕ} (hN : 1 ≤ N) :
    actualResponse rho hrho N = RoughMoebiusMixed.actualSquareResponse rho hrho N -
      actualSmallResponse rho hrho N := by
  have h := (hasSum_response (zetaRightHalfPoleJetFilter rho hrho) _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1)
    (N - 1) (by norm_num : (1 : ℝ) < (3 / 2 + I * rho.1.im : ℂ).re)).tsum_eq
  rw [show N - 1 + 1 = N by omega] at h
  simp only [actualResponse, RoughMoebiusMixed.actualSquareResponse, actualSmallResponse, response]
  rw [h, mul_sub]

/-- The complete multiplicity source survives on the large-prime carrier;
the small-prime logarithmic correction has independent geometric decay. -/
theorem tendsto_actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualResponse rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have h := (RoughMoebiusMixed.tendsto_actualSquareResponse rho hrho).sub
    (tendsto_actualSmallResponse rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (actualResponse_eq rho hrho hN).symm


/-- Every surviving coefficient admits a prime--cofactor factorization
with both factors beyond D. Complete small cofactors cancel exactly. -/
theorem exists_prime_cofactor_of_coefficient_ne_zero (D : ℕ) (S : Finset ℕ) {n : ℕ}
    (hn : coefficient D S n ≠ 0) :
    ∃ a m : ℕ, a.Prime ∧ D < a ∧ D < m ∧ n = a * m := by
  have hg : Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ ¬n.Prime := by
    by_contra h
    exact hn (by rw [coefficient, if_neg h])
  obtain ⟨a, ha, hDa⟩ := exists_large_prime_of_coefficient_ne_zero D S hn
  have hp := Nat.prime_of_mem_primeFactors ha
  have had := Nat.dvd_of_mem_primeFactors ha
  have he : a * (n / a) = n := Nat.mul_div_cancel' had
  have hm0 : 0 < n / a :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg.1.ne_zero) had) hp.pos
  have hm1 : n / a ≠ 1 := by
    intro h
    have hnA : n = a := by simpa [h] using he.symm
    exact hg.2.2 (hnA ▸ hp)
  have hDm : D < n / a := by
    by_contra h
    have hle : n / a ≤ D := by omega
    have hz : mask D n = 0 := by
      rw [← he, mask_large_prime hp hDa, mask_eq_unit hm0 hle, if_neg hm1]
    exact hn (by simp [coefficient, hz])
  exact ⟨a, n / a, hp, hDa, hDm, he.symm⟩

/-- The large-prime logarithmic coefficient is nonnegative before
multiplication by the unchanged complex kernel. -/
theorem coefficient_re_nonneg (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    0 ≤ (coefficient D S n).re := by
  unfold coefficient
  split_ifs
  · have hL : 0 ≤ (largeLog D n).re := by
      simp only [largeLog, Complex.re_sum, Complex.ofReal_re]
      exact Finset.sum_nonneg (fun a _ ↦ Real.log_natCast_nonneg a)
    have hMi : (mask D n ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, mask_im]
    rw [Complex.mul_re, hMi, zero_mul, sub_zero]
    exact mul_nonneg (mask_square_re_nonneg D n) hL
  · simp

/-- No imaginary component is introduced into the arithmetic coefficient. -/
theorem coefficient_im (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    (coefficient D S n).im = 0 := by
  unfold coefficient
  split_ifs
  · have hL : (largeLog D n).im = 0 := by
      simp only [largeLog, Complex.im_sum, Complex.ofReal_im, Finset.sum_const_zero]
    have hM : (mask D n ^ 2).im = 0 := by simp [pow_two, Complex.mul_im, mask_im]
    simp only [Complex.mul_im, hL, hM, mul_zero, zero_mul, add_zero]
  · rfl

/-- The actual difference from the complete square source has the
independent small-prime allowance at every positive order. -/
theorem exists_actual_source_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖actualResponse rho hrho N - RoughMoebiusMixed.actualSquareResponse rho hrho N‖ ≤
        C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_actualSmall_bound rho hrho
  refine ⟨C, hC, ?_⟩
  intro N hN
  rw [actualResponse_eq rho hrho hN, sub_sub_cancel_left, norm_neg]
  exact hb N hN


private theorem norm_mask_le (D n : ℕ) : ‖mask D n‖ ≤ D := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ‖if d ∣ n then (μ d : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · exact norm_moebius_le_one d
      · simp
    _ = _ := by simp

/-- The large-prime logarithm costs at most the complete logarithm. -/
theorem norm_largeLog_le (D : ℕ) {n : ℕ} (hn : Squarefree n) :
    ‖largeLog D n‖ ≤ Real.log n := by
  have hprod := congrArg (fun a : ℕ ↦ Real.log a) (Nat.prod_primeFactors_of_squarefree hn)
  rw [Nat.cast_prod, Real.log_prod (fun a ha ↦ by
    exact_mod_cast (Nat.prime_of_mem_primeFactors ha).ne_zero)] at hprod
  calc
    _ ≤ ∑ a ∈ n.primeFactors.filter (fun a ↦ D < a), ‖(Real.log a : ℂ)‖ := norm_sum_le _ _
    _ = ∑ a ∈ n.primeFactors.filter (fun a ↦ D < a), Real.log a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
    _ ≤ ∑ a ∈ n.primeFactors, Real.log a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ ↦ Real.log_natCast_nonneg a)
    _ = Real.log n := hprod

private theorem log_le_majorant {n : ℕ} (hn : 0 < n) :
    Real.log n ≤ zetaMoebiusLogMajorant n := by
  rw [zetaMoebiusLogMajorant, Nat.sum_divisorsAntidiagonal (fun _ b ↦ Real.log b)]
  have h := Finset.single_le_sum (fun d (_ : d ∈ n.divisors) ↦
    Real.log_natCast_nonneg (n / d)) (Nat.one_mem_divisors.mpr hn.ne')
  simpa using h

/-- The full coefficient has a quadratic mask cost against the original
summable divisor-log majorant, independent of the prime sieve. -/
theorem norm_coefficient_le (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    ‖coefficient D S n‖ ≤ (D : ℝ) ^ 2 * zetaMoebiusLogMajorant n := by
  unfold coefficient
  split_ifs with h
  · rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_mask_le D n) 2)
      ((norm_largeLog_le D h.1).trans (log_le_majorant (Nat.pos_of_ne_zero h.1.ne_zero)))
      (norm_nonneg _) (by positivity)
  · simp only [norm_zero]
    exact mul_nonneg (sq_nonneg _) (zetaMoebiusLogMajorant_nonneg n)

/-- Every selected subset of the cubic head has independent decay,
including the full squared mask and the exact large-prime logarithm. -/
theorem norm_normalized_head_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) (S : Finset ℕ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, n ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N ^ 3) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      coefficient (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N) S n *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      zetaArithmeticSmallProductConstant p * (1 / (2 * u)) ^ N := by
  exact norm_normalized_sum_zetaArithmetic_quadratic_cubic_le _ p N y hu hu1
    (fun n ↦ norm_coefficient_le _ S n) T hT

/-- The literal finite head of the large-prime response. -/
def actualHead (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    ∑ n ∈ Finset.Iic ((zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 3),
      coefficient (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n

/-- The actual head has geometric decay at the exact source-scale rate. -/
theorem norm_actualHead_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    ‖actualHead rho hrho N‖ ≤
      zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) *
        (1 / (2 * (3 / 2 - rho.1.re))) ^ N := by
  apply norm_normalized_head_le
  · linarith [NontrivialZetaZero.re_lt_one rho]
  · linarith
  · intro n hn
    exact Finset.mem_Iic.mp hn

/-- The complete finite head tends independently to zero. -/
theorem tendsto_actualHead (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualHead rho hrho) atTop (𝓝 0) := by
  have hu : 1 / 2 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  obtain ⟨hr0, hr1⟩ := zetaArithmetic_quadratic_cubic_rate_bounds hu
  apply squeeze_zero_norm (norm_actualHead_le rho hrho)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul
    (zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho))

/-- The literal remaining large-prime series is supported strictly
above the cubic product cutoff. Its complex kernel is unchanged. -/
def tailResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, if D ^ 3 < n then
    coefficient D S n * zetaPrimeFilterKernel p N s n else 0

private theorem summable_above {f : ℕ → ℂ} (hf : Summable f) (X : ℕ) :
    Summable (fun n ↦ if X < n then f n else 0) := by
  apply (hf.indicator {n | X < n}).congr
  intro n
  by_cases hn : X < n <;> simp [hn]

private theorem tsum_above_eq {f : ℕ → ℂ} (hf : Summable f) (X : ℕ) :
    (∑' n, if X < n then f n else 0) = (∑' n, f n) - ∑ n ∈ Finset.Iic X, f n := by
  have h := hf.sum_add_tsum_compl (s := Finset.Iic X)
  rw [tsum_subtype] at h
  have he : ((Finset.Iic X : Set ℕ)ᶜ).indicator f = (fun n ↦ if X < n then f n else 0) := by
    funext n
    by_cases hn : X < n <;> simp [hn]
  rw [he] at h
  linear_combination h

/-- The retained high-product series genuinely converges; its
restriction is justified on the original arithmetic summation variable. -/
theorem summable_tailResponse (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ if D ^ 3 < n then
      coefficient D S n * zetaPrimeFilterKernel p (N + 1) s n else 0) := by
  exact summable_above (hasSum_response p D hD S hS N hs).summable (D ^ 3)

/-- The complete large-prime response partitions into its finite head
and the literal infinite high-product series with no discarded boundary. -/
theorem tailResponse_eq (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    tailResponse p D S (N + 1) s = response p D S (N + 1) s -
      ∑ n ∈ Finset.Iic (D ^ 3),
        coefficient D S n * zetaPrimeFilterKernel p (N + 1) s n := by
  exact tsum_above_eq (hasSum_response p D hD S hS N hs).summable (D ^ 3)


/-- The unchanged normalization of the genuine large-prime tail. -/
def actualTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    tailResponse (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The exact source partition precedes both the head estimate and the limit. -/
theorem actualTail_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {N : ℕ} (hN : 1 ≤ N) :
    actualTail rho hrho N = actualResponse rho hrho N - actualHead rho hrho N := by
  have h := tailResponse_eq (zetaRightHalfPoleJetFilter rho hrho) _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1)
    (N - 1) (by norm_num : (1 : ℝ) < (3 / 2 + I * rho.1.im : ℂ).re)
  rw [show N - 1 + 1 = N by omega] at h
  rw [actualTail, h, mul_sub]
  rfl

/-- The full positive multiplicity source remains in the literal high-product
large-prime tail. Its independent strict signed upper bound remains open. -/
theorem tendsto_actualTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualTail rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have h := (tendsto_actualResponse rho hrho).sub (tendsto_actualHead rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (actualTail_eq rho hrho hN).symm

/-- The complete error allowance pays for both the logarithmic prime deletion
and the entire quadratic-mask head, at every positive moment order. -/
theorem exists_actualTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖actualTail rho hrho N - RoughMoebiusMixed.actualSquareResponse rho hrho N‖ ≤
        C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N +
          zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) *
            (1 / (2 * (3 / 2 - rho.1.re))) ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_actual_source_error_bound rho hrho
  refine ⟨C, hC, ?_⟩
  intro N hN
  rw [actualTail_eq rho hrho hN]
  have he : actualResponse rho hrho N - actualHead rho hrho N -
      RoughMoebiusMixed.actualSquareResponse rho hrho N =
      (actualResponse rho hrho N - RoughMoebiusMixed.actualSquareResponse rho hrho N) -
        actualHead rho hrho N := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (hb N hN) (norm_actualHead_le rho hrho N))

/-- A cofinal signed upper bound strictly below one closes the contradiction.
The displayed arithmetic upper-bound premise is not proved here. -/
theorem false_of_cofinal_tail_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, (actualTail rho hrho N).re ≤ 1 - ε) : False := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_actualTail rho hrho)
  have hb := le_of_tendsto_of_frequently h hbound
  simp only [Complex.natCast_re] at hb
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- All large-prime fibres retain the same exact cofactor mask.
Each distinct large prime is counted once; no preferred factor is selected. -/
theorem coefficient_eq_large_prime_fibres (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    coefficient D S n = ∑ a ∈ n.primeFactors.filter (fun a ↦ D < a),
      if Squarefree n ∧ (¬∃ p ∈ S, p ∣ n) ∧ ¬n.Prime then
        mask D (n / a) ^ 2 * (Real.log a : ℂ) else 0 := by
  by_cases hg : Squarefree n ∧ (¬∃ p ∈ S, p ∣ n) ∧ ¬n.Prime
  · rw [coefficient, if_pos hg, largeLog, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hf := Finset.mem_filter.mp ha
    have hp := Nat.prime_of_mem_primeFactors hf.1
    have had := Nat.dvd_of_mem_primeFactors hf.1
    have hm : mask D n = mask D (n / a) := by
      conv_lhs => rw [← Nat.mul_div_cancel' had]
      exact mask_large_prime hp hf.2 _
    rw [if_pos hg, hm]
  · rw [coefficient, if_neg hg]
    symm
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg hg


/-- The complete error relative to the square carrier tends independently
to zero using both proved geometric allowances, without a source-limit input. -/
theorem tendsto_actualTail_sub_square (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ actualTail rho hrho N - RoughMoebiusMixed.actualSquareResponse rho hrho N)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actualTail_error_bound rho hrho
  have hu : 1 / 2 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  obtain ⟨hr0, hr1⟩ := zetaArithmetic_quadratic_cubic_rate_bounds hu
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul
    (zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho))
  have ht := (RoughPrimeIncidence.tendsto_allowance rho hrho C).add hh
  simp only [mul_zero, add_zero] at ht
  exact squeeze_zero_norm' ((eventually_ge_atTop 1).mono (fun N hN ↦ hb N hN)) ht

end
end RiemannGaussian.RoughPrimeLog
