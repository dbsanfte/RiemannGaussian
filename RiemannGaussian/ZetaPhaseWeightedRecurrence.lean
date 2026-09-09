/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhasePrimeRecurrence
import RiemannGaussian.ZetaPhaseExactZeroBound

/-!
# Weighted phase returns strengthen the arithmetic floor

The finite Gram identity retains the triangular multiplicity of every
phase difference. Comparing those multiplicities with the actual
prime-power amplitudes gives a stronger arithmetic floor than bounding
each return separately by the entire prime sum. The argument applies to
arbitrary summable nonnegative real-frequency spectra.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

variable {a ω : ℕ → ℝ}

private theorem block_succ (K : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) (M : ℕ) (θ : ℝ) :
    (∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (M + 1),
      K ((j : ℝ) * θ - (i : ℝ) * θ)) =
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      K ((j : ℝ) * θ - (i : ℝ) * θ)) + K 0 +
      2 * ∑ k ∈ Finset.range M, K (((k + 1 : ℕ) : ℝ) * θ) := by
  have hrow : (∑ i ∈ Finset.range M, K ((M : ℝ) * θ - (i : ℝ) * θ)) =
      ∑ k ∈ Finset.range M, K (((k + 1 : ℕ) : ℝ) * θ) := by
    calc
      _ = ∑ i ∈ Finset.range M, K (((M - 1 - i + 1 : ℕ) : ℝ) * θ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiM := Finset.mem_range.mp hi
        rw [show M - 1 - i + 1 = M - i by omega, Nat.cast_sub (by omega : i ≤ M)]
        congr 1
        ring
      _ = _ := Finset.sum_range_reflect (fun k ↦ K (((k + 1 : ℕ) : ℝ) * θ)) M
  have hcol : (∑ j ∈ Finset.range M, K ((j : ℝ) * θ - (M : ℝ) * θ)) =
      ∑ k ∈ Finset.range M, K (((k + 1 : ℕ) : ℝ) * θ) := by
    rw [← hrow]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (j : ℝ) * θ - (M : ℝ) * θ = -((M : ℝ) * θ - (j : ℝ) * θ) by ring, hK]
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
  rw [hrow, hcol]
  ring

private theorem block_triangle (K : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) (N : ℕ) (θ : ℝ) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      K ((j : ℝ) * θ - (i : ℝ) * θ)) =
      ((N : ℝ) + 1) * K 0 +
        2 * ∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) * K (((k + 1 : ℕ) : ℝ) * θ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [block_succ K hK (N + 1), ih]
    have hw : (∑ k ∈ Finset.range (N + 1), ((N + 1 - k : ℕ) : ℝ) *
        K (((k + 1 : ℕ) : ℝ) * θ)) =
        (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) * K (((k + 1 : ℕ) : ℝ) * θ)) +
          ∑ k ∈ Finset.range (N + 1), K (((k + 1 : ℕ) : ℝ) * θ) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs : (∑ k ∈ Finset.range N, ((N + 1 - k : ℕ) : ℝ) *
          K (((k + 1 : ℕ) : ℝ) * θ)) =
          (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) * K (((k + 1 : ℕ) : ℝ) * θ)) +
            ∑ k ∈ Finset.range N, K (((k + 1 : ℕ) : ℝ) * θ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hkN := Finset.mem_range.mp hk
        rw [show N + 1 - k = N - k + 1 by omega, Nat.cast_add, Nat.cast_one]
        ring
      rw [hs]
      simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
      ring
    rw [hw]
    push_cast
    ring

/-- The exact Gram block retains every triangular return multiplicity.
This identity uses only evenness and holds before any positivity estimate. -/
theorem zetaPhase_gram_block_eq (a ω : ℕ → ℝ) (N : ℕ) (θ : ℝ) :
    (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      zetaPhaseKernel a ω ((j.val : ℝ) * θ - (i.val : ℝ) * θ)) =
      ((N : ℝ) + 1) * (∑' n : ℕ, a n) +
        2 * ∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) *
          zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  simpa only [Finset.sum_range, zetaPhaseKernel_zero] using
    block_triangle (zetaPhaseKernel a ω) (zetaPhaseKernel_neg a ω) N θ

/-- Zero-frequency mass forces the whole weighted return sum to be
large. All return multiplicities survive; no common ceiling is introduced. -/
theorem zetaPhase_weighted_returns_le (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) (N : ℕ) (θ : ℝ) :
    ((N : ℝ) + 1) * (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) ≤
      2 * ∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) *
        zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * θ) := by
  have h := zetaPhase_gramEnergy_zeroFrequency_le ha hs r hr
    (fun i : Fin (N + 1) ↦ (i.val : ℝ) * θ) (fun _ ↦ 1)
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at h
  rw [zetaPhase_gram_block_eq] at h
  nlinarith only [h]

/-- Actual prime-power amplitudes dominate the triangular return
multiplicities times the last amplitude of the block. -/
theorem zetaPhasePrimeBlockWeight_triangle_le {σ : ℝ} (hσ : 1 ≤ σ)
    {p : ℕ} (hp : p.Prime) {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ((N + 1 - k : ℕ) : ℝ) * zetaPhasePrimeBlockWeight σ p N ≤
      zetaPhasePrimeWeight σ (p ^ k) := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpow : ((N - k : ℕ) : ℝ) + 1 ≤ (p : ℝ) ^ (N - k) := by
    have hn : N - k + 1 ≤ p ^ (N - k) := Nat.lt_pow_self hp.one_lt
    exact_mod_cast hn
  have hexp : ((N + 1 - k : ℕ) : ℝ) ≤
      Real.exp (σ * ((N - k : ℕ) : ℝ) * Real.log p) := by
    rw [show N + 1 - k = N - k + 1 by omega, Nat.cast_add, Nat.cast_one]
    refine hpow.trans ?_
    rw [← Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ) < p), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    have h := mul_le_mul_of_nonneg_right hσ
      (mul_nonneg (Nat.cast_nonneg (N - k) : (0 : ℝ) ≤ ((N - k : ℕ) : ℝ)) hlog.le)
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-σ * (N : ℝ) * Real.log p)).le
  rw [← Real.exp_add] at hmul
  have he : σ * ((N - k : ℕ) : ℝ) * Real.log p + -σ * (N : ℝ) * Real.log p =
      -σ * ((k : ℝ) * Real.log p) := by
    rw [Nat.cast_sub hkN]
    ring
  rw [he] at hmul
  rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  unfold zetaPhasePrimeBlockWeight
  nlinarith only [mul_le_mul_of_nonneg_left hmul hlog.le]

/-- Preserving the weighted returns yields a floor larger by the
factor `N*(N+1)/2` than the separate-return bound at the same block length.
It holds for arbitrary finite or infinite real-frequency families. -/
theorem zetaPhase_weighted_primePower_floor (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) (N : ℕ) (y : ℝ) :
    zetaPhasePrimeBlockWeight σ p N *
        (((N : ℝ) + 1) * (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) / 2) ≤
      ∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  have hf := zetaPhase_finite_primeWork_le ha hs hP hσ y
    ((Finset.range N).image (fun k ↦ p ^ (k + 1)))
  rw [Finset.sum_image (fun i _ j _ hij ↦
    Nat.add_right_cancel (Nat.pow_right_injective hp.two_le hij))] at hf
  have hw : zetaPhasePrimeBlockWeight σ p N *
      (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) *
        zetaPhaseKernel a ω (((k + 1 : ℕ) : ℝ) * (y * Real.log p))) ≤
      ∑ k ∈ Finset.range N, zetaPhasePrimeWeight σ (p ^ (k + 1)) *
        zetaPhaseKernel a ω (y * Real.log (p ^ (k + 1) : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have h := zetaPhasePrimeBlockWeight_triangle_le hσ.le hp
      (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ N)
    rw [show N + 1 - (k + 1) = N - k by omega] at h
    have he : y * Real.log (p ^ (k + 1) : ℕ) =
        ((k + 1 : ℕ) : ℝ) * (y * Real.log p) := by
      rw [Nat.cast_pow, Real.log_pow]
      ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right h
      (hP (((k + 1 : ℕ) : ℝ) * (y * Real.log p)))]
  have hg := mul_le_mul_of_nonneg_left
    (zetaPhase_weighted_returns_le ha hs r hr N (y * Real.log p))
    (zetaPhasePrimeBlockWeight_pos σ hp N).le
  nlinarith only [hg, hw, hf]

private theorem exact_summable : Summable phaseContactExactFamily :=
  summable_of_phaseContactBudget phaseContactExactFamily_nonneg
    phaseContactExactFamily_hasSum_budget.summable

/-- The exact optimizer satisfies the stronger weighted prime-power
floor at every block length, prime, and height. All phase hypotheses are
discharged for its mathematically defined coefficients. -/
theorem phaseContactExact_weighted_primePower_floor {σ : ℝ} (hσ : 1 < σ)
    {p : ℕ} (hp : p.Prime) (N : ℕ) (y : ℝ) :
    zetaPhasePrimeBlockWeight σ p N *
        (((N : ℝ) + 1) * (((N : ℝ) + 1) * phaseContactExactFamily 0 -
          (∑' n : ℕ, phaseContactExactFamily n)) / 2) ≤
      ∑' m : ℕ, zetaPhasePrimeWeight σ m *
        phaseContactKernel phaseContactExactFamily (y * Real.log m) :=
  zetaPhase_weighted_primePower_floor (ω := fun n ↦ (n : ℝ))
    phaseContactExactFamily_nonneg exact_summable phaseContactExactFamily_kernel_nonneg
    0 (by norm_num) hσ hp N y

/-- A rational lower bound on the six-point Gram source, derived from
the proved enclosures of all nine exact coefficients. -/
theorem phaseContactExactFamily_six_mass_gap :
    (313 / 1000 : ℝ) ≤ 6 * phaseContactExactFamily 0 -
      (∑' n : ℕ, phaseContactExactFamily n) := by
  have h0 : (18453 / 100000 : ℝ) ≤ phaseContactExactFamily 0 := by
    have he := phaseContactFrequencyFamily_apply phaseContactExactCoefficients 0
    change phaseContactExactFamily 0 = phaseContactExactCoefficients 0 at he
    rw [he]
    have h := (abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le 0)).1
    norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ] at h
    linarith
  have hA : (∑' n : ℕ, phaseContactExactFamily n) ≤ (397 / 500 : ℝ) := by
    have he := (phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients
      (fun _ ↦ 1)).tsum_eq
    simp only [mul_one] at he
    change (∑' n : ℕ, phaseContactExactFamily n) = _ at he
    rw [he]
    calc
      _ ≤ ∑ i : Fin 9, (phaseContactPrimalCenter i + 1 / 10 ^ 15) := by
        apply Finset.sum_le_sum
        intro i _
        linarith [(abs_le.mp (abs_phaseContactExactCoefficients_sub_center_le i)).2]
      _ ≤ (397 / 500 : ℝ) := by
        norm_num [phaseContactPrimalCenter, phaseContactPrimalCenterQ, Fin.sum_univ_succ]
  linarith

private theorem five_weight_lower :
    (Real.log 2 / 77 : ℝ) ≤ zetaPhasePrimeBlockWeight (5 / 4) 2 5 := by
  have he : Real.exp ((25 / 4 : ℝ) * Real.log 2) ^ 4 = (2 : ℝ) ^ 25 := by
    rw [← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat]
    rw [show (4 : ℝ) * ((25 / 4 : ℝ) * Real.log 2) = 25 * Real.log 2 by ring]
    rw [show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.exp ((25 / 4 : ℝ) * Real.log 2) ≤ 77 :=
    le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 77)
      (by rw [he]; norm_num)
  have hinv : (1 / 77 : ℝ) ≤ Real.exp (-((25 / 4 : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hexp
  unfold zetaPhasePrimeBlockWeight
  have he' : -(5 / 4 : ℝ) * (5 : ℕ) * Real.log (2 : ℕ) = -((25 / 4 : ℝ) * Real.log 2) := by
    norm_num
  rw [he']
  simpa only [Nat.cast_ofNat, mul_one_div] using
    mul_le_mul_of_nonneg_left hinv (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Five linked powers of the prime two force at least `1/120` of
actual arithmetic work, uniformly in height and on `1 < sigma <= 5/4`.
This is an independent bound with no zero or cancellation hypothesis. -/
theorem phaseContactExact_arithmetic_floor {σ : ℝ} (hσ : 1 < σ) (hσle : σ ≤ 5 / 4)
    (y : ℝ) :
    (1 / 120 : ℝ) ≤ ∑' m : ℕ, zetaPhasePrimeWeight σ m *
      phaseContactKernel phaseContactExactFamily (y * Real.log m) := by
  have hw : zetaPhasePrimeBlockWeight (5 / 4) 2 5 ≤ zetaPhasePrimeBlockWeight σ 2 5 := by
    unfold zetaPhasePrimeBlockWeight
    apply mul_le_mul_of_nonneg_left _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hσle
      (show 0 ≤ (5 : ℝ) * Real.log 2 by positivity)
    norm_num at h ⊢
    nlinarith
  have hb : (Real.log 2 / 77 : ℝ) ≤ zetaPhasePrimeBlockWeight σ 2 5 :=
    five_weight_lower.trans hw
  have hc : (1 / 120 : ℝ) ≤ (Real.log 2 / 77) * (3 * (313 / 1000)) := by
    linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul hb (mul_le_mul_of_nonneg_left phaseContactExactFamily_six_mass_gap
    (by norm_num : (0 : ℝ) ≤ 3)) (by norm_num : (0 : ℝ) ≤ 3 * (313 / 1000))
      (zetaPhasePrimeBlockWeight_pos σ Nat.prime_two 5).le
  have hf := phaseContactExact_weighted_primePower_floor hσ Nat.prime_two 5 y
  norm_num at hf
  nlinarith only [hc, hm, hf]

/-- The explicit arithmetic floor strengthens the actual zero budget
while retaining the exact efficiency, analytic multiplicity, and height sum. -/
theorem phaseContactExact_weighted_zero_budget (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    phaseContactExactRoot 8 + (4 / 17 : ℝ) * phaseContactExactFamily 1 *
        ((analyticZetaZeroMultiplicity rho : ℝ) - 1) + (1 - rho.1.re) / 120 ≤
      448 * (1 - rho.1.re) * (∑' n : ℕ,
        phaseContactExactFamily n * localZetaLogHeight ((n : ℝ) * rho.1.im)) +
        (13 / 4 : ℝ) * phaseOscillatoryMass phaseContactExactFamily *
          (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hf := phaseContactExact_arithmetic_floor
    (by linarith : 1 < 1 + (13 / 4 : ℝ) * (1 - rho.1.re))
    (by linarith : 1 + (13 / 4 : ℝ) * (1 - rho.1.re) ≤ 5 / 4) rho.1.im
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  have h := phaseContactExact_source_add_primeWork_le rho hrho
  nlinarith only [hm, h]

/-- Every actual zero near the right edge pays an explicit `d/120`
arithmetic reserve in the rational height inequality, where `d=1-Re rho`. -/
theorem phaseContactExact_weighted_zero_source (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    (11 / 625 : ℝ) + (1 - rho.1.re) / 120 ≤
      448 * (1 - rho.1.re) * ((61 / 100 : ℝ) * localZetaLogHeight rho.1.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have h := phaseContactExact_weighted_zero_budget rho hrho
  have hd : 0 ≤ 1 - rho.1.re := (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hmult : 0 ≤ (4 / 17 : ℝ) * phaseContactExactFamily 1 *
      ((analyticZetaZeroMultiplicity rho : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (phaseContactExactFamily_nonneg 1)) (sub_nonneg.mpr hm)
  have hheight := mul_le_mul_of_nonneg_left (phaseContactExactFamily_height_le rho.1.im)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 448) hd)
  have hpole := mul_le_mul_of_nonneg_right phaseContactExactFamily_oscillatoryMass_le
    (show 0 ≤ (13 / 4 : ℝ) * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 by positivity)
  simp only [div_eq_mul_inv] at hpole h ⊢
  nlinarith [phaseContactExactRoot_source_lower]

/-- The improved independent floor gives a literal zeta nonvanishing
test. Every coefficient and arithmetic bound is discharged for the exact
optimizer; the displayed strict inequality describes the excluded region. -/
theorem phaseContactExact_weighted_exclusion (s : ℂ) (hs : 15 / 16 ≤ s.re)
    (hy : 1 ≤ |s.im|)
    (hgap : 448 * (1 - s.re) * ((61 / 100 : ℝ) * localZetaLogHeight s.im + 83 / 100) +
        (793 / 400 : ℝ) * (1 - s.re) ^ 2 / s.im ^ 2 <
      (11 / 625 : ℝ) + (1 - s.re) / 120) : riemannZeta s ≠ 0 := by
  intro hz
  have hspos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hy
  have hpole : riemannZeta₁ s = 0 := by
    rw [riemannZeta₁_eq_sub_one_mul hs1, hz, mul_zero]
  let rho : NontrivialZetaZero :=
    ⟨s, isNontrivialZetaZero_of_poleRemoved_eq_zero hspos hpole⟩
  exact (not_lt_of_ge (phaseContactExact_weighted_zero_source rho hs)) hgap

end

end RiemannGaussian
