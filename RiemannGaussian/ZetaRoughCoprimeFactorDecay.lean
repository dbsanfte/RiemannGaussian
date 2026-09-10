/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCoprimeEulerPhase
import RiemannGaussian.ZetaMoebiusWindowFactorDecay

/-!
# Uniform full coprime-factor decay from the actual rough prime structure

Every divisor of the actual rough physical support has subexponential
divisor complexity in the moment order. The existing complete response
bound therefore applies uniformly to moving factors throughout that support,
including their original finite prefixes. Finite complex families with the
stated total coefficient budget have a geometrically vanishing normalized
sum. Each sector still includes all coprime multiples; no union or arbitrary
restriction of these sectors is identified with the remaining rough source.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.zeta

namespace RiemannGaussian.RoughCoprimeFactor

noncomputable section

/-- The exact weighted coverage of every physical integer, including all
overlaps of the complete coprime factor sectors. -/
def coverage (S : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ P ∈ S, if P ∣ n ∧ P.Coprime (n / P) then w P else 0

/-- A weighted sector family multiplies the original coefficient by its
literal coverage, before a norm or a physical restriction is taken. -/
theorem sum_sectorCoefficient_eq_coverage (D : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) :
    (∑ P ∈ S, w P * zetaMoebiusFactorSectorCoefficient D P n) =
      zetaMoebiusLogTailCoefficient D n * coverage S w n := by
  rw [coverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [zetaMoebiusFactorSectorCoefficient_eq]
  split_ifs <;> ring

/-- Complete weighted coverage has a genuinely convergent arithmetic
series equal to the same signed family of full factor responses. -/
theorem hasSum_coverage (p : Polynomial ℂ) (D N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ P ∈ S, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ zetaMoebiusLogTailCoefficient D n * coverage S w n *
      zetaPrimeFilterKernel p N s n)
      (∑ P ∈ S, w P * zetaMoebiusFactorFilter p D P N s) := by
  have h := hasSum_sum (s := S) (fun P hP ↦
    (hasSum_zetaMoebiusFactorFilter p D N (hS P hP).1 (hS P hP).2.1 (hS P hP).2.2 hs).mul_left (w P))
  apply h.congr_fun
  intro n
  rw [← sum_sectorCoefficient_eq_coverage, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun P _ ↦ by ring)

/-- A mixed-prime divisor of a product of two primes is the entire product. -/
theorem mixed_divisor_semiprime_eq {P p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) (hdiv : P ∣ p * q) : P = p * q := by
  have hPd : P ∈ (p * q).divisors :=
    Nat.mem_divisors.mpr ⟨hdiv, mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rw [Nat.divisors_mul, Finset.mul_def] at hPd
  obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hPd
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  dsimp only at heq
  rcases hp.eq_one_or_self_of_dvd a (Nat.dvd_of_mem_divisors ha) with rfl | rfl <;>
    rcases hq.eq_one_or_self_of_dvd b (Nat.dvd_of_mem_divisors hb) with rfl | rfl
  · exact False.elim (hP1 heq.symm)
  · simp only [one_mul] at heq
    exact False.elim (hmix (heq ▸ hq.isPrimePow))
  · simp only [mul_one] at heq
    exact False.elim (hmix (heq ▸ hp.isPrimePow))
  · exact heq.symm

/-- On every semiprime the coverage of mixed-prime sectors is diagonal:
only that semiprime's own coefficient can contribute. -/
theorem coverage_semiprime (S : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ P ∈ S, P ≠ 1 ∧ ¬IsPrimePow P) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    coverage S w (p * q) = if p * q ∈ S then w (p * q) else 0 := by
  calc
    _ = ∑ P ∈ S, if P = p * q then w (p * q) else 0 := by
      apply Finset.sum_congr rfl
      intro P hP
      have he : (P ∣ p * q ∧ P.Coprime (p * q / P)) ↔ P = p * q := by
        constructor
        · exact fun h ↦ mixed_divisor_semiprime_eq hp hq (hS P hP).1 (hS P hP).2 h.1
        · rintro rfl
          refine ⟨dvd_rfl, ?_⟩
          rw [Nat.div_self (mul_pos hp.pos hq.pos)]
          exact Nat.coprime_one_right _
      simp only [he]
      split_ifs with h
      · rw [h]
      · rfl
    _ = _ := by simp

/-- Exact coverage of distinct physical semiprimes costs at least one
unit of coefficient mass per integer, for every mixed-prime factor family. -/
theorem card_semiprimes_le_mass_of_coverage_one (S T : Finset ℕ) (w : ℕ → ℂ)
    (hS : ∀ P ∈ S, P ≠ 1 ∧ ¬IsPrimePow P)
    (hT : ∀ n ∈ T, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q)
    (hcover : ∀ n ∈ T, coverage S w n = 1) :
    (T.card : ℝ) ≤ ∑ P ∈ S, ‖w P‖ := by
  have htw : ∀ n ∈ T, n ∈ S ∧ w n = 1 := by
    intro n hn
    obtain ⟨p, q, hp, hq, heq⟩ := hT n hn
    have h := hcover n hn
    rw [heq, coverage_semiprime S w hS hp hq] at h
    by_cases hmem : p * q ∈ S
    · rw [if_pos hmem] at h
      exact ⟨by simpa only [heq] using hmem, by simpa only [heq] using h⟩
    · simp [hmem] at h
  calc
    _ = ∑ _n ∈ T, (1 : ℝ) := by simp
    _ = ∑ n ∈ T, ‖w n‖ := Finset.sum_congr rfl (fun n hn ↦ by rw [(htw n hn).2, norm_one])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun n hn ↦ (htw n hn).1)
      (fun _ _ _ ↦ norm_nonneg _)

/-- Each divisor of a squarefree integer is a choice of its distinct primes. -/
theorem card_divisors_eq {P : ℕ} (hP : Squarefree P) :
    (P.divisors.card : ℝ) = 2 ^ P.primeFactors.card := by
  have h := ArithmeticFunction.isMultiplicative_zeta.natCast.prodPrimeFactors_one_add_of_squarefree
    (R := ℝ) hP
  have hs : (∑ d ∈ P.divisors, (ζ : ArithmeticFunction ℝ) d) = (P.divisors.card : ℝ) := by
    trans ∑ _d ∈ P.divisors, (1 : ℝ)
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]
    · simp
  rw [hs] at h
  rw [← h]
  trans ∏ _p ∈ P.primeFactors, (2 : ℝ)
  · apply Finset.prod_congr rfl
    intro p hp
    simp only [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (Nat.prime_of_mem_primeFactors hp).ne_zero, Nat.cast_one]
    norm_num
  · simp

/-- Roughness charges every distinct prime at its actual lower logarithmic scale. -/
theorem card_primeFactors_le_rough_log {P R : ℕ} (hP : Squarefree P) (hR : 1 < R)
    (hrough : ∀ p ∈ P.primeFactors, R ≤ p) :
    (P.primeFactors.card : ℝ) ≤ Real.log P / Real.log R := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  apply (le_div_iff₀ hlogR).mpr
  rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hP]
  calc
    _ = ∑ _p ∈ P.primeFactors, Real.log R := by simp
    _ ≤ _ := Finset.sum_le_sum (fun p hp ↦ Real.log_le_log hRpos (by exact_mod_cast hrough p hp))

/-- The original full-response complexity has a roughness-sensitive bound. -/
theorem complexity_le_rough_log {P R : ℕ} (hP : Squarefree P) (hR : 1 < R)
    (hrough : ∀ p ∈ P.primeFactors, R ≤ p) :
    zetaMoebiusFactorComplexity P ≤ (1 + 2 * Real.log P) *
      Real.exp (2 * Real.log 2 * (Real.log P / Real.log R)) := by
  have hcard := card_primeFactors_le_rough_log hP hR hrough
  have he : (P.divisors.card : ℝ) ^ 2 =
      Real.exp (2 * Real.log 2 * (P.primeFactors.card : ℝ)) := by
    conv_lhs => rw [card_divisors_eq hP, ← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold zetaMoebiusFactorComplexity
  rw [he, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hcard (by positivity)

/-- Every divisor of every nonzero actual window coefficient has the same
explicit complexity budget, with the original prime cutoff unchanged. -/
theorem actual_complexity_le (rho : NontrivialZetaZero) {N n P : ℕ}
    (hN : 1 ≤ N) (hc : zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0)
    (hPn : P ∣ n) (hR : 1 < zetaRightHalfPrimePatternCutoff rho N) :
    zetaMoebiusFactorComplexity P ≤ (1 + 16 * (N : ℝ)) *
      Real.exp (16 * Real.log 2 * N / Real.log (zetaRightHalfPrimePatternCutoff rho N)) := by
  obtain ⟨hw, _, hsf, _, hrough⟩ := zetaRightHalfRoughSquarefreeWindowCoefficient_support rho hN hc
  have hP := hsf.squarefree_of_dvd hPn
  have hlog : Real.log P ≤ 8 * N := by
    have hle : P ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsf.ne_zero) hPn
    exact (Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hP.ne_zero))
      (by exact_mod_cast hle : (P : ℝ) ≤ n)).trans hw.2
  apply (complexity_le_rough_log hP hR (fun p hp ↦
    (hrough p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hPn)).le)).trans
  have hlogR : 0 < Real.log (zetaRightHalfPrimePatternCutoff rho N) :=
    Real.log_pos (by exact_mod_cast hR)
  calc
    _ ≤ (1 + 2 * (8 * (N : ℝ))) *
        Real.exp (2 * Real.log 2 * ((8 * N) / Real.log (zetaRightHalfPrimePatternCutoff rho N))) := by
      gcongr
    _ = _ := by congr 2 <;> ring

/-- The complete divisor complexity grows more slowly than every geometric
base above one, simultaneously over all actual physical divisors. -/
theorem eventually_actual_complexity_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {b : ℝ} (hb : 1 < b) :
    ∀ᶠ N in atTop, ∀ n P : ℕ,
      zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 → P ∣ n →
      zetaMoebiusFactorComplexity P ≤ (1 + 16 * (N : ℝ)) * b ^ N := by
  have hbpos : 0 < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hR := tendsto_zetaRightHalfPrimePatternCutoff rho hrho
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hR)
  filter_upwards [eventually_ge_atTop 1, hR.eventually_ge_atTop 2,
    hlog.eventually_ge_atTop (16 * Real.log 2 / Real.log b)] with N hN hRN hlogN n P hc hPn
  dsimp only [Function.comp_apply] at hlogN
  have hRpos : 0 < Real.log (zetaRightHalfPrimePatternCutoff rho N) :=
    Real.log_pos (by exact_mod_cast (show 1 < zetaRightHalfPrimePatternCutoff rho N by omega))
  have hratio : 16 * Real.log 2 / Real.log (zetaRightHalfPrimePatternCutoff rho N) ≤ Real.log b := by
    apply (div_le_iff₀ hRpos).mpr
    have h := (div_le_iff₀ hlogb).mp hlogN
    nlinarith
  apply (actual_complexity_le rho hN hc hPn (by omega)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ Real.exp ((N : ℝ) * Real.log b) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (N : ℝ) * (16 * Real.log 2 / Real.log (zetaRightHalfPrimePatternCutoff rho N)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg N)
    _ = b ^ N := by rw [Real.exp_nat_mul, Real.exp_log hbpos]

/-- The original response estimate controls complete finite complex families
uniformly in all factors whose full complexity is bounded. -/
theorem exists_factor_family_complexity_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) (B : ℝ),
      (∀ P ∈ S, zetaMoebiusFactorComplexity P ≤ B) →
      ‖∑ P ∈ S, w P * zetaMoebiusFactorFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
          (3 / 2 + I * rho.1.im)‖ ≤
        C * (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) *
          B * ∑ P ∈ S, ‖w P‖ := by
  let p := zetaRightHalfPoleJetFilter rho hrho
  let L : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusFactorFilter_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho)
  refine ⟨C * L + 1, by positivity, ?_⟩
  intro N S w B hB
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  by_cases hS : S.Nonempty
  · have hB0 : 0 ≤ B := by
      obtain ⟨P, hP⟩ := hS
      exact (zetaMoebiusFactorComplexity_nonneg P).trans (hB P hP)
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ P ∈ S, ‖w P‖ * ((C * L + 1) * D * B) := by
        apply Finset.sum_le_sum
        intro P hP
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply (hb p D P N).trans
        calc
          _ ≤ C * D * B * L := by gcongr; exact hB P hP
          _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg D) hB0]
      _ = _ := by rw [← Finset.sum_mul]; ring
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [he]

/-- Complete coprime-factor families from the actual rough support have an
independent geometric bound, with total coefficient mass through `D_N²`.
Factors may vary over the entire physical divisor range. -/
theorem exists_actual_factor_family_budget_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop, ∀ (S : Finset ℕ) (w : ℕ → ℂ),
      (∀ P ∈ S, ∃ n, zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 ∧ P ∣ n) →
      (∑ P ∈ S, ‖w P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2 →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ∑ P ∈ S, w P * zetaMoebiusFactorFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
          (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + 16 * (N : ℝ)) * zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 1 < q := one_lt_zetaMoebiusHeadGrowth hu hu1
  have hsqrt : 1 < Real.sqrt q := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ q), Real.sqrt_nonneg q]
  obtain ⟨C, hC, hb⟩ := exists_factor_family_complexity_bound rho hrho
  refine ⟨C * u + 1, by positivity, ?_⟩
  filter_upwards [eventually_actual_complexity_le rho hrho hsqrt] with N hN S w hS hw
  let D := zetaMoebiusGeometricCutoff q N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith : 0 ≤ q) N)
  have hB : ∀ P ∈ S, zetaMoebiusFactorComplexity P ≤
      (1 + 16 * (N : ℝ)) * (Real.sqrt q) ^ N := by
    intro P hP
    obtain ⟨n, hc, hPn⟩ := hS P hP
    exact hN n P hc hPn
  have hf := hb N S w _ hB
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D * ((1 + 16 * (N : ℝ)) * (Real.sqrt q) ^ N) * ∑ P ∈ S, ‖w P‖) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N) * ((1 + 16 * (N : ℝ)) * (Real.sqrt q) ^ N) * (q ^ N) ^ 2) := by
      gcongr
      exact hw.trans (by gcongr)
    _ = (C * u) * (1 + 16 * (N : ℝ)) * (u * Real.sqrt q * q ^ 3) ^ N := by
      rw [mul_pow, mul_pow, pow_succ, show (q ^ 3) ^ N = (q ^ N) ^ 3 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ = (C * u) * (1 + 16 * (N : ℝ)) * zetaMoebiusCubicRate u ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
    _ ≤ _ := by
      gcongr
      · exact pow_nonneg (zetaMoebiusCubicRate_pos hu).le N
      · linarith

/-- The geometric family allowance vanishes for every hypothetical
right-half zero, including its linear moment-order factor. -/
theorem tendsto_family_allowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N : ℕ ↦ C * (1 + 16 * (N : ℝ)) *
      zetaMoebiusCubicRate (3 / 2 - rho.1.re) ^ N) atTop (𝓝 0) := by
  have h0 := (zetaMoebiusCubicRate_pos (u := 3 / 2 - rho.1.re)
    (by linarith [NontrivialZetaZero.re_lt_one rho])).le
  have h1 := zetaMoebiusCubicRate_lt_one (u := 3 / 2 - rho.1.re) (by linarith)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hn := tendsto_self_mul_const_pow_of_lt_one h0 h1
  have h := (hp.add (hn.const_mul 16)).const_mul C
  convert h using 1
  · funext N
    ring
  · simp

/-- The full source-normalized response tends to zero for all moving
families satisfying the proved physical eligibility and explicit mass budget. -/
theorem tendsto_actual_factor_family (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hS : ∀ᶠ N in atTop,
      (∀ P ∈ S N, ∃ n, zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 ∧ P ∣ n) ∧
      (∑ P ∈ S N, ‖w N P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ P ∈ S N, w N P * zetaMoebiusFactorFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actual_factor_family_budget_bound rho hrho
  apply squeeze_zero_norm' _ (tendsto_family_allowance rho hrho C)
  filter_upwards [hb, hS] with N hN hSN
  exact hN (S N) (w N) hSN.1 hSN.2

/-- The same decay holds for the genuine original arithmetic sector
series. Every coprime multiple, cutoff, logarithmic moment and complex
phase remains in the sum; this is not a restricted rough-sector bound. -/
theorem tendsto_actual_factor_family_arithmetic (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hS : ∀ᶠ N in atTop,
      (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P ∧
        ∃ n, zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 ∧ P ∣ n) ∧
      (∑ P ∈ S N, ‖w N P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ P ∈ S N, w N P * ∑' n,
        zetaMoebiusFactorSectorCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) P n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_actual_factor_family rho hrho S w
    (hS.mono (fun N h ↦ ⟨fun P hP ↦ (h.1 P hP).2.2.2, h.2⟩))).congr'
  filter_upwards [hS] with N hN
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hP0, hP1, hmix, _⟩ := hN.1 P hP
  rw [(hasSum_zetaMoebiusFactorFilter _ _ N hP0 hP1 hmix (by norm_num)).tsum_eq]

/-- The exact covered original arithmetic sum decays for every eligible
moving family within the coefficient budget. No claim that this coverage
equals the full surviving rough squarefree mask is made or assumed. -/
theorem tendsto_actual_coverage (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hS : ∀ᶠ N in atTop,
      (∀ P ∈ S N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P ∧
        ∃ n, zetaRightHalfRoughSquarefreeWindowCoefficient rho N n ≠ 0 ∧ P ∣ n) ∧
      (∑ P ∈ S N, ‖w N P‖) ≤
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      zetaMoebiusLogTailCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n *
      coverage (S N) (w N) n *
      zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_actual_factor_family rho hrho S w
    (hS.mono (fun N h ↦ ⟨fun P hP ↦ (h.1 P hP).2.2.2, h.2⟩))).congr'
  filter_upwards [hS] with N hN
  rw [(hasSum_coverage _ _ N (S N) (w N)
    (fun P hP ↦ ⟨(hN.1 P hP).1, (hN.1 P hP).2.1, (hN.1 P hP).2.2.1⟩)
    (by norm_num)).tsum_eq]

end
end RiemannGaussian.RoughCoprimeFactor
