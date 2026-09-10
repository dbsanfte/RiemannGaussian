/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughMoebiusMixedDecay

/-!
# Exact divisor reflection of the compensated arithmetic carrier

Divisor complementation changes the strict tail `D < d` into the prefix
through `n / (D + 1)`. On the literal rough squarefree composite support,
the compensated coefficient is minus the mixed Möbius coefficient at this
integer-dependent cutoff. A fixed-cutoff estimate cannot be applied to
this response without controlling that dependence.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughMoebiusHyperbola
noncomputable section
open RoughMoebiusIncidence

/-- A divisor prefix can be written over the complete divisor set,
with its original inclusive endpoint retained. -/
theorem sum_prefix_eq_divisors (D : ℕ) {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, if d ∣ n then f d else 0) =
      ∑ d ∈ n.divisors, if d ≤ D then f d else 0 := by
  have he : n.divisors.filter (fun d ↦ d ≤ D) =
      (Finset.Icc 1 D).filter (fun d ↦ d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hD⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, hD⟩, hd⟩
    · rintro ⟨⟨_, hD⟩, hd⟩
      exact ⟨⟨hd, hn.ne'⟩, hD⟩
  rw [← Finset.sum_filter, ← he, Finset.sum_filter]

/-- The strict divisor tail reflects to precisely the inclusive
integer cutoff `n / (D + 1)`, with no omitted boundary divisor. -/
theorem divisor_reflected_cutoff (D : ℕ) {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    D < n / d ↔ d ≤ n / (D + 1) := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  rw [Nat.le_div_iff_mul_le (by omega)]
  constructor
  · intro h
    exact (Nat.mul_le_mul_left d h).trans_eq (Nat.mul_div_cancel' hd)
  · intro h
    exact Nat.le_of_mul_le_mul_left
      (h.trans_eq (Nat.mul_div_cancel' hd).symm) hd0

/-- For squarefree integers the Möbius sign of the complementary
divisor retains the full parity of the original integer. -/
theorem moebius_cofactor {n d : ℕ} (hsf : Squarefree n) (hd : d ∣ n) :
    (μ (n / d) : ℂ) = (μ n : ℂ) * (μ d : ℂ) := by
  have hp : d * (n / d) = n := Nat.mul_div_cancel' hd
  have hc : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (hp.symm ▸ hsf)
  have hm : (μ d : ℂ) * (μ (n / d) : ℂ) = (μ n : ℂ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    rw [hp] at h
    exact_mod_cast h.symm
  have hs : (μ d : ℂ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsf.squarefree_of_dvd hd)
  calc
    _ = (μ d : ℂ) ^ 2 * (μ (n / d) : ℂ) := by rw [hs, one_mul]
    _ = (μ d : ℂ) * ((μ d : ℂ) * (μ (n / d) : ℂ)) := by ring
    _ = _ := by rw [hm]; ring

/-- Complementation reflects every weighted Möbius tail exactly.
The weight and total squarefree parity remain inside the identity. -/
theorem weighted_tail_reflection (D : ℕ) {n : ℕ} (hsf : Squarefree n) (f : ℕ → ℂ) :
    (∑ d ∈ n.divisors, if D < d then (μ d : ℂ) * f (n / d) else 0) =
      (μ n : ℂ) * ∑ d ∈ Finset.Icc 1 (n / (D + 1)),
        if d ∣ n then (μ d : ℂ) * f d else 0 := by
  rw [sum_prefix_eq_divisors _ (Nat.pos_of_ne_zero hsf.ne_zero)]
  rw [← Nat.sum_div_divisors n (fun d ↦ if D < d then (μ d : ℂ) * f (n / d) else 0),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn := Nat.dvd_of_mem_divisors hd
  simp only [divisor_reflected_cutoff D (Nat.pos_of_ne_zero hsf.ne_zero) hdn,
    Nat.div_div_self hdn hsf.ne_zero, moebius_cofactor hsf hdn]
  split_ifs <;> ring

/-- The two complementary masks have opposite total Möbius parity
on every nonunit squarefree integer. -/
theorem mask_reflection (D : ℕ) {n : ℕ} (hsf : Squarefree n) (hn1 : n ≠ 1) :
    mask D n + (μ n : ℂ) * mask (n / (D + 1)) n = 0 := by
  have hn := Nat.pos_of_ne_zero hsf.ne_zero
  have ht := weighted_tail_reflection D hsf (fun _ ↦ 1)
  simp only [mul_one] at ht
  change (∑ d ∈ n.divisors, if D < d then (μ d : ℂ) else 0) =
    (μ n : ℂ) * mask (n / (D + 1)) n at ht
  rw [← ht, mask, sum_prefix_eq_divisors D hn, ← Finset.sum_add_distrib]
  calc
    _ = ∑ d ∈ n.divisors, (μ d : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : d ≤ D <;> simp [h, Nat.lt_of_not_ge, Nat.not_lt_of_ge]
    _ = 0 := by
      have h := congrArg (fun f : ArithmeticFunction ℂ ↦ f n)
        (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
      simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
        ArithmeticFunction.one_apply, if_neg hn1] using h

/-- The original rough squarefree tail is the complementary
logarithmic mask with its exact total Möbius sign. -/
theorem roughCoefficient_reflection (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hsf : Squarefree n) (hcomp : ¬n.Prime)
    (hrough : ¬∃ a ∈ S, a ∣ n) :
    zetaRoughSquarefreeCoefficient D S n = (μ n : ℂ) * logMask (n / (D + 1)) n := by
  rw [zetaRoughSquarefreeCoefficient_eq_tail_on_support D hD S hS hsf hcomp hrough,
    zetaMoebiusLogTailCoefficient_divisors]
  exact weighted_tail_reflection D hsf (fun d ↦ (Real.log d : ℂ))

/-- The fully supported compensated coefficient is minus the mixed
term at the reflected, integer-dependent cutoff. Zero, the unit, primes,
nonsquarefree integers and excluded sieve terms are included. -/
theorem compensatedCoefficient_reflection (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    RoughMoebiusIncidence.coefficient D D S n =
      -RoughMoebiusMixed.coefficient (n / (D + 1)) S n := by
  by_cases hp : n.Prime
  · rw [RoughMoebiusMixed.coefficient_prime _ S hp]
    have hz : zetaRoughSquarefreeCoefficient D S n = 0 := by
      simp [zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient,
        zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hp.primeFactors]
    simp [RoughMoebiusIncidence.coefficient, hz]
  by_cases hsf : Squarefree n
  · by_cases hs : ∃ a ∈ S, a ∣ n
    · simp [RoughMoebiusIncidence.coefficient, zetaRoughSquarefreeCoefficient,
        RoughMoebiusMixed.coefficient, RoughSquarefreeBare.coefficient, hs]
    · by_cases hn1 : n = 1
      · subst n
        have hdiv : 1 / (D + 1) = 0 := Nat.div_eq_of_lt (by omega)
        simp [RoughMoebiusIncidence.coefficient, zetaRoughSquarefreeCoefficient,
          zetaSquarefreeCoefficient, zetaMoebiusSievedPrimeCoefficient,
          zetaMoebiusDistinctPrimeCoefficient, RoughMoebiusMixed.coefficient, hdiv, logMask]
      have hm := mask_reflection D hsf hn1
      have hμ : (μ n : ℂ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [RoughMoebiusIncidence.coefficient, roughCoefficient_reflection D hD S hS hsf hp hs]
      simp only [RoughMoebiusMixed.coefficient, RoughSquarefreeBare.coefficient,
        if_pos (show Squarefree n ∧ (¬∃ a ∈ S, a ∣ n) ∧ 1 ∣ n from ⟨hsf, hs, one_dvd n⟩), one_mul]
      linear_combination (μ n : ℂ) * logMask (n / (D + 1)) n * hm -
        mask (n / (D + 1)) n * logMask (n / (D + 1)) n * hμ
  · simp [RoughMoebiusIncidence.coefficient, zetaRoughSquarefreeCoefficient,
      zetaSquarefreeCoefficient, RoughMoebiusMixed.coefficient,
      RoughSquarefreeBare.coefficient, hsf]

/-- The nonnegative square coefficient is exactly the sum of the
fixed-cutoff and complementary-cutoff mixed terms. Neither sign is lost. -/
theorem squareCoefficient_eq_complementary_mixed (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    RoughMoebiusMixed.squareCoefficient D S n =
      RoughMoebiusMixed.coefficient D S n + RoughMoebiusMixed.coefficient (n / (D + 1)) S n := by
  have h := RoughMoebiusMixed.compensatedCoefficient_eq_neg_square_add_mixed D hD S hS n
  rw [compensatedCoefficient_reflection D hD S hS n] at h
  linear_combination h

/-- The exact reflected arithmetic series, whose cutoff depends
on its physical integer rather than only on the moment order. -/
def response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, RoughMoebiusMixed.coefficient (n / (D + 1)) S n * zetaPrimeFilterKernel p N s n

/-- The cutoff `n / 2` recovers the entire rough squarefree composite
logarithmic coefficient, including every excluded index. Thus dependence
on the summation integer cannot be removed from a mixed-term estimate. -/
theorem coefficient_half_cutoff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    RoughMoebiusMixed.coefficient (n / 2) S n =
      (zetaRoughSquarefreeCompositeLogWeight S n : ℂ) := by
  have h := compensatedCoefficient_reflection 1 le_rfl S hS n
  simpa [RoughMoebiusIncidence.coefficient, RoughMoebiusIncidence.mask,
    zetaRoughSquarefreeCoefficient_one S hS] using h.symm

/-- At original cutoff one the reflected response is exactly the
complete composite logarithmic response, with the same complex kernel.
Its genuine convergence for `Re s > 1` follows from `hasSum_response`. -/
theorem response_one (p : Polynomial ℂ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) (s : ℂ) :
    response p 1 S N s = zetaRoughSquarefreeCompositeLogFilter p S N s := by
  unfold response zetaRoughSquarefreeCompositeLogFilter
  simp only [show (1 + 1 : ℕ) = 2 by norm_num, coefficient_half_cutoff S hS]

/-- The reflected series genuinely converges and equals minus the
complete compensated series, with the original kernel unchanged. -/
theorem hasSum_response (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ RoughMoebiusMixed.coefficient (n / (D + 1)) S n * zetaPrimeFilterKernel p N s n)
      (-(∑' n, RoughMoebiusIncidence.coefficient D D S n * zetaPrimeFilterKernel p N s n)) := by
  have h := (RoughMoebiusIncidence.hasSum_coefficient p D D N hD hD S hS hs).summable.hasSum.neg
  apply h.congr_fun
  intro n
  rw [compensatedCoefficient_reflection D hD S hS n]
  ring

/-- The adaptive reflected series at the original zero-source normalization. -/
def actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    response (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- Reflection preserves the complete response with the exact
opposite sign; it does not invoke a fixed-cutoff decay estimate. -/
theorem actualResponse_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    actualResponse rho hrho N = -RoughMoebiusIncidence.response rho hrho N
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) := by
  rw [actualResponse, response, (hasSum_response _ _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) N (by norm_num)).tsum_eq]
  exact mul_neg _ _

/-- The reflected mixed response carries the entire positive
multiplicity source. Pointwise adaptation of a cutoff is therefore a
substantive distinction from the already controlled fixed-cutoff family. -/
theorem tendsto_actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualResponse rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have h := (RoughMoebiusIncidence.tendsto_response rho hrho
    (fun N ↦ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (Eventually.of_forall (fun N ↦ by
      have hD := zetaRightHalfPoleJetCutoff_pos rho hrho N
      exact ⟨hD, by simpa using pow_le_pow_right₀ hD (by norm_num : 1 ≤ 4)⟩))).neg
  simp only [neg_neg] at h
  exact h.congr (fun N ↦ (actualResponse_eq rho hrho N).symm)

private theorem norm_mask_le (D n : ℕ) : ‖mask D n‖ ≤ D := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ‖if d ∣ n then (μ d : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      · simp
    _ = _ := by simp

/-- The adaptive mixed coefficient has the original majorant
times only the fixed head size, despite its much larger reflected cutoff. -/
theorem norm_reflected_coefficient_le (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    ‖RoughMoebiusMixed.coefficient (n / (D + 1)) S n‖ ≤ D * zetaMoebiusLogMajorant n := by
  rw [← norm_neg, ← compensatedCoefficient_reflection D hD S hS n,
    RoughMoebiusIncidence.coefficient, norm_mul]
  exact mul_le_mul (norm_mask_le D n) (norm_zetaRoughSquarefreeCoefficient_le D S n)
    (norm_nonneg _) (Nat.cast_nonneg D)

private theorem headGrowth_le {u : ℝ} (hu : 1 / 2 < u) : zetaMoebiusHeadGrowth u ≤ 6 / 5 := by
  have hu0 : 0 < u := by linarith
  have hs : 25 / 36 < Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have ht : 5 / 6 < Real.sqrt (Real.sqrt u) := by
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg u), Real.sqrt_nonneg (Real.sqrt u)]
  unfold zetaMoebiusHeadGrowth
  rw [← one_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu0))).mpr
  linarith

/-- Every selected set of reflected terms through the cubic product
cutoff has an independent geometric bound, uniformly in its complex filter
and ordinate. The full extra Möbius mask is paid for in the rate. -/
theorem norm_normalized_reflected_head_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (T : Finset ℕ)
    (hT : ∀ n ∈ T, n ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N ^ 3) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      RoughMoebiusMixed.coefficient
        (n / (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u) N + 1)) S n *
          zetaPrimeFilterKernel p N (3 / 2 + I * y) n‖ ≤
      zetaArithmeticSmallProductConstant p * (9 / 10 : ℝ) ^ N := by
  let q := zetaMoebiusHeadGrowth u
  let D := zetaMoebiusGeometricCutoff q N
  let C := zetaArithmeticSmallProductConstant p
  have hu0 : 0 < u := by linarith
  have hq : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth hu0 hu1).le
  have hD : 1 ≤ D := Nat.le_floor (by simpa using one_le_pow₀ hq (n := N))
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDq : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg (by linarith : 0 ≤ q) N)
  have hq6 : q ≤ 6 / 5 := headGrowth_le hu
  have hC : 0 ≤ C := zetaArithmeticSmallProductConstant_nonneg p
  let a := fun n ↦ RoughMoebiusMixed.coefficient (n / (D + 1)) S n / (D : ℂ)
  have ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n := by
    intro n
    dsimp [a]
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hD0).mpr
    simpa only [mul_comm] using norm_reflected_coefficient_le D hD S hS n
  have hb := norm_normalized_sum_zetaArithmetic_cubic_product_le a ha p N y hu hu1 T hT
  simp only [a, div_mul_eq_mul_div] at hb
  rw [← Finset.sum_div, ← mul_div_assoc, norm_div, Complex.norm_natCast] at hb
  have hb' := (div_le_iff₀ hD0).mp hb
  calc
    _ ≤ C * (3 / 4 : ℝ) ^ N * (D : ℝ) := hb'
    _ ≤ C * (3 / 4 : ℝ) ^ N * q ^ N := by gcongr
    _ = C * (q * (3 / 4)) ^ N := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity)
      nlinarith

/-- Above the cubic physical cutoff, the reflected divisor cutoff
is at least quadratic up to the explicit additive head correction. -/
theorem reflected_cutoff_large {D n : ℕ} (hn : D ^ 3 < n) :
    D ^ 2 < n / (D + 1) + D := by
  by_contra h
  have hle : n / (D + 1) + D ≤ D ^ 2 := by omega
  have hm := Nat.mul_le_mul_right (D + 1) hle
  have hdiv := Nat.mod_add_div n (D + 1)
  have hmod := Nat.mod_lt n (show 0 < D + 1 by omega)
  nlinarith

/-- The complete finite small-product part of the actual reflected source. -/
def actualHead (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑ n ∈ Finset.Iic (D ^ 3),
    RoughMoebiusMixed.coefficient (n / (D + 1)) (zetaRightHalfPrimePatternPrimes rho N) n *
      zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n

/-- The actual reflected head has an independently proved geometric
allowance; no zero-source limit enters this bound. -/
theorem norm_actualHead_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    ‖actualHead rho hrho N‖ ≤
      zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (9 / 10 : ℝ) ^ N := by
  exact norm_normalized_reflected_head_le _ N rho.1.im
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) _
    (fun _ hn ↦ Finset.mem_Iic.mp hn)

/-- The entire reflected small-product contribution tends to zero
despite its adaptive divisor cutoff and complete Möbius multiplicity. -/
theorem tendsto_actualHead (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualHead rho hrho) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_actualHead_le rho hrho)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num : (9 / 10 : ℝ) < 1)).const_mul
        (zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho))

/-- The literal remaining reflected series is supported strictly
above the cubic product cutoff. Its complex kernel is unchanged. -/
def tailResponse (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, if D ^ 3 < n then
    RoughMoebiusMixed.coefficient (n / (D + 1)) S n * zetaPrimeFilterKernel p N s n else 0

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
      RoughMoebiusMixed.coefficient (n / (D + 1)) S n * zetaPrimeFilterKernel p N s n else 0) := by
  exact summable_above (hasSum_response p D hD S hS N hs).summable (D ^ 3)

/-- The complete reflected response partitions into its finite head
and the literal infinite high-product series with no discarded boundary. -/
theorem tailResponse_eq (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    tailResponse p D S N s = response p D S N s -
      ∑ n ∈ Finset.Iic (D ^ 3),
        RoughMoebiusMixed.coefficient (n / (D + 1)) S n * zetaPrimeFilterKernel p N s n := by
  exact tsum_above_eq (hasSum_response p D hD S hS N hs).summable (D ^ 3)

/-- The unchanged source normalization of the literal reflected high-product series. -/
def actualTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    tailResponse (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The exact signed source partition precedes either estimate or limit. -/
theorem actualTail_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    actualTail rho hrho N = actualResponse rho hrho N - actualHead rho hrho N := by
  rw [actualTail, tailResponse_eq _ _ (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) N (by norm_num), mul_sub]
  rfl

/-- After the independent small-product estimate, the entire
multiplicity source remains in the actual reflected high-product series.
Its strict signed upper bound is still an open arithmetic obligation. -/
theorem tendsto_actualTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (actualTail rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have h := (tendsto_actualResponse rho hrho).sub (tendsto_actualHead rho hrho)
  simp only [sub_zero] at h
  exact h.congr (fun N ↦ (actualTail_eq rho hrho N).symm)

end
end RiemannGaussian.RoughMoebiusHyperbola
