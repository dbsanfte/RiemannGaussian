/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughDivisorIncidence
import RiemannGaussian.ZetaRoughPrimeIncidenceSource

/-!
# Exact Möbius compensation with all divisor intersections retained

The all-family divisor bound controls the complete truncated Möbius
incidence sum. Its coefficients are mathematically fixed and include every
prime intersection fitting the cutoff. The original source is preserved
for every admissible moving divisor cutoff, with an independent allowance.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.RoughMoebiusIncidence
noncomputable section

/-- The complete truncated Möbius divisor sum, with the original
integer endpoint and all prime intersections retained. -/
def mask (Y n : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 Y, if d ∣ n then (μ d : ℂ) else 0

/-- Every eligible nontrivial squarefree divisor through the chosen
cutoff; its prime factors avoid the original small-prime sieve. -/
def factors (Y : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun P ↦ Squarefree P ∧ P ≠ 1 ∧ ∀ a ∈ P.primeFactors, a ∉ S)

/-- Möbius compensation multiplies the original rough squarefree
coefficient by its full truncated divisor sum. -/
def coefficient (D Y : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  mask Y n * zetaRoughSquarefreeCoefficient D S n

/-- Every selected divisor has exactly the hypotheses needed by the
all-family arithmetic bound. -/
theorem mem_factors {Y P : ℕ} {S : Finset ℕ} :
    P ∈ factors Y S ↔ Squarefree P ∧ P ≠ 1 ∧ P ≤ Y ∧ ∀ a ∈ P.primeFactors, a ∉ S := by
  simp only [factors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, hPY⟩, hsf, hP1, hPS⟩
    exact ⟨hsf, hP1, hPY, hPS⟩
  · rintro ⟨hsf, hP1, hPY, hPS⟩
    exact ⟨⟨Nat.pos_of_ne_zero hsf.ne_zero, hPY⟩, hsf, hP1, hPS⟩

/-- On rough squarefree integers the full divisor mask is exactly
one plus all retained nontrivial Möbius incidences, with no missing overlaps. -/
theorem mask_eq_one_add_weight (Y : ℕ) (hY : 1 ≤ Y) (S : Finset ℕ) {n : ℕ}
    (hsf : Squarefree n) (hrough : ¬∃ a ∈ S, a ∣ n) :
    mask Y n = 1 + RoughPrimeIncidence.weight (factors Y S) (fun d ↦ (μ d : ℂ)) n := by
  let f := fun d : ℕ ↦ if d ∣ n then (μ d : ℂ) else 0
  have h1 : 1 ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨le_rfl, hY⟩
  have hsub : factors Y S ⊆ (Finset.Icc 1 Y).erase 1 := by
    intro d hd
    obtain ⟨hdSF, hd1, hdY, _⟩ := mem_factors.mp hd
    exact Finset.mem_erase.mpr ⟨hd1, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hdSF.ne_zero, hdY⟩⟩
  have hsum : (∑ d ∈ factors Y S, f d) = ∑ d ∈ (Finset.Icc 1 Y).erase 1, f d := by
    apply Finset.sum_subset hsub
    intro d hd hdF
    have hnot : ¬d ∣ n := by
      intro hdn
      have hdSF : Squarefree d := hsf.squarefree_of_dvd hdn
      have hdPS : ∀ a ∈ d.primeFactors, a ∉ S := by
        intro a ha haS
        exact hrough ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hdn⟩
      exact hdF (mem_factors.mpr ⟨hdSF, (Finset.mem_erase.mp hd).1,
        (Finset.mem_Icc.mp (Finset.mem_erase.mp hd).2).2, hdPS⟩)
    simp [f, hnot]
  unfold mask RoughPrimeIncidence.weight
  change (∑ d ∈ Finset.Icc 1 Y, f d) = 1 + ∑ d ∈ factors Y S, f d
  rw [hsum, ← Finset.add_sum_erase _ _ h1]
  simp [f]

/-- The exact original arithmetic coefficient plus all Möbius
divisor marks is the compensated coefficient, including zero-support cases. -/
theorem coefficient_eq_add_fibres (D Y : ℕ) (hY : 1 ≤ Y) (S : Finset ℕ) (n : ℕ) :
    coefficient D Y S n = zetaRoughSquarefreeCoefficient D S n +
      ∑ P ∈ factors Y S, (μ P : ℂ) * RoughPrimeIncidence.fibreCoefficient D S P n := by
  by_cases hc : zetaRoughSquarefreeCoefficient D S n = 0
  · simp [coefficient, RoughPrimeIncidence.fibreCoefficient, hc]
  have hrough : ¬∃ a ∈ S, a ∣ n := by
    intro h
    exact hc (by simp [zetaRoughSquarefreeCoefficient, h])
  have hsf : Squarefree n := by
    by_contra h
    exact hc (by simp [zetaRoughSquarefreeCoefficient, hrough, zetaSquarefreeCoefficient, h])
  rw [coefficient, mask_eq_one_add_weight Y hY S hsf hrough, add_mul, one_mul]
  congr 1
  rw [RoughPrimeIncidence.weight, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun P _ ↦ by
    by_cases hPn : P ∣ n <;> simp [RoughPrimeIncidence.fibreCoefficient, hPn])

/-- The compensated series genuinely converges and retains the full
original complex response plus the complete finite Möbius family. -/
theorem hasSum_coefficient (p : Polynomial ℂ) (D Y N : ℕ) (hD : 1 ≤ D) (hY : 1 ≤ Y)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient D Y S n * zetaPrimeFilterKernel p N s n)
      (zetaRoughSquarefreeFilter p D S N s +
        ∑ P ∈ factors Y S, (μ P : ℂ) * RoughPrimeIncidence.fibre p D S N s P) := by
  have hm := hasSum_sum (s := factors Y S) (fun P _ ↦
    (RoughPrimeIncidence.summable_fibre p D N hD S hS P hs).hasSum.mul_left (μ P : ℂ))
  apply ((summable_zetaRoughSquarefreeFilter p D N hD S hS hs).hasSum.add hm).congr_fun
  intro n
  rw [coefficient_eq_add_fibres D Y hY S n, add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun P _ ↦ by ring)

/-- Completing the divisor range gives the exact Möbius unit law. -/
theorem mask_eq_unit {Y n : ℕ} (hn : 0 < n) (hnY : n ≤ Y) :
    mask Y n = if n = 1 then 1 else 0 := by
  have he : mask Y n = ∑ d ∈ n.divisors, (μ d : ℂ) := by
    unfold mask
    calc
      _ = ∑ d ∈ n.divisors, if d ∣ n then (μ d : ℂ) else 0 := by
        symm
        apply Finset.sum_subset (fun d hd ↦ Finset.mem_Icc.mpr
          ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)).trans hnY⟩)
        intro d _ hd
        have hnot : ¬d ∣ n := fun h ↦ hd (Nat.mem_divisors.mpr ⟨h, hn.ne'⟩)
        simp [hnot]
      _ = _ := Finset.sum_congr rfl (fun d hd ↦ if_pos (Nat.dvd_of_mem_divisors hd))
  rw [he]
  have h := congrArg (fun f : ArithmeticFunction ℂ ↦ f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

/-- Every compensated integer at most the mask cutoff disappears
exactly. This is algebraic cancellation, not a magnitude estimate. -/
theorem coefficient_eq_zero_of_le (D Y : ℕ) (S : Finset ℕ) {n : ℕ} (hn : n ≤ Y) :
    coefficient D Y S n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [coefficient, zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient]
  by_cases hn1 : n = 1
  · subst n
    simp [coefficient, zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient,
      zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient]
  simp [coefficient, mask_eq_unit (Nat.pos_of_ne_zero hn0) hn, hn1]

/-- A prime beyond the mask cutoff contributes no new truncated
divisor. Its entire cofactor keeps the same exact Möbius mask. -/
theorem mask_large_prime {Y p : ℕ} (hp : p.Prime) (hYp : Y < p) (m : ℕ) :
    mask Y (p * m) = mask Y m := by
  unfold mask
  apply Finset.sum_congr rfl
  intro d hd
  have hpd : ¬p ∣ d := by
    intro h
    have hle := Nat.le_of_dvd (Finset.mem_Icc.mp hd).1 h
    have hdY := (Finset.mem_Icc.mp hd).2
    omega
  have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
  simp only [hcop.dvd_mul_left]

/-- Every large-prime term with a nontrivial complete small cofactor
vanishes after Möbius compensation, without a separate bound on that sector. -/
theorem coefficient_large_prime_small_cofactor_zero (D Y : ℕ) (S : Finset ℕ)
    {p m : ℕ} (hp : p.Prime) (hYp : Y < p) (hm : 1 < m) (hmY : m ≤ Y) :
    coefficient D Y S (p * m) = 0 := by
  rw [coefficient, mask_large_prime hp hYp m, mask_eq_unit (by omega) hmY, if_neg (by omega), zero_mul]

/-- The logarithmic companion of the same truncated Möbius mask. -/
def logMask (D n : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ n then (μ d : ℂ) * (Real.log d : ℂ) else 0

/-- The original rough squarefree composite coefficient is exactly
its Möbius mask times the full logarithm plus its signed logarithmic companion. -/
theorem roughCoefficient_eq_mask_log (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hsf : Squarefree n) (hcomp : ¬n.Prime)
    (hrough : ¬∃ a ∈ S, a ∣ n) :
    zetaRoughSquarefreeCoefficient D S n =
      -(mask D n) * (Real.log n : ℂ) + logMask D n := by
  have he : zetaRoughSquarefreeCoefficient D S n = zetaDivisibilityPrefixCoefficient D 1 n := by
    rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS n]
    simp [zetaRoughSquarefreePrefixCoefficient, zetaSquarefreeDivisibilityPrefixCoefficient,
      zetaRoughPrimeCoefficient, hrough, hsf, hcomp]
  have hlog {d : ℕ} (hd : d ∈ Finset.Icc 1 D) (hdn : d ∣ n) :
      Real.log (n / d : ℕ) = Real.log n - Real.log d := by
    have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [Nat.cast_div hdn (by exact_mod_cast hd0),
      Real.log_div (by exact_mod_cast hsf.ne_zero) (by exact_mod_cast hd0)]
  rw [he]
  have hp : zetaDivisibilityPrefixCoefficient D 1 n =
      -(∑ d ∈ Finset.Icc 1 D, if d ∣ n then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) := by
    simp [zetaDivisibilityPrefixCoefficient, zetaMultipleLogCoefficient, mul_ite]
  rw [hp, mask, logMask, neg_mul, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn, hlog hd hdn, Complex.ofReal_sub]
    ring
  · simp [hdn]

/-- At the original divisor cutoff, full Möbius compensation
produces an exact square and its mixed logarithmic term. Both are retained. -/
theorem coefficient_eq_square_add_mixed (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hsf : Squarefree n) (hcomp : ¬n.Prime)
    (hrough : ¬∃ a ∈ S, a ∣ n) :
    coefficient D D S n = -(mask D n) ^ 2 * (Real.log n : ℂ) + mask D n * logMask D n := by
  rw [coefficient, roughCoefficient_eq_mask_log D hD S hS hsf hcomp hrough]
  ring

/-- The exact Möbius mask is real before it is multiplied by the
complex arithmetic kernel. -/
theorem mask_im (Y n : ℕ) : (mask Y n).im = 0 := by
  unfold mask
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro d _
  split_ifs <;> simp

/-- The square exposed by the exact compensation is nonnegative
as a real coefficient; its mixed logarithmic companion is not discarded. -/
theorem mask_square_re_nonneg (Y n : ℕ) : 0 ≤ (mask Y n ^ 2).re := by
  rw [pow_two, Complex.mul_re, mask_im]
  simpa only [mul_zero, sub_zero, pow_two] using sq_nonneg (mask Y n).re

/-- The actual source-normalized response with an arbitrary
admissible Möbius divisor cutoff. -/
def response (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N Y : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
    coefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) Y
      (zetaRightHalfPrimePatternPrimes rho N) n *
      zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n

private theorem norm_moebius_le_one (P : ℕ) : ‖(μ P : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := P)

/-- The exact full source comparison retains the signs of the entire
finite Möbius family before estimating any error. -/
theorem response_eq_source_add_fibres (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N Y : ℕ) (hY : 1 ≤ Y) :
    response rho hrho N Y =
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) +
        ∑ P ∈ factors Y (zetaRightHalfPrimePatternPrimes rho N),
          (μ P : ℂ) * RoughPrimeIncidence.actualFibre rho hrho N P := by
  rw [response, (hasSum_coefficient _ _ Y N (zetaRightHalfPoleJetCutoff_pos rho hrho N) hY _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)).tsum_eq,
    mul_add, Finset.mul_sum (factors Y _)]
  congr 1
  exact Finset.sum_congr rfl (fun P _ ↦ by unfold RoughPrimeIncidence.actualFibre; ring)

/-- Every admissible mask cutoff has the same independent geometric
error bound relative to the original full source. The constant is uniform
over the cutoff, with every higher prime intersection included. -/
theorem exists_response_error_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y : ℕ), 1 ≤ Y →
      Y ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 →
      ‖response rho hrho N Y -
        ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
  obtain ⟨C, hC, hb⟩ := RoughDivisorIncidence.exists_actual_sum_norm_bound rho hrho
  refine ⟨C, hC, ?_⟩
  intro N Y hY hY4
  rw [response_eq_source_add_fibres rho hrho N Y hY, add_sub_cancel_left]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun P _ ↦ ?_)).trans
    (hb N (factors Y (zetaRightHalfPrimePatternPrimes rho N)) (fun P hP ↦ ?_))
  · rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (norm_moebius_le_one P)
      (norm_nonneg (RoughPrimeIncidence.actualFibre rho hrho N P))
  · obtain ⟨hSF, hP1, hPY, hPS⟩ := mem_factors.mp hP
    exact ⟨hSF, hP1, hPY.trans hY4, hPS⟩

/-- Every moving admissible mask cutoff retains the full original
negative-multiplicity source; the Möbius coefficients have no search parameter. -/
theorem tendsto_response (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (Y : ℕ → ℕ)
    (hY : ∀ᶠ N in atTop, 1 ≤ Y N ∧ Y N ≤
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4) :
    Tendsto (fun N ↦ response rho hrho N (Y N)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hf := RoughDivisorIncidence.tendsto_actual_weighted_fibres rho hrho
    (fun N ↦ factors (Y N) (zetaRightHalfPrimePatternPrimes rho N)) (fun _ P ↦ (μ P : ℂ))
    (by
      filter_upwards [hY] with N hN
      intro P hP
      obtain ⟨hSF, hP1, hPY, hPS⟩ := mem_factors.mp hP
      exact ⟨hSF, hP1, hPY.trans hN.2, hPS⟩)
    (Eventually.of_forall (fun _ _ _ ↦ norm_moebius_le_one _))
  have h := (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho).add hf
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [hY] with N hN
  exact (response_eq_source_add_fibres rho hrho N (Y N) hN.1).symm

/-- The new full source is carried strictly beyond `D_N^4`, with
all original coefficients multiplied by their exact truncated Möbius mask. -/
theorem tendsto_fourth_cutoff_response (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ response rho hrho N
      ((zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply tendsto_response rho hrho _
  filter_upwards [] with N
  exact ⟨one_le_pow₀ (zetaRightHalfPoleJetCutoff_pos rho hrho N), le_rfl⟩

/-- Any admissible moving cutoff may be used for a strict cofinal
signed contradiction. The arithmetic inequality is still an open premise. -/
theorem false_of_cofinal_response_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (Y : ℕ → ℕ)
    (hY : ∀ᶠ N in atTop, 1 ≤ Y N ∧ Y N ≤
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4)
    {ε : ℝ} (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, -1 + ε ≤ (response rho hrho N (Y N)).re) : False := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_response rho hrho Y hY)
  have hb := ge_of_tendsto_of_frequently h hbound
  simp only [Complex.neg_re, Complex.natCast_re] at hb
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

end
end RiemannGaussian.RoughMoebiusIncidence
