/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughDivisorLinearBound
import RiemannGaussian.ZetaRoughPrimeLogSource

/-!
# Larger prime-logarithm deletion from complete lcm bounds

The full bare marked response retains its physical divisor correction.
Summing all prime insertions and ordered pairs then costs D*sqrt(D)*log(D).
The actual small-prime correction consequently decays uniformly through
D_N squared. The full source survives with both prime and cofactor beyond
that larger cutoff, so every nonzero product lies beyond D_N to the fourth
power. The original kernel and all prime intersections remain intact; an
independent strict signed upper bound for this survivor is still open.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section
namespace RoughSquarefreeBare

/-- Logarithm removal retains the entire lcm mass in the bound on the
genuine marked bare series, including all prime-sieve intersections. -/
theorem exists_response_lcm_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N R : ℕ) (S : Finset ℕ) (P : ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖response p S P (N + 1) (3 / 2 + I * y)‖ ≤
        C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) * lcmSqrtFactorMass P := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  let w := primeSquareCorrectedWeight τ
  refine ⟨C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p N R S P hS
  have hm : 0 ≤ lcmSqrtFactorMass P := lcmSqrtFactorMass_nonneg P
  have hnonneg : 0 ≤ (C * Real.exp (2 * primeSquareWeightMass τ)) *
      Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
        (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) * lcmSqrtFactorMass P := by positivity
  by_cases hgood : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · obtain ⟨hP, hPS⟩ := hgood
    let A := C * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hw : ∀ a, 0 ≤ w a := primeSquareCorrectedWeight_nonneg τ
    rw [response, (hasSum_response p S (fun a ha ↦ (hS a ha).1) hP N (by norm_num)).tsum_eq]
    calc
      _ ≤ ∑ W ∈ S.powerset, A * (lcmSqrtFactorMass P * ∏ a ∈ W, w a) := by
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
          (zetaSquareSieveExponent_gt_half hr1).le)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left he (by positivity))
          (mul_le_mul_of_nonneg_right hf (Finset.prod_nonneg (fun a _ ↦ hw a)))
          (mul_nonneg (Finset.prod_nonneg (fun a _ ↦ hw a))
            (Finset.prod_nonneg (fun a _ ↦ hw a))) hA
      _ = (A * lcmSqrtFactorMass P) * ∏ a ∈ S, (1 + w a) := by
        rw [Finset.prod_one_add, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun W _ ↦ by ring)
      _ ≤ (A * lcmSqrtFactorMass P) * ∏ a ∈ S, (1 + 2 * w a) := mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun a _ ↦ by linarith [hw a])
          (fun a _ ↦ by linarith [hw a])) (by positivity)
      _ ≤ (A * lcmSqrtFactorMass P) * (Real.exp (2 * primeSquareWeightMass τ) * Real.exp (4 * Real.sqrt R)) :=
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


end RoughSquarefreeBare

namespace RoughPrimeLogLcm

/-- Prime insertion keeps the shared-prime case distinct from a new
coprime factor, before either part is estimated. -/
theorem mass_prime_lcm {a : ℕ} (ha : a.Prime) (P : ℕ) :
    lcmSqrtFactorMass (Nat.lcm a P) =
      if a ∣ P then lcmSqrtFactorMass P else lcmSqrtFactorMass a * lcmSqrtFactorMass P := by
  by_cases h : a ∣ P
  · rw [if_pos h, Nat.lcm_eq_right_iff_dvd.mpr h]
  · have hc := ha.coprime_iff_not_dvd.mpr h
    rw [if_neg h, hc.lcm_eq_mul, lcmSqrtFactorMass_mul hc]

/-- The logarithm of any selected set of distinct prime divisors is
bounded by the logarithm of the original positive integer. -/
theorem sum_prime_log_dvd_le (D : ℕ) {P : ℕ} (hP : 0 < P) :
    (∑ a ∈ zetaSquarePrimesThrough D, if a ∣ P then Real.log a else 0) ≤ Real.log P := by
  let T := (zetaSquarePrimesThrough D).filter (fun a ↦ a ∣ P)
  have hT (a : ℕ) (ha : a ∈ T) : a.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
  have hdiv : (∏ a ∈ T, a) ∣ P := (prod_primes_dvd_iff T hT P).mpr
    (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hpos : 0 < ∏ a ∈ T, a := Finset.prod_pos (fun a ha ↦ (hT a ha).pos)
  rw [← Finset.sum_filter]
  change (∑ a ∈ T, Real.log (a : ℝ)) ≤ _
  rw [← Real.log_prod (s := T) (f := fun a : ℕ ↦ (a : ℝ))
    (fun a ha ↦ show (a : ℝ) ≠ 0 by exact_mod_cast (hT a ha).ne_zero),
    ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.le_of_dvd hP hdiv)

/-- Prime logarithms times their entire divisor mass have a square-root
budget, with a fixed convergent constant and the physical logarithm. -/
theorem sum_prime_log_mass_le (D : ℕ) :
    (∑ a ∈ zetaSquarePrimesThrough D, Real.log a * lcmSqrtFactorMass a) ≤
      2 * (∑' d, zetaPrimeExpWeight (3 / 2) d) * Real.sqrt D * Real.log D := by
  have hlog := Real.log_natCast_nonneg D
  calc
    _ ≤ ∑ a ∈ zetaSquarePrimesThrough D, Real.log D * lcmSqrtFactorMass a := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨haD, _⟩ := Finset.mem_filter.mp ha
      exact mul_le_mul_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp haD).1)
          (by exact_mod_cast (Finset.mem_Icc.mp haD).2)) (lcmSqrtFactorMass_nonneg a)
    _ ≤ ∑ a ∈ Finset.Icc 1 D, Real.log D * lcmSqrtFactorMass a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ ↦ mul_nonneg hlog (lcmSqrtFactorMass_nonneg a))
    _ = Real.log D * ∑ a ∈ Finset.Icc 1 D, lcmSqrtFactorMass a := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log D * (2 * Real.sqrt D * ∑' d, zetaPrimeExpWeight (3 / 2) d) :=
      mul_le_mul_of_nonneg_left (RoughDivisorIncidence.sum_lcmSqrtFactorMass_le D) hlog
    _ = _ := by ring

/-- Inserting every selected prime costs its square-root mass plus only
the logarithm of the primes already shared with the original mark. -/
theorem sum_prime_log_lcm_mass_le (D : ℕ) {P : ℕ} (hP : 0 < P) :
    (∑ a ∈ zetaSquarePrimesThrough D, Real.log a * lcmSqrtFactorMass (Nat.lcm a P)) ≤
      lcmSqrtFactorMass P *
        (2 * (∑' d, zetaPrimeExpWeight (3 / 2) d) * Real.sqrt D * Real.log D + Real.log P) := by
  have hm := lcmSqrtFactorMass_nonneg P
  calc
    _ ≤ ∑ a ∈ zetaSquarePrimesThrough D,
        lcmSqrtFactorMass P * (Real.log a * lcmSqrtFactorMass a +
          if a ∣ P then Real.log a else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      have hap := (Finset.mem_filter.mp ha).2
      have haM := lcmSqrtFactorMass_nonneg a
      have hl := Real.log_natCast_nonneg a
      rw [mass_prime_lcm hap P]
      by_cases hd : a ∣ P
      · simp only [if_pos hd]
        nlinarith [mul_nonneg hm (mul_nonneg hl haM)]
      · simp only [if_neg hd, add_zero]
        exact le_of_eq (by ring)
    _ = lcmSqrtFactorMass P *
        ((∑ a ∈ zetaSquarePrimesThrough D, Real.log a * lcmSqrtFactorMass a) +
          ∑ a ∈ zetaSquarePrimesThrough D, if a ∣ P then Real.log a else 0) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (sum_prime_log_mass_le D) (sum_prime_log_dvd_le D hP)) hm

/-- The entire three-index prime-logarithmic lcm mass costs only
`D*sqrt(D)*log(D)`, including all shared-prime intersections. -/
theorem exists_triple_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      (∑ a ∈ zetaSquarePrimesThrough D, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        Real.log a * lcmSqrtFactorMass (Nat.lcm a (Nat.lcm d e))) ≤
          C * D * Real.sqrt D * Real.log D := by
  let Z := ∑' d, zetaPrimeExpWeight (3 / 2) d
  let M := 16 * Z ^ 2 * (∑' d, zetaPrimeExpWeight (5 / 4) d)
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hM : 0 ≤ M := mul_nonneg (by positivity) (tsum_nonneg (fun _ ↦ (Real.exp_pos _).le))
  refine ⟨M * (2 * Z + 2) + 1, by positivity, ?_⟩
  intro D hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hS : (1 : ℝ) ≤ Real.sqrt D := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ D by exact_mod_cast hD)
  have hl := Real.log_natCast_nonneg D
  let A := (2 * Z + 2) * Real.sqrt D * Real.log D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (d e : ℕ) (hd : d ∈ Finset.Icc 1 D) (he : e ∈ Finset.Icc 1 D) :
      (∑ a ∈ zetaSquarePrimesThrough D, Real.log a * lcmSqrtFactorMass (Nat.lcm a (Nat.lcm d e))) ≤
        lcmSqrtFactorMass (Nat.lcm d e) * A := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    have he0 := (Finset.mem_Icc.mp he).1
    have hL : 0 < Nat.lcm d e := Nat.lcm_pos hd0 he0
    have hLD : Nat.lcm d e ≤ D ^ 2 := by
      have hdiv : Nat.lcm d e ∣ d * e := Nat.lcm_dvd (Nat.dvd_mul_right d e) (Nat.dvd_mul_left e d)
      exact (Nat.le_of_dvd (Nat.mul_pos hd0 he0) hdiv).trans
        (by simpa only [pow_two] using Nat.mul_le_mul (Finset.mem_Icc.mp hd).2 (Finset.mem_Icc.mp he).2)
    have hlog : Real.log (Nat.lcm d e) ≤ 2 * Real.log D := by
      have h := Real.log_le_log (show (0 : ℝ) < Nat.lcm d e by exact_mod_cast hL)
        (show (Nat.lcm d e : ℝ) ≤ (D ^ 2 : ℕ) by exact_mod_cast hLD)
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
    apply (sum_prime_log_lcm_mass_le D hL).trans
    apply mul_le_mul_of_nonneg_left _ (lcmSqrtFactorMass_nonneg _)
    dsimp [A]
    have hlS : Real.log D ≤ Real.sqrt D * Real.log D := le_mul_of_one_le_left hl hS
    change 2 * Z * Real.sqrt D * Real.log D + Real.log (Nat.lcm d e) ≤ _
    nlinarith
  calc
    _ = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, ∑ a ∈ zetaSquarePrimesThrough D,
        Real.log a * lcmSqrtFactorMass (Nat.lcm a (Nat.lcm d e)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lcmSqrtFactorMass (Nat.lcm d e) * A :=
      Finset.sum_le_sum (fun d hd ↦ Finset.sum_le_sum (fun e he ↦ hpoint d e hd he))
    _ = (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lcmSqrtFactorMass (Nat.lcm d e)) * A := by
      simp_rw [← Finset.sum_mul]
    _ ≤ (M * D) * A := mul_le_mul_of_nonneg_right (sum_pair_lcmSqrtFactorMass_le_linear D) hA
    _ = (M * (2 * Z + 2)) * (D * Real.sqrt D * Real.log D) := by dsimp [A]; ring
    _ ≤ (M * (2 * Z + 2) + 1) * (D * Real.sqrt D * Real.log D) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The literal complete small-prime logarithmic response has the
improved three-halves divisor cost, with the original phase and sieve. -/
theorem exists_smallResponse_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ),
      1 ≤ D → (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖RoughPrimeLog.smallResponse p D S (N + 1) (3 / 2 + I * y)‖ ≤
        C * D * Real.sqrt D * Real.log D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) := by
  obtain ⟨C, hC, hb⟩ := RoughSquarefreeBare.exists_response_lcm_bound y hy hr hr1
  obtain ⟨M, hM, hm⟩ := exists_triple_mass_bound
  refine ⟨C * M, by positivity, ?_⟩
  intro p D N R S hD hS
  let A := C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
    (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmu (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [RoughPrimeLog.smallResponse,
    (RoughPrimeLog.hasSum_smallResponse p D S (fun a ha ↦ (hS a ha).1) N (by norm_num)).tsum_eq]
  calc
    _ ≤ ∑ a ∈ zetaSquarePrimesThrough D, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        A * (Real.log a * lcmSqrtFactorMass (Nat.lcm a (Nat.lcm d e))) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg a)]
      have hw : ‖(μ d : ℂ)‖ * ‖(μ e : ℂ)‖ * Real.log a ≤ Real.log a := by
        have h := mul_le_one₀ (hmu d) (norm_nonneg _) (hmu e)
        exact (mul_le_mul_of_nonneg_right h (Real.log_natCast_nonneg a)).trans_eq (one_mul _)
      apply (mul_le_mul hw (hb p N R S (Nat.lcm a (Nat.lcm d e)) hS)
        (norm_nonneg _) (Real.log_natCast_nonneg a)).trans_eq
      dsimp [A]
      ring
    _ = A * (∑ a ∈ zetaSquarePrimesThrough D, ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        Real.log a * lcmSqrtFactorMass (Nat.lcm a (Nat.lcm d e))) := by
      simp_rw [← Finset.mul_sum]
    _ ≤ A * (M * D * Real.sqrt D * Real.log D) := mul_le_mul_of_nonneg_left (hm D hD) hA
    _ = _ := by dsimp [A]; ring

/-- The unchanged source normalization and sieve, with the divisor and
prime-logarithm cutoff allowed to vary independently of the original schedule. -/
def normalizedSmallResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    RoughPrimeLog.smallResponse (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- The entire small-prime logarithmic contribution has a uniformly
vanishing geometric allowance at every divisor cutoff through D_N squared. -/
theorem exists_square_cutoff_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2 →
      ‖normalizedSmallResponse rho hrho N D‖ ≤
        C * (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by
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
  intro N D hN hDpos hcut
  have hf : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have hD : (D : ℝ) ≤ (q ^ N) ^ 2 := by
    have h : (D : ℝ) ≤ (zetaMoebiusGeometricCutoff q N : ℝ) ^ 2 := by exact_mod_cast hcut
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2)
  have hsqrt : Real.sqrt D ≤ q ^ N := by
    have h := Real.sqrt_le_sqrt hD
    rwa [Real.sqrt_sq (pow_nonneg hq.le N)] at h
  have hDhalf : (D : ℝ) * Real.sqrt D ≤ q ^ N * (q ^ N) ^ 2 :=
    (mul_le_mul hD hsqrt (Real.sqrt_nonneg D) (sq_nonneg _)).trans_eq (by ring)
  have he := RoughPrimeIncidence.exp_sqrt_cutoff_bound rho hrho N
  have hlog : Real.log D ≤ 1 + 4 * (N : ℝ) * Real.log q := by
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpred : N - 1 + 1 = N := by omega
  have hbN := hb p D (N - 1) (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) hDpos (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [hpred] at hbN
  have hpow : r⁻¹ ^ (N - 1) ≤ r⁻¹ ^ N := pow_le_pow_right₀ hri (by omega)
  rw [normalizedSmallResponse, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * ((D : ℝ) * Real.sqrt D) * Real.log D *
        Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ (N - 1) * B) := by
      exact (mul_le_mul_of_nonneg_left hbN (by positivity : 0 ≤ u ^ (N + 1))).trans_eq (by ring)
    _ ≤ u ^ (N + 1) * (C * (q ^ N * (q ^ N) ^ 2) *
        (1 + 4 * (N : ℝ) * Real.log q) * (Real.sqrt q) ^ N * r⁻¹ ^ N * B) := by gcongr
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
    _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) := by ring
    _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- Every moving prime-logarithm cutoff through the square of the
original divisor schedule has independently vanishing full response. -/
theorem tendsto_square_cutoff (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ normalizedSmallResponse rho hrho N (D N)) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_square_cutoff_bound rho hrho
  apply squeeze_zero_norm' _ (RoughPrimeIncidence.tendsto_allowance rho hrho C)
  filter_upwards [hD, eventually_ge_atTop 1] with N h hN
  exact hb N (D N) hN h.1 h.2

/-- The actual large-prime arithmetic carrier at an arbitrary common
divisor and prime-logarithm cutoff, with unchanged normalization. -/
def normalizedLargeResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    RoughPrimeLog.response (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- At every positive order the larger-cutoff carrier is exactly the
complete Mobius-square correlation minus the full small-prime correction. -/
theorem normalizedLargeResponse_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D) :
    normalizedLargeResponse rho hrho N D =
      RoughDivisorLinear.normalizedResponse rho hrho N D (fun d ↦ (μ d : ℂ)) (fun d ↦ (μ d : ℂ)) -
        normalizedSmallResponse rho hrho N D := by
  have h := (RoughPrimeLog.hasSum_response (zetaRightHalfPoleJetFilter rho hrho) D hD _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1)
    (N - 1) (by norm_num : (1 : ℝ) < (3 / 2 + I * rho.1.im : ℂ).re)).tsum_eq
  rw [show N - 1 + 1 = N by omega] at h
  simp only [normalizedLargeResponse, normalizedSmallResponse, RoughDivisorLinear.normalizedResponse,
    RoughDivisorCorrelation.response, RoughDivisorCorrelation.coefficient_moebius,
    RoughPrimeLog.response]
  rw [h, mul_sub]
  rfl

/-- The full positive multiplicity source survives after deletion of
all small-prime logarithms at every moving cutoff through D_N squared. -/
theorem tendsto_large_square_cutoff (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (fun N ↦ normalizedLargeResponse rho hrho N (D N)) atTop
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  let w := fun (_ : ℕ) (d : ℕ) ↦ (μ d : ℂ)
  have hm (d : ℕ) : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hcube : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 3 ∧
      (∀ d ∈ Finset.Icc 1 (D N), ‖w N d‖ ≤ 1) ∧
      (∀ e ∈ Finset.Icc 1 (D N), ‖w N e‖ ≤ 1) := by
    filter_upwards [hD] with N h
    have hbase := zetaRightHalfPoleJetCutoff_pos rho hrho N
    refine ⟨h.1, h.2.trans ?_, fun d _ ↦ hm d, fun e _ ↦ hm e⟩
    nlinarith
  have hsquare := RoughDivisorLinear.tendsto_cubic_cutoff_source rho hrho D w w hcube
    (c := (1 : ℂ)) (by simp [w])
  have h := hsquare.sub (tendsto_square_cutoff rho hrho D hD)
  simp only [one_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [hD, eventually_ge_atTop 1] with N hd hN
  exact (normalizedLargeResponse_eq rho hrho hN hd.1).symm

/-- Complete small cofactors cancel: the new large-prime coefficient
is identically zero through the square of its own divisor cutoff. -/
theorem coefficient_eq_zero_of_le_square (D : ℕ) (S : Finset ℕ) {n : ℕ} (hn : n ≤ D ^ 2) :
    RoughPrimeLog.coefficient D S n = 0 := by
  by_contra h
  obtain ⟨a, m, _, ha, hm, he⟩ :=
    RoughPrimeLog.exists_prime_cofactor_of_coefficient_ne_zero D S h
  nlinarith [Nat.mul_lt_mul_of_lt_of_lt ha hm]

/-- The complete large-prime response is exactly its square-cutoff
tail, without estimating or discarding any nonzero head contribution. -/
theorem response_eq_square_tail (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ) (N : ℕ) (s : ℂ) :
    RoughPrimeLog.response p D S N s = ∑' n,
      if D ^ 2 < n then RoughPrimeLog.coefficient D S n * zetaPrimeFilterKernel p N s n else 0 := by
  apply tsum_congr
  intro n
  by_cases h : D ^ 2 < n
  · simp only [if_pos h]
  · rw [if_neg h, coefficient_eq_zero_of_le_square D S (by omega), zero_mul]

/-- The exact square-cutoff tail is genuinely summable at every positive
moment order in the original absolute-convergence half-plane. -/
theorem summable_square_tail (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ if D ^ 2 < n then
      RoughPrimeLog.coefficient D S n * zetaPrimeFilterKernel p (N + 1) s n else 0) := by
  apply (RoughPrimeLog.hasSum_response p D hD S hS N hs).summable.congr
  intro n
  by_cases h : D ^ 2 < n
  · simp only [if_pos h]
  · rw [if_neg h, coefficient_eq_zero_of_le_square D S (by omega), zero_mul]

/-- At the squared divisor schedule the entire normalized source is
exactly the product tail beyond the fourth power of the original cutoff. -/
theorem normalizedLargeResponse_eq_fourth_tail (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    normalizedLargeResponse rho hrho N
      ((zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) =
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
        if (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 < n then
          RoughPrimeLog.coefficient
            ((zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)
            (zetaRightHalfPrimePatternPrimes rho N) n *
            zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n
        else 0 := by
  simp only [normalizedLargeResponse, response_eq_square_tail, ← pow_mul, Nat.reduceMul]

/-- At the squared original divisor cutoff, the whole large-prime
carrier still converges to the full zero multiplicity. -/
theorem tendsto_doubled_log_cutoff_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ normalizedLargeResponse rho hrho N
      ((zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)) atTop
        (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  apply tendsto_large_square_cutoff
  exact Eventually.of_forall (fun N ↦ ⟨one_le_pow₀ (zetaRightHalfPoleJetCutoff_pos rho hrho N), le_rfl⟩)

end RoughPrimeLogLcm
end
end RiemannGaussian
