/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughMoebiusMixedDecay

/-!
# All divisor correlations and their surviving unit coefficient

The complete complex correlation retains both divisor-weight families and
every least-common-multiple intersection. All nonunit entries have an
independent uniform bound. The unit entry is kept separately and exactly,
so the full source cannot be mistaken for cancellation in the other rows.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.RoughDivisorCorrelation
noncomputable section
open RoughPrimeIncidence

/-- The complete ordered divisor pairs through the physical cutoff. -/
def pairs (D : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 D).product (Finset.Icc 1 D)

/-- A complex correlation of two arbitrary divisor-weight families
on the original rough squarefree composite logarithmic coefficient. -/
def coefficient (D : ℕ) (S : Finset ℕ) (w v : ℕ → ℂ) (n : ℕ) : ℂ :=
  weight (Finset.Icc 1 D) w n * star (weight (Finset.Icc 1 D) v n) *
    (zetaRoughSquarefreeCompositeLogWeight S n : ℂ)

/-- The exact lcm matrix expansion retains both complex coefficient
families and every ordered shared-prime intersection. -/
theorem coefficient_eq_pairs (D : ℕ) (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    (w v : ℕ → ℂ) (n : ℕ) :
    coefficient D S w v n = ∑ a ∈ pairs D,
      -(w a.1 * star (v a.2)) * fibreCoefficient 1 S (Nat.lcm a.1 a.2) n := by
  rw [show (∑ a ∈ pairs D, -(w a.1 * star (v a.2)) *
      fibreCoefficient 1 S (Nat.lcm a.1 a.2) n) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        -(w d * star (v e)) * fibreCoefficient 1 S (Nat.lcm d e) n from
      Finset.sum_product _ _ _]
  unfold coefficient weight
  rw [star_sum]
  conv_lhs => arg 1; rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [fibreCoefficient, zetaRoughSquarefreeCoefficient_one S hS n]
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;>
    simp [Nat.lcm_dvd_iff, hd, he]

/-- The literal complete arithmetic correlation, with its original
polynomial kernel and complex ordinate. -/
def response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (w v : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n, coefficient D S w v n * zetaPrimeFilterKernel p N s n

/-- Every entry of the finite correlation matrix is a genuine
convergent arithmetic series; the full signed expansion commutes with it. -/
theorem hasSum_response (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ coefficient D S w v n * zetaPrimeFilterKernel p N s n)
      (∑ a ∈ pairs D, -(w a.1 * star (v a.2)) * fibre p 1 S N s (Nat.lcm a.1 a.2)) := by
  have h := hasSum_sum (s := pairs D) (fun a _ ↦
    (summable_fibre p 1 N le_rfl S hS (Nat.lcm a.1 a.2) hs).hasSum.mul_left
      (-(w a.1 * star (v a.2))))
  apply h.congr_fun
  intro n
  rw [coefficient_eq_pairs D S hS w v n, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun a _ ↦ by ring)

/-- The exact nonunit matrix contribution, before any norm is taken. -/
def remainder (p : Polynomial ℂ) (D : ℕ) (S : Finset ℕ)
    (w v : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ a ∈ (pairs D).erase (1, 1),
    -(w a.1 * star (v a.2)) * fibre p 1 S N s (Nat.lcm a.1 a.2)

/-- The complete correlation is its literal unit coefficient times
the original composite logarithmic response, plus every remaining entry. -/
theorem response_eq_unit_add_remainder (p : Polynomial ℂ) (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (w v : ℕ → ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    response p D S w v N s =
      (w 1 * star (v 1)) * zetaRoughSquarefreeCompositeLogFilter p S N s +
        remainder p D S w v N s := by
  have h1 : (1, 1) ∈ pairs D := by simp [pairs, hD]
  have hf : fibre p 1 S N s 1 = -zetaRoughSquarefreeCompositeLogFilter p S N s := by
    simp only [fibre, fibreCoefficient, one_dvd, if_true]
    exact zetaRoughSquarefreeFilter_one p S hS N s
  rw [response, (hasSum_response p D S hS w v N hs).tsum_eq,
    ← Finset.add_sum_erase _ _ h1]
  change -(w 1 * star (v 1)) * fibre p 1 S N s (Nat.lcm 1 1) + _ = _
  simp only [Nat.lcm_self, hf, neg_mul_neg]
  rfl

private theorem fibre_zero_of_ineligible (p : Polynomial ℂ) (S : Finset ℕ)
    {P : ℕ} (hP : ¬(Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S)) (N : ℕ) (s : ℂ) :
    fibre p 1 S N s P = 0 := by
  have hz (n : ℕ) : fibreCoefficient 1 S P n = 0 := by
    by_cases hd : P ∣ n
    · by_cases hsf : Squarefree n
      · have he : ∃ a ∈ S, a ∣ n := by
          by_contra he
          apply hP
          exact ⟨hsf.squarefree_of_dvd hd, fun a ha haS ↦
            he ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hd⟩⟩
        simp [fibreCoefficient, zetaRoughSquarefreeCoefficient, he]
      · simp [fibreCoefficient, zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient, hsf]
    · simp [fibreCoefficient, hd]
  simp [fibre, hz]

/-- Every nonunit matrix entry is bounded uniformly through the
chosen factor cutoff. Ineligible marks vanish exactly; the complete prime
correction of each eligible entry is included in the bound. -/
theorem exists_entry_bound (y : ℝ) (hy : 1 < |y|) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N R X : ℕ) (S : Finset ℕ) (P : ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) → P ≠ 1 → P ≤ X →
      ‖fibre p 1 S N (3 / 2 + I * y) P‖ ≤
        C * Real.exp (4 * Real.sqrt R) * Real.sqrt X * (1 + Real.log X) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := RoughDivisorIncidence.exists_sum_norm_fibre_bound y hy hr hr1
  refine ⟨C, hC, ?_⟩
  intro p N R X S P hS hP1 hPX
  by_cases hP : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · have h := hb p 1 N R X S {P} le_rfl hS (by
      intro a ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact ⟨hP.1, hP1, hPX, hP.2⟩)
    simpa using h
  · rw [fibre_zero_of_ineligible p S hP N, norm_zero]
    positivity

private theorem nonunit_pair_eligible {D : ℕ} {a : ℕ × ℕ}
    (ha : a ∈ (pairs D).erase (1, 1)) : Nat.lcm a.1 a.2 ≠ 1 ∧ Nat.lcm a.1 a.2 ≤ D ^ 2 := by
  obtain ⟨hne, ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hd, he⟩ := Finset.mem_product.mp ha
  obtain ⟨hd0, hdD⟩ := Finset.mem_Icc.mp hd
  obtain ⟨he0, heD⟩ := Finset.mem_Icc.mp he
  constructor
  · intro h
    have hd1 : a.1 = 1 := Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_lcm_left a.1 a.2)
    have he1 : a.2 = 1 := Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_lcm_right a.1 a.2)
    exact hne (Prod.ext hd1 he1)
  · have hdiv : Nat.lcm a.1 a.2 ∣ a.1 * a.2 :=
      Nat.lcm_dvd (Nat.dvd_mul_right a.1 a.2) (Nat.dvd_mul_left a.2 a.1)
    exact (Nat.le_of_dvd (Nat.mul_pos hd0 he0) hdiv).trans
      (by simpa only [pow_two] using Nat.mul_le_mul hdD heD)

/-- Every nonunit correlation is controlled at once by the product
of the two coefficient masses. All cross terms remain in the exact
remainder; this estimate is uniform over both complex families. -/
theorem exists_remainder_bound (y : ℝ) (hy : 1 < |y|) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ) (w v : ℕ → ℂ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      ‖remainder p D S w v N (3 / 2 + I * y)‖ ≤
        C * ((∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖)) *
          D * (1 + Real.log ((D ^ 2 : ℕ) : ℝ)) * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
            ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_entry_bound y hy hr hr1
  refine ⟨C, hC, ?_⟩
  intro p D N R S w v hS
  let A := C * Real.exp (4 * Real.sqrt R) * Real.sqrt ((D ^ 2 : ℕ) : ℝ) *
    (1 + Real.log ((D ^ 2 : ℕ) : ℝ)) * r⁻¹ ^ N *
      ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmass : (∑ a ∈ (pairs D).erase (1, 1), ‖w a.1‖ * ‖v a.2‖) ≤
      (∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖) := by
    calc
      _ ≤ ∑ a ∈ pairs D, ‖w a.1‖ * ‖v a.2‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ by positivity)
      _ = _ := by
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        exact Finset.sum_product _ _ _
  unfold remainder
  calc
    _ ≤ ∑ a ∈ (pairs D).erase (1, 1), (‖w a.1‖ * ‖v a.2‖) * A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul, norm_neg, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left
        (hb p N R (D ^ 2) S (Nat.lcm a.1 a.2) hS
          (nonunit_pair_eligible ha).1 (nonunit_pair_eligible ha).2) (by positivity)
    _ = (∑ a ∈ (pairs D).erase (1, 1), ‖w a.1‖ * ‖v a.2‖) * A :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ ((∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖)) * A :=
      mul_le_mul_of_nonneg_right hmass hA
    _ = _ := by
      dsimp [A]
      rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg D)]
      ring

/-- The source-normalized complete divisor correlation at the
original moving cutoff, retaining both weight families. -/
def actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N : ℕ) (w v : ℕ → ℂ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    response (zetaRightHalfPoleJetFilter rho hrho)
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) w v N (3 / 2 + I * rho.1.im)

/-- The unchanged unweighted composite logarithmic response in the
unit matrix entry, with the original zero-source normalization. -/
def unitResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    zetaRoughSquarefreeCompositeLogFilter (zetaRightHalfPoleJetFilter rho hrho)
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- Both weight families preserve their unit interaction exactly;
every other entry remains in the complete normalized remainder. -/
theorem actualResponse_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N : ℕ) (w v : ℕ → ℂ) :
    actualResponse rho hrho N w v = (w 1 * star (v 1)) * unitResponse rho hrho N +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        remainder (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) w v N (3 / 2 + I * rho.1.im) := by
  rw [actualResponse, response_eq_unit_add_remainder _ _
    (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) w v N (by norm_num)]
  unfold unitResponse
  ring

/-- The full two-family correlation differs from its rank-one unit
entry by an independent geometric allowance, uniformly over all moving
complex weights whose product of coefficient masses is at most `D_N^2`. -/
theorem exists_actual_error_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (w v : ℕ → ℂ),
      (∑ d ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖w d‖) *
        (∑ e ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖v e‖) ≤
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2 →
      ‖actualResponse rho hrho N w v - (w 1 * star (v 1)) * unitResponse rho hrho N‖ ≤
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
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_remainder_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + 4 * Real.log q) + 1, by positivity, ?_⟩
  intro N w v hmass
  let D := zetaMoebiusGeometricCutoff q N
  have hDpos : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have he := RoughPrimeIncidence.exp_sqrt_cutoff_bound rho hrho N
  have hlog : Real.log ((D ^ 2 : ℕ) : ℝ) ≤ 4 * (N : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow] at h
    norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hm : (∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖) ≤ (q ^ N) ^ 2 :=
    hmass.trans (pow_le_pow_left₀ (by positivity) hD 2)
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) w v (zetaRightHalfPrimePatternPrimes_eligible rho N)
  rw [actualResponse_eq, add_sub_cancel_left, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * ((∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖)) *
        D * (1 + Real.log ((D ^ 2 : ℕ) : ℝ)) *
        Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N) ^ 2 * q ^ N *
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
    _ ≤ _ := by
      have h0 : 0 ≤ (1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N := by positivity
      calc
        _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) := by ring
        _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * RoughPrimeIncidence.rate rho ^ N) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
        _ = _ := by ring

/-- Every admissible pair of moving coefficient families has
vanishing response after subtracting its complete unit interaction. -/
theorem tendsto_actual_error (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (w v : ℕ → ℕ → ℂ)
    (hmass : ∀ᶠ N in atTop,
      (∑ d ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖w N d‖) *
        (∑ e ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖v N e‖) ≤
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2) :
    Tendsto (fun N ↦ actualResponse rho hrho N (w N) (v N) -
      (w N 1 * star (v N 1)) * unitResponse rho hrho N) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actual_error_bound rho hrho
  exact squeeze_zero_norm' (hmass.mono (fun N hN ↦ hb N (w N) (v N) hN))
    (RoughPrimeIncidence.tendsto_allowance rho hrho C)

/-- The limiting source of every admissible two-family correlation
is exactly its limiting unit interaction times the zero multiplicity.
All nonunit phases and cross terms have been independently bounded. -/
theorem tendsto_actualResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (w v : ℕ → ℕ → ℂ)
    (hmass : ∀ᶠ N in atTop,
      (∑ d ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖w N d‖) *
        (∑ e ∈ Finset.Icc 1 (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N), ‖v N e‖) ≤
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N : ℝ) ^ 2)
    {c : ℂ} (hc : Tendsto (fun N ↦ w N 1 * star (v N 1)) atTop (𝓝 c)) :
    Tendsto (fun N ↦ actualResponse rho hrho N (w N) (v N)) atTop
      (𝓝 (c * (analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : Tendsto (unitResponse rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) :=
    tendsto_zetaRightHalfRoughSquarefreeCompositeLogFilter rho hrho
  have h := (hc.mul hu).add (tendsto_actual_error rho hrho w v hmass)
  simp only [add_zero] at h
  convert h using 1
  funext N
  ring

/-- In the diagonal correlation the divisor coefficient is the
literal nonnegative squared norm; the arithmetic kernel is still complex. -/
theorem coefficient_self_eq (D : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) (n : ℕ) :
    coefficient D S w w n =
      ((‖weight (Finset.Icc 1 D) w n‖ ^ 2 * zetaRoughSquarefreeCompositeLogWeight S n : ℝ) : ℂ) := by
  rw [coefficient, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_mul]

/-- Every pair of pointwise bounded complex families satisfies the
coefficient-mass budget. The theorem also admits larger sparse weights
whenever their total masses meet the same product bound. -/
theorem mass_budget_of_norm_le_one (D : ℕ) (w v : ℕ → ℂ)
    (hw : ∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1)
    (hv : ∀ d ∈ Finset.Icc 1 D, ‖v d‖ ≤ 1) :
    (∑ d ∈ Finset.Icc 1 D, ‖w d‖) * (∑ e ∈ Finset.Icc 1 D, ‖v e‖) ≤ (D : ℝ) ^ 2 := by
  have hwD : (∑ d ∈ Finset.Icc 1 D, ‖w d‖) ≤ D := by
    simpa using Finset.sum_le_sum hw
  have hvD : (∑ d ∈ Finset.Icc 1 D, ‖v d‖) ≤ D := by
    simpa using Finset.sum_le_sum hv
  simpa only [pow_two] using mul_le_mul hwD hvD (by positivity) (by positivity)

/-- The actual Möbius square is precisely the diagonal member of
this full complex correlation family, with no altered support or kernel. -/
theorem coefficient_moebius (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    coefficient D S (fun d ↦ (ArithmeticFunction.moebius d : ℂ))
      (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) n = RoughMoebiusMixed.squareCoefficient D S n := by
  have hs : star (RoughMoebiusIncidence.mask D n) = RoughMoebiusIncidence.mask D n := by
    apply Complex.ext <;> simp [RoughMoebiusIncidence.mask_im]
  change RoughMoebiusIncidence.mask D n * star (RoughMoebiusIncidence.mask D n) * _ = _
  rw [hs, RoughMoebiusMixed.squareCoefficient, pow_two]

/-- The already constructed square source is exactly recovered
inside the general all-family response, including its moving cutoff. -/
theorem actualResponse_moebius (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    actualResponse rho hrho N (fun d ↦ (ArithmeticFunction.moebius d : ℂ))
      (fun d ↦ (ArithmeticFunction.moebius d : ℂ)) = RoughMoebiusMixed.actualSquareResponse rho hrho N := by
  simp only [actualResponse, response, coefficient_moebius,
    RoughMoebiusMixed.actualSquareResponse, RoughMoebiusMixed.squareResponse]

end
end RiemannGaussian.RoughDivisorCorrelation
