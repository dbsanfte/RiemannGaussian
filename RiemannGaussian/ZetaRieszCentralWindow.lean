/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnnulusJoint

/-!
# Independent central-window bounds for the actual signed carrier

For 0<u<exp(-2/3), all divisor-majorized coefficients outside
3N/2<log(n)<=8N/3 have two explicit strict geometric allowances.
The full actual annulus can be intersected with this window while retaining
every earlier arithmetic cut and the entire exposed-zero source. The signed
central sum remains open; this is not a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCentralWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaArithmeticLogWindow

/-- The full divisor-log mass includes the (1,n) incidence, so it
dominates one logarithm without any primality or squarefreeness premise. -/
theorem log_le_divisor_majorant (n : ℕ) : Real.log n ≤ zetaMoebiusLogMajorant n := by
  by_cases hn : n = 0
  · simp [hn, zetaMoebiusLogMajorant]
  · exact Finset.single_le_sum (fun ap _ => Real.log_natCast_nonneg ap.2)
      (show (1, n) ∈ n.divisorsAntidiagonal by simp [Nat.mem_divisorsAntidiagonal, hn])

/-- The explicit geometric base for the full lower central window. -/
def centralLowerRate : ℝ := (3 / 2) * Real.exp (-(631 / 1536 : ℝ))

/-- Exact logarithm inequalities make the new base strictly subunit. -/
theorem centralLowerRate_lt_one : centralLowerRate < 1 := by
  have hlog : Real.log (3 / 2 : ℝ) - 631 / 1536 < 0 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have he : centralLowerRate = Real.exp (Real.log (3 / 2 : ℝ) - 631 / 1536) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), centralLowerRate, Real.exp_neg]
    ring
  rw [he, Real.exp_lt_one_iff]
  exact hlog

/-- Every finite signed, divisor-majorized sum below log(n)=3N/2 has
an independent geometric bound after the original source normalization.
The coefficient family, finite support, phase and filter are unrestricted. -/
theorem norm_lower_central_sum_le (S : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ S, ‖f n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hS : ∀ n ∈ S, Real.log n ≤ (3 / 2 : ℝ) * N) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      centralLowerRate ^ N * (u * tiltConstant P (2 / 3) (257 / 256)) := by
  have hb := norm_sum_filter_of_log_bound S f hf P N y (257 / 256) (2 / 3) (131 / 512)
    (by norm_num) (by norm_num) (by intro n hn; have h := hS n hn; nlinarith)
  have hC : 0 ≤ tiltConstant P (2 / 3) (257 / 256) := by
    unfold tiltConstant
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
      (zetaMoebiusLogMajorantMass_nonneg _)
  have hr : u * ((2 / 3 : ℝ)⁻¹ * Real.exp (131 / 512)) ≤ centralLowerRate := by
    calc
      _ ≤ Real.exp (-(2 / 3 : ℝ)) * ((2 / 3 : ℝ)⁻¹ * Real.exp (131 / 512)) := by gcongr
      _ = _ := by
        unfold centralLowerRate
        rw [mul_left_comm, ← Real.exp_add]
        norm_num
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (((2 / 3 : ℝ)⁻¹ * Real.exp (131 / 512)) ^ N *
        tiltConstant P (2 / 3) (257 / 256)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (u * ((2 / 3 : ℝ)⁻¹ * Real.exp (131 / 512))) ^ N *
        (u * tiltConstant P (2 / 3) (257 / 256)) := by rw [pow_succ, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr N)
      (mul_nonneg hu.le hC)

/-- The entire lower central window vanishes for every changing
finite mask of actual dominated coefficients, without a hypothetical zero. -/
theorem tendsto_lower_central_sum (S : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ)
    (hf : ∀ N n, n ∈ S N → ‖f N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hS : ∀ N n, n ∈ S N → Real.log n ≤ (3 / 2 : ℝ) * N) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ∑ n ∈ S N,
      f N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun N => norm_lower_central_sum_le (S N) (f N) (hf N) P N y hu huh (hS N))
  have hr0 : 0 ≤ centralLowerRate := by unfold centralLowerRate; positivity
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 centralLowerRate_lt_one).mul_const
      (u * tiltConstant P (2 / 3) (257 / 256))

/-- The explicit geometric base for the upper central deletion. -/
def centralUpperRate : ℝ := (8 / 3) * Real.exp (-(95 / 96 : ℝ))

/-- The existing exact degree-rate comparison also certifies this
unrestricted integer-tail bound; no prime-count premise is needed. -/
theorem centralUpperRate_lt_one : centralUpperRate < 1 := by
  convert ZetaRieszLowerDegreeBounds.two_degree_rate_lt_one using 1
  norm_num [centralUpperRate, ZetaRieszLowerDegreeBounds.degreeRate]

/-- Every finite dominated sum above log(n)=8N/3 has the same strict
upper allowance, regardless of the number or placement of its prime factors. -/
theorem norm_upper_central_sum_le (S : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ S, ‖f n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hS : ∀ n ∈ S, (8 / 3 : ℝ) * N ≤ Real.log n) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      centralUpperRate ^ N * (u * tiltConstant P (3 / 8) (257 / 256)) := by
  have hb := norm_sum_filter_of_log_bound S f hf P N y (257 / 256) (3 / 8) (-(31 / 96))
    (by norm_num) (by norm_num) (by intro n hn; have h := hS n hn; nlinarith)
  have hC : 0 ≤ tiltConstant P (3 / 8) (257 / 256) := by
    unfold tiltConstant
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
      (zetaMoebiusLogMajorantMass_nonneg _)
  have hr : u * ((3 / 8 : ℝ)⁻¹ * Real.exp (-(31 / 96))) ≤ centralUpperRate := by
    calc
      _ ≤ Real.exp (-(2 / 3 : ℝ)) * ((3 / 8 : ℝ)⁻¹ * Real.exp (-(31 / 96))) := by gcongr
      _ = _ := by
        unfold centralUpperRate
        rw [mul_left_comm, ← Real.exp_add]
        norm_num
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (((3 / 8 : ℝ)⁻¹ * Real.exp (-(31 / 96))) ^ N *
        tiltConstant P (3 / 8) (257 / 256)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (u * ((3 / 8 : ℝ)⁻¹ * Real.exp (-(31 / 96)))) ^ N *
        (u * tiltConstant P (3 / 8) (257 / 256)) := by rw [pow_succ, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr N)
      (mul_nonneg hu.le hC)

/-- An exact central logarithmic window intersects, and never replaces,
the previous actual arithmetic support. -/
def centralBand (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  S.filter (fun n => (3 / 2 : ℝ) * N < Real.log n ∧ Real.log n ≤ (8 / 3 : ℝ) * N)

/-- Exact signed partition at the new central endpoints, before any norm
is applied. The same integer atoms occur in every component. -/
theorem sum_sub_centralBand (S : Finset ℕ) (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ S, f n) - (∑ n ∈ centralBand S N, f n) =
      (∑ n ∈ S.filter (fun (n : ℕ) => Real.log n ≤ (3 / 2 : ℝ) * N), f n) +
      (∑ n ∈ S.filter (fun (n : ℕ) => (8 / 3 : ℝ) * N < Real.log n), f n) := by
  have he : (3 / 2 : ℝ) * N ≤ (8 / 3 : ℝ) * N := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  simp only [centralBand, Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hl : (3 / 2 : ℝ) * N < Real.log n
  · by_cases hh : Real.log n ≤ (8 / 3 : ℝ) * N
    · simp [hl, hh, not_le.mpr hl, not_lt.mpr hh]
    · simp [hl, hh, not_le.mpr hl, lt_of_not_ge hh]
  · have hh : Real.log n ≤ (8 / 3 : ℝ) * N := (le_of_not_gt hl).trans he
    simp [hl, le_of_not_gt hl, not_lt.mpr hh]

/-- The entire two-sided deletion is paid by two explicit geometric
allowances, uniformly in height and arbitrary dominated coefficient masks. -/
theorem norm_sub_centralBand_le (S : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ S, ‖f n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ‖(u : ℂ) ^ (N + 1) * ((∑ n ∈ S,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
      ∑ n ∈ centralBand S N, f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)‖ ≤
      centralLowerRate ^ N * (u * tiltConstant P (2 / 3) (257 / 256)) +
        centralUpperRate ^ N * (u * tiltConstant P (3 / 8) (257 / 256)) := by
  rw [sum_sub_centralBand, mul_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact norm_lower_central_sum_le _ f (fun n hn => hf n (Finset.mem_filter.mp hn).1)
      P N y hu huh (fun _ hn => (Finset.mem_filter.mp hn).2)
  · exact norm_upper_central_sum_le _ f (fun n hn => hf n (Finset.mem_filter.mp hn).1)
      P N y hu huh (fun _ hn => (Finset.mem_filter.mp hn).2.le)

/-- The complete central-window deletion has independently vanishing
source error for every changing finite coefficient family and fixed filter. -/
theorem tendsto_sub_centralBand (S : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ)
    (hf : ∀ N n, n ∈ S N → ‖f N n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * ((∑ n ∈ S N,
      f N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
      ∑ n ∈ centralBand (S N) N,
        f N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun N => norm_sub_centralBand_le (S N) (f N) (hf N) P N y hu huh)
  have hl0 : 0 ≤ centralLowerRate := by unfold centralLowerRate; positivity
  have hh0 : 0 ≤ centralUpperRate := by unfold centralUpperRate; positivity
  simpa only [zero_mul, zero_add] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hl0 centralLowerRate_lt_one).mul_const
      (u * tiltConstant P (2 / 3) (257 / 256))).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hh0 centralUpperRate_lt_one).mul_const
        (u * tiltConstant P (3 / 8) (257 / 256)))

/-- The original actual annular carrier restricted to the independently
proved central logarithmic window. All previous support cuts survive. -/
def centralAnnulusResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ centralBand (ZetaRieszPhysicalAnnulus.annulusBand u N) N,
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The entire actual annulus loses both outer central pieces with
independently vanishing error. No cancellation premise is used. -/
theorem tendsto_annulus_sub_central (P : Polynomial ℂ) (y : ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszPhysicalAnnulus.annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u -
        centralAnnulusResponse P u y N)) atTop (nhds 0) :=
  tendsto_sub_centralBand (ZetaRieszPhysicalAnnulus.annulusBand u) _
    (fun N n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P y hu huh

/-- The newly narrowed ACTUAL Riesz sum retains the entire exposed-zero
source on the annular interval. Its remaining signed central sum still
requires an independent cofinal floor. -/
theorem tendsto_centralAnnulus_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      centralAnnulusResponse 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszPhysicalAnnulus.tendsto_normalizedAnnulus rho hrho hexposed).sub
    (tendsto_annulus_sub_central 1 rho.1.im hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold ZetaRieszPhysicalAnnulus.normalizedAnnulus
  ring

end

end RiemannGaussian.ZetaRieszCentralWindow
