/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallCompositeCells
import RiemannGaussian.ZetaRieszCofactorTiltRate

/-!
# Source-adapted logarithmic owner windows

These independent component estimates retain the original full filter,
all heights and the actual floor-defined cutoff. They preserve the full
pole-jet source but do not bound the remaining semiprime and large-owner
signed response or prove a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszOwnerWindow
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells ZetaRieszArithmeticCells
open ZetaRieszConditionedEnergy ZetaArithmeticLogWindow

/-- The whole-coefficient logarithmic-window rate, retaining the source
radius, window edge and summable majorant exponent together. -/
def windowRate (u c q σ : ℝ) : ℝ :=
  u * q⁻¹ * Real.exp ((σ - 3 / 2 + q) * c)

theorem windowRate_pos {u q : ℝ} (hu : 0 < u) (hq : 0 < q) (c σ : ℝ) :
    0 < windowRate u c q σ := by unfold windowRate; positivity

/-- The actual damped integer cutoff obeys the source-radius ceiling
eventually throughout (0,1), without fixing a rational upper radius. -/
theorem eventually_length_le_source_log {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop,
      SquarefreeVaughanLogSource.length u N ≤ -2 * Real.log u * N := by
  have hp := (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hu).mpr hu1)).eventually_ge_atTop 4
  filter_upwards [hp, eventually_ge_atTop 3] with N hpN hN
  have hNc : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hD : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤ u⁻¹ ^ N / 4 :=
    hfloor.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith))
  have hb : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ≤ u⁻¹ ^ N := by
    linarith
  have hlog := Real.log_le_log (by positivity) hb
  rw [Real.log_pow, Real.log_inv] at hlog
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- A general normalized bound for any finite dominated sum below a
linear logarithmic ceiling; the ordinate and full filter are unrestricted. -/
theorem norm_window_sum_le (S : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ S, ‖f n‖ ≤ zetaMoebiusLogMajorant n)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) {u c q σ : ℝ}
    (hu : 0 < u) (hq : 1 / 2 < q) (hσ : 1 < σ)
    (hS : ∀ n ∈ S, Real.log n ≤ c * N) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ S,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) n‖ ≤
        windowRate u c q σ ^ N * (u * tiltConstant P q σ) := by
  have hq0 : 0 < q := by linarith
  have hb := norm_sum_filter_of_log_bound S f hf P N t σ q ((σ - 3 / 2 + q) * c)
    hσ hq0 (by
      intro n hn
      have h := mul_le_mul_of_nonneg_left (hS n hn) (show 0 ≤ σ - 3 / 2 + q by linarith)
      nlinarith)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * ((q⁻¹ * Real.exp ((σ - 3 / 2 + q) * c)) ^ N *
        tiltConstant P q σ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by unfold windowRate; rw [pow_succ, mul_pow, mul_pow]; ring

/-- At the physical boundary and the summability edge, the full
coefficient estimate has the previously audited exact scalar tilt rate. -/
theorem windowRate_at_boundary {u : ℝ} (hu : 0 < u) (q : ℝ) :
    windowRate u (-2 * Real.log u) q 1 = ZetaRieszCofactorTiltRate.tiltRate u q := by
  unfold windowRate ZetaRieszCofactorTiltRate.tiltRate
  rw [show (1 - 3 / 2 + q) * (-2 * Real.log u) = (1 - 2 * q) * Real.log u by ring]
  have he : u * Real.exp ((1 - 2 * q) * Real.log u) =
      Real.exp ((2 - 2 * q) * Real.log u) := by
    calc
      _ = Real.exp (Real.log u) * Real.exp ((1 - 2 * q) * Real.log u) := by
        rw [Real.exp_log hu]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (u * Real.exp ((1 - 2 * q) * Real.log u)) / q := by ring
    _ = _ := by rw [he]

/-- A strict scalar margin allows both a positive exponentially growing
cofactor window and a genuinely summable arithmetic majorant. The tilt
is the exact analytic optimum, not a numerical candidate search. -/
theorem exists_owner_window_parameters {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hne : u ≠ Real.exp (-(1 / 2 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < -2 * Real.log u ∧
      windowRate u (-2 * Real.log u + δ)
        (ZetaRieszCofactorTiltRate.optimalTilt u) (1 + δ) < 1 := by
  have hu0 : 0 < u := by linarith
  have hc0 : 0 < -2 * Real.log u := by linarith [Real.log_neg hu0 hu1]
  let q := ZetaRieszCofactorTiltRate.optimalTilt u
  have hr : windowRate u (-2 * Real.log u) q 1 < 1 := by
    rw [windowRate_at_boundary hu0, ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1]
    exact ZetaRieszCofactorTiltRate.minimumRate_lt_one hu0 hne
  have hcont : ContinuousAt (fun δ : ℝ => windowRate u (-2 * Real.log u + δ) q (1 + δ)) 0 := by
    unfold windowRate
    fun_prop
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0,
      windowRate u (-2 * Real.log u + δ) q (1 + δ) < 1 :=
    hcont.eventually (gt_mem_nhds (by simpa using hr))
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min r (-2 * Real.log u) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_left r (-2 * Real.log u)]
  have hδc : δ < -2 * Real.log u := by dsimp [δ]; linarith [min_le_right r (-2 * Real.log u)]
  refine ⟨δ, hδ, hδc, hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδr

/-- The rate can be audited without separating the physical cutoff
from its source radius. This retains the crucial logarithmic correlation. -/
theorem windowRate_source_eq {u : ℝ} (hu : 0 < u) (δ q σ : ℝ) :
    windowRate u (-2 * Real.log u + δ) q σ = q⁻¹ *
      Real.exp ((4 - 2 * σ - 2 * q) * Real.log u + (σ - 3 / 2 + q) * δ) := by
  unfold windowRate
  calc
    _ = q⁻¹ * (Real.exp (Real.log u) *
        Real.exp ((σ - 3 / 2 + q) * (-2 * Real.log u + δ))) := by
      rw [Real.exp_log hu]
      ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- A uniform upper source radius yields one explicit common
geometric base, while preserving the length-radius correlation. -/
theorem windowRate_source_le {u : ℝ} (hu : 0 < u) (δ q σ h : ℝ)
    (hq : 0 < q) (ha : 0 ≤ 4 - 2 * σ - 2 * q) (huh : u < Real.exp (-h)) :
    windowRate u (-2 * Real.log u + δ) q σ ≤
      q⁻¹ * Real.exp (-(4 - 2 * σ - 2 * q) * h + (σ - 3 / 2 + q) * δ) := by
  have hlu : Real.log u < -h := by simpa only [Real.log_exp] using Real.log_lt_log hu huh
  rw [windowRate_source_eq hu]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr hq.le)
  nlinarith [mul_le_mul_of_nonneg_left hlu.le ha]

end
end RiemannGaussian.ZetaRieszOwnerWindow
