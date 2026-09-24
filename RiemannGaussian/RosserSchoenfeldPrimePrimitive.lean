/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldPrimeKernel
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageMellinTransform

/-!
# The literal logarithmically smoothed von-Mangoldt sum

The moving finite prime-power window agrees exactly with the sum of its
continuous positive hinges. Their absolutely convergent Laplace integrals
recover the actual zeta logarithmic derivative on its convergence half-plane.
-/

namespace RiemannGaussian.RosserSchoenfeldPrimePrimitive
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology ArithmeticFunction
open RosserSchoenfeldLaplace RosserSchoenfeldPrimeKernel

/-- One literal logarithmic prime-power event, including its cutoff. -/
def term (n : ℕ) (t : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * max (t-Real.log n) 0

/-- The actual finite smoothed von-Mangoldt sum. -/
def value (t : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, term n t

/-- Every hinge is nonnegative. -/
theorem term_nonneg (n : ℕ) (t : ℝ) : 0 ≤ term n t := by
  unfold term
  positivity

/-- Increasing logarithmic time increases each literal event. -/
theorem monotone_term (n : ℕ) : Monotone (term n) := by
  intro t v h
  unfold term
  gcongr

/-- The hinge is continuous even when a prime power enters the window. -/
theorem continuous_term (n : ℕ) : Continuous (term n) := by unfold term; fun_prop

/-- No event outside the finite prime-power window contributes. -/
theorem term_eq_zero_of_not_mem {n : ℕ} {t : ℝ}
    (hn : n ∉ Finset.Icc 1 ⌊Real.exp t⌋₊) : term n t = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [term]
  have hnl : ⌊Real.exp t⌋₊ < n := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have ht : t < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).mpr ((Nat.floor_lt (Real.exp_pos t).le).mp hnl)
  simp [term, max_eq_right (sub_nonpos.mpr ht.le)]

/-- The finite moving window is exactly the full hinge series. -/
theorem tsum_term (t : ℝ) : (∑' n : ℕ, term n t) = value t :=
  tsum_eq_sum (fun _ hn => term_eq_zero_of_not_mem hn)

/-- The literal signed linear weight agrees with the positive hinge in its window. -/
theorem value_eq_sum (t : ℝ) : value t =
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
      ArithmeticFunction.vonMangoldt n * (t-Real.log n) := by
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hn⟩ := Finset.mem_Icc.mp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp hnpos).mpr
    ((Nat.le_floor_iff (Real.exp_pos t).le).mp hn)
  simp only [term, max_eq_left (sub_nonneg.mpr hlog)]

/-- Any larger finite window evaluates the original sum exactly. -/
theorem value_eq_fixed_sum {t T : ℝ} (ht : t ≤ T) :
    value t = ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, term n t := by
  rw [← tsum_term]
  apply tsum_eq_sum
  intro n hn
  have hz := term_eq_zero_of_not_mem hn
  exact le_antisymm ((monotone_term n ht).trans hz.le) (term_nonneg n t)

/-- Local finite support proves continuity of the actual moving prime sum. -/
theorem continuous_value : Continuous value := by
  rw [continuous_iff_continuousAt]
  intro t
  have he : value =ᶠ[𝓝 t]
      (fun x => ∑ n ∈ Finset.Icc 1 ⌊Real.exp (t+1)⌋₊, term n x) := by
    filter_upwards [Iio_mem_nhds (show t < t+1 by linarith)] with x hx
    exact value_eq_fixed_sum hx.le
  apply (continuousAt_congr he).mpr
  exact (continuous_finsetSum _ (fun n _ => continuous_term n)).continuousAt

/-- The initial prime window contributes exactly zero. -/
@[simp] theorem value_zero : value 0 = 0 := by simp [value, term]

private lemma damped_term_eq (s : ℂ) (n : ℕ) :
    (fun t : ℝ => Complex.exp (-s*t)*(term n t : ℂ)) =
      (Ioi (Real.log n)).indicator (fun t : ℝ =>
        (ArithmeticFunction.vonMangoldt n : ℂ)*
          (Complex.exp (-s*t)*((t-Real.log n : ℝ) : ℂ))) := by
  funext t
  by_cases ht : Real.log n < t
  · have hmem : t ∈ Ioi (Real.log n) := ht
    simp only [Set.indicator_of_mem hmem, term, max_eq_left (sub_nonneg.mpr ht.le)]
    push_cast
    ring
  · have h : t-Real.log n ≤ 0 := by linarith
    simp [ht, term, max_eq_right h]

/-- Absolute integrability holds for every original damped prime event. -/
theorem integrable_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*(term n t : ℂ)) (Ioi 0) := by
  rw [damped_term_eq, integrableOn_indicator_iff measurableSet_Ioi]
  rw [inter_eq_left.mpr (Ioi_subset_Ioi (Real.log_natCast_nonneg n))]
  exact (integrable_hinge hs (Real.log_natCast_nonneg n)).const_mul _

/-- Exact damped integral of one prime event before Dirichlet-series notation. -/
theorem integral_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-s*t)*(term n t : ℂ)) =
      (ArithmeticFunction.vonMangoldt n : ℂ)*Complex.exp (-s*Real.log n)/s^2 := by
  rw [damped_term_eq, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (Real.log_natCast_nonneg n)),
    integral_const_mul, integral_hinge hs (Real.log_natCast_nonneg n)]
  ring

/-- The real damped event has the same evaluated positive integral. -/
theorem integral_real_term {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-a*t)*term n t) =
      ArithmeticFunction.vonMangoldt n * Real.exp (-a*Real.log n)/a^2 := by
  have hh := integral_term (s := (a : ℂ)) (by simpa using ha) n
  have he (t : ℝ) : Complex.exp (-(a : ℂ)*t)*(term n t : ℂ) =
      ((Real.exp (-a*t)*term n t : ℝ) : ℂ) := by
    push_cast
    rfl
  simp only [he] at hh
  exact_mod_cast hh

/-- The absolute integral is evaluated using the real part of the damping parameter. -/
theorem integral_norm_term {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖Complex.exp (-s*t)*(term n t : ℂ)‖) =
      ArithmeticFunction.vonMangoldt n * Real.exp (-s.re*Real.log n)/s.re^2 := by
  have he (t : ℝ) : ‖Complex.exp (-s*t)*(term n t : ℂ)‖ =
      Real.exp (-s.re*t)*term n t := by
    simp [Complex.norm_exp, abs_of_nonneg (term_nonneg n t)]
  simp only [he]
  exact integral_real_term hs n

/-- Genuine absolute convergence justifies summing the original prime integrals. -/
theorem summable_integral_norm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖Complex.exp (-s*t)*(term n t : ℂ)‖) := by
  apply ((summable_vonMangoldt_mul_rpow_neg_of_one_lt hs).div_const (s.re^2)).congr
  intro n
  rw [integral_norm_term (by linarith)]
  by_cases hn : n = 0
  · simp [hn]
  · rw [Real.rpow_def_of_pos (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)]
    congr 3
    ring

/-- A complex prime event is exactly the corresponding Dirichlet-series term. -/
theorem integral_term_eq_LSeries {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-s*t)*(term n t : ℂ)) =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n / s^2 := by
  rw [integral_term hs]
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    simp only [div_eq_mul_inv, ← Complex.exp_neg, Complex.natCast_log]
    congr 2
    congr 1
    ring

private lemma damped_tsum (s : ℂ) (t : ℝ) :
    (∑' n : ℕ, Complex.exp (-s*t)*(term n t : ℂ)) =
      Complex.exp (-s*t)*(value t : ℂ) := by
  rw [tsum_mul_left, ← Complex.ofReal_tsum, tsum_term]

/-- The full damped prime sum is genuinely integrable. -/
theorem integrable_value {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*(value t : ℂ)) (Ioi 0) := by
  have hterm := integrable_term (s := s) (by linarith : 0 < s.re)
  have hsum : IntegrableOn (fun t : ℝ => ∑' n : ℕ,
      Complex.exp (-s*t)*(term n t : ℂ)) (Ioi 0) := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hterm n).aestronglyMeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ t : ℝ in Ioi 0, ‖∑' n : ℕ, Complex.exp (-s*t)*(term n t : ℂ)‖ₑ) ≤
          ∫⁻ t : ℝ in Ioi 0, ∑' n : ℕ, ‖Complex.exp (-s*t)*(term n t : ℂ)‖ₑ :=
        lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
      _ = ∑' n : ℕ, ∫⁻ t : ℝ in Ioi 0, ‖Complex.exp (-s*t)*(term n t : ℂ)‖ₑ := by
        rw [lintegral_tsum (fun n => (hterm n).aestronglyMeasurable.enorm)]
      _ = ∑' n : ℕ, ENNReal.ofReal
          (∫ t : ℝ in Ioi 0, ‖Complex.exp (-s*t)*(term n t : ℂ)‖) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_norm_eq_lintegral_enorm (hterm n)).symm
      _ < ⊤ := (summable_integral_norm hs).tsum_ofReal_lt_top
  simpa only [damped_tsum] using hsum

/-- The exact Laplace transform is the actual zeta logarithmic derivative,
with every convergence and interchange premise discharged. -/
theorem transform_value {s : ℂ} (hs : 1 < s.re) :
    transform s (fun t => (value t : ℂ)) = -logDeriv riemannZeta s / s^2 := by
  have hh := integral_tsum_of_summable_integral_norm
    (integrable_term (s := s) (by linarith : 0 < s.re)) (summable_integral_norm hs)
  simp only [damped_tsum, integral_term_eq_LSeries (by linarith : 0 < s.re),
    tsum_div_const] at hh
  rw [transform, ← hh]
  change LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s / s^2 = _
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  simp only [logDeriv_apply, neg_div]

end
end RiemannGaussian.RosserSchoenfeldPrimePrimitive
