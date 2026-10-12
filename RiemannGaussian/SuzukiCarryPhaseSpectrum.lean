/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseEta
import RiemannGaussian.SuzukiCarryPhaseQuadrature
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The small-lag channel of the regularized spectrum

The ordinary grid remainder is absolutely summable. The alternating bulk
is retained as the entire eta continuation. Identifying this spectrum with
the literal Mellin phase contrast is a separate integral identity.
-/

namespace RiemannGaussian.SuzukiCarryPhaseSpectrum
noncomputable section
open Complex MeasureTheory Set Filter
open SuzukiCarryPhaseEta SuzukiCarryPhaseQuadrature
open scoped BigOperators Topology

/-- Alternating Mellin weight of one exact lag quadrature remainder. -/
def lagTerm (s : ℂ) (v : ℝ) (h : ℕ) : ℂ :=
  (-1 : ℂ)^(h+1)*Complex.exp (-s*(Real.log (h+1) : ℂ))*
    (lagRemainder v (h+1) : ℂ)

/-- Absolutely convergent sum of the weighted lag remainders. -/
def errorSpectrum (s : ℂ) (v : ℝ) : ℂ := ∑' h : ℕ, lagTerm s v h

/-- Joined eta channel and exact quadrature remainder of the lag spectrum. -/
def bracket (s : ℂ) (v : ℝ) : ℂ :=
  -SuzukiCarryPhaseEta.eta (s-1)*(overlapIntegral v : ℂ)/(v : ℂ)+errorSpectrum s v

/-- Summable power majorant for the complete quadrature remainder. -/
def powerBudget (s : ℂ) : ℝ := ∑' h : ℕ, ((h+1 : ℕ) : ℝ)^(-s.re-1)

theorem summable_powerBudget {s : ℂ} (hs : 0 < s.re) :
    Summable (fun h : ℕ => ((h+1 : ℕ) : ℝ)^(-s.re-1)) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))

theorem powerBudget_nonneg (s : ℂ) : 0 ≤ powerBudget s := by
  exact tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)

theorem lagTerm_norm_le {s : ℂ} {v : ℝ} (hv : 0 < v) (h : ℕ) :
    ‖lagTerm s v h‖ ≤ 2*v*((h+1 : ℕ) : ℝ)^(-s.re-1) := by
  have hh : (0 : ℝ) < (h+1 : ℕ) := by positivity
  have hn : ‖Complex.exp (-s*(Real.log (h+1) : ℂ))‖ =
      ((h+1 : ℕ) : ℝ)^(-s.re) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos hh]
    congr 1
    simp [Complex.mul_re, mul_comm]
  unfold lagTerm
  rw [norm_mul, norm_mul, norm_pow]
  norm_num only [norm_neg, norm_one, one_pow, one_mul]
  rw [hn, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ((h+1 : ℕ) : ℝ)^(-s.re)*(2*v/((h+1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (lagRemainder_abs_le hv (by omega))
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [show -s.re-1 = -s.re+(-1) by ring, Real.rpow_add hh, Real.rpow_neg_one]
      ring

theorem summable_lagTerm {s : ℂ} (hs : 0 < s.re) {v : ℝ} (hv : 0 < v) :
    Summable (fun h => lagTerm s v h) :=
  ((summable_powerBudget hs).mul_left (2*v)).of_norm_bounded (lagTerm_norm_le hv)

theorem errorSpectrum_norm_le {s : ℂ} (hs : 0 < s.re) {v : ℝ} (hv : 0 < v) :
    ‖errorSpectrum s v‖ ≤ 2*v*powerBudget s := by
  have hb := (summable_powerBudget hs).mul_left (2*v)
  have hn := hb.of_nonneg_of_le (fun _ => norm_nonneg _) (lagTerm_norm_le (s := s) hv)
  unfold errorSpectrum powerBudget
  apply (norm_tsum_le_tsum_norm hn).trans
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (lagTerm_norm_le hv) hn hb

/-- The complete absolutely summed quadrature error is too small to
annihilate the eta bulk as the positive lag tends to zero. -/
theorem tendsto_scaled_errorSpectrum {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun v : ℝ => (v : ℂ)*errorSpectrum s v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun v : ℝ => 2*powerBudget s*v^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun v : ℝ => 2*powerBudget s*v^2) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  exact (mul_le_mul_of_nonneg_left (errorSpectrum_norm_le hs hv) hv.le).trans_eq (by ring)

theorem tendsto_scaled_bracket {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun v : ℝ => (v : ℂ)*bracket s v) (𝓝[>] (0 : ℝ))
      (𝓝 (-(2/3 : ℂ)*SuzukiCarryPhaseEta.eta (s-1))) := by
  have hi : Tendsto (fun v : ℝ => (smallOverlapIntegral v : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2/3 : ℂ)) := by
    have hc : Continuous (fun v : ℝ => (smallOverlapIntegral v : ℂ)) := by
      unfold smallOverlapIntegral; fun_prop
    simpa [smallOverlapIntegral] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have he := ((tendsto_const_nhds (x := -SuzukiCarryPhaseEta.eta (s-1))).mul hi).add
    (tendsto_scaled_errorSpectrum hs)
  simp only [add_zero] at he
  rw [show -SuzukiCarryPhaseEta.eta (s-1)*(2/3 : ℂ) =
    -(2/3 : ℂ)*SuzukiCarryPhaseEta.eta (s-1) by ring] at he
  have hsmall : ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ), v < 1 :=
    mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
      (fun _ h => h)
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin,hsmall] with v hv hv1
  unfold bracket overlapIntegral
  rw [ite_eq_left hv1.le]
  have hn : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

/-- At every nonzero height there is a nonvanishing small-lag channel.
No quadratic/quartic wedge or special-height numerical premise enters. -/
theorem eventually_bracket_ne_zero {y : ℝ} (hy : y ≠ 0) :
    ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ), bracket (1-I*y) v ≠ 0 := by
  have hs : 0 < (1-I*y).re := by simp
  have hz : SuzukiCarryPhaseEta.eta ((1-I*y)-1) ≠ 0 :=
    eta_ne_zero_on_zero_line (by simp) (by simpa using neg_ne_zero.mpr hy)
  have hm : -(2/3 : ℂ)*SuzukiCarryPhaseEta.eta ((1-I*y)-1) ≠ 0 := mul_ne_zero (by norm_num) hz
  have he := (tendsto_scaled_bracket hs).eventually
    (isOpen_ne.mem_nhds hm)
  filter_upwards [he] with v hv
  intro hb
  exact hv (by rw [hb, mul_zero])

end
end RiemannGaussian.SuzukiCarryPhaseSpectrum
