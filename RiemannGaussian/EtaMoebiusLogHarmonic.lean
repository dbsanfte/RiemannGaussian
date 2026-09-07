import RiemannGaussian.EtaMoebiusTrialCoefficients
import RiemannGaussian.MoebiusHarmonicCancellation
import Mathlib.Algebra.BigOperators.Module

/-!
# Decay of the exact logarithmic Möbius harmonic correction

The endpoint correction in the actual arithmetic candidates is a finite
logarithmic average of the original signed harmonic Möbius prefixes.
Discrete summation by parts retains this identity before a positive
averaging estimate proves that the correction tends to zero.
-/

open Filter
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact weighted harmonic endpoint subtracted in every logarithmic trial primitive. -/
def pairedEtaMoebiusLogHarmonic (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, (μ n : ℝ) * pairedEtaMoebiusTrialLogWeight M n / n

private theorem harmonic_prefix_eq_range (M : ℕ) :
    moebiusHarmonicPrefix M = ∑ n ∈ Finset.range (M + 1), (μ n : ℝ) / n := by
  rw [moebiusHarmonicPrefix,
    show Finset.range (M + 1) = Finset.Icc 1 M ∪ {0} by ext n; simp; omega,
    Finset.sum_union (by simp)]
  simp

private theorem log_step_nonneg (n : ℕ) :
    0 ≤ Real.log (n + 1 : ℝ) - Real.log (n : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  · exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn) (by linarith))

/-- The exact harmonic correction is the logarithmic average of the original signed Möbius prefixes. -/
theorem pairedEtaMoebiusLogHarmonic_eq_log_average {M : ℕ} (hM : 1 < M) :
    pairedEtaMoebiusLogHarmonic M =
      (∑ n ∈ Finset.range M,
        moebiusHarmonicPrefix n * (Real.log (n + 1 : ℝ) - Real.log (n : ℝ))) / Real.log M := by
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  have hab := Finset.sum_range_by_parts (fun n : ℕ ↦ Real.log (n : ℝ))
    (fun n : ℕ ↦ (μ n : ℝ) / n) (M + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, ← harmonic_prefix_eq_range,
    Nat.cast_add, Nat.cast_one] at hab
  have hsum : pairedEtaMoebiusLogHarmonic M = moebiusHarmonicPrefix M -
      (∑ n ∈ Finset.range (M + 1), Real.log (n : ℝ) * ((μ n : ℝ) / n)) / Real.log M := by
    rw [pairedEtaMoebiusLogHarmonic, moebiusHarmonicPrefix]
    rw [show (Finset.range (M + 1)) = Finset.Icc 1 M ∪ {0} by ext n; simp; omega,
      Finset.sum_union (by simp), Finset.sum_singleton, Nat.cast_zero, div_zero, mul_zero, add_zero, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [pairedEtaMoebiusTrialLogWeight, if_pos hM]
    ring
  rw [hsum, hab]
  simp_rw [mul_comm (Real.log (_ + 1 : ℝ) - Real.log (_ : ℝ))]
  field_simp
  ring

private theorem sum_log_steps (M : ℕ) :
    (∑ n ∈ Finset.range M, (Real.log (n + 1 : ℝ) - Real.log (n : ℝ))) = Real.log M := by
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, sub_zero] using
    Finset.sum_range_sub (fun n : ℕ ↦ Real.log (n : ℝ)) M

/-- A finite signed prefix and a uniform small harmonic tail control the entire logarithmic correction. -/
theorem abs_pairedEtaMoebiusLogHarmonic_le {M N : ℕ} (hM : 1 < M) (hNM : N ≤ M)
    {e : ℝ} (he : 0 ≤ e) (hH : ∀ n, N ≤ n → |moebiusHarmonicPrefix n| ≤ e) :
    |pairedEtaMoebiusLogHarmonic M| ≤ e +
      (∑ n ∈ Finset.range N, |moebiusHarmonicPrefix n| *
        (Real.log (n + 1 : ℝ) - Real.log (n : ℝ))) / Real.log M := by
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  rw [pairedEtaMoebiusLogHarmonic_eq_log_average hM, abs_div, abs_of_pos hlog]
  apply (div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hlog.le).trans
  simp_rw [abs_mul, abs_of_nonneg (log_step_nonneg _)]
  apply (div_le_iff₀ hlog).mpr
  rw [add_mul, div_mul_cancel₀ _ hlog.ne']
  have hpoint (n : ℕ) : |moebiusHarmonicPrefix n| *
      (Real.log (n + 1 : ℝ) - Real.log (n : ℝ)) ≤
      e * (Real.log (n + 1 : ℝ) - Real.log (n : ℝ)) +
        (if n < N then |moebiusHarmonicPrefix n| *
          (Real.log (n + 1 : ℝ) - Real.log (n : ℝ)) else 0) := by
    by_cases hn : n < N
    · rw [if_pos hn]
      linarith [mul_nonneg he (log_step_nonneg n)]
    · rw [if_neg hn, add_zero]
      exact mul_le_mul_of_nonneg_right (hH n (by omega)) (log_step_nonneg n)
  have hs := Finset.sum_le_sum (s := Finset.range M) (fun n _ ↦ hpoint n)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_steps] at hs
  have hfilter : (Finset.range M).filter (fun n ↦ n < N) = Finset.range N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simpa only [← Finset.sum_filter, hfilter] using hs

/-- The actual logarithmic harmonic endpoint correction tends to zero, using the proved arithmetic cancellation rather than numerical fitting. -/
theorem pairedEtaMoebiusLogHarmonic_tendsto_zero :
    Tendsto pairedEtaMoebiusLogHarmonic atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp moebiusHarmonicPrefix_tendsto_zero (e / 2) (by positivity)
  let C := ∑ n ∈ Finset.range N, |moebiusHarmonicPrefix n| *
    (Real.log (n + 1 : ℝ) - Real.log (n : ℝ))
  have hlog : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun M : ℕ ↦ C / Real.log (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hC (e / 2) (by positivity)
  refine ⟨max 2 (max N K), fun M hM ↦ ?_⟩
  have hM2 : 1 < M := by omega
  have hNM : N ≤ M := by omega
  have hKM : K ≤ M := by omega
  have hb := abs_pairedEtaMoebiusLogHarmonic_le hM2 hNM (by positivity : 0 ≤ e / 2)
    (fun n hn ↦ le_of_lt (by simpa only [Real.dist_eq, sub_zero] using hN n hn))
  have hc := hK M hKM
  simp only [Real.dist_eq, sub_zero] at hc ⊢
  exact hb.trans_lt (by change e / 2 + C / Real.log (M : ℝ) < e; linarith [le_abs_self (C / Real.log (M : ℝ))])

end

end RiemannGaussian
