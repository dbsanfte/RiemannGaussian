import RiemannGaussian.EtaMoebiusFirstMean
import RiemannGaussian.EtaMoebiusBilinearWindow

/-!
# The source in a quarter-power quotient range

Direct signed averaging controls all divisors through `u^3` on the physical
window starting at `u^4` and of length `u^4`. Its error is at most a fixed
constant times `u^(2-4*Re(rho))`. Consequently the remaining complex first
mean tends to the nonzero source at a hypothetical right-half zero.

The remaining mean is an exact single signed product sum with the literal
window weights. An independent upper bound below the source norm would
close the reductio. No such upper bound, mean-square extension, or RH proof
is asserted here.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The quartic window with cubic divisor cutoff leaves fewer than `2*u` possible quotient indices, including the clipped endpoint. -/
theorem pairedEtaMoebiusHighQuotientCap_quartic_lt
    {u t : ℕ} (ht : t < u ^ 4) :
    (u ^ 4 + t) / (u ^ 3 + 1) < 2 * u := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < u ^ 3 + 1)).mpr
  have h : u ^ 4 + t < 2 * u ^ 4 := by omega
  apply h.trans_le
  nlinarith

/-- Taking the complete low divisor selection gives the already defined complex small-family average. -/
theorem pairedEtaCompletedMoebiusSelectedFirstMean_Icc
    (rho : NontrivialZetaZero) (A D : ℕ) :
    pairedEtaCompletedMoebiusSelectedFirstMean rho (Finset.Icc 1 D) A =
      pairedEtaCompletedMoebiusSmallAverage rho A A D := rfl

/-- The whole low family through `u^3` has a vanishing first-mean allowance on the quartic physical window whenever the real part exceeds one half. -/
theorem norm_pairedEtaCompletedMoebiusSmallAverage_quartic_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 1 ≤ u) :
    ‖pairedEtaCompletedMoebiusSmallAverage rho (u ^ 4) (u ^ 4) (u ^ 3)‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have h34 : u ^ 3 ≤ u ^ 4 := by
    exact Nat.pow_le_pow_right hu (by norm_num)
  have hb := norm_pairedEtaCompletedMoebiusSelectedFirstMean_le rho
    (S := Finset.Icc 1 (u ^ 3)) (A := u ^ 4) (D := u ^ 3)
    (fun _ h ↦ h) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 4 (by omega))) h34
  rw [pairedEtaCompletedMoebiusSelectedFirstMean_Icc] at hb
  apply hb.trans_eq
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul huR.le]
  rw [← pow_mul, ← Real.rpow_natCast (u : ℝ) (3 * 2), mul_assoc, ← Real.rpow_add huR]
  congr 2
  norm_num
  ring

/-- Direct parity cancellation makes the entire low complex average vanish on quartic windows, without a mean-square sampling assertion. -/
theorem pairedEtaCompletedMoebiusSmallAverage_quartic_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusSmallAverage rho (u ^ 4) (u ^ 4) (u ^ 3))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 4 * rho.1.re)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : 0 < 4 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun _ hu ↦
      norm_pairedEtaCompletedMoebiusSmallAverage_quartic_le rho hu)
  simpa only [mul_zero] using hp.const_mul (pairedEtaMoebiusFirstMeanConstant rho)

/-- The first complex mean of the original completed large-divisor aggregate, keeping all signed terms before averaging. -/
def pairedEtaCompletedMoebiusLargeFirstMean (rho : NontrivialZetaZero) (A D : ℕ) : ℂ :=
  (∑ t ∈ Finset.range A, pairedEtaCompletedMoebiusLargeAggregate rho (A + t) D) / A

/-- The original source identity survives the first-mean operation exactly. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_eq_source_sub
    (rho : NontrivialZetaZero) {A D : ℕ} (hA : 2 ≤ A) (hDA : D ≤ A) :
    pairedEtaCompletedMoebiusLargeFirstMean rho A D =
      pairedEtaCompletedMoebiusSource rho - pairedEtaCompletedMoebiusSmallAverage rho A A D := by
  have hAne : (A : ℂ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  unfold pairedEtaCompletedMoebiusLargeFirstMean pairedEtaCompletedMoebiusSmallAverage
  simp_rw [pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub rho
    (hA.trans (Nat.le_add_right A _)) (hDA.trans (Nat.le_add_right A _))]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- The whole remaining first mean differs from the source by the explicit quartic low-family allowance. -/
theorem norm_pairedEtaCompletedMoebiusLargeFirstMean_quartic_sub_source_le
    (rho : NontrivialZetaZero) {u : ℕ} (hu : 2 ≤ u) :
    ‖pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3) -
        pairedEtaCompletedMoebiusSource rho‖ ≤
      pairedEtaMoebiusFirstMeanConstant rho * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have h34 : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  rw [pairedEtaCompletedMoebiusLargeFirstMean_eq_source_sub rho
    (hu.trans (Nat.le_self_pow (by decide : 4 ≠ 0) u)) h34,
    sub_sub_cancel_left, norm_neg]
  exact norm_pairedEtaCompletedMoebiusSmallAverage_quartic_le rho (by omega)

/-- At a hypothetical right-half zero, the unchanged large-divisor first mean on quartic windows tends to the nonzero source itself. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_quartic_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun u : ℕ ↦ pairedEtaCompletedMoebiusLargeFirstMean rho (u ^ 4) (u ^ 3))
      atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hz := (tendsto_const_nhds (x := pairedEtaCompletedMoebiusSource rho)).sub
    (pairedEtaCompletedMoebiusSmallAverage_quartic_tendsto_zero rho hrho)
  simp only [sub_zero] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 2] with u hu
  exact (pairedEtaCompletedMoebiusLargeFirstMean_eq_source_sub rho
    (hu.trans (Nat.le_self_pow (by decide : 4 ≠ 0) u))
    (Nat.pow_le_pow_right (by omega) (by norm_num))).symm

private theorem sum_window_prefix (A : ℕ) (g : ℕ → ℂ) :
    (∑ t ∈ Finset.range A, ∑ n ∈ Finset.Icc 1 (A + t), g n) =
      ∑ n ∈ Finset.Icc 1 (A + A), ((A - (n - A) : ℕ) : ℂ) * g n := by
  have hp (t : ℕ) (ht : t ∈ Finset.range A) :
      (∑ n ∈ Finset.Icc 1 (A + t), g n) =
        ∑ n ∈ Finset.Icc 1 (A + A), if n ≤ A + t then g n else 0 := by
    have he : (Finset.Icc 1 (A + A)).filter (fun n ↦ n ≤ A + t) = Finset.Icc 1 (A + t) := by
      ext n
      have htA := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← Finset.sum_filter, he]
  rw [Finset.sum_congr rfl hp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc := card_pairedEtaBilinearPrefixWindow A A n n
  simp only [and_self, max_self] at hc
  rw [hc]

/-- The remaining first mean is one exact signed product sum with the literal ramp window; no product correlation or phase is discarded inside that sum. -/
theorem pairedEtaCompletedMoebiusLargeFirstMean_eq_product_window
    (rho : NontrivialZetaZero) (A D : ℕ) :
    pairedEtaCompletedMoebiusLargeFirstMean rho A D =
      pairedEtaXiCompletionFactor rho.1 *
        ∑ n ∈ Finset.Icc 1 (A + A),
          (pairedEtaBilinearPrefixWindowKernel A A n n : ℂ) *
            (pairedEtaMoebiusHighProductCoefficient D n : ℂ) * (n : ℂ) ^ (-rho.1) := by
  simp only [pairedEtaCompletedMoebiusLargeFirstMean,
    pairedEtaCompletedMoebiusLargeAggregate_eq_product_prefix,
    pairedEtaMoebiusHighProductPrefix, ← Finset.mul_sum]
  rw [sum_window_prefix, mul_div_assoc, Finset.sum_div]
  apply congrArg (fun z : ℂ ↦ pairedEtaXiCompletionFactor rho.1 * z)
  apply Finset.sum_congr rfl
  intro n _
  simp only [pairedEtaBilinearPrefixWindowKernel, max_self,
    Complex.ofReal_div, Complex.ofReal_natCast]
  ring

end

end RiemannGaussian
