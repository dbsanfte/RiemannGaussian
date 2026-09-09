/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteLaplaceCurvature
import RiemannGaussian.EtaMoebiusFinitePrefix
import RiemannGaussian.SuzukiEtaFiniteSmoothSource

/-!
# The literal eta logarithmic-gap expansion

The finite Laplace identity is applied to the unchanged odd/even eta
prefixes. The complete bilinear logarithmic-gap sum converges throughout
`Re s > 0`; no rearrangement into separately infinite odd/even sums is used.
The expansion reaches the actual finite smoothed source, retaining the
completion curvature and the original denominator.
-/

open Complex Filter Set Topology
namespace RiemannGaussian
noncomputable section

/-- The complete finite signed eta pair sum, with the original common
prefix cutoff and the two logarithmic frequencies. -/
def pairedEtaFiniteLogGapSum (N : ℕ) (s : ℂ) : ℂ :=
  finiteLaplaceGapSum (Finset.Icc 1 (2 * N))
    (fun n => (pairedEtaDirichletSign n : ℂ)) (fun n => Real.log n) s

/-- The zeroth finite Laplace moment is the literal eta prefix at every
complex argument, not merely on a selected vertical line. -/
theorem finiteLaplaceMoment_eta_zero (N : ℕ) :
    finiteLaplaceMoment (Finset.Icc 1 (2 * N))
      (fun n => (pairedEtaDirichletSign n : ℂ)) (fun n => Real.log n) 0 =
        pairedEtaCorePartialSum N := by
  funext s
  rw [← pairedEtaUnpairedDirichletPrefix_even]
  unfold finiteLaplaceMoment pairedEtaUnpairedDirichletPrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnzero : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [Complex.cpow_def_of_ne_zero hnzero,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) from (Complex.ofReal_log hnpos.le).symm]
  simp only [pow_zero, mul_one]
  congr 2
  ring

/-- The pair phase is the original integer-product phase. Its coefficient
keeps both parity signs; no conjugation turns it into a Gram entry. -/
theorem pairedEtaFiniteLogGapSum_eq_dirichlet (N : ℕ) (s : ℂ) :
    pairedEtaFiniteLogGapSum N s =
      ∑ m ∈ Finset.Icc 1 (2 * N), ∑ n ∈ Finset.Icc 1 (2 * N),
        (pairedEtaDirichletSign m : ℂ) * (pairedEtaDirichletSign n : ℂ) *
          ((m * n : ℕ) : ℂ) ^ (-s) * ((Real.log m : ℂ) - (Real.log n : ℂ)) ^ 2 := by
  unfold pairedEtaFiniteLogGapSum finiteLaplaceGapSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hp : 0 < ((m * n : ℕ) : ℝ) := by simpa only [Nat.cast_mul] using mul_pos hmpos hnpos
  have hz : ((m * n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hz,
    show Complex.log ((m * n : ℕ) : ℂ) = (Real.log ((m * n : ℕ) : ℝ) : ℂ) from
      (Complex.ofReal_log hp.le).symm, Nat.cast_mul,
    Real.log_mul hmpos.ne' hnpos.ne', Complex.ofReal_add]
  congr 3
  ring

/-- The actual finite eta curvature has exactly the signed logarithmic-gap
expansion, including at its zeros. -/
theorem pairedEtaCorePartialSum_curvature_eq_logGap (N : ℕ) (s : ℂ) :
    deriv (pairedEtaCorePartialSum N) s ^ 2 -
      pairedEtaCorePartialSum N s * deriv (deriv (pairedEtaCorePartialSum N)) s =
        -(1 / 2 : ℂ) * pairedEtaFiniteLogGapSum N s := by
  simpa only [finiteLaplaceMoment_eta_zero, pairedEtaFiniteLogGapSum] using
    finiteLaplace_curvature_eq_gapSum (Finset.Icc 1 (2 * N))
      (fun n => (pairedEtaDirichletSign n : ℂ)) (fun n => Real.log n) s

/-- The entire common-cutoff signed pair sum converges in the full
positive half-plane, including eta zeros. The assertion is a limit of
the complete finite sums, not a separate unpaired double series. -/
theorem tendsto_pairedEtaFiniteLogGapSum {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N => pairedEtaFiniteLogGapSum N s) atTop
      (𝓝 (-2 * (deriv pairedEtaCore s ^ 2 - pairedEtaCore s * deriv (deriv pairedEtaCore) s))) := by
  have h0 := tendstoLocallyUniformlyOn_pairedEtaCorePartialSum
  have h1 := h0.deriv
    (Eventually.of_forall fun N => (differentiable_pairedEtaCorePartialSum N).differentiableOn)
    (Complex.isOpen_re_gt 0)
  have h2 := h1.deriv
    (Eventually.of_forall fun N w _ =>
      ((differentiable_pairedEtaCorePartialSum N).analyticAt w).deriv.differentiableAt.differentiableWithinAt)
    (Complex.isOpen_re_gt 0)
  have h := (((h1.tendsto_at hs).pow 2).sub ((h0.tendsto_at hs).mul
    (h2.tendsto_at hs))).const_mul (-2 : ℂ)
  apply h.congr'
  filter_upwards with N
  have he := pairedEtaCorePartialSum_curvature_eq_logGap N s
  change -2 * (deriv (pairedEtaCorePartialSum N) s ^ 2 -
    pairedEtaCorePartialSum N s * deriv (deriv (pairedEtaCorePartialSum N)) s) = _
  rw [he]
  ring

/-- The finite arithmetic Wronskian retains the explicit completion
curvature alongside all logarithmic-gap pairs. -/
theorem suzukiEtaFiniteCarrier_wronskian_eq_logGap (N : ℕ) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    deriv (pairedEtaCorePartialSum N) s * suzukiEtaFiniteCarrierDenominator N s -
      pairedEtaCorePartialSum N s * deriv (suzukiEtaFiniteCarrierDenominator N) s =
      -(1 / 2 : ℂ) * pairedEtaFiniteLogGapSum N s -
        deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCorePartialSum N s ^ 2 := by
  rw [suzukiEtaFiniteCarrier_wronskian_eq_curvature N hs,
    pairedEtaCorePartialSum_curvature_eq_logGap]

/-- The complete finite smooth source has its actual signed pair
expansion, retaining the smoothing denominator and completion term.
This includes all totalized finite values; it asserts no sign bound. -/
theorem suzukiEtaFiniteSpectralSmoothSource_eq_logGap (r : ℝ) (N : ℕ) {s : ℂ}
    (hs : s ∈ pairedEtaCompletionDomain) :
    suzukiEtaFiniteSpectralSmoothSource r N s =
      -I * (r : ℂ) ^ 2 * pairedEtaCorePartialSum N s ^ 2 *
        starRingEnd ℂ (pairedEtaFiniteLogGapSum N s +
          2 * deriv pairedEtaArithmeticXiRegularCorrection s * pairedEtaCorePartialSum N s ^ 2) /
        ((normSq (suzukiEtaFiniteCarrierDenominator N s) +
          r ^ 2 * normSq (pairedEtaCorePartialSum N s) : ℝ) : ℂ) ^ 2 := by
  unfold suzukiEtaFiniteSpectralSmoothSource
  rw [suzukiEtaFiniteCarrier_wronskian_eq_logGap N hs]
  simp only [map_sub, map_neg, map_div₀, map_one, map_ofNat, map_mul, map_add]
  ring

end
end RiemannGaussian
