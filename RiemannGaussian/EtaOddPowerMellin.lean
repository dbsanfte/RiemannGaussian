import RiemannGaussian.EtaOddPowerQuadrature

/-!
# The retained Mellin phase of a complete grouped inverse block

The complete top-half odd power sum has an explicit nonzero complex main
coefficient and a decaying error. The main coefficient retains its ordinate
dependence. In particular, summing this whole equal-cutoff block before
taking its norm does not remove its positive cutoff power.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The exact complex Mellin coefficient for the top-half odd inverse
block, including its oscillatory numerator and its ordinate denominator. -/
def pairedEtaOddTopPowerCoefficient (rho : NontrivialZetaZero) : ℂ :=
  ((2 : ℂ) ^ (1 - rho.1) - 1) / (2 * (1 - rho.1))

/-- The Mellin coefficient cannot vanish anywhere in the open critical
strip, since the numerator's power has norm strictly greater than one. -/
theorem pairedEtaOddTopPowerCoefficient_ne_zero (rho : NontrivialZetaZero) :
    pairedEtaOddTopPowerCoefficient rho ≠ 0 := by
  have hden : 1 - rho.1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hpow : 1 < ‖(2 : ℂ) ^ (1 - rho.1)‖ := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1 - rho.1)
    simp only [Complex.ofReal_ofNat, Complex.sub_re, Complex.one_re] at h
    rw [h]
    exact Real.one_lt_rpow (by norm_num) (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))
  apply div_ne_zero _ (mul_ne_zero (by norm_num) hden)
  intro h
  have hp := sub_eq_zero.mp h
  rw [hp, norm_one] at hpow
  exact (lt_irrefl (1 : ℝ)) hpow

/-- The exact integral main term retains the complete complex cutoff
power, without taking its norm or replacing its coefficient by a modulus. -/
theorem half_integral_cpow_eq_pairedEtaOddTopPowerMain (rho : NontrivialZetaZero) (K : ℕ) :
    (∫ t : ℝ in (2 * K : ℝ)..(4 * K : ℝ), (t : ℂ) ^ (-rho.1)) / 2 =
      ((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho := by
  rw [integral_cpow (Or.inl (by simp only [Complex.neg_re]; linarith [NontrivialZetaZero.re_lt_one rho]))]
  rw [show -rho.1 + 1 = 1 - rho.1 by ring]
  have h2 : ((2 * K : ℝ) : ℂ) = ((2 * K : ℕ) : ℂ) := by push_cast; rfl
  have h4 : ((4 * K : ℝ) : ℂ) = ((4 * K : ℕ) : ℂ) := by push_cast; rfl
  rw [h2, h4, show 4 * K = 2 * (2 * K) by omega, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  unfold pairedEtaOddTopPowerCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- The full grouped odd power sum has a one-power-smaller error from
its exact complex Mellin main term, at every positive cutoff parameter. -/
theorem norm_pairedEtaOddTopPowerSum_sub_main_le (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaOddTopPowerSum rho K -
      ((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho‖ ≤
        (‖rho.1‖ / 2) * (2 * K : ℝ) ^ (-rho.1.re) := by
  rw [← half_integral_cpow_eq_pairedEtaOddTopPowerMain]
  refine (norm_pairedEtaOddTopPowerSum_sub_half_integral_le rho hK).trans_eq ?_
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Real.rpow_sub (by positivity : (0 : ℝ) < 2 * K), Real.rpow_one]
  field_simp

/-- An explicit lower estimate for the norm of the complete grouped
sum, obtained only after the complex Mellin identity and its error bound. -/
theorem pairedEtaOddTopPowerSum_norm_lower (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaOddTopPowerCoefficient rho‖ * (2 * K : ℝ) ^ (1 - rho.1.re) -
      (‖rho.1‖ / 2) * (2 * K : ℝ) ^ (-rho.1.re) ≤ ‖pairedEtaOddTopPowerSum rho K‖ := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  have hmain : ‖((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho‖ =
      ‖pairedEtaOddTopPowerCoefficient rho‖ * (2 * K : ℝ) ^ (1 - rho.1.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < 2 * K)]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have htri := norm_le_insert' (((2 * K : ℝ) : ℂ) ^ (1 - rho.1) * pairedEtaOddTopPowerCoefficient rho)
    (pairedEtaOddTopPowerSum rho K)
  rw [hmain, norm_sub_rev] at htri
  linarith [norm_pairedEtaOddTopPowerSum_sub_main_le rho hK]

/-- The complete grouped sum still has a positive-power lower bound
once its explicit one-power-smaller error is below half the main term. -/
theorem pairedEtaOddTopPowerSum_norm_lower_of_cutoff (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K)
    (hlarge : ‖rho.1‖ ≤ (2 * K : ℝ) * ‖pairedEtaOddTopPowerCoefficient rho‖) :
    (‖pairedEtaOddTopPowerCoefficient rho‖ / 2) * (2 * K : ℝ) ^ (1 - rho.1.re) ≤
      ‖pairedEtaOddTopPowerSum rho K‖ := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  have hp : (2 * K : ℝ) ^ (1 - rho.1.re) = (2 * K : ℝ) * (2 * K : ℝ) ^ (-rho.1.re) := by
    rw [show 1 - rho.1.re = 1 + (-rho.1.re) by ring, Real.rpow_add (by positivity), Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * K) (-rho.1.re))
  have hlower := pairedEtaOddTopPowerSum_norm_lower rho hK
  rw [hp] at hlower ⊢
  nlinarith

/-- Even after all equal-cutoff divisor phases in the top half are
summed, their grouped coefficient is unbounded at every actual zero.
This is a coefficient statement, not divergence of the original current. -/
theorem pairedEtaOddTopPowerSum_norm_tendsto_atTop (rho : NontrivialZetaZero) :
    Tendsto (fun K : ℕ ↦ ‖pairedEtaOddTopPowerSum rho K‖) atTop atTop := by
  have hb : 0 < ‖pairedEtaOddTopPowerCoefficient rho‖ :=
    norm_pos_iff.mpr (pairedEtaOddTopPowerCoefficient_ne_zero rho)
  have hscale : Tendsto (fun K : ℕ ↦ (2 * K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hlarge := (hscale.const_mul_atTop hb).eventually_ge_atTop ‖rho.1‖
  have hbound := ((tendsto_rpow_atTop (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))).comp hscale).const_mul_atTop
    (by positivity : 0 < ‖pairedEtaOddTopPowerCoefficient rho‖ / 2)
  apply tendsto_atTop_mono' atTop _ hbound
  filter_upwards [eventually_ge_atTop 1, hlarge] with K hK hlargeK
  exact pairedEtaOddTopPowerSum_norm_lower_of_cutoff rho hK (by simpa only [mul_comm] using hlargeK)

end

end RiemannGaussian
