import RiemannGaussian.EtaZetaMultiplicitySchwarz

/-!
# Prime positivity with the full analytic zero multiplicity

The three-four-one prime product uses the higher-order small value proved
from the actual eta strip bound. Its gap exponent is `4*m-3`: the repeated
zero supplies `4*m`, while the real-axis pole costs three powers. This is
an arithmetic constraint on the original zero, with no assumed derivative
estimate or vanishing order.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The classical prime-product inequality retains the entire actual
multiplicity in its horizontal zero-gap exponent. -/
theorem one_le_etaPrimeProduct_multiplicity_gap (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    1 ≤ (16 * 3200 ^ 3 * 8 ^ (4 * analyticZetaZeroMultiplicity rho + 4) *
      (|rho.1.im| + 21) ^ 10 / |rho.1.im| ^ 5) *
        (1 - rho.1.re) ^ (4 * analyticZetaZeroMultiplicity rho - 3) := by
  let d := 1 - rho.1.re
  let t := |rho.1.im|
  let m := analyticZetaZeroMultiplicity rho
  have hm : 1 ≤ m := analyticZetaZeroMultiplicity_positive rho
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hdhi : d ≤ 1 / 4 := by dsimp [d]; linarith
  have him := NontrivialZetaZero.im_ne_zero_of_eta_mass rho
  have ht : 0 < t := abs_pos.mpr him
  have hbase : (1 + (d : ℂ) + I * rho.1.im) =
      (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) := by dsimp [d]; push_cast; ring
  have hvalue : ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ≤
      8 * (t + 21) ^ 2 * (8 * d) ^ m / t := by
    have him' : (1 + (d : ℂ) + I * rho.1.im).im = rho.1.im := by simp
    calc
      _ ≤ ‖riemannZeta₁ (1 + (d : ℂ) + I * rho.1.im)‖ / t := by
        simpa only [him', t] using norm_riemannZeta_le_poleRemoved_div_abs_im
          (s := 1 + (d : ℂ) + I * rho.1.im) (by rw [him']; exact him)
      _ ≤ _ := by
        rw [hbase]
        exact div_le_div_of_nonneg_right
          (norm_riemannZeta₁_reflected_across_one_le_multiplicity rho hrho) ht.le
  have hreal := norm_riemannZeta_one_add_le_etaPole hd hdhi
  have hdouble := norm_riemannZeta_one_add_double_ordinate_le hd hdhi him
  have hp := one_le_riemannZeta_three_four_one hd rho.1.im
  have hupper : ‖riemannZeta (1 + (d : ℂ))‖ ^ 3 *
      ‖riemannZeta (1 + (d : ℂ) + I * rho.1.im)‖ ^ 4 *
      ‖riemannZeta (1 + (d : ℂ) + 2 * I * rho.1.im)‖ ≤
      (3200 / d) ^ 3 * (8 * (t + 21) ^ 2 * (8 * d) ^ m / t) ^ 4 *
        (16 * (t + 21) ^ 2 / t) := by
    gcongr
  refine (hp.trans hupper).trans_eq ?_
  change (3200 / d) ^ 3 * (8 * (t + 21) ^ 2 * (8 * d) ^ m / t) ^ 4 *
      (16 * (t + 21) ^ 2 / t) =
    (16 * 3200 ^ 3 * 8 ^ (4 * m + 4) * (t + 21) ^ 10 / t ^ 5) * d ^ (4 * m - 3)
  have he' : 4 * m + 4 = (4 * m - 3) + 7 := by omega
  have hpow (x : ℝ) : x ^ (m * 4) = x ^ 3 * x ^ (m * 4 - 3) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [div_pow, mul_pow, he', pow_add]
  field_simp
  ring_nf
  rw [hpow d, hpow 8]
  ring

/-- A zero near the pole line has an explicit lower bound on the
`4*m-3` power of its horizontal distance from that line. -/
theorem etaPrimeProduct_multiplicity_gap_power_le (rho : NontrivialZetaZero)
    (hrho : 15 / 16 ≤ rho.1.re) :
    |rho.1.im| ^ 5 /
      (16 * 3200 ^ 3 * 8 ^ (4 * analyticZetaZeroMultiplicity rho + 4) * (|rho.1.im| + 21) ^ 10) ≤
        (1 - rho.1.re) ^ (4 * analyticZetaZeroMultiplicity rho - 3) := by
  have ht : 0 < |rho.1.im| := abs_pos.mpr (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hc : 0 < 16 * 3200 ^ 3 * 8 ^ (4 * analyticZetaZeroMultiplicity rho + 4) *
      (|rho.1.im| + 21) ^ 10 := by positivity
  rw [div_le_iff₀ hc]
  have h := one_le_etaPrimeProduct_multiplicity_gap rho hrho
  rw [div_mul_eq_mul_div] at h
  have hp := (le_div_iff₀ (pow_pos ht 5)).mp h
  simpa only [one_mul, mul_one, mul_comm] using hp

end

end RiemannGaussian
