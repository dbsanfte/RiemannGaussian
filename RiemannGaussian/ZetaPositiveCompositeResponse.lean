/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusConvolutionPositivity

/-!
# A positive arithmetic series with a universal signed zeta-zero source

The nonnegative composite convolution represents one fixed function of
zeta. At every zero to the right of one half this response has a double
pole with leading coefficient minus the square of the actual multiplicity.
The leading zeta phase cancels exactly, independently of a selected filter
or a simplicity hypothesis. The positive triple pole at one is also kept;
positivity of the coefficients alone does not exclude the other poles.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The logarithmic derivative cancels the leading phase of any genuine
finite nonzero meromorphic order, leaving that exact integer as coefficient. -/
theorem meromorphicTrailingCoeffAt_logDeriv_of_order {f : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hf : MeromorphicAt f s) (hn : (n : ℂ) ≠ 0) (ho : meromorphicOrderAt f s = n) :
    meromorphicTrailingCoeffAt (logDeriv f) s = (n : ℂ) := by
  have hc : meromorphicTrailingCoeffAt f s ≠ 0 :=
    hf.meromorphicTrailingCoeffAt_ne_zero (by rw [ho]; exact WithTop.coe_ne_top)
  change meromorphicTrailingCoeffAt (deriv f / f) s = _
  rw [div_eq_mul_inv, hf.deriv.meromorphicTrailingCoeffAt_mul hf.inv,
    meromorphicTrailingCoeffAt_inv, meromorphicTrailingCoeffAt_deriv_of_order hf hn ho]
  exact mul_inv_cancel_right₀ hc _

private theorem response_eq :
    zetaPositiveCompositeResponse = -(logDeriv riemannZeta) ^ 2 +
      deriv riemannZeta * (logDeriv riemannZeta + zetaProperPrimePowerSeries) := by
  funext s
  rw [zetaPositiveCompositeResponse_eq]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Pi.mul_apply]
  ring

/-- The universal response has a genuine meromorphic continuation in
the whole half-plane where its proper-prime-power correction is analytic. -/
theorem meromorphicAt_zetaPositiveCompositeResponse {s : ℂ} (hs : 1 / 2 < s.re) :
    MeromorphicAt zetaPositiveCompositeResponse s := by
  rw [response_eq]
  have hz := meromorphicAt_riemannZeta s
  have hl : MeromorphicAt (logDeriv riemannZeta) s := hz.deriv.div hz
  exact (hl.pow 2).neg.add (hz.deriv.mul
    (hl.add (analyticAt_zetaProperPrimePowerSeries hs).meromorphicAt))

private theorem order_log_zero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (logDeriv riemannZeta) rho.1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta rho.1)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    have hm := analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (show (analyticZetaZeroMultiplicity rho : ℤ) ≠ 0 by omega)
  · rw [meromorphicOrderAt_riemannZeta_nontrivialZero]
    exact WithTop.coe_ne_top

private theorem order_negative_square {s : ℂ}
    (ho : meromorphicOrderAt (logDeriv riemannZeta) s = -1) :
    meromorphicOrderAt (-(logDeriv riemannZeta) ^ 2) s = -2 := by
  have hz := meromorphicAt_riemannZeta s
  have hl : MeromorphicAt (logDeriv riemannZeta) s := hz.deriv.div hz
  rw [← meromorphicOrderAt_neg, meromorphicOrderAt_pow hl, ho]
  change ((2 : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_mul, WithTop.coe_inj]
  norm_num

private theorem order_log_add_correction {s : ℂ} (hs : 1 / 2 < s.re)
    (ho : meromorphicOrderAt (logDeriv riemannZeta) s = -1) :
    meromorphicOrderAt (logDeriv riemannZeta + zetaProperPrimePowerSeries) s = -1 := by
  have he := analyticAt_zetaProperPrimePowerSeries hs
  rw [meromorphicOrderAt_add_eq_left_of_lt he.meromorphicAt, ho]
  rw [ho]
  apply lt_of_lt_of_le _ he.meromorphicOrderAt_nonneg
  change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.mpr (by norm_num)

private theorem order_lower_zero (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (deriv riemannZeta * (logDeriv riemannZeta + zetaProperPrimePowerSeries)) rho.1 =
      ((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) := by
  have hz := meromorphicAt_riemannZeta rho.1
  have hl : MeromorphicAt (logDeriv riemannZeta) rho.1 := hz.deriv.div hz
  rw [meromorphicOrderAt_mul hz.deriv
      (hl.add (analyticAt_zetaProperPrimePowerSeries hrho).meromorphicAt),
    meromorphicOrderAt_deriv_riemannZeta_nontrivialZero,
    order_log_add_correction hrho (order_log_zero rho)]
  change (((analyticZetaZeroMultiplicity rho : ℤ) - 1 : ℤ) : WithTop ℤ) +
    ((-1 : ℤ) : WithTop ℤ) = _
  rw [← WithTop.coe_add, WithTop.coe_inj]
  ring

private theorem order_main_lt_lower (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt (-(logDeriv riemannZeta) ^ 2) rho.1 <
      meromorphicOrderAt (deriv riemannZeta * (logDeriv riemannZeta + zetaProperPrimePowerSeries)) rho.1 := by
  rw [order_negative_square (order_log_zero rho), order_lower_zero rho hrho]
  change ((-2 : ℤ) : WithTop ℤ) < (((analyticZetaZeroMultiplicity rho : ℤ) - 2 : ℤ) : WithTop ℤ)
  rw [WithTop.coe_lt_coe]
  have := analyticZetaZeroMultiplicity_positive rho
  omega

/-- One fixed arithmetic response has an exact double pole at every
right-half zeta zero, regardless of the zero's multiplicity. -/
theorem meromorphicOrderAt_zetaPositiveCompositeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicOrderAt zetaPositiveCompositeResponse rho.1 = -2 := by
  have hz := meromorphicAt_riemannZeta rho.1
  have hl : MeromorphicAt (logDeriv riemannZeta) rho.1 := hz.deriv.div hz
  rw [response_eq, meromorphicOrderAt_add_eq_left_of_lt
      (hz.deriv.mul (hl.add (analyticAt_zetaProperPrimePowerSeries hrho).meromorphicAt))
      (order_main_lt_lower rho hrho), order_negative_square (order_log_zero rho)]

/-- The leading coefficient at each zero is exactly the negative real
integer square `-m^2`; no unknown derivative phase survives. -/
theorem meromorphicTrailingCoeffAt_zetaPositiveCompositeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    meromorphicTrailingCoeffAt zetaPositiveCompositeResponse rho.1 =
      -(analyticZetaZeroMultiplicity rho : ℂ) ^ 2 := by
  have hz := meromorphicAt_riemannZeta rho.1
  have hl : MeromorphicAt (logDeriv riemannZeta) rho.1 := hz.deriv.div hz
  have hc := hz.deriv.mul (hl.add (analyticAt_zetaProperPrimePowerSeries hrho).meromorphicAt)
  have hm : ((analyticZetaZeroMultiplicity rho : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho))
  rw [response_eq, hc.meromorphicTrailingCoeffAt_add_eq_left_of_lt (order_main_lt_lower rho hrho),
    meromorphicTrailingCoeffAt_neg, hl.meromorphicTrailingCoeffAt_pow,
    meromorphicTrailingCoeffAt_logDeriv_of_order hz hm (meromorphicOrderAt_riemannZeta_nontrivialZero rho)]
  norm_cast

/-- The exact signed pole coefficient is retained as a punctured
complex limit of the universal positive arithmetic response. -/
theorem tendsto_zetaPositiveCompositeResponse_mul_sq (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * zetaPositiveCompositeResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) ^ 2)) := by
  change Tendsto ((fun s : ℂ ↦ s - rho.1) ^ (2 : ℕ) * zetaPositiveCompositeResponse) _ _
  simpa [meromorphicOrderAt_zetaPositiveCompositeResponse rho hrho,
    meromorphicTrailingCoeffAt_zetaPositiveCompositeResponse rho hrho, smul_eq_mul] using
    (meromorphicAt_zetaPositiveCompositeResponse hrho).tendsto_nhds_meromorphicTrailingCoeffAt

private theorem order_log_one : meromorphicOrderAt (logDeriv riemannZeta) 1 = -1 := by
  apply meromorphicOrderAt_logDeriv_eq_neg_one (meromorphicAt_riemannZeta 1)
  · rw [meromorphicOrderAt_riemannZeta_one]
    norm_num
  · rw [meromorphicOrderAt_riemannZeta_one]
    exact WithTop.coe_ne_top

private theorem order_deriv_one : meromorphicOrderAt (deriv riemannZeta) 1 = -2 := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0)
    meromorphicOrderAt_riemannZeta_one

private theorem order_lower_one :
    meromorphicOrderAt (deriv riemannZeta * (logDeriv riemannZeta + zetaProperPrimePowerSeries)) 1 = -3 := by
  have hz := meromorphicAt_riemannZeta 1
  have hl : MeromorphicAt (logDeriv riemannZeta) 1 := hz.deriv.div hz
  rw [meromorphicOrderAt_mul hz.deriv (hl.add
      (analyticAt_zetaProperPrimePowerSeries (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)).meromorphicAt),
    order_deriv_one, order_log_add_correction (by norm_num) order_log_one]
  change ((-2 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) = ((-3 : ℤ) : WithTop ℤ)
  rw [← WithTop.coe_add, WithTop.coe_inj]
  norm_num

/-- The positive response retains a triple pole at one. This pole
must be handled in any global argument using coefficient positivity. -/
theorem meromorphicOrderAt_zetaPositiveCompositeResponse_one :
    meromorphicOrderAt zetaPositiveCompositeResponse 1 = -3 := by
  have hz := meromorphicAt_riemannZeta 1
  have hl : MeromorphicAt (logDeriv riemannZeta) 1 := hz.deriv.div hz
  rw [response_eq, meromorphicOrderAt_add_eq_right_of_lt (hl.pow 2).neg,
    order_lower_one]
  rw [order_lower_one, order_negative_square order_log_one]
  change ((-3 : ℤ) : WithTop ℤ) < ((-2 : ℤ) : WithTop ℤ)
  exact WithTop.coe_lt_coe.mpr (by norm_num)

private theorem trailing_zeta_one : meromorphicTrailingCoeffAt riemannZeta 1 = 1 := by
  have h := (meromorphicAt_riemannZeta 1).tendsto_nhds_meromorphicTrailingCoeffAt
  have h' : Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1)
      (𝓝 (meromorphicTrailingCoeffAt riemannZeta 1)) := by
    change Tendsto ((fun s : ℂ ↦ s - 1) * riemannZeta) _ _
    simpa [meromorphicOrderAt_riemannZeta_one, smul_eq_mul] using h
  exact tendsto_nhds_unique h' riemannZeta_residue_one

/-- The leading triple pole at one has positive coefficient exactly one,
whereas every right-half zero has coefficient `-m^2` at its double pole. -/
theorem meromorphicTrailingCoeffAt_zetaPositiveCompositeResponse_one :
    meromorphicTrailingCoeffAt zetaPositiveCompositeResponse 1 = 1 := by
  have hz := meromorphicAt_riemannZeta 1
  have he := analyticAt_zetaProperPrimePowerSeries (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)
  have hlog : MeromorphicAt (logDeriv riemannZeta) 1 := hz.deriv.div hz
  have hlt : meromorphicOrderAt (deriv riemannZeta *
      (logDeriv riemannZeta + zetaProperPrimePowerSeries)) 1 <
      meromorphicOrderAt (-(logDeriv riemannZeta) ^ 2) 1 := by
    rw [order_lower_one, order_negative_square order_log_one]
    change ((-3 : ℤ) : WithTop ℤ) < ((-2 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have he_lt : meromorphicOrderAt (logDeriv riemannZeta) 1 <
      meromorphicOrderAt zetaProperPrimePowerSeries 1 := by
    rw [order_log_one]
    apply lt_of_lt_of_le _ he.meromorphicOrderAt_nonneg
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  rw [response_eq, add_comm (-(logDeriv riemannZeta) ^ 2),
    ((hlog.pow 2).neg).meromorphicTrailingCoeffAt_add_eq_left_of_lt hlt,
    hz.deriv.meromorphicTrailingCoeffAt_mul (hlog.add he.meromorphicAt),
    he.meromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt he_lt,
    meromorphicTrailingCoeffAt_deriv_of_order hz (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0)
      meromorphicOrderAt_riemannZeta_one,
    meromorphicTrailingCoeffAt_logDeriv_of_order hz (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0)
      meromorphicOrderAt_riemannZeta_one, trailing_zeta_one]
  norm_num

/-- The previous multiplicity-weighted composite Wronskian is exactly
the universal positive response times one retained derivative cofactor. -/
theorem zetaMoebiusCompositeWronskian_eq_positiveResponse (rho : NontrivialZetaZero) (s : ℂ) :
    zetaMoebiusCompositeWronskian rho s =
      (-deriv riemannZeta s / (s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1)) *
        zetaPositiveCompositeResponse s := by
  simp only [zetaMoebiusCompositeWronskian, zetaMoebiusWronskian, zetaMoebiusPrimeWronskian,
    zetaMoebiusWronskianCofactor, zetaPositiveCompositeResponse, div_eq_mul_inv]
  ring

end

end RiemannGaussian
