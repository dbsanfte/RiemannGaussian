/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiGlobalBlaschkeSplit

/-!
# The full weighted contribution of a simple carrier pole

At an actual carrier pole, the logarithmic derivative equals `i`.
Differentiating the actual denominator shows that its simple residue is
the reciprocal logarithmic-derivative slope. Every finite complex test
then has an exact reflected bilinear pole contribution. It involves the
test at both `c` and `conj c`, not a norm square at one point. This retains
the phase and all mixed terms needed in a signed contour comparison.

Arbitrary-order poles remain covered by `SuzukiCarrierPoleResidues`; the
simple-pole formula here is explicitly conditional on that analytic order.
-/

open Complex Filter Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The derivative of the genuine carrier denominator at one of its
poles is `i*A*q'`. This connects the residue to the full xi logarithmic
derivative without any estimate of the xi amplitude. -/
theorem deriv_suzukiXiEValue_at_pole {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    deriv suzukiXiEValue c =
      I * riemannXiSpectral c * deriv (logDeriv riemannXiSpectral) c := by
  have hq : AnalyticAt ℂ (logDeriv riemannXiSpectral) c := by
    simpa only [logDeriv] using
      (analyticAt_riemannXiSpectral c).deriv.div (analyticAt_riemannXiSpectral c) hxi
  have heq : suzukiXiEValue =ᶠ[𝓝 c] fun z =>
      riemannXiSpectral z * (1 + I * logDeriv riemannXiSpectral z) := by
    filter_upwards [(analyticAt_riemannXiSpectral c).continuousAt.eventually_ne hxi] with z hz
    simpa only [suzukiXiEValue, ofReal_one, mul_one] using
      analyticEValue_riemannXiSpectral_eq_mul_logDeriv hz 1
  have hder := heq.deriv_eq
  have hf : DifferentiableAt ℂ (fun z => 1 + I * logDeriv riemannXiSpectral z) c := by
    fun_prop
  rw [deriv_fun_mul (analyticAt_riemannXiSpectral c).differentiableAt
    hf] at hder
  rw [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_mul_I,
    add_neg_cancel, mul_zero, zero_add, deriv_const_add, deriv_const_mul_field] at hder
  exact hder.trans (by ring)

/-- A simple actual carrier pole has nonzero logarithmic-derivative
slope. Higher-order poles must use the full Taylor-jet residue instead. -/
theorem deriv_logDeriv_riemannXiSpectral_ne_zero_at_simple_carrier_pole {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    deriv (logDeriv riemannXiSpectral) c ≠ 0 := by
  have hd : deriv suzukiXiEValue c ≠ 0 := by
    rw [← suzukiXiEZeroUnit_eq_deriv_of_order_one hm]
    exact suzukiXiEZeroUnit_ne_zero c
  rw [deriv_suzukiXiEValue_at_pole hE hxi] at hd
  exact (mul_ne_zero_iff.mp hd).2

/-- The mixed residue at a simple actual carrier pole is its reciprocal
logarithmic-derivative slope times both original node denominators. -/
theorem suzukiXiMixedCarrierPoleResidue_eq_inv_logDeriv_slope
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    suzukiXiMixedCarrierPoleResidue rho sigma c =
      1 / (deriv (logDeriv riemannXiSpectral) c *
        ((c - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (c - zetaSpectralCoordinate sigma.1))) := by
  rw [suzukiXiMixedCarrierPoleResidue_of_order_one rho sigma hm,
    deriv_suzukiXiEValue_at_pole hE hxi]
  rw [mul_assoc (I * riemannXiSpectral c)]
  simpa only [mul_one] using mul_div_mul_left 1 _ (mul_ne_zero I_ne_zero hxi)

/-- The actual finite complex Cauchy test on arbitrary genuine zero
nodes. The same coefficients are retained at conjugate observation points. -/
def suzukiXiFiniteCauchyTest (S : Finset NontrivialZetaZero)
    (w : NontrivialZetaZero → ℂ) (z : ℂ) : ℂ :=
  ∑ rho ∈ S, w rho / (z - zetaSpectralCoordinate rho.1)

/-- Every finite complex coefficient family has a full reflected
bilinear simple-pole residue. This preserves all mixed terms and the
phase between its two observation points, rather than imposing a
positive norm-square interpretation on a nonreal carrier pole. -/
theorem suzukiXiMixedCarrierPoleResidue_quadratic_eq_reflected_test
    (S : Finset NontrivialZetaZero) (w : NontrivialZetaZero → ℂ) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0)
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    (∑ rho ∈ S, ∑ sigma ∈ S,
      starRingEnd ℂ (w rho) * w sigma * suzukiXiMixedCarrierPoleResidue rho sigma c) =
      starRingEnd ℂ (suzukiXiFiniteCauchyTest S w (starRingEnd ℂ c)) *
        suzukiXiFiniteCauchyTest S w c / deriv (logDeriv riemannXiSpectral) c := by
  simp_rw [suzukiXiMixedCarrierPoleResidue_eq_inv_logDeriv_slope _ _ hE hxi hm]
  simp only [suzukiXiFiniteCauchyTest, map_sum, map_div₀, map_sub, conj_conj]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  simp only [div_eq_mul_inv, mul_inv]
  ring

end
end RiemannGaussian
