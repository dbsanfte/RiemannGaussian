/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSafeHalfPlane

/-!
# The actual carrier poles and their mixed residues

Zeros of `E=A+i*A'` away from the xi divisor are genuine poles of the
upper carrier. We retain their complete analytic order, construct its
analytic numerator after removing that power, and evaluate the small
circle integral of every mixed channel by the corresponding derivative.
The reflected channel is analytic at these poles. Thus the signed Gram
continuation retains an explicit contribution from each such pole.

No simplicity, sign of a residue, or cancellation of different poles is
assumed. These are the terms that cannot be dropped when closing the
actual boundary integrals.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Suzuki's actual denominator is entire. -/
theorem analyticAt_suzukiXiEValue (z : ℂ) : AnalyticAt ℂ suzukiXiEValue z :=
  (analyticAt_riemannXiSpectral z).add (analyticAt_const.mul
    (analyticAt_riemannXiSpectral z).deriv)

/-- The reflected denominator is also entire. -/
theorem analyticAt_suzukiXiESharpValue (z : ℂ) : AnalyticAt ℂ suzukiXiESharpValue z :=
  (analyticAt_riemannXiSpectral z).sub (analyticAt_const.mul
    (analyticAt_riemannXiSpectral z).deriv)

/-- Every actual denominator zero has finite analytic order. Nonvanishing
at the safe point `i` rules out the identically zero function. -/
theorem analyticOrderAt_suzukiXiEValue_ne_top (z : ℂ) :
    analyticOrderAt suzukiXiEValue z ≠ ⊤ := by
  intro htop
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z analyticAt_suzukiXiEValue).mp htop
  have hI := suzukiXiEValue_ne_zero_of_half_le_im (z := I) (by norm_num)
  exact hI (congrFun hzero I)

/-- At each point the actual entire denominator has its canonical local
power factorization, with a nonzero analytic unit. -/
theorem exists_suzukiXiEZeroUnit (z : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      suzukiXiEValue =ᶠ[𝓝 z] fun w =>
        (w - z) ^ analyticOrderNatAt suzukiXiEValue z * g w := by
  simpa only [smul_eq_mul] using
    (analyticAt_suzukiXiEValue z).analyticOrderAt_ne_top.mp
      (analyticOrderAt_suzukiXiEValue_ne_top z)

/-- A chosen analytic unit for the genuine denominator's exact local
factorization. Only its germ is used in the residue formulas. -/
def suzukiXiEZeroUnit (z : ℂ) : ℂ → ℂ :=
  Classical.choose (exists_suzukiXiEZeroUnit z)

/-- The chosen unit is analytic at its center. -/
theorem analyticAt_suzukiXiEZeroUnit (z : ℂ) :
    AnalyticAt ℂ (suzukiXiEZeroUnit z) z :=
  (Classical.choose_spec (exists_suzukiXiEZeroUnit z)).1

/-- The chosen unit does not vanish at its center. -/
theorem suzukiXiEZeroUnit_ne_zero (z : ℂ) : suzukiXiEZeroUnit z z ≠ 0 :=
  (Classical.choose_spec (exists_suzukiXiEZeroUnit z)).2.1

/-- Exact local factorization of the actual denominator, including its
full analytic multiplicity. -/
theorem suzukiXiEValue_eventually_eq_power_mul_unit (z : ℂ) :
    suzukiXiEValue =ᶠ[𝓝 z] fun w =>
      (w - z) ^ analyticOrderNatAt suzukiXiEValue z * suzukiXiEZeroUnit z w :=
  (Classical.choose_spec (exists_suzukiXiEZeroUnit z)).2.2

/-- A zero of the actual denominator has strictly positive finite order. -/
theorem analyticOrderNatAt_suzukiXiEValue_pos {z : ℂ} (hz : suzukiXiEValue z = 0) :
    0 < analyticOrderNatAt suzukiXiEValue z := by
  have hnonzero := (analyticAt_suzukiXiEValue z).analyticOrderAt_ne_zero.mpr hz
  have hcast := Nat.cast_analyticOrderNatAt (analyticOrderAt_suzukiXiEValue_ne_top z)
  by_contra h
  have hm : analyticOrderNatAt suzukiXiEValue z = 0 := Nat.eq_zero_of_not_pos h
  rw [hm, Nat.cast_zero] at hcast
  exact hnonzero hcast.symm

/-- The analytic numerator after removing the complete denominator pole
power from the actual carrier. -/
def suzukiXiCarrierPoleNumerator (c z : ℂ) : ℂ :=
  I * riemannXiSpectral z / suzukiXiEZeroUnit c z

/-- The pole numerator is analytic at its center, with no unproved
extension of the original carrier at its pole. -/
theorem analyticAt_suzukiXiCarrierPoleNumerator (c : ℂ) :
    AnalyticAt ℂ (suzukiXiCarrierPoleNumerator c) c :=
  (analyticAt_const.mul (analyticAt_riemannXiSpectral c)).div
    (analyticAt_suzukiXiEZeroUnit c) (suzukiXiEZeroUnit_ne_zero c)

/-- Away from the xi divisor, the numerator is nonzero. Consequently the
entire denominator's full order is a genuine pole order of the carrier. -/
theorem suzukiXiCarrierPoleNumerator_ne_zero {c : ℂ} (hc : riemannXiSpectral c ≠ 0) :
    suzukiXiCarrierPoleNumerator c c ≠ 0 :=
  div_ne_zero (mul_ne_zero I_ne_zero hc) (suzukiXiEZeroUnit_ne_zero c)

/-- Exact punctured local model for the actual carrier, with its complete
pole power and an analytic nonzero numerator retained. -/
theorem suzukiXiZeroCarrier_eventually_eq_power_pole (c : ℂ) :
    suzukiXiZeroCarrier =ᶠ[𝓝[≠] c] fun z =>
      suzukiXiCarrierPoleNumerator c z / (z - c) ^ analyticOrderNatAt suzukiXiEValue c := by
  have hunit := (analyticAt_suzukiXiEZeroUnit c).continuousAt.eventually_ne
    (suzukiXiEZeroUnit_ne_zero c)
  filter_upwards [(suzukiXiEValue_eventually_eq_power_mul_unit c).filter_mono nhdsWithin_le_nhds,
    hunit.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z heq hunit hz
  have hp : (z - c) ^ analyticOrderNatAt suzukiXiEValue c ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr hz)
  have hE : suzukiXiEValue z ≠ 0 := by rw [heq]; exact mul_ne_zero hp hunit
  rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, heq]
  unfold suzukiXiCarrierPoleNumerator
  ring

private lemma mixed_denominator_ne_zero {c : ℂ} (hc : riemannXiSpectral c ≠ 0)
    (rho sigma : NontrivialZetaZero) :
    (c - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (c - zetaSpectralCoordinate sigma.1) ≠ 0 := by
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro heq
    apply hc
    rw [heq, ← NontrivialZetaZero.spectralCoordinate_conjugatePartner]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨_, rfl⟩
  · apply sub_ne_zero.mpr
    intro heq
    apply hc
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨sigma, rfl⟩

/-- The full analytic numerator for an actual mixed channel at a carrier
pole. The two genuine node factors retain their order and conjugation. -/
def suzukiXiMixedCarrierPoleNumerator (rho sigma : NontrivialZetaZero) (c z : ℂ) : ℂ :=
  suzukiXiCarrierPoleNumerator c z /
    ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) * (z - zetaSpectralCoordinate sigma.1))

/-- Both mixed node denominators are nonzero at a genuine carrier pole,
so the corresponding mixed numerator is analytic there. -/
theorem analyticAt_suzukiXiMixedCarrierPoleNumerator
    (rho sigma : NontrivialZetaZero) {c : ℂ} (hc : riemannXiSpectral c ≠ 0) :
    AnalyticAt ℂ (suzukiXiMixedCarrierPoleNumerator rho sigma c) c :=
  (analyticAt_suzukiXiCarrierPoleNumerator c).div
    ((analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const))
    (mixed_denominator_ne_zero hc rho sigma)

/-- The exact local residue of an arbitrary-order actual carrier pole in
one mixed channel. Lower Taylor coefficients contribute when the pole is
multiple; they are retained in the derivative of the full mixed numerator. -/
def suzukiXiMixedCarrierPoleResidue (rho sigma : NontrivialZetaZero) (c : ℂ) : ℂ :=
  iteratedDeriv (analyticOrderNatAt suzukiXiEValue c - 1)
    (suzukiXiMixedCarrierPoleNumerator rho sigma c) c /
      ((analyticOrderNatAt suzukiXiEValue c - 1).factorial : ℂ)

private lemma eventually_circleIntegral_power_pole {f F : ℂ → ℂ} {c : ℂ} (k : ℕ)
    (hF : AnalyticAt ℂ F c)
    (he : f =ᶠ[𝓝[≠] c] fun z => F z / (z - c) ^ (k + 1)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, CircleIntegrable f c r ∧
      (∮ z in C(c, r), f z) =
        (2 * Real.pi * I) * (iteratedDeriv k F c / (k.factorial : ℂ)) := by
  change ∀ᶠ z in 𝓝[≠] c, f z = F z / (z - c) ^ (k + 1) at he
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨R, hR, heR⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨D, hD, hFD⟩ := hF.exists_ball_analyticOnNhd
  filter_upwards [Ioo_mem_nhdsGT (lt_min hR hD)] with r hr
  have hsphere : ∀ z ∈ sphere c r, z ≠ c ∧ z ∈ ball c R ∧ z ∈ ball c D := by
    intro z hz
    have hd : dist z c = r := mem_sphere.mp hz
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      rw [heq, dist_self] at hd
      linarith [hr.1]
    · exact mem_ball.mpr (hd.trans_lt (lt_of_lt_of_le hr.2 (min_le_left _ _)))
    · exact mem_ball.mpr (hd.trans_lt (lt_of_lt_of_le hr.2 (min_le_right _ _)))
  have heq : EqOn f (fun z => F z / (z - c) ^ (k + 1)) (sphere c r) := by
    intro z hz
    exact heR (hsphere z hz).2.1 (hsphere z hz).1
  have hcont : ContinuousOn (fun z => F z / (z - c) ^ (k + 1)) (sphere c r) :=
    (hFD.continuousOn.mono (fun z hz => (hsphere z hz).2.2)).div
      (((continuous_id.sub continuous_const).pow (k + 1)).continuousOn)
      (fun z hz => pow_ne_zero _ (sub_ne_zero.mpr (hsphere z hz).1))
  have hclosed : closedBall c r ⊆ ball c D := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt
      (lt_of_lt_of_le hr.2 (min_le_right _ _)))
  have hdiff := hFD.differentiableOn.mono hclosed
  refine ⟨?_, ?_⟩
  · apply (circleIntegrable_congr ?_).mpr (hcont.circleIntegrable hr.1.le)
    intro z hz
    exact heq (by simpa only [abs_of_pos hr.1] using hz)
  · rw [circleIntegral.integral_congr hr.1.le heq]
    calc
      (∮ z in C(c, r), F z / (z - c) ^ (k + 1)) =
          ∮ z in C(c, r), (1 / (z - c) ^ (k + 1)) • F z := by
        congr 1
        funext z
        simp only [smul_eq_mul]
        ring
      _ = (2 * Real.pi * I / (k.factorial : ℂ)) • iteratedDeriv k F c :=
        hdiff.circleIntegral_one_div_sub_center_pow_smul hr.1 k
      _ = _ := by simp only [smul_eq_mul]; ring

/-- Every actual carrier pole away from the xi divisor has its complete
mixed small-circle contribution evaluated exactly, for every sufficiently
small positive radius. This includes poles of arbitrary analytic order. -/
theorem eventually_suzukiXiCarrier_pole_circle_residue
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable (fun z => suzukiXiZeroCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) c r ∧
      (∮ z in C(c, r), suzukiXiZeroCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) =
        (2 * Real.pi * I) * suzukiXiMixedCarrierPoleResidue rho sigma c := by
  have hm := analyticOrderNatAt_suzukiXiEValue_pos hE
  apply eventually_circleIntegral_power_pole (analyticOrderNatAt suzukiXiEValue c - 1)
    (analyticAt_suzukiXiMixedCarrierPoleNumerator rho sigma hxi)
  filter_upwards [suzukiXiZeroCarrier_eventually_eq_power_pole c] with z hz
  rw [hz, Nat.sub_add_cancel hm]
  unfold suzukiXiMixedCarrierPoleNumerator
  ring

/-- Away from xi zeros, a pole of the first channel cannot also be a pole
of the reflected channel: their denominator sum is exactly twice xi. -/
theorem suzukiXiESharpValue_ne_zero_of_E_zero {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    suzukiXiESharpValue c ≠ 0 := by
  intro hsharp
  have hsum := suzukiXiEValue_add_sharp c
  rw [hE, hsharp, zero_add] at hsum
  exact hxi ((mul_eq_zero.mp hsum.symm).resolve_left (by norm_num))

/-- The reflected carrier is analytic wherever its own denominator is
nonzero, retaining the actual quotient through its local equality. -/
theorem analyticAt_suzukiXiSharpCarrier_of_ESharp_ne_zero {c : ℂ}
    (hc : suzukiXiESharpValue c ≠ 0) : AnalyticAt ℂ suzukiXiSharpCarrier c := by
  have hmodel : AnalyticAt ℂ (fun z => -I * riemannXiSpectral z / suzukiXiESharpValue z) c :=
    (analyticAt_const.mul (analyticAt_riemannXiSpectral c)).div
      (analyticAt_suzukiXiESharpValue c) hc
  apply hmodel.congr
  filter_upwards [(analyticAt_suzukiXiESharpValue c).continuousAt.eventually_ne hc] with z hz
  exact (suzukiXiSharpCarrier_eq_neg_i_mul_xi_div_sharp hz).symm

private lemma eventually_circleIntegral_analytic {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, CircleIntegrable f c r ∧ (∮ z in C(c, r), f z) = 0 := by
  have hF : AnalyticAt ℂ (fun z => (z - c) * f z) c :=
    (analyticAt_id.sub analyticAt_const).mul hf
  have he : f =ᶠ[𝓝[≠] c] fun z => ((z - c) * f z) / (z - c) ^ (0 + 1) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [sub_ne_zero.mpr hz]
  simpa using eventually_circleIntegral_power_pole 0 hF he

/-- At a genuine pole of the first carrier, the reflected mixed channel
has exactly zero small-circle contribution. -/
theorem eventually_suzukiXiSharpCarrier_circle_zero_at_E_pole
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable (fun z => suzukiXiSharpCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) c r ∧
      (∮ z in C(c, r), suzukiXiSharpCarrier z /
        ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
          (z - zetaSpectralCoordinate sigma.1))) = 0 := by
  apply eventually_circleIntegral_analytic
  exact (analyticAt_suzukiXiSharpCarrier_of_ESharp_ne_zero
    (suzukiXiESharpValue_ne_zero_of_E_zero hE hxi)).div
      ((analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const))
      (mixed_denominator_ne_zero hxi rho sigma)

/-- The full signed mixed Gram continuation has the explicit small-circle
contribution `pi * residue` at every actual first-channel pole. This term
survives channel subtraction; it is not an omitted xi-node pole. -/
theorem eventually_suzukiXiCarrierGram_circle_at_E_pole
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable (suzukiXiCarrierGramContinuation rho sigma) c r ∧
      (∮ z in C(c, r), suzukiXiCarrierGramContinuation rho sigma z) =
        (Real.pi : ℂ) * suzukiXiMixedCarrierPoleResidue rho sigma c := by
  have hfun : suzukiXiCarrierGramContinuation rho sigma = fun z =>
      (suzukiXiZeroCarrier z /
          ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
            (z - zetaSpectralCoordinate sigma.1)) -
        suzukiXiSharpCarrier z /
          ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
            (z - zetaSpectralCoordinate sigma.1))) / (2 * I) := by
    funext z
    unfold suzukiXiCarrierGramContinuation
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hfun]
  filter_upwards [eventually_suzukiXiCarrier_pole_circle_residue rho sigma hE hxi,
    eventually_suzukiXiSharpCarrier_circle_zero_at_E_pole rho sigma hE hxi] with r hC hS
  refine ⟨(hC.1.sub hS.1).div_const _, ?_⟩
  have hdiv (f : ℂ → ℂ) :
      (∮ z in C(c, r), f z / (2 * I)) = (∮ z in C(c, r), f z) / (2 * I) := by
    have heq : (fun z => f z / (2 * I)) = fun z => (2 * I)⁻¹ * f z := by
      funext z
      ring
    rw [heq, circleIntegral.integral_const_mul]
    ring
  rw [hdiv, circleIntegral.integral_sub hC.1 hS.1, hC.2, hS.2,
    sub_zero]
  field_simp

/-- For a simple denominator zero, its canonical analytic unit equals
the actual derivative of the denominator. -/
theorem suzukiXiEZeroUnit_eq_deriv_of_order_one {c : ℂ}
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    suzukiXiEZeroUnit c c = deriv suzukiXiEValue c := by
  have he := suzukiXiEValue_eventually_eq_power_mul_unit c
  simp only [hm, pow_one] at he
  have hder := he.deriv_eq
  rw [deriv_fun_mul (by fun_prop) (analyticAt_suzukiXiEZeroUnit c).differentiableAt] at hder
  simpa using hder.symm

/-- A simple actual carrier pole has the explicit complex mixed residue
`i*A(c)/(E'(c)*D(rho,sigma,c))`. Its phase is not replaced by a magnitude. -/
theorem suzukiXiMixedCarrierPoleResidue_of_order_one
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hm : analyticOrderNatAt suzukiXiEValue c = 1) :
    suzukiXiMixedCarrierPoleResidue rho sigma c =
      I * riemannXiSpectral c /
        (deriv suzukiXiEValue c *
          ((c - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
            (c - zetaSpectralCoordinate sigma.1))) := by
  simp only [suzukiXiMixedCarrierPoleResidue, hm, Nat.sub_self, iteratedDeriv_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, suzukiXiMixedCarrierPoleNumerator,
    suzukiXiCarrierPoleNumerator, suzukiXiEZeroUnit_eq_deriv_of_order_one hm]
  simp only [div_eq_mul_inv, mul_inv]
  ring

end

end RiemannGaussian
