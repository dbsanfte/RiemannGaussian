/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RectangularPoleIntegral

/-!
# Complete finite pole data for the actual mixed Suzuki channel

Every potential singularity is retained. At xi nodes the original local
models give the exact common simple coefficient, with higher xi
multiplicity already canceled in the carrier. Away from xi nodes the
genuine analytic order of `E` and its full mixed numerator are used.
This supplies actual pole data, including the zero coefficients of
removable singularities, for finite rectangular contour assembly.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- The original first mixed carrier channel, with ordered reflected
and unreflected node factors. -/
def suzukiXiMixedCarrierChannel (rho sigma : NontrivialZetaZero) (z : ℂ) : ℂ :=
  suzukiXiZeroCarrier z /
    ((z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) * (z - zetaSpectralCoordinate sigma.1))

/-- The exact common xi-node coefficient, with its analytic multiplicity.
It survives precisely when both original mixed nodes equal the center. -/
def suzukiXiMixedXiNodeResidue (rho sigma : NontrivialZetaZero) (c : ℂ) : ℂ :=
  if starRingEnd ℂ (zetaSpectralCoordinate rho.1) = c ∧ zetaSpectralCoordinate sigma.1 = c then
    (analyticOrderNatAt riemannXiSpectral c : ℂ)⁻¹ else 0

private lemma exists_xi_node_numerator (rho sigma : NontrivialZetaZero)
    {c : ℂ} (hc : riemannXiSpectral c = 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F c ∧ F c = suzukiXiMixedXiNodeResidue rho sigma c ∧
      suzukiXiMixedCarrierChannel rho sigma =ᶠ[𝓝[≠] c] fun z => F z / (z - c) ^ 1 := by
  obtain ⟨tau, rfl⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero c).mp hc
  obtain ⟨p, _q, hp, _hq, he⟩ := exists_suzukiXiCarrier_mixed_polar_models rho sigma tau
  let L : ℂ := suzukiXiMixedXiNodeResidue rho sigma (zetaSpectralCoordinate tau.1)
  refine ⟨fun z => L + (z - zetaSpectralCoordinate tau.1) * p z,
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hp), ?_, ?_⟩
  · simp only [sub_self, zero_mul, add_zero]
    rfl
  · filter_upwards [he, self_mem_nhdsWithin] with z hz hzc
    have hL : L = if starRingEnd ℂ (zetaSpectralCoordinate rho.1) =
        zetaSpectralCoordinate tau.1 ∧ zetaSpectralCoordinate sigma.1 = zetaSpectralCoordinate tau.1 then
          (analyticZetaZeroMultiplicity tau : ℂ)⁻¹ else 0 := by
      simp only [L, suzukiXiMixedXiNodeResidue,
        analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate]
    unfold suzukiXiMixedCarrierChannel
    rw [hz.1, ← hL, pow_one]
    field_simp [sub_ne_zero.mpr hzc]

/-- The actual local order used in the mixed channel: one at xi nodes,
and the complete denominator order everywhere else. Removable xi nodes
have zero simple coefficient, so are not silently omitted. -/
def suzukiXiMixedCarrierLocalOrder (c : ℂ) : ℕ :=
  if riemannXiSpectral c = 0 then 1 else analyticOrderNatAt suzukiXiEValue c

/-- An analytic numerator for every actual mixed-channel local model.
Away from xi zeros this is exactly the already-constructed pole numerator. -/
def suzukiXiMixedCarrierLocalNumerator (rho sigma : NontrivialZetaZero) (c : ℂ) : ℂ → ℂ :=
  if h : riemannXiSpectral c = 0 then Classical.choose (exists_xi_node_numerator rho sigma h)
  else suzukiXiMixedCarrierPoleNumerator rho sigma c

/-- Every selected actual local numerator is analytic at its center. -/
theorem analyticAt_suzukiXiMixedCarrierLocalNumerator
    (rho sigma : NontrivialZetaZero) (c : ℂ) :
    AnalyticAt ℂ (suzukiXiMixedCarrierLocalNumerator rho sigma c) c := by
  by_cases hc : riemannXiSpectral c = 0
  · simp only [suzukiXiMixedCarrierLocalNumerator, dif_pos hc]
    exact (Classical.choose_spec (exists_xi_node_numerator rho sigma hc)).1
  · simp only [suzukiXiMixedCarrierLocalNumerator, dif_neg hc]
    exact analyticAt_suzukiXiMixedCarrierPoleNumerator rho sigma hc

/-- The actual mixed channel has its full punctured model at every
complex point. Both xi-node cancellations and true carrier poles occur
in the same finite-contour interface. -/
theorem suzukiXiMixedCarrierChannel_eventually_eq_local_model
    (rho sigma : NontrivialZetaZero) (c : ℂ) :
    suzukiXiMixedCarrierChannel rho sigma =ᶠ[𝓝[≠] c] fun z =>
      suzukiXiMixedCarrierLocalNumerator rho sigma c z / (z - c) ^ suzukiXiMixedCarrierLocalOrder c := by
  by_cases hc : riemannXiSpectral c = 0
  · simp only [suzukiXiMixedCarrierLocalNumerator, suzukiXiMixedCarrierLocalOrder, dif_pos hc, if_pos hc]
    exact (Classical.choose_spec (exists_xi_node_numerator rho sigma hc)).2.2
  · simp only [suzukiXiMixedCarrierLocalNumerator, suzukiXiMixedCarrierLocalOrder, dif_neg hc, if_neg hc]
    filter_upwards [suzukiXiZeroCarrier_eventually_eq_power_pole c] with z hz
    unfold suzukiXiMixedCarrierChannel suzukiXiMixedCarrierPoleNumerator
    rw [hz]
    ring

/-- The genuine residue used in the complete finite contour. It covers
xi-node terms, arbitrary carrier-pole orders and regular points uniformly. -/
def suzukiXiMixedCarrierLocalResidue (rho sigma : NontrivialZetaZero) (c : ℂ) : ℂ :=
  poleTaylorResidue (suzukiXiMixedCarrierLocalOrder c)
    (suzukiXiMixedCarrierLocalNumerator rho sigma c) c

/-- At a xi node the complete residue is precisely the original common
mixed coefficient, including the inverse analytic multiplicity. -/
theorem suzukiXiMixedCarrierLocalResidue_at_xi_node
    (rho sigma : NontrivialZetaZero) {c : ℂ} (hc : riemannXiSpectral c = 0) :
    suzukiXiMixedCarrierLocalResidue rho sigma c = suzukiXiMixedXiNodeResidue rho sigma c := by
  simp only [suzukiXiMixedCarrierLocalResidue, suzukiXiMixedCarrierLocalOrder, if_pos hc,
    poleTaylorResidue, one_ne_zero, if_false, Nat.sub_self, iteratedDeriv_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, suzukiXiMixedCarrierLocalNumerator, dif_pos hc]
  exact (Classical.choose_spec (exists_xi_node_numerator rho sigma hc)).2.1

/-- At a genuine carrier pole the complete residue is the previously
evaluated arbitrary-order mixed circle residue, with no change of phase. -/
theorem suzukiXiMixedCarrierLocalResidue_at_E_pole
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c = 0) (hxi : riemannXiSpectral c ≠ 0) :
    suzukiXiMixedCarrierLocalResidue rho sigma c = suzukiXiMixedCarrierPoleResidue rho sigma c := by
  simp only [suzukiXiMixedCarrierLocalResidue, suzukiXiMixedCarrierLocalOrder, if_neg hxi,
    suzukiXiMixedCarrierLocalNumerator, dif_neg hxi, poleTaylorResidue,
    if_neg (Nat.ne_of_gt (analyticOrderNatAt_suzukiXiEValue_pos hE)), suzukiXiMixedCarrierPoleResidue]

/-- Regular non-xi points have zero coefficient in the finite residue
sum, so including them cannot create a spurious source. -/
theorem suzukiXiMixedCarrierLocalResidue_eq_zero_of_regular
    (rho sigma : NontrivialZetaZero) {c : ℂ}
    (hE : suzukiXiEValue c ≠ 0) (hxi : riemannXiSpectral c ≠ 0) :
    suzukiXiMixedCarrierLocalResidue rho sigma c = 0 := by
  have ho : analyticOrderNatAt suzukiXiEValue c = 0 := by
    simp only [analyticOrderNatAt, (analyticAt_suzukiXiEValue c).analyticOrderAt_eq_zero.mpr hE,
      ENat.toNat_zero]
  simp only [suzukiXiMixedCarrierLocalResidue, suzukiXiMixedCarrierLocalOrder,
    if_neg hxi, ho, poleTaylorResidue, if_true]

/-- The potential singular set for the actual channel, keeping xi nodes
as well as all zeros of the genuine de Branges denominator. -/
def suzukiXiCarrierSingularSet : Set ℂ :=
  {c | riemannXiSpectral c = 0 ∨ suzukiXiEValue c = 0}

/-- The full potential singular set is finite in every compact region.
This follows from the actual entire product, nonzero at the safe point i. -/
theorem IsCompact.inter_suzukiXiCarrierSingularSet_finite {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ suzukiXiCarrierSingularSet).Finite := by
  let g : ℂ → ℂ := fun z => riemannXiSpectral z * suzukiXiEValue z
  have hg : ∀ z, AnalyticAt ℂ g z := fun z =>
    (analyticAt_riemannXiSpectral z).mul (analyticAt_suzukiXiEValue z)
  have hgne : g I ≠ 0 := mul_ne_zero
    (riemannXiSpectral_ne_zero_of_half_le_abs_im (by norm_num))
    (suzukiXiEValue_ne_zero_of_half_le_im (by norm_num))
  have hset : suzukiXiCarrierSingularSet = {z | g z = 0} := by
    ext z
    simp only [suzukiXiCarrierSingularSet, Set.mem_ofPred_eq, g, mul_eq_zero]
  rw [hset]
  have hclosed : IsClosed {z | g z = 0} := isClosed_eq
    (continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt) continuous_const
  have hdisc : IsDiscrete {z | g z = 0} := by
    have hco := (show AnalyticOnNhd ℂ g Set.univ from fun z _ => hg z).preimage_zero_mem_codiscrete hgne
    have he : (g ⁻¹' ({0} : Set ℂ)ᶜ)ᶜ = {z | g z = 0} := by
      ext z
      simp
    rw [← he]
    exact (mem_codiscrete'.mp hco).2
  exact (hK.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)

/-- Away from the complete actual singular set, the original mixed
channel is analytic, with all denominator exclusions discharged. -/
theorem analyticAt_suzukiXiMixedCarrierChannel_of_not_mem
    (rho sigma : NontrivialZetaZero) {c : ℂ} (hc : c ∉ suzukiXiCarrierSingularSet) :
    AnalyticAt ℂ (suzukiXiMixedCarrierChannel rho sigma) c := by
  have hxi : riemannXiSpectral c ≠ 0 := fun h => hc (Or.inl h)
  have hE : suzukiXiEValue c ≠ 0 := fun h => hc (Or.inr h)
  have hrho : c - starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hxi
    rw [he, ← NontrivialZetaZero.spectralCoordinate_conjugatePartner]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨_, rfl⟩
  have hsigma : c - zetaSpectralCoordinate sigma.1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hxi ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨sigma, he⟩)
  have hC : AnalyticAt ℂ suzukiXiZeroCarrier c := by
    unfold suzukiXiZeroCarrier suzukiXiThetaValue
    exact (analyticAt_const.mul (analyticAt_const.add
      ((analyticAt_suzukiXiESharpValue c).div (analyticAt_suzukiXiEValue c) hE))).div_const
  exact hC.div ((analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero hrho hsigma)

end
end RiemannGaussian
