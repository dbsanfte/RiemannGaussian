/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiJensenDiskBound

/-!
# Finite signed budgets and local geometry of actual Suzuki poles

The complete xi expansion gives a finite signed upper budget with a
nonpositive infinite tail. At a genuine carrier pole the exact level
equation `A'/A=i` forces every eligible finite head to reach one. A head
below one excludes the pole and gives an explicit carrier norm bound.

Every genuine upper carrier pole lies inside a Jensen disk of an actual
reflected zero pair. Outside the union of those disks the literal carrier
is bounded by one even within the zero strip. These estimates do not bound
the full signed residue correction or prove the remaining source ceiling.
-/

open Complex Filter Set Topology
open scoped Classical Topology
namespace RiemannGaussian
noncomputable section

/-- Every genuine upper carrier pole forces a unit contribution in every
sufficiently wide actual finite Cauchy window. All omitted terms have the
favorable sign, so there is no unknown infinite-tail allowance here. -/
theorem one_le_im_finite_cauchy_window_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 ≤ z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : |z.re| + 1 / 2 ≤ T) :
    1 ≤ (riemannXiSpectralWindowCauchySum T z).im := by
  have h := im_logDeriv_riemannXiSpectral_le_finite_window hz hxi hT
  simpa only [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] using h

/-- A strict finite signed budget excludes a genuine carrier pole.
The threshold is checked against the literal Cauchy head, retaining every
critical zero and both members of every reflected pair. -/
theorem suzukiXiEValue_ne_zero_of_finite_cauchy_budget {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ}
    (hT : |z.re| + 1 / 2 ≤ T) (hbudget : (riemannXiSpectralWindowCauchySum T z).im < 1) :
    suzukiXiEValue z ≠ 0 := by
  intro hE
  exact (not_lt_of_ge (one_le_im_finite_cauchy_window_at_suzukiXiE_pole hz hE hxi hT)) hbudget

private lemma norm_carrier_le_of_im_bound {z : ℂ} (hxi : riemannXiSpectral z ≠ 0)
    (hE : suzukiXiEValue z ≠ 0) {B : ℝ} (hB : B < 1)
    (hq : (logDeriv riemannXiSpectral z).im ≤ B) :
    ‖suzukiXiZeroCarrier z‖ ≤ 1 / (1 - B) := by
  rw [suzukiXiZeroCarrier_eq_I_div_one_add_logDeriv hxi hE, norm_div, norm_I]
  apply one_div_le_one_div_of_le (sub_pos.mpr hB)
  calc
    1 - B ≤ 1 - (logDeriv riemannXiSpectral z).im := by linarith
    _ = (1 + I * logDeriv riemannXiSpectral z).re := by simp [sub_eq_add_neg]
    _ ≤ _ := Complex.re_le_norm _

/-- The same finite head gives a quantitative upper bound on the actual
carrier, including observation points inside the zero strip. -/
theorem norm_suzukiXiZeroCarrier_le_of_finite_cauchy_budget {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) {T : ℝ}
    (hT : |z.re| + 1 / 2 ≤ T) (hbudget : (riemannXiSpectralWindowCauchySum T z).im < 1) :
    ‖suzukiXiZeroCarrier z‖ ≤ 1 / (1 - (riemannXiSpectralWindowCauchySum T z).im) :=
  norm_carrier_le_of_im_bound hxi
    (suzukiXiEValue_ne_zero_of_finite_cauchy_budget hz hxi hT hbudget) hbudget
    (im_logDeriv_riemannXiSpectral_le_finite_window hz hxi hT)

/-- The unit pole threshold already holds in every local ordinate band
of radius at least one half. This retains the local critical divisor and
the full signed reflected pairs, rather than only their positive parts. -/
theorem one_le_im_local_paired_window_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 ≤ z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0)
    {L : ℝ} (hL : 1 / 2 ≤ L) :
    1 ≤ (riemannXiLocalPairedCauchyWindow z L).im := by
  have h := im_logDeriv_riemannXiSpectral_le_local_paired_window hz hxi hL
  simpa only [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] using h

/-- A signed local ordinate band below the unit threshold excludes the
actual carrier pole, with the complete omitted divisor handled by sign. -/
theorem suzukiXiEValue_ne_zero_of_local_paired_budget {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) {L : ℝ} (hL : 1 / 2 ≤ L)
    (hbudget : (riemannXiLocalPairedCauchyWindow z L).im < 1) :
    suzukiXiEValue z ≠ 0 := by
  intro hE
  exact (not_lt_of_ge (one_le_im_local_paired_window_at_suzukiXiE_pole hz hE hxi hL)) hbudget

/-- The literal carrier has an explicit norm bound from the signed local
band alone. No separate global Blaschke or infinite-tail estimate is needed. -/
theorem norm_suzukiXiZeroCarrier_le_of_local_paired_budget {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) {L : ℝ} (hL : 1 / 2 ≤ L)
    (hbudget : (riemannXiLocalPairedCauchyWindow z L).im < 1) :
    ‖suzukiXiZeroCarrier z‖ ≤ 1 / (1 - (riemannXiLocalPairedCauchyWindow z L).im) :=
  norm_carrier_le_of_im_bound hxi
    (suzukiXiEValue_ne_zero_of_local_paired_budget hz hxi hL hbudget) hbudget
    (im_logDeriv_riemannXiSpectral_le_local_paired_window hz hxi hL)

/-- Finitely many local Jensen pairs must supply at least one unit at
every genuine upper carrier pole. Distant off-axis pairs cannot supply it. -/
theorem one_le_local_jensen_budget_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 ≤ z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0) :
    1 ≤ riemannXiLocalJensenBudget z := by
  have h := im_logDeriv_riemannXiSpectral_le_local_jensen_budget hz hxi
  simpa only [logDeriv_riemannXiSpectral_eq_I_at_carrier_pole hE hxi, I_im] using h

/-- Every genuine upper carrier pole belongs to an actual local Jensen
disk. This is an unconditional localization, not an assumption about the
positions of unknown carrier poles. -/
theorem exists_local_jensen_pair_at_suzukiXiE_pole {z : ℂ}
    (hz : 0 ≤ z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ rho : NontrivialZetaZero, rho ∈ riemannXiLocalJensenWindow z := by
  have hb := one_le_local_jensen_budget_at_suzukiXiE_pole hz hE hxi
  by_contra! hn
  have he : riemannXiLocalJensenBudget z = 0 := by
    apply Finset.sum_eq_zero
    intro rho hrho
    exact (hn rho hrho).elim
  linarith

/-- In zeta coordinates every genuine upper carrier pole requires a
nearby right-half zero whose squared distance from the critical line
strictly exceeds the pole's squared height plus the ordinate mismatch. -/
theorem exists_rightHalf_zero_near_suzukiXiE_pole {z : ℂ}
    (hz : 0 ≤ z.im) (hE : suzukiXiEValue z = 0) (hxi : riemannXiSpectral z ≠ 0) :
    ∃ rho : NontrivialZetaZero, 1 / 2 < rho.1.re ∧
      (z.re - rho.1.im) ^ 2 + z.im ^ 2 < (rho.1.re - 1 / 2) ^ 2 := by
  obtain ⟨rho, hrho⟩ := exists_local_jensen_pair_at_suzukiXiE_pole hz hE hxi
  obtain ⟨hu, hd⟩ := (mem_riemannXiLocalJensenWindow z rho).mp hrho
  refine ⟨rho.conjugatePartner, ?_, ?_⟩
  · rw [zetaSpectralCoordinate_im] at hu
    simp only [NontrivialZetaZero.conjugatePartner_coe, sub_re, one_re, conj_re]
    linarith
  · change (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
      (zetaSpectralCoordinate rho.1).im ^ 2 at hd
    simpa only [zetaSpectralCoordinate_re, zetaSpectralCoordinate_im,
      NontrivialZetaZero.conjugatePartner_coe, sub_im, one_im, conj_im, zero_sub, neg_neg,
      sub_re, one_re, conj_re, show ∀ a : ℝ, 1 - a - 1 / 2 = 1 / 2 - a by intro a; ring] using hd

/-- Outside all local reflected disks, the full logarithmic derivative
has nonpositive imaginary part even within the original zero strip. -/
theorem im_logDeriv_riemannXiSpectral_nonpos_outside_jensen_disks {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0)
    (hout : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im → z ∉ zetaSpectralJensenDisk rho) :
    (logDeriv riemannXiSpectral z).im ≤ 0 := by
  have h := im_logDeriv_riemannXiSpectral_le_local_jensen_budget hz hxi
  have he : riemannXiLocalJensenBudget z = 0 := by
    apply Finset.sum_eq_zero
    intro rho hrho
    have hm := (mem_riemannXiLocalJensenWindow z rho).mp hrho
    exact (hout rho hm.1 hm.2).elim
  rwa [he] at h

/-- The literal carrier is bounded by one outside the union of actual
Jensen disks, including within the zero strip and at totalized xi-node
values. No zero-avoidance premise is needed for this norm statement. -/
theorem norm_suzukiXiZeroCarrier_le_one_outside_jensen_disks {z : ℂ}
    (hz : 0 ≤ z.im)
    (hout : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im → z ∉ zetaSpectralJensenDisk rho) :
    ‖suzukiXiZeroCarrier z‖ ≤ 1 := by
  by_cases hE : suzukiXiEValue z = 0
  · change ‖I * (1 + suzukiXiESharpValue z / suzukiXiEValue z) / 2‖ ≤ 1
    rw [hE]
    norm_num
  by_cases hxi : riemannXiSpectral z = 0
  · rw [suzukiXiZeroCarrier_eq_i_mul_xi_div_E hE, hxi]
    simp
  have hq := im_logDeriv_riemannXiSpectral_nonpos_outside_jensen_disks hz hxi hout
  simpa only [sub_zero, div_one] using norm_carrier_le_of_im_bound hxi hE (by norm_num : (0 : ℝ) < 1) hq

end
end RiemannGaussian
