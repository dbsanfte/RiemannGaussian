/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierReflectedReserve

/-!
# Signed localization of the complete xi logarithmic derivative

Pairing a spectral zero with its critical-line reflection confines its
positive imaginary contribution to the open disk between the two nodes.
Outside these classical Jensen disks every pair contributes nonpositively.
The complete xi expansion therefore admits finite signed upper bounds:
once a symmetric window contains every possible positive pair, enlarging
it can only decrease its imaginary part. All complex window identities
remain available before taking this one-sided projection.
-/

open Complex Filter Set Topology
open scoped Classical Topology
namespace RiemannGaussian
noncomputable section

/-- The imaginary part of a conjugate Cauchy pair, with its exact signed
numerator and both distance denominators retained. -/
theorem im_conjugate_cauchy_pair {z a : ℂ}
    (ha : z ≠ a) (hconj : z ≠ starRingEnd ℂ a) :
    ((z - a)⁻¹ + (z - starRingEnd ℂ a)⁻¹).im =
      2 * z.im * (a.im ^ 2 - (z.re - a.re) ^ 2 - z.im ^ 2) /
        (normSq (z - a) * normSq (z - starRingEnd ℂ a)) := by
  have h1 : normSq (z - a) ≠ 0 := (normSq_pos.mpr (sub_ne_zero.mpr ha)).ne'
  have h2 : normSq (z - starRingEnd ℂ a) ≠ 0 :=
    (normSq_pos.mpr (sub_ne_zero.mpr hconj)).ne'
  simp only [add_im, inv_im]
  field_simp
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im]
  ring

/-- The complete complex contribution of one reflected spectral pair.
The genuine analytic multiplicity occurs in both summands. -/
def zetaSpectralConjugateCauchyPair (z : ℂ) (rho : NontrivialZetaZero) : ℂ :=
  zetaSpectralLogDerivativePrincipalPart rho z +
    zetaSpectralLogDerivativePrincipalPart rho.conjugatePartner z

/-- The open disk whose diameter joins the reflected spectral nodes.
Its radius is the zero's actual distance from the critical line. -/
def zetaSpectralJensenDisk (rho : NontrivialZetaZero) : Set ℂ :=
  {z | (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
    (zetaSpectralCoordinate rho.1).im ^ 2}

/-- Exact signed disk numerator for the actual multiplicity-weighted pair. -/
theorem zetaSpectralConjugateCauchyPair_im {z : ℂ} (rho : NontrivialZetaZero)
    (hxi : riemannXiSpectral z ≠ 0) :
    (zetaSpectralConjugateCauchyPair z rho).im =
      2 * (analyticZetaZeroMultiplicity rho : ℝ) * z.im *
        ((zetaSpectralCoordinate rho.1).im ^ 2 -
          (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 - z.im ^ 2) /
        (normSq (z - zetaSpectralCoordinate rho.1) *
          normSq (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))) := by
  have hne (sigma : NontrivialZetaZero) : z ≠ zetaSpectralCoordinate sigma.1 := by
    intro he
    exact hxi ((riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mpr ⟨sigma, he⟩)
  have hc : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1) := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hne rho.conjugatePartner
  have he : zetaSpectralConjugateCauchyPair z rho =
      (analyticZetaZeroMultiplicity rho : ℂ) *
        ((z - zetaSpectralCoordinate rho.1)⁻¹ +
          (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹) := by
    simp only [zetaSpectralConjugateCauchyPair,
      zetaSpectralLogDerivativePrincipalPart, analyticZetaZeroMultiplicity_conjugatePartner,
      NontrivialZetaZero.spectralCoordinate_conjugatePartner, div_eq_mul_inv, mul_add]
  rw [he, mul_im]
  simp only [natCast_re, natCast_im, zero_mul, add_zero,
    im_conjugate_cauchy_pair (hne rho) hc]
  ring

/-- Outside its own open Jensen disk a reflected pair has nonpositive
imaginary part in the upper half-plane, regardless of all other zeros. -/
theorem zetaSpectralConjugateCauchyPair_im_nonpos {z : ℂ}
    (hz : 0 ≤ z.im) (rho : NontrivialZetaZero) (hxi : riemannXiSpectral z ≠ 0)
    (hout : z ∉ zetaSpectralJensenDisk rho) :
    (zetaSpectralConjugateCauchyPair z rho).im ≤ 0 := by
  rw [zetaSpectralConjugateCauchyPair_im rho hxi]
  apply div_nonpos_of_nonpos_of_nonneg
  · apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · change ¬ ((z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
        (zetaSpectralCoordinate rho.1).im ^ 2) at hout
      linarith [not_lt.mp hout]
  · exact mul_nonneg (normSq_nonneg _) (normSq_nonneg _)

/-- The finite full Cauchy window is the critical divisor plus complete
reflected pairs, before any sign or norm is taken. -/
theorem riemannXiSpectralWindowCauchySum_eq_critical_add_pairs {T : ℝ}
    (hT : 0 ≤ T) (z : ℂ) :
    riemannXiSpectralWindowCauchySum T z =
      riemannXiSpectralCriticalCauchyWindow z T +
        ∑ rho ∈ spectralUpperZetaZeroWindow T, zetaSpectralConjugateCauchyPair z rho := by
  rw [riemannXiSpectralWindowCauchySum_eq_upper_add_critical_add_lower,
    riemannXiSpectralLowerCauchyWindow_eq_upper_conjugatePartner_sum hT]
  simp only [zetaSpectralConjugateCauchyPair, Finset.sum_add_distrib,
    riemannXiSpectralUpperCauchyWindow]
  ring

private lemma outside_disk_of_horizontal_gap {z : ℂ} (rho : NontrivialZetaZero)
    (hgap : |z.re| + 1 / 2 ≤ |(zetaSpectralCoordinate rho.1).re|) :
    z ∉ zetaSpectralJensenDisk rho := by
  have htri : |(zetaSpectralCoordinate rho.1).re| ≤
      |z.re| + |z.re - (zetaSpectralCoordinate rho.1).re| := by
    simpa only [add_sub_cancel, abs_sub_comm] using
      abs_add_le z.re ((zetaSpectralCoordinate rho.1).re - z.re)
  have hd : 1 / 2 ≤ |z.re - (zetaSpectralCoordinate rho.1).re| := by linarith
  have hi := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hisq : (zetaSpectralCoordinate rho.1).im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zetaSpectralCoordinate rho.1).im, abs_nonneg (zetaSpectralCoordinate rho.1).im]
  have hdsq : (1 / 2 : ℝ) ^ 2 ≤ (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 := by
    nlinarith [sq_abs (z.re - (zetaSpectralCoordinate rho.1).re)]
  change ¬ ((z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
    (zetaSpectralCoordinate rho.1).im ^ 2)
  linarith [sq_nonneg z.im]

private lemma window_subset {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    spectralZetaZeroWindow S ⊆ spectralZetaZeroWindow T := by
  intro rho hrho
  exact (mem_spectralZetaZeroWindow (hS.trans hST) rho).mpr
    (((mem_spectralZetaZeroWindow hS rho).mp hrho).trans hST)

private lemma sum_le_sum_of_nonpos_outside {ι : Type*} {S T : Finset ι} (f : ι → ℝ)
    (hsub : S ⊆ T) (hneg : ∀ i ∈ T, i ∉ S → f i ≤ 0) :
    ∑ i ∈ T, f i ≤ ∑ i ∈ S, f i := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i hi hn => neg_nonneg.mpr (hneg i hi hn))
  simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using h

private lemma critical_principal_im_nonpos {z : ℂ} (hz : 0 ≤ z.im)
    (rho : NontrivialZetaZero) (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    (zetaSpectralLogDerivativePrincipalPart rho z).im ≤ 0 := by
  have hp := zetaSpectralPoissonContribution_nonneg rho (by simpa only [hrho] using hz)
  rw [zetaSpectralPoissonContribution_eq_neg_im] at hp
  linarith

/-- Once a symmetric spectral window contains every possible positive
Jensen pair, enlarging that literal window can only decrease its imaginary
part. The omitted critical zeros and full reflected pairs have a proved sign. -/
theorem riemannXiSpectralWindowCauchySum_im_antitone_after_local_window
    {z : ℂ} (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0)
    {S T : ℝ} (hS : |z.re| + 1 / 2 ≤ S) (hST : S ≤ T) :
    (riemannXiSpectralWindowCauchySum T z).im ≤
      (riemannXiSpectralWindowCauchySum S z).im := by
  have hS0 : 0 ≤ S := by linarith [abs_nonneg z.re]
  have hT0 := hS0.trans hST
  rw [riemannXiSpectralWindowCauchySum_eq_critical_add_pairs hT0,
    riemannXiSpectralWindowCauchySum_eq_critical_add_pairs hS0, add_im, add_im]
  apply add_le_add
  · simp only [riemannXiSpectralCriticalCauchyWindow, Complex.im_sum]
    apply sum_le_sum_of_nonpos_outside _ (Finset.filter_subset_filter _ (window_subset hS0 hST))
    intro rho hrho _hn
    exact critical_principal_im_nonpos hz rho (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  · simp only [Complex.im_sum]
    apply sum_le_sum_of_nonpos_outside _ (Finset.filter_subset_filter _ (window_subset hS0 hST))
    intro rho hrho hn
    apply zetaSpectralConjugateCauchyPair_im_nonpos hz rho hxi
    apply outside_disk_of_horizontal_gap
    have hu := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    have hnot : rho ∉ spectralZetaZeroWindow S := by
      intro hm
      exact hn (mem_spectralUpperZetaZeroWindow.mpr ⟨hm, hu⟩)
    rw [mem_spectralZetaZeroWindow hS0] at hnot
    exact hS.trans (not_le.mp hnot).le

/-- The complete logarithmic derivative has an independent finite signed
upper bound. Its infinite tail is nonpositive once the head reaches the
observation ordinate plus one half; no unknown remainder bound is assumed. -/
theorem im_logDeriv_riemannXiSpectral_le_finite_window
    {z : ℂ} (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : |z.re| + 1 / 2 ≤ T) :
    (logDeriv riemannXiSpectral z).im ≤ (riemannXiSpectralWindowCauchySum T z).im := by
  apply le_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectralWindowCauchySum hxi))
  filter_upwards [eventually_ge_atTop T] with U hTU
  exact riemannXiSpectralWindowCauchySum_im_antitone_after_local_window hz hxi hT hTU

/-- A point in a genuine Jensen disk is closer in ordinate than the
zero's actual distance from the critical line, hence closer than one half. -/
theorem abs_re_sub_lt_half_of_mem_zetaSpectralJensenDisk {z : ℂ}
    (rho : NontrivialZetaZero) (hd : z ∈ zetaSpectralJensenDisk rho) :
    |z.re - (zetaSpectralCoordinate rho.1).re| < 1 / 2 := by
  change (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
    (zetaSpectralCoordinate rho.1).im ^ 2 at hd
  have hi := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hisq : (zetaSpectralCoordinate rho.1).im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zetaSpectralCoordinate rho.1).im, abs_nonneg (zetaSpectralCoordinate rho.1).im]
  nlinarith [sq_nonneg z.im, sq_abs (z.re - (zetaSpectralCoordinate rho.1).re),
    abs_nonneg (z.re - (zetaSpectralCoordinate rho.1).re)]

/-- The complete complex local Cauchy head in an ordinate band centered
at the observation point. Critical zeros and both entries of every
reflected pair are kept with their original analytic multiplicities. -/
def riemannXiLocalPairedCauchyWindow (z : ℂ) (L : ℝ) : ℂ :=
  (∑ rho ∈ spectralCriticalZetaZeroWindow (|z.re| + L),
    if |z.re - (zetaSpectralCoordinate rho.1).re| ≤ L then
      zetaSpectralLogDerivativePrincipalPart rho z else 0) +
    ∑ rho ∈ spectralUpperZetaZeroWindow (|z.re| + L),
      if |z.re - (zetaSpectralCoordinate rho.1).re| ≤ L then
        zetaSpectralConjugateCauchyPair z rho else 0

/-- A band of ordinate radius at least one half already bounds the full
imaginary logarithmic derivative from above. This keeps the local negative
terms as well as every local positive pair; all distant terms have a
proved favorable sign. -/
theorem im_logDeriv_riemannXiSpectral_le_local_paired_window {z : ℂ}
    (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) {L : ℝ} (hL : 1 / 2 ≤ L) :
    (logDeriv riemannXiSpectral z).im ≤ (riemannXiLocalPairedCauchyWindow z L).im := by
  have hT : |z.re| + 1 / 2 ≤ |z.re| + L := by linarith
  apply (im_logDeriv_riemannXiSpectral_le_finite_window hz hxi hT).trans
  rw [riemannXiSpectralWindowCauchySum_eq_critical_add_pairs (by positivity)]
  simp only [riemannXiLocalPairedCauchyWindow, riemannXiSpectralCriticalCauchyWindow,
    add_im, Complex.im_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro rho hrho
    split_ifs
    · exact le_rfl
    · exact critical_principal_im_nonpos hz rho (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  · apply Finset.sum_le_sum
    intro rho _hrho
    split_ifs with hn
    · exact le_rfl
    · apply zetaSpectralConjugateCauchyPair_im_nonpos hz rho hxi
      intro hd
      exact hn ((abs_re_sub_lt_half_of_mem_zetaSpectralJensenDisk rho hd).le.trans hL)

/-- All upper spectral pairs whose Jensen disks contain the observation
point. The known strip makes this set a literal finite zero window. -/
def riemannXiLocalJensenWindow (z : ℂ) : Finset NontrivialZetaZero :=
  (spectralUpperZetaZeroWindow (|z.re| + 1 / 2)).filter
    (fun rho => z ∈ zetaSpectralJensenDisk rho)

/-- The finite definition includes every positive pair, with no additional
cutoff restriction on the mathematical membership condition. -/
@[simp] theorem mem_riemannXiLocalJensenWindow (z : ℂ) (rho : NontrivialZetaZero) :
    rho ∈ riemannXiLocalJensenWindow z ↔
      0 < (zetaSpectralCoordinate rho.1).im ∧ z ∈ zetaSpectralJensenDisk rho := by
  classical
  rw [riemannXiLocalJensenWindow, Finset.mem_filter, mem_spectralUpperZetaZeroWindow]
  constructor
  · rintro ⟨⟨_, hu⟩, hd⟩
    exact ⟨hu, hd⟩
  · rintro ⟨hu, hd⟩
    refine ⟨⟨?_, hu⟩, hd⟩
    apply (mem_spectralZetaZeroWindow (by positivity) rho).mpr
    by_contra hn
    exact outside_disk_of_horizontal_gap rho (not_le.mp hn).le hd

/-- In the upper half-plane the pair contributes positively exactly
inside its Jensen disk. Both node exclusions and multiplicity are genuine. -/
theorem zetaSpectralConjugateCauchyPair_im_pos_iff {z : ℂ}
    (hz : 0 < z.im) (rho : NontrivialZetaZero) (hxi : riemannXiSpectral z ≠ 0) :
    0 < (zetaSpectralConjugateCauchyPair z rho).im ↔ z ∈ zetaSpectralJensenDisk rho := by
  have hne (sigma : NontrivialZetaZero) : z - zetaSpectralCoordinate sigma.1 ≠ 0 := by
    intro he
    exact hxi ((riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mpr ⟨sigma, sub_eq_zero.mp he⟩)
  have hc : z - starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ 0 := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hne rho.conjugatePartner
  have hd := mul_pos (normSq_pos.mpr (hne rho)) (normSq_pos.mpr hc)
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  rw [zetaSpectralConjugateCauchyPair_im rho hxi, div_pos_iff_of_pos_right hd,
    mul_pos_iff_of_pos_left (mul_pos (mul_pos (by norm_num) hm) hz)]
  change 0 < (zetaSpectralCoordinate rho.1).im ^ 2 -
      (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 - z.im ^ 2 ↔
    (z.re - (zetaSpectralCoordinate rho.1).re) ^ 2 + z.im ^ 2 <
      (zetaSpectralCoordinate rho.1).im ^ 2
  constructor <;> intro h <;> linarith

/-- The exact sum of all locally positive reflected contributions.
The global negative remainder is not replaced by an absolute-value tail. -/
def riemannXiLocalJensenBudget (z : ℂ) : ℝ :=
  ∑ rho ∈ riemannXiLocalJensenWindow z, (zetaSpectralConjugateCauchyPair z rho).im

/-- Every term in the actual local budget is nonnegative. -/
theorem riemannXiLocalJensenBudget_nonneg {z : ℂ}
    (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    0 ≤ riemannXiLocalJensenBudget z := by
  apply Finset.sum_nonneg
  intro rho hrho
  exact ((zetaSpectralConjugateCauchyPair_im_pos_iff hz rho hxi).mpr
    (mem_riemannXiLocalJensenWindow z rho |>.mp hrho).2).le

/-- All possible positive imaginary contribution of the COMPLETE xi
logarithmic derivative is bounded by finitely many nearby reflected pairs.
All remaining pairs and all critical zeros have a proved nonpositive sign. -/
theorem im_logDeriv_riemannXiSpectral_le_local_jensen_budget
    {z : ℂ} (hz : 0 ≤ z.im) (hxi : riemannXiSpectral z ≠ 0) :
    (logDeriv riemannXiSpectral z).im ≤ riemannXiLocalJensenBudget z := by
  classical
  have hhead := im_logDeriv_riemannXiSpectral_le_finite_window hz hxi (le_refl (|z.re| + 1 / 2))
  rw [riemannXiSpectralWindowCauchySum_eq_critical_add_pairs (by positivity), add_im,
    Complex.im_sum] at hhead
  have hc : (riemannXiSpectralCriticalCauchyWindow z (|z.re| + 1 / 2)).im ≤ 0 := by
    rw [riemannXiSpectralCriticalCauchyWindow, Complex.im_sum]
    apply Finset.sum_nonpos
    intro rho hrho
    exact critical_principal_im_nonpos hz rho (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  have hp : (∑ rho ∈ spectralUpperZetaZeroWindow (|z.re| + 1 / 2),
      (zetaSpectralConjugateCauchyPair z rho).im) ≤ riemannXiLocalJensenBudget z := by
    simp only [riemannXiLocalJensenBudget, riemannXiLocalJensenWindow, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro rho _hrho
    split_ifs with hd
    · exact le_rfl
    · exact zetaSpectralConjugateCauchyPair_im_nonpos hz rho hxi hd
  linarith

end
end RiemannGaussian
