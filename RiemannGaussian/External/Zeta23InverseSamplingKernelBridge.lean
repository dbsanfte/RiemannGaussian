import RiemannGaussian.External.Zeta23InverseSamplingZeroSide
import Zeta23.Poisson
import Zeta23.ThmD.ZeroSideD

/-!
# The Montgomery--Taylor kernel inside the literal Zeta23 sampler

This file connects the exact inverse-sampling kernel to the window and
Poisson identities used by the pinned Zeta23 zero-side theorem.  The bridge
retains the full infinite sample correlation and gives an explicit uniform
error for the ramped finite-height window.
-/

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped BigOperators

namespace RiemannGaussian
namespace Zeta23InverseSampling

/-- The real part of the paper-convention Fourier transform is the cosine
transform, with no hidden normalization constant. -/
lemma re_paperFT_ofReal_eq_integral_mul_cos
    {v : ℝ → ℝ} (hv : Integrable v) (r : ℝ) :
    (Zeta23.paperFT (fun u => (v u : ℂ)) r).re =
      ∫ u, v u * Real.cos (r * u) := by
  have hexp : AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * u)) :=
    (by fun_prop : Continuous
      (fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * u))).aestronglyMeasurable
  have hint : Integrable
      (fun u : ℝ => (v u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * u)) := by
    exact hv.ofReal.mul_bdd (c := 1) hexp (ae_of_all _ fun u => by
      rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (r * u)))
  rw [Zeta23.paperFT_def, ← Zeta23.integral_re_C hint]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change ((v u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re =
    v u * Real.cos (r * u)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_ofReal_mul_I_re (r * u)

/-- A cosine wave integrated over a symmetric interval, in the totalized
`sinc` form valid also at frequency zero. -/
lemma intervalIntegral_cos_mul_symmetric_sinc (L y : ℝ) :
    ∫ u in (-(L / 2))..(L / 2), Real.cos (y * u) =
      L * Real.sinc (y * L / 2) := by
  by_cases hL : L = 0
  · subst L
    simp
  by_cases hy : y = 0
  · subst y
    simp
  · rw [intervalIntegral.integral_comp_mul_left Real.cos hy,
      integral_cos, smul_eq_mul,
      Real.sinc_of_ne_zero (div_ne_zero (mul_ne_zero hy hL) two_ne_zero)]
    have hneg : y * -(L / 2) = -(y * L / 2) := by ring
    rw [hneg, Real.sin_neg]
    field_simp
    ring_nf

/-- Exact cosine transform of the endpoint sharp Montgomery--Taylor window.
The right side is the same normalized kernel used by the inverse-sampling
certificate. -/
theorem sharpW_one_cosineTransform
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    ∫ u, Zeta23.ThmD.sharpW 1 L u * Real.cos ((x / L) * u) =
      L * Real.sinc montgomeryTaylorTheta * montgomeryTaylorKernel x := by
  have hfun : (fun u => Zeta23.ThmD.sharpW 1 L u * Real.cos ((x / L) * u)) =
      (Set.Icc (-(L / 2)) (L / 2)).indicator
        (fun u => Zeta23.ThmD.vStar 1 (u / L) * Real.cos ((x / L) * u)) := by
    funext u
    simp only [Zeta23.ThmD.sharpW]
    by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
    · simp [hu]
    · simp [hu]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
  have hpoint : ∀ u : ℝ,
      Zeta23.ThmD.vStar 1 (u / L) * Real.cos ((x / L) * u) =
        (Real.cos (((Real.sqrt 2 - x) / L) * u) +
          Real.cos (((Real.sqrt 2 + x) / L) * u)) / 2 := by
    intro u
    unfold Zeta23.ThmD.vStar
    have hsub : ((Real.sqrt 2 - x) / L) * u =
        Real.sqrt 2 * (u / L) - (x / L) * u := by field_simp
    have hadd : ((Real.sqrt 2 + x) / L) * u =
        Real.sqrt 2 * (u / L) + (x / L) * u := by field_simp
    rw [hsub, hadd, Real.cos_sub, Real.cos_add]
    ring_nf
  simp_rw [hpoint]
  have hcontMinus : Continuous
      (fun u : ℝ => Real.cos (((Real.sqrt 2 - x) / L) * u)) := by fun_prop
  have hcontPlus : Continuous
      (fun u : ℝ => Real.cos (((Real.sqrt 2 + x) / L) * u)) := by fun_prop
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (hcontMinus.intervalIntegrable _ _) (hcontPlus.intervalIntegrable _ _),
    intervalIntegral_cos_mul_symmetric_sinc,
    intervalIntegral_cos_mul_symmetric_sinc]
  have hminus : ((Real.sqrt 2 - x) / L) * L / 2 =
      -((x - Real.sqrt 2) / 2) := by
    rw [div_mul_cancel₀ _ hL.ne']
    ring
  have hplus : ((Real.sqrt 2 + x) / L) * L / 2 =
      (x + Real.sqrt 2) / 2 := by
    rw [div_mul_cancel₀ _ hL.ne']
    ring
  rw [hminus, hplus, Real.sinc_neg]
  unfold montgomeryTaylorKernel montgomeryTaylorTheta
  have hsinc : Real.sinc (Real.sqrt 2 / 2) ≠ 0 :=
    sinc_montgomeryTaylorTheta_pos.ne'
  field_simp [hsinc]

lemma sinc_montgomeryTaylorTheta_eq :
    Real.sinc montgomeryTaylorTheta =
      Real.sqrt 2 * Real.sin montgomeryTaylorTheta := by
  rw [Real.sinc_of_ne_zero montgomeryTaylorTheta_pos.ne']
  unfold montgomeryTaylorTheta
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrt]
  rw [hsqrtSq]

lemma aStar_one_eq_sinc_montgomeryTaylorTheta :
    Zeta23.ThmD.aStar 1 = Real.sinc montgomeryTaylorTheta := by
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htheta : Zeta23.ThmD.theta 1 = montgomeryTaylorTheta := by
    unfold Zeta23.ThmD.theta montgomeryTaylorTheta
    field_simp [hsqrt]
    nlinarith
  rw [Zeta23.ThmD.aStar_eq one_pos, div_one, htheta,
    sinc_montgomeryTaylorTheta_eq]

/-- A uniform rational envelope for the exact kernel.  The slightly loose
constant keeps later ramp-error arithmetic fully exact. -/
lemma abs_montgomeryTaylorKernel_le_twelve_elevenths (x : ℝ) :
    |montgomeryTaylorKernel x| ≤ (12 : ℝ) / 11 := by
  have hsinc : (11 : ℝ) / 12 ≤ Real.sinc montgomeryTaylorTheta := by
    rw [sinc_montgomeryTaylorTheta_eq]
    exact eleven_twelfths_le_sqrt_two_mul_sin_theta
  have hden : 0 < 2 * Real.sinc montgomeryTaylorTheta := by
    positivity
  have hnum : |Real.sinc ((x - Real.sqrt 2) / 2) +
      Real.sinc ((x + Real.sqrt 2) / 2)| ≤ 2 := by
    calc
      |Real.sinc ((x - Real.sqrt 2) / 2) +
          Real.sinc ((x + Real.sqrt 2) / 2)| ≤
          |Real.sinc ((x - Real.sqrt 2) / 2)| +
            |Real.sinc ((x + Real.sqrt 2) / 2)| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sinc_le_one _) (Real.abs_sinc_le_one _)
      _ = 2 := by norm_num
  rw [montgomeryTaylorKernel, abs_div, abs_of_pos hden,
    div_le_iff₀ hden]
  nlinarith

/-! ## The literal endpoint window -/

open Zeta23

/-- The `Params` Fourier profile of the realizing endpoint window is the
corresponding admissible-window transform. -/
lemma atD_PhiR_eq_VPhiR
    {P : Params} (hP : P.Valid) (T : ℝ) :
    (P.atD T).PhiR T = AdmWindow.VPhiR (P.phiD T) := by
  show AdmWindow.VPhiR ((P.atD T).phi T) = _
  rw [Params.atD_phi_valid T hP]

/-- The full cross-correlation Poisson identity for the literal endpoint
window.  The existing zero-side only consumes its diagonal specialization;
inverse sampling needs this phase-preserving two-ordinate form. -/
theorem atD_hasSum_phiHatR_mul
    {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
    (gamma gamma' : ℝ) :
    HasSum (fun k : ℤ =>
      (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
        (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k))
      ((P.atD T).L T * (P.atD T).PhiR T (gamma - gamma')) := by
  have hW := ThmD.admWindow_params hP h8
  have h := hW.hasSum_vHatR_mul T gamma gamma'
  simpa only [ThmD.atD_phiHatR hP T, ThmD.atD_tau_eq,
    Params.atD_L, atD_PhiR_eq_VPhiR hP T] using h

/-- The Fourier kernel of the actual Montgomery--Taylor window is its literal
cosine transform. -/
theorem atD_PhiR_eq_integral_phiD_sq_mul_cos
    {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r : ℝ) :
    (P.atD T).PhiR T r =
      ∫ u, P.phiD T u ^ 2 * Real.cos (r * u) := by
  have hW := ThmD.admWindow_params hP h8
  unfold Params.PhiR Params.Phi
  rw [Params.atD_phi_valid T hP]
  exact re_paperFT_ofReal_eq_integral_mul_cos (hW.integrable_pow two_pos) r

/-- Uniform Fourier approximation of the literal ramped endpoint window by
the exact Montgomery--Taylor kernel.  This is a pointwise theorem for every
frequency, not an asymptotic assertion. -/
theorem atD_PhiR_div_L_close_montgomeryTaylorKernel
    {P : Params} (hP : P.Valid) (hlam : P.lam = 1)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (x : ℝ) :
    |(P.atD T).PhiR T (x / P.L T) / P.L T -
        Real.sinc montgomeryTaylorTheta * montgomeryTaylorKernel x| ≤
      2 * P.w / P.L T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hW := ThmD.admWindow_params hP h8
  let f : ℝ → ℝ := fun u => P.phiD T u ^ 2
  let k : ℝ → ℝ := ThmD.sharpW 1 (P.L T)
  let c : ℝ → ℝ := fun u => Real.cos ((x / P.L T) * u)
  have hf : Integrable f := by
    exact hW.integrable_pow two_pos
  have hk : Integrable k := by
    unfold k ThmD.sharpW
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (((by unfold ThmD.vStar; fun_prop : Continuous
        (fun u : ℝ => ThmD.vStar 1 (u / P.L T))).continuousOn).integrableOn_compact
          isCompact_Icc)
  have hc : Continuous c := by unfold c; fun_prop
  have hfc : Integrable (fun u => f u * c u) :=
    hf.mul_bdd hc.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa [c] using Real.abs_cos_le_one ((x / P.L T) * u))
  have hkc : Integrable (fun u => k u * c u) :=
    hk.mul_bdd hc.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa [c] using Real.abs_cos_le_one ((x / P.L T) * u))
  have hdiff : Integrable (fun u => |f u - k u|) := hf.sub hk |>.abs
  have hedge := ThmD.integral_abs_phiDsq_sub_sharp
    hP.taper hP.lam_pos hP.lam_le_one (by linarith [hP.one_le_w])
      (by linarith : 2 * P.w ≤ P.L T)
  rw [hlam] at hedge
  have hFourier : |(∫ u, f u * c u) - (∫ u, k u * c u)| ≤ 2 * P.w := by
    have hsub : (∫ u, f u * c u) - ∫ u, k u * c u =
        ∫ u, (f u * c u - k u * c u) :=
      (integral_sub hfc hkc).symm
    calc
      |(∫ u, f u * c u) - (∫ u, k u * c u)| =
          |∫ u, (f u - k u) * c u| := by
            rw [hsub]
            congr 2 with u
            ring
      _ ≤ ∫ u, |(f u - k u) * c u| := abs_integral_le_integral_abs
      _ ≤ ∫ u, |f u - k u| := by
        apply integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hdiff
        apply ae_of_all
        intro u
        change |(f u - k u) * c u| ≤ |f u - k u|
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (by
          simpa [c] using Real.abs_cos_le_one ((x / P.L T) * u))
      _ ≤ 2 * P.w := by
        simpa [f, k, Params.phiD, hlam] using hedge
  have hPhi := atD_PhiR_eq_integral_phiD_sq_mul_cos hP h8 (x / P.L T)
  have hsharp := sharpW_one_cosineTransform hL x
  rw [hPhi]
  change |(∫ u, f u * c u) / P.L T -
      Real.sinc montgomeryTaylorTheta * montgomeryTaylorKernel x| ≤
        2 * P.w / P.L T
  rw [show Real.sinc montgomeryTaylorTheta * montgomeryTaylorKernel x =
      (∫ u, k u * c u) / P.L T by
        change Real.sinc montgomeryTaylorTheta * montgomeryTaylorKernel x =
          (∫ u, ThmD.sharpW 1 (P.L T) u * Real.cos ((x / P.L T) * u)) /
            P.L T
        rw [hsharp]
        field_simp]
  rw [← sub_div, abs_div, abs_of_pos hL]
  exact (div_le_div_iff_of_pos_right hL).2 hFourier

/-- The literal endpoint-window mass has the same explicit scale-free target
as the kernel normalization. -/
theorem atD_a_close_sinc_montgomeryTaylorTheta
    {P : Params} (hP : P.Valid) (hlam : P.lam = 1)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    |(P.atD T).a T - Real.sinc montgomeryTaylorTheta| ≤
      4 * P.w / P.L T := by
  have h := ThmD.aD_close hP.taper hP.lam_pos hP.lam_le_one
    hP.one_le_w h8
  rw [hlam] at h
  rw [ThmD.atD_a_eq_av hP T]
  simpa [AdmWindow.av, Params.phiD, hlam,
    aStar_one_eq_sinc_montgomeryTaylorTheta] using h

/-- After the literal Poisson normalization, the full endpoint sampler is
uniformly within `14w/L` of the exact inverse-sampling kernel. -/
theorem atD_normalizedPhiR_close_montgomeryTaylorKernel
    {P : Params} (hP : P.Valid) (hlam : P.lam = 1)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T) (x : ℝ) :
    |(P.atD T).PhiR T (x / P.L T) /
          ((P.atD T).a T * P.L T) - montgomeryTaylorKernel x| ≤
      14 * (P.w / P.L T) := by
  let a : ℝ := (P.atD T).a T
  let p : ℝ := (P.atD T).PhiR T (x / P.L T) / P.L T
  let q : ℝ := Real.sinc montgomeryTaylorTheta
  let K : ℝ := montgomeryTaylorKernel x
  let e : ℝ := P.w / P.L T
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have he : 0 ≤ e := by
    exact div_nonneg (le_trans zero_le_one hP.one_le_w) hL.le
  have haLower : (1 : ℝ) / 2 ≤ a := by
    exact (ThmD.aD_range_of hP h8 h4pi).1
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  have hp : |p - q * K| ≤ 2 * e := by
    have h := atD_PhiR_div_L_close_montgomeryTaylorKernel hP hlam h8 x
    dsimp [p, q, K, e]
    convert h using 1
    ring
  have ha : |a - q| ≤ 4 * e := by
    have h := atD_a_close_sinc_montgomeryTaylorTheta hP hlam h8
    dsimp [a, q, e]
    convert h using 1
    ring
  have hK : |K| ≤ (12 : ℝ) / 11 := by
    exact abs_montgomeryTaylorKernel_le_twelve_elevenths x
  have hsecond : |(q - a) * K| ≤ (48 : ℝ) / 11 * e := by
    rw [abs_mul]
    calc
      |q - a| * |K| ≤ (4 * e) * |K| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg K)
        simpa [abs_sub_comm] using ha
      _ ≤ (4 * e) * ((12 : ℝ) / 11) := by
        exact mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num) he)
      _ = (48 : ℝ) / 11 * e := by ring
  have hnum : |(p - q * K) + (q - a) * K| ≤ 7 * e := by
    calc
      |(p - q * K) + (q - a) * K| ≤
          |p - q * K| + |(q - a) * K| := abs_add_le _ _
      _ ≤ 2 * e + (48 : ℝ) / 11 * e := add_le_add hp hsecond
      _ ≤ 7 * e := by nlinarith
  have hid : (P.atD T).PhiR T (x / P.L T) /
        ((P.atD T).a T * P.L T) - montgomeryTaylorKernel x =
      ((p - q * K) + (q - a) * K) / a := by
    have hnorm : (P.atD T).PhiR T (x / P.L T) /
          ((P.atD T).a T * P.L T) = p / a := by
      dsimp [p, a]
      field_simp [hL.ne', haPos.ne']
    rw [hnorm]
    change p / a - K = ((p - q * K) + (q - a) * K) / a
    have hcollapse : (p - q * K) + (q - a) * K = p - a * K := by ring
    rw [hcollapse, sub_div, mul_div_cancel_left₀ K haPos.ne']
  rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
  have hmargin : 0 ≤ e * (a - (1 : ℝ) / 2) :=
    mul_nonneg he (sub_nonneg.mpr haLower)
  nlinarith

/-- Exact normalization of the complete literal sampling correlation. -/
theorem atD_tsum_normalized_eq_normalizedPhiR
    {P : Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (gamma gamma' : ℝ) :
    (∑' k : ℤ,
        (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
          (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)) /
        ((P.atD T).a T * P.L T ^ 2) =
      (P.atD T).PhiR T (gamma - gamma') /
        ((P.atD T).a T * P.L T) := by
  have hsum := (atD_hasSum_phiHatR_mul hP h8 gamma gamma').tsum_eq
  rw [hsum, Params.atD_L]
  have hL : P.L T ≠ 0 := by linarith [hP.one_le_w]
  have ha : (P.atD T).a T ≠ 0 := by
    have := (ThmD.aD_range_of hP h8 h4pi).1
    positivity
  field_simp [hL, ha]

/-- The complete literal endpoint sampler realizes the exact
Montgomery--Taylor correlation at normalized zero spacing, with explicit
uniform error `14w/L`.  Passing from this complete sum to the finite Zeta23
Gram is now only a sample-tail problem. -/
theorem atD_fullNormalizedCorrelation_close_montgomeryTaylorKernel
    {P : Params} (hP : P.Valid) (hlam : P.lam = 1)
    {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (gamma gamma' : ℝ) :
    |(∑' k : ℤ,
        (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
          (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)) /
          ((P.atD T).a T * P.L T ^ 2) -
        montgomeryTaylorKernel (P.L T * (gamma - gamma'))| ≤
      14 * (P.w / P.L T) := by
  rw [atD_tsum_normalized_eq_normalizedPhiR hP h8 h4pi gamma gamma']
  have h := atD_normalizedPhiR_close_montgomeryTaylorKernel
    hP hlam h8 h4pi (P.L T * (gamma - gamma'))
  have hL : P.L T ≠ 0 := by linarith [hP.one_le_w]
  simpa [hL] using h

end Zeta23InverseSampling
end RiemannGaussian
