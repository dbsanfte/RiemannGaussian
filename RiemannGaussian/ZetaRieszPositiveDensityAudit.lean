/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedGamma
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A positive, phase-consistent null model for adjacent factorial moments

This is a CONTINUOUS density, not the arithmetic ordinary-prime measure.
Its full factorial moments tend to the retained negative source despite
positivity and exact common-phase/order coupling. No prime-sum bound,
arithmetic floor or zero exclusion is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter MeasureTheory Set Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPositiveDensityAudit
open ZetaRieszSelectedGamma

/-- One positive-density candidate, with a small relative oscillatory ripple. -/
def density (u y t : ℝ) : ℝ :=
  (exp t-2*exp ((3/2-u)*t)*cos (y*t))/t

/-- Positivity does not remove this coherent phase ripple. -/
theorem density_pos {u y t : ℝ} (ht : 0<t) (hgap : 1≤(u-1/2)*t) :
    0<density u y t := by
  have he : (2 : ℝ)<exp 1 := by
    have hh := add_one_lt_exp (by norm_num : (1 : ℝ)≠0)
    norm_num at hh
    exact hh
  have hg : 2<exp ((u-1/2)*t) := he.trans_le (exp_le_exp.mpr hgap)
  have hsplit : exp t=exp ((3/2-u)*t)*exp ((u-1/2)*t) := by
    rw [←exp_add]
    congr 1
    ring
  have hc := cos_le_one (y*t)
  have hp := exp_pos ((3/2-u)*t)
  unfold density
  apply div_pos _ ht
  rw [hsplit]
  nlinarith only [hg,hc,hp]

/-- At the current radius ceiling the model is strictly positive on the
entire log half-line starting at 20000, for every phase height. -/
theorem density_ceiling_pos (y : ℝ) {t : ℝ} (ht : 20000≤t) :
    0<density (10001/20000) y t := by
  apply density_pos (by linarith only [ht])
  norm_num
  linarith only [ht]

/-- The ripple is exponentially small relative to the smooth density;
its exact phase and rate are retained. -/
theorem relative_density_eq (u y : ℝ) {t : ℝ} (ht : t≠0) :
    t*density u y t/exp t-1=-2*exp (-(u-1/2)*t)*cos (y*t) := by
  have he : exp ((3/2-u)*t)=exp t*exp (-(u-1/2)*t) := by
    rw [←exp_add]
    congr 1
    ring
  unfold density
  rw [he]
  field_simp [ht,(exp_pos t).ne']
  ring

/-- Even a fixed power-sized relative ripple can carry the moment source. -/
theorem relative_density_abs_le (u y : ℝ) {t : ℝ} (ht : t≠0) :
    |t*density u y t/exp t-1|≤2*exp (-(u-1/2)*t) := by
  rw [relative_density_eq u y ht,abs_mul,abs_mul]
  norm_num only [abs_neg,abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one (y*t))

/-- Exact phase identity; the density is not replaced by its asymptotic main. -/
theorem density_phase_eq (u y t : ℝ) :
    Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ)=
      (Complex.exp (-(1/2+Complex.I*y)*(t : ℂ))-
        Complex.exp (-(u : ℂ)*(t : ℂ))-
          Complex.exp (-((u : ℂ)+2*Complex.I*y)*(t : ℂ)))/(t : ℂ) := by
  have hc : 2*(cos (y*t) : ℂ)=
      Complex.exp (Complex.I*y*(t : ℂ))+Complex.exp (-Complex.I*y*(t : ℂ)) := by
    rw [Complex.ofReal_cos,Complex.cos]
    push_cast
    ring
  have h1 : Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*Complex.exp (t : ℂ)=
      Complex.exp (-(1/2+Complex.I*y)*(t : ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*
      Complex.exp (((3/2-u)*t : ℝ) : ℂ)*Complex.exp (Complex.I*y*(t : ℂ))=
      Complex.exp (-(u : ℂ)*(t : ℂ)) := by
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    push_cast
    ring
  have h3 : Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*
      Complex.exp (((3/2-u)*t : ℝ) : ℂ)*Complex.exp (-Complex.I*y*(t : ℂ))=
      Complex.exp (-((u : ℂ)+2*Complex.I*y)*(t : ℂ)) := by
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold density
  push_cast
  push_cast at hc h2 h3
  rw [←mul_div_assoc]
  congr 1
  calc
    _ = Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*Complex.exp (t : ℂ)-
        Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*
          Complex.exp (((3/2-u)*t : ℝ) : ℂ)*(2*(cos (y*t) : ℂ)) := by
      push_cast
      ring
    _ = _ := by
      push_cast
      rw [hc,mul_add,h1,h2,h3]
      ring

/-- The same factorial integrand at every channel, including logged order zero. -/
def integrand (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ)^n/(n.factorial : ℂ)*Complex.exp (-z*t)

/-- The literal lower-threshold integral; no complete-leg limit is substituted. -/
def tailLeg (u : ℝ) (z : ℂ) (B : ℝ) (n : ℕ) : ℂ :=
  (u : ℂ)^(n+1)*∫ t : ℝ in Ioi B,integrand z n t

/-- Exact bounded-log complement of the same integral. -/
def headLeg (u : ℝ) (z : ℂ) (B : ℝ) (n : ℕ) : ℂ :=
  (u : ℂ)^(n+1)*∫ t : ℝ in Ioc 0 B,integrand z n t

/-- All lower-threshold channels are genuinely integrable. -/
theorem integrand_integrable {z : ℂ} (hz : 0<z.re) {B : ℝ} (hB : 0≤B) (n : ℕ) :
    IntegrableOn (integrand z n) (Ioi B) :=
  (complex_factorial_laplace hz n).1.mono_set (Ioi_subset_Ioi hB)

/-- The finite-log head has a factorial bound, uniform in the imaginary damping. -/
theorem norm_headLeg_le {u B : ℝ} (hu : 0≤u) (hB : 0≤B)
    {z : ℂ} (hz : 0≤z.re) (n : ℕ) :
    ‖headLeg u z B n‖≤u*B*((u*B)^n/(n.factorial : ℝ)) := by
  have hp (t : ℝ) (ht : t∈Ioc (0 : ℝ) B) :
      ‖integrand z n t‖≤B^n/(n.factorial : ℝ) := by
    have he : ‖Complex.exp (-z*(t : ℂ))‖≤1 := by
      rw [Complex.norm_exp]
      apply exp_le_one_iff.mpr
      simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,
        Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hz ht.1.le)
    unfold integrand
    rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht.1.le,
      Complex.norm_natCast]
    exact (mul_le_of_le_one_right
        (div_nonneg (pow_nonneg ht.1.le n) (Nat.cast_nonneg _)) he).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ ht.1.le ht.2 n) (Nat.cast_nonneg _))
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc (0 : ℝ) B) measure_Ioc_lt_top hp
  rw [Real.volume_real_Ioc_of_le hB,sub_zero] at hi
  unfold headLeg
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  apply (mul_le_mul_of_nonneg_left hi (pow_nonneg hu (n+1))).trans_eq
  rw [pow_succ,mul_pow]
  ring

/-- A fixed lower log threshold contributes no asymptotic factorial source. -/
theorem headLeg_tendsto {u B : ℝ} (hu : 0≤u) (hB : 0≤B) {z : ℂ} (hz : 0≤z.re) :
    Tendsto (headLeg u z B) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => norm_headLeg_le hu hB hz n)
  simpa only [mul_zero] using
    (FloorSemiring.tendsto_pow_div_factorial_atTop (u*B)).const_mul (u*B)

/-- Complete minus head is an exact integral identity, not a mask inference. -/
theorem tailLeg_eq_complete_sub_head (u : ℝ) {z : ℂ} (hz : 0<z.re)
    {B : ℝ} (hB : 0≤B) (n : ℕ) :
    tailLeg u z B n=((u : ℂ)/z)^(n+1)-headLeg u z B n := by
  have hs : Ioi B=Ioi (0 : ℝ)\Ioc 0 B := by
    ext t
    simp only [mem_Ioi,Set.mem_sdiff,mem_Ioc]
    constructor <;> intro ht
    · exact ⟨lt_of_le_of_lt hB ht,by rintro ⟨_,hle⟩; exact (not_le_of_gt ht) hle⟩
    · by_contra h
      exact ht.2 ⟨ht.1,le_of_not_gt h⟩
  unfold tailLeg headLeg
  have hi : IntegrableOn (integrand z n) (Ioi 0) := (complex_factorial_laplace hz n).1
  rw [hs,setIntegral_sdiff measurableSet_Ioc hi Ioc_subset_Ioi_self]
  change (u : ℂ)^(n+1)*((∫ t : ℝ in Ioi 0,(t : ℂ)^n/(n.factorial : ℂ)*
    Complex.exp (-z*t))-∫ t : ℝ in Ioc 0 B,integrand z n t)=_
  rw [(complex_factorial_laplace hz n).2,mul_sub,div_eq_mul_inv,mul_pow]

/-- A separated channel decays while its exact lower-threshold head is retained. -/
theorem tailLeg_tendsto_zero {u B : ℝ} (hu : 0≤u) (hB : 0≤B)
    {z : ℂ} (hz : 0<z.re) (hgap : u<‖z‖) :
    Tendsto (tailLeg u z B) atTop (𝓝 0) := by
  have hn : ‖(u : ℂ)/z‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hu]
    exact (div_lt_one (lt_of_le_of_lt hu hgap)).mpr hgap
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).comp (tendsto_add_atTop_nat 1)
  have hh := headLeg_tendsto hu hB hz.le
  simpa only [zero_sub,neg_zero,Function.comp_def] using
    (hp.sub hh).congr (fun n => (tailLeg_eq_complete_sub_head u hz hB n).symm)

/-- The selected real damping preserves the negative channel's unit source. -/
theorem tailLeg_tendsto_one {u B : ℝ} (hu : 0<u) (hB : 0≤B) :
    Tendsto (tailLeg u (u : ℂ) B) atTop (𝓝 1) := by
  have hh := headLeg_tendsto hu.le hB (z := (u : ℂ)) (by simpa using hu.le)
  have he (n : ℕ) : tailLeg u (u : ℂ) B n=1-headLeg u (u : ℂ) B n := by
    rw [tailLeg_eq_complete_sub_head u (by simpa using hu) hB,
      div_self (by exact_mod_cast hu.ne'),one_pow]
  simpa only [sub_zero] using
    (((tendsto_const_nhds (x := (1 : ℂ))).sub hh).congr (fun n => (he n).symm))

/-- The actual common-phase factorial moment of the continuous density.
Every logged order is kept, starting at zero. This is not a prime sum. -/
def densityMoment (u y B : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Ioi B,(u : ℂ)^(n+1)*(t : ℂ)^(n+1)/(n.factorial : ℂ)*
    Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ)

private theorem moment_integrand_eq (u y : ℝ) (n : ℕ) {t : ℝ} (ht : 0<t) :
    (u : ℂ)^(n+1)*(t : ℂ)^(n+1)/(n.factorial : ℂ)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ)=
    (u : ℂ)^(n+1)*(integrand (1/2+Complex.I*y) n t-
      integrand (u : ℂ) n t-integrand ((u : ℂ)+2*Complex.I*y) n t) := by
  have ht0 : (t : ℂ)≠0 := by exact_mod_cast ht.ne'
  have hn0 : (n.factorial : ℂ)≠0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  calc
    _ = (u : ℂ)^(n+1)*(t : ℂ)^(n+1)/(n.factorial : ℂ)*
      (Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ)) := by ring
    _ = _ := by
      rw [density_phase_eq]
      unfold integrand
      rw [pow_succ]
      field_simp [ht0,hn0]
      ring

/-- The full density moment is exactly the three lower-threshold channels,
not three independent limiting surrogates. -/
theorem densityMoment_eq_channels {u B : ℝ} (hu : 0<u) (hB : 0≤B) (y : ℝ) (n : ℕ) :
    densityMoment u y B n=tailLeg u (1/2+Complex.I*y) B n-
      tailLeg u (u : ℂ) B n-tailLeg u ((u : ℂ)+2*Complex.I*y) B n := by
  have h1 := integrand_integrable (z := 1/2+Complex.I*y) (by norm_num) hB n
  have h2 := integrand_integrable (z := (u : ℂ)) (by simpa using hu) hB n
  have h3 := integrand_integrable (z := (u : ℂ)+2*Complex.I*y) (by simpa using hu) hB n
  unfold densityMoment
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => moment_integrand_eq u y n (lt_of_le_of_lt hB ht))]
  rw [integral_const_mul]
  have hi := (integral_sub (h1.sub h2) h3).trans
    (congrArg (fun v : ℂ => v-∫ t : ℝ in Ioi B,integrand ((u : ℂ)+2*Complex.I*y) n t)
      (integral_sub h1 h2))
  simp only [Pi.sub_apply] at hi
  rw [hi]
  unfold tailLeg
  ring

/-- Genuine integrability of the positive-density/common-phase moment. -/
theorem densityMoment_integrable {u B : ℝ} (hu : 0<u) (hB : 0≤B) (y : ℝ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (u : ℂ)^(n+1)*(t : ℂ)^(n+1)/(n.factorial : ℂ)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ)) (Ioi B) := by
  have h1 := integrand_integrable (z := 1/2+Complex.I*y) (by norm_num) hB n
  have h2 := integrand_integrable (z := (u : ℂ)) (by simpa using hu) hB n
  have h3 := integrand_integrable (z := (u : ℂ)+2*Complex.I*y) (by simpa using hu) hB n
  apply (((h1.sub h2).sub h3).const_mul ((u : ℂ)^(n+1))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (moment_integrand_eq u y n (lt_of_le_of_lt hB ht)).symm

/-- This positive, phase-consistent model reproduces the selected moment
source `-1`. Positivity/factorial coupling alone cannot prohibit that source. -/
theorem densityMoment_tendsto {u B : ℝ} (hu : 0<u) (hu1 : u<1) (hB : 0≤B)
    {y : ℝ} (hy : 1≤|y|) :
    Tendsto (densityMoment u y B) atTop (𝓝 (-1)) := by
  have hp : |y|≤‖(1/2 : ℂ)+Complex.I*y‖ := by
    simpa using Complex.abs_im_le_norm ((1/2 : ℂ)+Complex.I*y)
  have hc : 2*|y|≤‖(u : ℂ)+2*Complex.I*y‖ := by
    simpa [abs_mul] using
        Complex.abs_im_le_norm ((u : ℂ)+2*Complex.I*y)
  have h1 := tailLeg_tendsto_zero hu.le hB (z := (1/2 : ℂ)+Complex.I*y)
    (by norm_num) (lt_of_lt_of_le hu1 (hy.trans hp))
  have h2 := tailLeg_tendsto_one hu hB
  have h3 := tailLeg_tendsto_zero hu.le hB (z := (u : ℂ)+2*Complex.I*y)
    (by simpa using hu) (by linarith only [hu1,hy,hc])
  have h := (h1.sub h2).sub h3
  simpa only [zero_sub,sub_zero,Function.comp_def] using
    h.congr (fun n => (densityMoment_eq_channels hu hB y n).symm)

/-- Concrete model at the current radius, with no exposed-zero hypothesis
and no restriction on low factorial orders. -/
theorem density_ceiling_moment_tendsto {y : ℝ} (hy : 1≤|y|) :
    Tendsto (densityMoment (10001/20000) y 20000) atTop (𝓝 (-1)) :=
  densityMoment_tendsto (by norm_num) (by norm_num) (by norm_num) hy

end RiemannGaussian.ZetaRieszPositiveDensityAudit
