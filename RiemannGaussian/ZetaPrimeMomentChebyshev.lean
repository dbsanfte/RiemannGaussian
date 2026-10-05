/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentCoherence
import RiemannGaussian.SignedLaplaceMoments
import RiemannGaussian.AnalyticDoublePoleMoments
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The literal prime moment and the Chebyshev error

The signed relative Chebyshev error in logarithmic coordinates is retained
inside the Laplace integral, including its complex phase. These identities
do not assert an arithmetic cancellation bound or a zero-free region.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Complex Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaPrimeMomentChebyshev
open ZetaPrimeMomentCoherence

/-- The actual relative Chebyshev error after `x=exp(t)`. -/
def logError (t : ℝ) : ℝ := Real.exp (-t)*Chebyshev.psi (Real.exp t)-1

/-- Its one-sided complex Laplace transform. -/
def errorLaplace (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (logError t : ℂ)*Complex.exp (-z*t)

/-- The complete signed factorial moment of that error, with full phase. -/
def errorMoment (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    ((logError t : ℂ)*(t : ℂ)^k*Complex.exp (-z*t))/(k.factorial : ℂ)

private theorem psi_le_six_mul {x : ℝ} (hx : 0≤x) : Chebyshev.psi x≤6*x := by
  have hlog : Real.log 4≤2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    have he : Real.log (4 : ℝ)=2*Real.log 2 := by
      rw [show (4 : ℝ)=2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [he]
    linarith
  exact (Chebyshev.psi_le_const_mul_self hx).trans
    (mul_le_mul_of_nonneg_right (by linarith) hx)

/-- A global Chebyshev envelope suffices for the Laplace identities;
it is not used as a source-scale cancellation estimate. -/
theorem abs_logError_le (t : ℝ) : |logError t|≤5 := by
  have hp := Chebyshev.psi_nonneg (Real.exp t)
  have hb := psi_le_six_mul (Real.exp_pos t).le
  have he : Real.exp (-t)*Real.exp t=1 := by rw [←Real.exp_add]; simp
  unfold logError
  rw [abs_le]
  constructor
  · have hn := mul_nonneg (Real.exp_pos (-t)).le hp
    linarith
  · have h := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-t)).le
    nlinarith only [h,he]

theorem measurable_logError : Measurable logError := by
  unfold logError
  exact ((Real.measurable_exp.comp measurable_neg).mul
    (Chebyshev.psi_mono.measurable.comp Real.measurable_exp)).sub measurable_const

theorem integrable_logError_exp {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun t : ℝ => logError t*Real.exp (-x*t)) (Ioi 0) := by
  have h := (integrableOn_exp_mul_Ioi (by linarith : -x<0) 0).const_mul (5 : ℝ)
  apply h.mono' ((measurable_logError.mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards with t
  change ‖logError t*Real.exp (-x*t)‖≤5*Real.exp (-x*t)
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
    mul_le_mul_of_nonneg_right (abs_logError_le t) (Real.exp_pos _).le

/-- Every derivative of the literal signed error transform is an
integrable factorial moment. No exposure or zero assumption enters. -/
theorem analytic_errorLaplace_and_moments {z : ℂ} (hz : 0<z.re) :
    AnalyticAt ℂ errorLaplace z ∧ ∀ k : ℕ,
      IntegrableOn (fun t : ℝ => (logError t : ℂ)*(t : ℂ)^k*
        Complex.exp (-z*t)) (Ioi 0) ∧
      signedTaylorMoment k errorLaplace z=errorMoment k z :=
  signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := logError) measurable_logError.aemeasurable
    (fun _ hx => integrable_logError_exp hx) hz

private theorem psi_sum (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n)=Chebyshev.psi x := by
  unfold Chebyshev.psi
  congr 1

/-- The exact Mellin formula for the actual von Mangoldt sequence. -/
theorem logDeriv_eq_psi_integral {s : ℂ} (hs : 1<s.re) :
    -logDeriv riemannZeta s =
      s*∫ x : ℝ in Ioi 1, (Chebyshev.psi x : ℂ)*(x : ℂ)^(-(s+1)) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] (fun n : ℕ => (n : ℝ)^(1 : ℝ)) := by
    apply IsBigO.of_bound 6
    filter_upwards with n
    have he := psi_sum (n : ℝ)
    simp only [Nat.floor_natCast] at he
    rw [he]
    simp only [Real.norm_eq_abs,Real.rpow_one,abs_of_nonneg (Chebyshev.psi_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
    exact psi_le_six_mul (Nat.cast_nonneg n)
  have h := LSeries_eq_mul_integral_of_nonneg
    ArithmeticFunction.vonMangoldt (r := 1) zero_le_one hs hO (by intro n; positivity)
  have he := neg_logDeriv_riemannZeta_eq_vonMangoldt hs
  change -logDeriv riemannZeta s=LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s at he
  rw [he,h]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [←Complex.ofReal_sum,psi_sum]

private theorem exponential_mellin (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ)*(Real.exp t : ℂ)^(-(s+1))=Complex.exp (-s*t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ←Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp,Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  ring

/-- A global substitution, not a truncation or prime-density approximation. -/
theorem logDeriv_eq_psi_log_integral {s : ℂ} (hs : 1<s.re) :
    -logDeriv riemannZeta s =
      s*∫ t : ℝ in Ioi 0, (Chebyshev.psi (Real.exp t) : ℂ)*Complex.exp (-s*t) := by
  rw [logDeriv_eq_psi_integral hs]
  congr 1
  rw [←show Real.exp (0 : ℝ)=1 by simp,←integral_comp_exp_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.real_smul]
  rw [mul_left_comm,exponential_mellin]

private theorem psi_integrand_split (s : ℂ) (t : ℝ) :
    (Chebyshev.psi (Real.exp t) : ℂ)*Complex.exp (-s*t)=
      Complex.exp (-(s-1)*t)+(logError t : ℂ)*Complex.exp (-(s-1)*t) := by
  have he : (Real.exp (-t) : ℂ)*Complex.exp (-(s-1)*t)=Complex.exp (-s*t) := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [←he]
  simp only [logError,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  ring

/-- The elementary `psi(x)=x` part and the literal signed error are
separated exactly on the Euler half-plane. -/
theorem logDeriv_eq_errorLaplace {s : ℂ} (hs : 1<s.re) :
    -logDeriv riemannZeta s=s/(s-1)+s*errorLaplace (s-1) := by
  have hz : 0<(s-1).re := by simpa using sub_pos.mpr hs
  have h := signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun _ => (1 : ℝ)) (b := 0) aemeasurable_const
    (fun x hx => by
      simpa only [one_mul,IntegrableOn] using integrableOn_exp_mul_Ioi (by linarith : -x<0) 0) hz
  have hi := (h.2 0).1
  simp only [Complex.ofReal_one,pow_zero,mul_one,one_mul] at hi
  have hj := (analytic_errorLaplace_and_moments hz).2 0
  simp only [pow_zero,mul_one] at hj
  rw [logDeriv_eq_psi_log_integral hs]
  have he : (fun t : ℝ => (Chebyshev.psi (Real.exp t) : ℂ)*Complex.exp (-s*t))=
      (fun t : ℝ => Complex.exp (-(s-1)*t)+(logError t : ℂ)*Complex.exp (-(s-1)*t)) :=
    funext (psi_integrand_split s)
  rw [he,integral_add hi hj.1]
  have hp := integral_exp_mul_complex_Ioi (a := -(s-1))
    (by simpa only [Complex.neg_re] using neg_neg_of_pos hz) 0
  rw [hp]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq,one_div]
  change s*((s-1)⁻¹+errorLaplace (s-1))=s/(s-1)+s*errorLaplace (s-1)
  ring

private theorem moment_id (n : ℕ) (s : ℂ) :
    signedTaylorMoment n (fun w : ℂ => w) s=
      if n=0 then s else if n=1 then -1 else 0 := by
  rcases n with _ | n
  · simp [signedTaylorMoment]
  rcases n with _ | n
  · simp [signedTaylorMoment,iteratedDeriv_succ]
  · simp [signedTaylorMoment,iteratedDeriv_fun_id]

private theorem moment_linear_mul {g : ℂ→ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    signedTaylorMoment (k+1) (fun w : ℂ => w*g w) s=
      s*signedTaylorMoment (k+1) g s-signedTaylorMoment k g s := by
  rw [signedTaylorMoment_mul (f := fun w : ℂ => w) (g := g) analyticAt_id hg]
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  simp [moment_id]
  ring

private theorem moment_error_translate {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    signedTaylorMoment k (fun w => errorLaplace (w-1)) s=errorMoment k (s-1) := by
  have ht := congrFun (iteratedDeriv_comp_add_const k errorLaplace (-1)) s
  simp only [←sub_eq_add_neg] at ht
  unfold signedTaylorMoment
  rw [ht]
  exact (analytic_errorLaplace_and_moments (by simpa using sub_pos.mpr hs)).2 k |>.2

/-- Every positive-order full von Mangoldt moment is an exact linear
combination of consecutive signed Chebyshev-error moments. -/
theorem vonMangoldt_moment_eq_error {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    zetaPrimeLogMoment (k+1) s=
      ((s-1)⁻¹)^(k+2)+s*errorMoment (k+1) (s-1)-errorMoment k (s-1) := by
  have hz : s-1≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [sub_re,one_re,zero_re] at this
    linarith
  have he : (fun w : ℂ => -logDeriv riemannZeta w)=ᶠ[𝓝 s]
      (fun w => (1+(w-1)⁻¹)+w*errorLaplace (w-1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).eventually_mem hs] with w hw
    rw [logDeriv_eq_errorLaplace hw]
    have hw0 : w-1≠0 := by
      intro h
      have := congrArg Complex.re h
      simp only [sub_re,one_re,zero_re] at this
      linarith
    field_simp
    ring
  have hg : AnalyticAt ℂ (fun w : ℂ => errorLaplace (w-1)) s :=
    (analytic_errorLaplace_and_moments (by simpa using sub_pos.mpr hs)).1.comp
      (analyticAt_id.sub analyticAt_const)
  have hp : AnalyticAt ℂ (fun w : ℂ => (w-1)⁻¹) s :=
    (analyticAt_id.sub analyticAt_const).inv hz
  rw [zetaPrimeLogMoment,signedTaylorMoment_congr (k+1) he,
    signedTaylorMoment_add (f := fun w : ℂ => 1+(w-1)⁻¹)
      (g := fun w : ℂ => w*errorLaplace (w-1)) _
      (analyticAt_const.add hp) (analyticAt_id.mul hg),
    signedTaylorMoment_add (f := fun _ : ℂ => 1) (g := fun w : ℂ => (w-1)⁻¹)
      _ analyticAt_const hp,signedTaylorMoment_inv_sub,
    moment_linear_mul hg,moment_error_translate hs,moment_error_translate hs]
  simp only [signedTaylorMoment,iteratedDeriv_const,Nat.add_eq_zero_iff,one_ne_zero,
    and_false,↓reduceIte,mul_zero,zero_add]
  rw [show k+1+1=k+2 by omega]
  ring

/-- The actual ordinary-prime source, with the proper-prime-power term
explicit. All phases, the moving source radius, and factorial orders are
unchanged. This is independent of exposure and of every Riesz carrier. -/
theorem ordinary_moment_eq_error (u y : ℝ) (k : ℕ) :
    moments u y (k+1)=(u : ℂ)^(k+2)*
      (((center y-1)⁻¹)^(k+2)+center y*errorMoment (k+1) (center y-1)-
        errorMoment k (center y-1)-zetaProperPrimePowerMoment (k+1) (center y)) := by
  have he := zetaPrimeLogMoment_eq_prime_add_proper (k+1)
    (by norm_num [ZetaPrimeMomentCoherence.center] : 1<(center y).re)
  have hm := vonMangoldt_moment_eq_error
    (by norm_num [ZetaPrimeMomentCoherence.center] : 1<(center y).re) k
  unfold moments
  rw [show k+1+1=k+2 by omega]
  congr 1
  linear_combination hm-he

/-- Order zero retains the boundary term `s/(s-1)` explicitly. -/
theorem ordinary_moment_zero_eq_error (u y : ℝ) :
    moments u y 0=(u : ℂ)*
      (center y/(center y-1)+center y*errorLaplace (center y-1)-
        zetaProperPrimePowerMoment 0 (center y)) := by
  have he := zetaPrimeLogMoment_eq_prime_add_proper 0
    (by norm_num [ZetaPrimeMomentCoherence.center] : 1<(center y).re)
  have hm := logDeriv_eq_errorLaplace
    (by norm_num [ZetaPrimeMomentCoherence.center] : 1<(center y).re)
  simp only [moments,pow_one,Nat.zero_add,zetaPrimeLogMoment,
    signedTaylorMoment,iteratedDeriv_zero,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,one_mul] at he ⊢
  linear_combination (u : ℂ)*(hm-he)

private theorem absolute_error_integrand (s : ℂ) (t : ℝ) :
    (logError t : ℂ)*Complex.exp (-(s-1)*t)=
      ((Chebyshev.psi (Real.exp t)-Real.exp t : ℝ) : ℂ)*Complex.exp (-s*t) := by
  have h1 : (Real.exp (-t) : ℂ)*Complex.exp (-(s-1)*t)=Complex.exp (-s*t) := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : (Real.exp t : ℂ)*Complex.exp (-s*t)=Complex.exp (-(s-1)*t) := by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    ring
  simp only [logError,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  calc
    _ = (Chebyshev.psi (Real.exp t) : ℂ)*
        ((Real.exp (-t) : ℂ)*Complex.exp (-(s-1)*t))-Complex.exp (-(s-1)*t) := by ring
    _ = _ := by rw [h1,←h2]; ring

/-- The error is literally `psi(exp(t))-exp(t)` against a centered
factorial test. No asymptotic prime-density replacement has been made. -/
theorem centered_error_eq_integral {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    s*errorMoment (k+1) (s-1)-errorMoment k (s-1)=
      ∫ t : ℝ in Ioi 0,
        ((Chebyshev.psi (Real.exp t)-Real.exp t : ℝ) : ℂ)*
        (s*(t : ℂ)^(k+1)/((k+1).factorial : ℂ)-(t : ℂ)^k/(k.factorial : ℂ))*
        Complex.exp (-s*t) := by
  have h := analytic_errorLaplace_and_moments (z := s-1)
    (by simpa using sub_pos.mpr hs)
  unfold errorMoment
  rw [←integral_const_mul,←integral_sub ((h.2 (k+1)).1.div_const _ |>.const_mul s)
    ((h.2 k).1.div_const _)]
  apply integral_congr_ae
  filter_upwards with t
  calc
    _ = ((logError t : ℂ)*Complex.exp (-(s-1)*t))*
        (s*(t : ℂ)^(k+1)/((k+1).factorial : ℂ)-(t : ℂ)^k/(k.factorial : ℂ)) := by ring
    _ = _ := by rw [absolute_error_integrand]; ring

/-- The exact literal-prime Mellin/Laplace error representation. -/
theorem ordinary_moment_eq_psi_error_integral (u y : ℝ) (k : ℕ) :
    moments u y (k+1)=(u : ℂ)^(k+2)*
      (((center y-1)⁻¹)^(k+2)+
        (∫ t : ℝ in Ioi 0,
          ((Chebyshev.psi (Real.exp t)-Real.exp t : ℝ) : ℂ)*
          (center y*(t : ℂ)^(k+1)/((k+1).factorial : ℂ)-
            (t : ℂ)^k/(k.factorial : ℂ))*Complex.exp (-center y*t))-
        zetaProperPrimePowerMoment (k+1) (center y)) := by
  rw [ordinary_moment_eq_error,←centered_error_eq_integral
    (by norm_num [ZetaPrimeMomentCoherence.center] : 1<(center y).re)]
  ring

/-- The centered signed error moment at the unchanged prime source scale. -/
def errorSource (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+2)*(center y*errorMoment (k+1) (center y-1)-errorMoment k (center y-1))

private theorem proper_error_tendsto {u : ℝ} (hu : 0≤u) (hu1 : u<1) (y : ℝ) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (center y))
      atTop (𝓝 0) := by
  have ht := tendsto_zetaProperPrimePowerFilter_mul_pow (1 : Polynomial ℂ) y
    (a := (u : ℂ)) (by simpa only [Complex.norm_real,Real.norm_of_nonneg hu] using hu1)
  have hs : (1 : Polynomial ℂ).support={0} := by
    ext k
    by_cases hk : k=0 <;> simp [Polynomial.mem_support_iff,Polynomial.coeff_one,hk]
  simpa only [zetaProperPrimePowerFilter,hs,Finset.sum_singleton,
    Polynomial.coeff_one_zero,one_mul,Nat.add_zero,ZetaPrimeMomentCoherence.center] using ht

/-- In the fixed nonzero-height regime, coherence is exactly the same
limit for the centered actual Chebyshev-error moment. Main density and
proper prime powers are paid independently; exposure is not assumed. -/
theorem errorSource_tendsto_iff {u y : ℝ} (hu : 0≤u) (hu1 : u<1) (hy : 1≤|y|)
    (l : ℂ) :
    Tendsto (errorSource u y) atTop (𝓝 l) ↔ Tendsto (moments u y) atTop (𝓝 l) := by
  have hgap : u<‖center y-1‖ := by
    have hh := Complex.abs_im_le_norm (center y-1)
    have hi : (center y-1).im=y := by norm_num [ZetaPrimeMomentCoherence.center]
    rw [hi] at hh
    linarith
  have hratio : ‖(u : ℂ)/(center y-1)‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hu]
    exact (div_lt_one (lt_of_le_of_lt hu hgap)).mpr hgap
  have hmain := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hratio).comp
    (tendsto_add_atTop_nat 2)
  have hpower := (proper_error_tendsto hu hu1 y).comp (tendsto_add_atTop_nat 1)
  have he (k : ℕ) : moments u y (k+1)=errorSource u y k+
      (((u : ℂ)/(center y-1))^(k+2)-
        (u : ℂ)^(k+2)*zetaProperPrimePowerMoment (k+1) (center y)) := by
    rw [ordinary_moment_eq_error,errorSource,div_pow,div_eq_mul_inv,inv_pow]
    ring
  have hpaid : Tendsto (fun k : ℕ => ((u : ℂ)/(center y-1))^(k+2)-
      (u : ℂ)^(k+2)*zetaProperPrimePowerMoment (k+1) (center y)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_sub,neg_zero,Nat.add_assoc] using hmain.sub hpower
  constructor
  · intro ht
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [add_zero] using (ht.add hpaid).congr (fun k => (he k).symm)
  · intro ht
    have hs := (tendsto_add_atTop_iff_nat 1).mpr ht
    simpa only [sub_zero] using (hs.sub hpaid).congr (fun k => by rw [he]; ring)

private theorem reciprocal_moment (s : ℂ) (n : ℕ) :
    signedTaylorMoment n (fun z : ℂ => z⁻¹) s=(s⁻¹)^(n+1) := by
  simpa only [sub_zero] using signedTaylorMoment_inv_sub n 0 s

private theorem complex_factorial_laplace {z : ℂ} (hz : 0<z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^n/(n.factorial : ℂ)*
      Complex.exp (-z*t)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t : ℂ)^n/(n.factorial : ℂ)*
      Complex.exp (-z*t))=(z⁻¹)^(n+1) := by
  have h := signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun _ => (1 : ℝ)) (b := 0) aemeasurable_const
    (fun x hx => by
      simpa only [one_mul,IntegrableOn] using integrableOn_exp_mul_Ioi (by linarith : -x<0) 0) hz
  simp only [Complex.ofReal_one,one_mul] at h
  have he : (fun w : ℂ => ∫ t : ℝ in Ioi 0, Complex.exp (-w*t))=ᶠ[𝓝 z]
      (fun w => w⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hz]
      with w hw
    simpa using integral_exp_mul_complex_Ioi
      (a := -w) (by simpa only [Complex.neg_re] using neg_neg_of_pos hw) 0
  have hv := (h.2 n).2
  rw [signedTaylorMoment_congr n he,reciprocal_moment] at hv
  constructor
  · apply ((h.2 n).1.div_const (n.factorial : ℂ)).congr
    filter_upwards with t
    ring
  · convert hv.symm using 1
    congr 1
    ext t
    ring

/-- The relative logarithmic Chebyshev component of a zero of
location `rho` and residue multiplicity `m`. This is a diagnostic model,
not an asserted asymptotic expansion of the actual Chebyshev error. -/
def persistentComponent (rho : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  -(m : ℂ)/rho*Complex.exp ((rho-1)*t)

/-- The full phased factorial integral of the diagnostic component. -/
def componentMoment (rho : ℂ) (m k : ℕ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    persistentComponent rho m t*(t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-1)*t)

/-- The exact factorial transform of the diagnostic component. -/
theorem componentMoment_eq {rho s : ℂ} (h : 0<(s-rho).re) (m k : ℕ) :
    componentMoment rho m k s=-(m : ℂ)/rho*((s-rho)⁻¹)^(k+1) := by
  have he : (fun t : ℝ => persistentComponent rho m t*(t : ℂ)^k/(k.factorial : ℂ)*
      Complex.exp (-(s-1)*t))=
      (fun t : ℝ => (-(m : ℂ)/rho)*
        ((t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-rho)*t))) := by
    funext t
    unfold persistentComponent
    have hx : Complex.exp ((rho-1)*t)*Complex.exp (-(s-1)*t)=
        Complex.exp (-(s-rho)*t) := by rw [←Complex.exp_add]; congr 1; ring
    calc
      _ = (-(m : ℂ)/rho)*((t : ℂ)^k/(k.factorial : ℂ))*
          (Complex.exp ((rho-1)*t)*Complex.exp (-(s-1)*t)) := by ring
      _ = _ := by rw [hx]; ring
  unfold componentMoment
  rw [he,integral_const_mul,(complex_factorial_laplace h k).2]

/-- A matched Chebyshev component yields the entire coherent source,
exactly at every positive factorial order. No Riesz rearrangement is used. -/
theorem component_exact_source {u y : ℝ} (hu : 0<u)
    (hrho : candidate u y≠0) (m k : ℕ) :
    (u : ℂ)^(k+2)*
      (center y*componentMoment (candidate u y) m (k+1) (center y)-
        componentMoment (candidate u y) m k (center y))=-(m : ℂ) := by
  have hc : center y-candidate u y=(u : ℂ) := by unfold candidate; ring
  have hh : 0<(center y-candidate u y).re := by rw [hc]; exact hu
  rw [componentMoment_eq hh,componentMoment_eq hh,hc]
  have hu0 : (u : ℂ)≠0 := by exact_mod_cast hu.ne'
  have he : center y=(candidate u y)+(u : ℂ) := by unfold candidate; ring
  rw [he]
  simp only [inv_pow,pow_succ]
  field_simp
  ring

end RiemannGaussian.ZetaPrimeMomentChebyshev
