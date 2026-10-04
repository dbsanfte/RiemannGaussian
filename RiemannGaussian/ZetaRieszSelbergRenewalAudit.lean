/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhaseRadius
import Mathlib.Analysis.Convolution

/-!
# A strict test of a generic Selberg renewal floor

This is a continuous positive model, NOT the ordinary-prime measure. Its
complete logarithmic-derivative and Selberg symbols are rational, and its
factorial moments retain one common phase at every order. It tests the
proposed signed inequality before introducing an arithmetic representation.
The extra real pole/number-count normalization is stated explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Real Complex Filter Topology MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSelbergRenewalAudit
open ZetaRieszSelbergSourceAudit ZetaRieszSelectedGamma

/-- Positive continuous prime-density numerator; no literal primes are
assigned to this model. Its second positive channel is intentional. -/
def numerator (u y t : ℝ) : ℝ :=
  Real.exp t+Real.exp ((2-2*u)*t)-2*Real.exp ((3/2-u)*t)*Real.cos (y*t)

/-- Exact square decomposition, valid before any phase averaging. -/
theorem numerator_eq_squares (u y t : ℝ) :
    numerator u y t=(Real.exp (t/2)-Real.exp ((1-u)*t))^2+
      2*Real.exp ((3/2-u)*t)*(1-Real.cos (y*t)) := by
  have h1 : (Real.exp (t/2))^2=Real.exp t := by
    rw [pow_two,←Real.exp_add]; congr 1; ring
  have h2 : (Real.exp ((1-u)*t))^2=Real.exp ((2-2*u)*t) := by
    rw [pow_two,←Real.exp_add]; congr 1; ring
  have h3 : Real.exp (t/2)*Real.exp ((1-u)*t)=Real.exp ((3/2-u)*t) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [sub_sq,h1,h2]
  dsimp only [numerator]
  nlinarith only [h3]

/-- The model is positive on the whole logarithmic half-line, not just
past a threshold. Positivity alone does not certify ordinary primes. -/
theorem numerator_nonneg (u y t : ℝ) : 0≤numerator u y t := by
  rw [numerator_eq_squares]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
    (sub_nonneg.mpr (Real.cos_le_one _)))

/-- The selected point is a zero of the model rational function only. -/
def testZero (u y : ℝ) : ℂ := (3/2-u)+Complex.I*y

/-- The second REAL pole. Ordinary zeta has no such pole. -/
def extraPole (u : ℝ) : ℂ := (2-2*u : ℝ)

/-- A finite rational logarithmic derivative with two positive pole
channels and a conjugate pair of negative zero channels. -/
def logSymbol (u y : ℝ) (s : ℂ) : ℂ :=
  (s-1)⁻¹+(s-extraPole u)⁻¹-(s-testZero u y)⁻¹-
    (s-star (testZero u y))⁻¹

/-- Its exact rational count transform; not the ordinary integer series. -/
def countSymbol (u y : ℝ) (s : ℂ) : ℂ :=
  ((s-testZero u y)*(s-star (testZero u y)))/((s-1)*(s-extraPole u))

private theorem logDeriv_linear (s a : ℂ) : logDeriv (fun z : ℂ => z-a) s=(s-a)⁻¹ := by
  simp [logDeriv_apply]

/-- The model is an exact logarithmic derivative, rather than a freely
chosen array that only happens to pass one asymptotic trace test. -/
theorem neg_logDeriv_countSymbol {u y : ℝ} {s : ℂ}
    (h1 : s-1≠0) (h2 : s-extraPole u≠0)
    (h3 : s-testZero u y≠0) (h4 : s-star (testZero u y)≠0) :
    -logDeriv (countSymbol u y) s=logSymbol u y s := by
  unfold countSymbol
  rw [logDeriv_div (f := fun z : ℂ => (z-testZero u y)*(z-star (testZero u y)))
    (g := fun z : ℂ => (z-1)*(z-extraPole u)) s
    (mul_ne_zero h3 h4) (mul_ne_zero h1 h2)
    (by fun_prop) (by fun_prop),
    logDeriv_mul (f := fun z : ℂ => z-testZero u y)
      (g := fun z : ℂ => z-star (testZero u y)) s h3 h4 (by fun_prop) (by fun_prop),
    logDeriv_mul (f := fun z : ℂ => z-1)
      (g := fun z : ℂ => z-extraPole u) s h1 h2 (by fun_prop) (by fun_prop)]
  simp only [logDeriv_linear,logSymbol]
  ring

/-- The full second logarithmic convolution is the same Riccati symbol
as in the classical Selberg identity. No truncated pair surrogate is used. -/
def selbergSymbol (u y : ℝ) (s : ℂ) : ℂ :=
  logSymbol u y s^2-deriv (logSymbol u y) s

private theorem deriv_logSymbol {u y : ℝ} {s : ℂ}
    (h1 : s-1≠0) (h2 : s-extraPole u≠0)
    (h3 : s-testZero u y≠0) (h4 : s-star (testZero u y)≠0) :
    deriv (logSymbol u y) s=
      -(s-1)⁻¹^2-(s-extraPole u)⁻¹^2+
        (s-testZero u y)⁻¹^2+(s-star (testZero u y))⁻¹^2 := by
  have hh a (ha : s-a≠0) :
      HasDerivAt (fun z : ℂ => (z-a)⁻¹) (-(s-a)⁻¹^2) s := by
    simpa only [id_eq,neg_div,one_div,inv_pow] using
      ((hasDerivAt_id s).sub_const a).fun_inv ha
  have hd := (((hh 1 h1).add (hh (extraPole u) h2)).sub
    (hh (testZero u y) h3)).sub (hh (star (testZero u y)) h4)
  convert hd.deriv using 1
  · rfl
  · ring

/-- Full Selberg cancels the selected DOUBLE pole exactly. It leaves
a simple pole determined by the regular part, and does not bound the
partial central/successor functional in the requested floor. -/
theorem selberg_selected_double_pole_cancels {u y : ℝ} {s : ℂ}
    (h1 : s-1≠0) (h2 : s-extraPole u≠0)
    (h3 : s-testZero u y≠0) (h4 : s-star (testZero u y)≠0) :
    selbergSymbol u y s=
      -2*((s-1)⁻¹+(s-extraPole u)⁻¹-(s-star (testZero u y))⁻¹)*
        (s-testZero u y)⁻¹+
      ((s-1)⁻¹+(s-extraPole u)⁻¹-(s-star (testZero u y))⁻¹)^2+
      (s-1)⁻¹^2+(s-extraPole u)⁻¹^2-(s-star (testZero u y))⁻¹^2 := by
  rw [selbergSymbol,deriv_logSymbol h1 h2 h3 h4,logSymbol]
  ring

/-- The actual positive time-domain second-convolution kernel in this
continuous test. It keeps the two terms joined before inspection. -/
def selbergKernel (u y t : ℝ) : ℝ :=
  t*numerator u y t+∫ v : ℝ in Icc 0 t,numerator u y v*numerator u y (t-v)

/-- Both the density and its FULL Selberg convolution have positive
time kernels. This statement has no ordinary-integer interpretation. -/
theorem selbergKernel_nonneg (u y : ℝ) {t : ℝ} (ht : 0≤t) :
    0 ≤ selbergKernel u y t := by
  exact add_nonneg (mul_nonneg ht (numerator_nonneg _ _ _))
    (integral_nonneg (fun _ => mul_nonneg (numerator_nonneg _ _ _)
      (numerator_nonneg _ _ _)))

/-- Exact all-order factorial array for the one common phase of the
positive model. The unshifted pole, real pole and opposite-height zero
are retained, rather than removed as low-order errors. -/
def array (u y : ℝ) (k : ℕ) : ℂ :=
  ((u : ℂ)/(1/2+Complex.I*y))^(k+1)+
    ((u : ℂ)/(2*u-1/2+Complex.I*y))^(k+1)-1-
      ((u : ℂ)/(u+2*Complex.I*y))^(k+1)

/-- Pointwise Laplace identity with the SAME phase for all four
channels, rather than a separately prescribed sequence of moments. -/
theorem numerator_laplace_expansion (u y : ℝ) (s : ℂ) (t : ℝ) :
    Complex.exp (-s*t)*(numerator u y t : ℂ)=
      Complex.exp (-(s-1)*t)+Complex.exp (-(s-extraPole u)*t)-
        Complex.exp (-(s-testZero u y)*t)-
          Complex.exp (-(s-star (testZero u y))*t) := by
  have hc : 2*(Real.cos (y*t) : ℂ)=
      Complex.exp (Complex.I*y*t)+Complex.exp (-Complex.I*y*t) := by
    rw [Complex.ofReal_cos,Complex.cos]
    push_cast
    rw [show ((y : ℂ)*t)*Complex.I=Complex.I*y*t by ring,
      show -((y : ℂ)*t)*Complex.I=-Complex.I*y*t by ring]
    ring
  have hstar : star (testZero u y)=(3/2-(u : ℂ))-Complex.I*y := by
    simp [testZero]
    ring
  have he1 : Complex.exp (-s*t)*Complex.exp (t : ℂ)=
      Complex.exp (-(s-1)*t) := by
    rw [←Complex.exp_add]; congr 1; ring
  have he2 : Complex.exp (-s*t)*Complex.exp (((2-2*u)*t : ℝ) : ℂ)=
      Complex.exp (-(s-extraPole u)*t) := by
    rw [←Complex.exp_add]; congr 1; unfold extraPole; push_cast; ring
  have he3 : Complex.exp (-s*t)*Complex.exp (((3/2-u)*t : ℝ) : ℂ)*
      Complex.exp (Complex.I*y*t)=Complex.exp (-(s-testZero u y)*t) := by
    rw [←Complex.exp_add,←Complex.exp_add]; congr 1; unfold testZero; push_cast; ring
  have he4 : Complex.exp (-s*t)*Complex.exp (((3/2-u)*t : ℝ) : ℂ)*
      Complex.exp (-Complex.I*y*t)=Complex.exp (-(s-star (testZero u y))*t) := by
    rw [hstar,←Complex.exp_add,←Complex.exp_add]; congr 1; push_cast; ring
  unfold numerator
  push_cast
  calc
    _ = Complex.exp (-s*t)*Complex.exp (t : ℂ)+
        Complex.exp (-s*t)*Complex.exp (((2-2*u)*t : ℝ) : ℂ)-
        Complex.exp (-s*t)*Complex.exp (((3/2-u)*t : ℝ) : ℂ)*
          (2*(Real.cos (y*t) : ℂ)) := by push_cast; ring
    _ = _ := by rw [hc,mul_add,he1,he2,he3,he4]; ring

/-- Complete common-phase factorial moment of the positive numerator.
There is no arbitrary low-order modification. -/
def phaseMoment (u y : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  ∫ t : ℝ in Ioi 0,(t : ℂ)^k/(k.factorial : ℂ)*
    Complex.exp (-s*t)*(numerator u y t : ℂ)

/-- Genuine integrability and exact factorial moments of all four
channels, including logged order zero. -/
theorem phaseMoment_eq {u y : ℝ} {s : ℂ}
    (h1 : 0<(s-1).re) (h2 : 0<(s-extraPole u).re)
    (h3 : 0<(s-testZero u y).re) (h4 : 0<(s-star (testZero u y)).re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^k/(k.factorial : ℂ)*
      Complex.exp (-s*t)*(numerator u y t : ℂ)) (Ioi 0) ∧
    phaseMoment u y s k=(s-1)⁻¹^(k+1)+(s-extraPole u)⁻¹^(k+1)-
      (s-testZero u y)⁻¹^(k+1)-(s-star (testZero u y))⁻¹^(k+1) := by
  have hf (t : ℝ) :
      (t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-s*t)*(numerator u y t : ℂ)=
        (t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-1)*t)+
        (t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-extraPole u)*t)-
        (t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-testZero u y)*t)-
        (t : ℂ)^k/(k.factorial : ℂ)*Complex.exp (-(s-star (testZero u y))*t) := by
    rw [mul_assoc,numerator_laplace_expansion]; ring
  have hi1 := (complex_factorial_laplace h1 k).1
  have hi2 := (complex_factorial_laplace h2 k).1
  have hi3 := (complex_factorial_laplace h3 k).1
  have hi4 := (complex_factorial_laplace h4 k).1
  constructor
  · exact (((hi1.add hi2).sub hi3).sub hi4).congr (by
      filter_upwards with t; exact (hf t).symm)
  · unfold phaseMoment
    simp_rw [hf]
    have he4 := integral_sub ((hi1.add hi2).sub hi3) hi4
    simp only [Pi.sub_apply,Pi.add_apply] at he4
    have he3 := integral_sub (hi1.add hi2) hi3
    simp only [Pi.add_apply] at he3
    rw [he4,he3,integral_add hi1 hi2,
      (complex_factorial_laplace h1 k).2,(complex_factorial_laplace h2 k).2,
      (complex_factorial_laplace h3 k).2,(complex_factorial_laplace h4 k).2]

/-- The countertest array comes from the positive numerator and a
single evaluation height; it is not four freely adjusted marginals. -/
theorem array_eq_phaseMoment {u : ℝ} (hu : 1/2≤u) (y : ℝ) (k : ℕ) :
    array u y k=(u : ℂ)^(k+1)*phaseMoment u y (3/2+Complex.I*y) k := by
  have hs1 : (3/2+Complex.I*y : ℂ)-1=1/2+Complex.I*y := by ring
  have hs2 : (3/2+Complex.I*y : ℂ)-extraPole u=2*u-1/2+Complex.I*y := by
    unfold extraPole; push_cast; ring
  have hs3 : (3/2+Complex.I*y : ℂ)-testZero u y=(u : ℂ) := by
    unfold testZero; ring
  have hs4 : (3/2+Complex.I*y : ℂ)-star (testZero u y)=u+2*Complex.I*y := by
    simp [testZero]
    ring
  rw [(phaseMoment_eq (s := 3/2+Complex.I*y)
    (by rw [hs1]; norm_num) (by rw [hs2]; norm_num; linarith only [hu])
    (by rw [hs3]; norm_num; linarith only [hu])
    (by rw [hs4]; norm_num; linarith only [hu]) k).2,hs1,hs2,hs3,hs4]
  unfold array
  simp only [div_eq_mul_inv,mul_pow]
  have hcancel : (u : ℂ)^(k+1)*((u : ℂ)⁻¹)^(k+1)=1 := by
    rw [←mul_pow,mul_inv_cancel₀ (by exact_mod_cast (by linarith only [hu] : u≠0)),one_pow]
  rw [mul_sub,mul_sub,mul_add,hcancel]

/-- Exact Laplace identification of the FULL second-convolution kernel.
This is an equality for the continuous test, not a transported prime
density estimate. Integrability is proved before the convolution swap. -/
theorem selbergKernel_laplace {u y : ℝ} {s : ℂ}
    (h1 : 0<(s-1).re) (h2 : 0<(s-extraPole u).re)
    (h3 : 0<(s-testZero u y).re) (h4 : 0<(s-star (testZero u y)).re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*t)*(selbergKernel u y t : ℂ)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0,Complex.exp (-s*t)*(selbergKernel u y t : ℂ))=
      selbergSymbol u y s := by
  let f : ℝ→ℂ := fun t => Complex.exp (-s*t)*(numerator u y t : ℂ)
  have hi : IntegrableOn f (Ioi 0) := by
    simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_self (one_ne_zero : (1 : ℂ)≠0),
      one_mul,f] using (phaseMoment_eq h1 h2 h3 h4 0).1
  have hf : (∫ t : ℝ in Ioi 0,f t)=logSymbol u y s := by
    simpa only [phaseMoment,pow_zero,Nat.factorial_zero,Nat.cast_one,
      div_self (one_ne_zero : (1 : ℂ)≠0),one_mul,Nat.zero_add,pow_one,f,logSymbol]
      using (phaseMoment_eq h1 h2 h3 h4 0).2
  have hc (t : ℝ) (ht : 0<t) :
      posConvolution f f (ContinuousLinearMap.mul ℝ ℂ) volume t=
        Complex.exp (-s*t)*
          ((∫ v : ℝ in Icc 0 t,numerator u y v*numerator u y (t-v) : ℝ) : ℂ) := by
    rw [posConvolution,indicator_of_mem (mem_Ioi.mpr ht),
      intervalIntegral.integral_of_le ht.le,←integral_Icc_eq_integral_Ioc]
    rw [←integral_complex_ofReal (μ := volume.restrict (Icc 0 t)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [ContinuousLinearMap.mul_apply',f,Complex.ofReal_mul,Complex.ofReal_sub]
    have he : Complex.exp (-s*v)*Complex.exp (-s*(t-v))=Complex.exp (-s*t) := by
      rw [←Complex.exp_add]; congr 1; ring
    calc
      _ = (Complex.exp (-s*v)*Complex.exp (-s*(t-v)))*
          (numerator u y v : ℂ)*(numerator u y (t-v) : ℂ) := by ring
      _ = _ := by rw [he]; ring
  have hci := (integrable_posConvolution hi hi (ContinuousLinearMap.mul ℝ ℂ)).integrableOn
    (s := Ioi (0 : ℝ))
  have hcv := integral_posConvolution hi hi (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply',hf] at hcv
  have hce : (∫ t : ℝ in Ioi 0,posConvolution f f (ContinuousLinearMap.mul ℝ ℂ) volume t)=
      (logSymbol u y s)^2 := by
    calc
      _ = ∫ t : ℝ in Ioi 0,∫ v : ℝ in 0..t,f v*f (t-v) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp only [posConvolution,indicator_of_mem ht,ContinuousLinearMap.mul_apply']
      _ = _ := by simpa only [pow_two] using hcv
  have ht := (phaseMoment_eq h1 h2 h3 h4 1).1
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at ht
  have he (t : ℝ) (ht : t∈Ioi (0 : ℝ)) :
      Complex.exp (-s*t)*(selbergKernel u y t : ℂ)=
        (t : ℂ)*Complex.exp (-s*t)*(numerator u y t : ℂ)+
          posConvolution f f (ContinuousLinearMap.mul ℝ ℂ) volume t := by
    rw [hc t ht]
    simp only [selbergKernel,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  have hsum : IntegrableOn (fun t : ℝ =>
      (t : ℂ)*Complex.exp (-s*t)*(numerator u y t : ℂ)+
        posConvolution f f (ContinuousLinearMap.mul ℝ ℂ) volume t) (Ioi 0) := ht.add hci
  constructor
  · apply hsum.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (he t ht).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi he,integral_add ht hci,hce]
    have hmoment := (phaseMoment_eq h1 h2 h3 h4 1).2
    simp only [phaseMoment,pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hmoment
    rw [hmoment,selbergSymbol,deriv_logSymbol
      (by intro h; rw [h] at h1; simp at h1)
      (by intro h; rw [h] at h2; simp at h2)
      (by intro h; rw [h] at h3; simp at h3)
      (by intro h; rw [h] at h4; simp at h4)]
    ring

private theorem power_tendsto {u : ℝ} (hu : 0≤u) {z : ℂ} (hgap : u<‖z‖) :
    Tendsto (fun k : ℕ => ((u : ℂ)/z)^(k+1)) atTop (𝓝 0) := by
  have hn : ‖(u : ℂ)/z‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hu]
    exact (div_lt_one (lt_of_le_of_lt hu hgap)).mpr hgap
  simpa only [Function.comp_def] using
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).comp (tendsto_add_atTop_nat 1)

/-- The finite rational model retains the unit negative source, even
while its exact full Selberg convolution has no selected double pole. -/
theorem array_tendsto {u y : ℝ} (hu : 0<u) (hu1 : u<1) (hy : 54≤|y|) :
    Tendsto (array u y) atTop (𝓝 (-1)) := by
  have h1 : u<‖(1/2+Complex.I*y : ℂ)‖ := by
    have hh := Complex.abs_im_le_norm (1/2+Complex.I*(y : ℂ))
    norm_num at hh
    linarith only [hy,hu1,hh]
  have h2 : u<‖(2*u-1/2+Complex.I*y : ℂ)‖ := by
    have hh := Complex.abs_im_le_norm (2*(u : ℂ)-1/2+Complex.I*(y : ℂ))
    norm_num at hh
    linarith only [hy,hu1,hh]
  have h3 : u<‖(u+2*Complex.I*y : ℂ)‖ := by
    have hh := Complex.abs_im_le_norm ((u : ℂ)+2*Complex.I*(y : ℂ))
    norm_num [abs_mul] at hh
    linarith only [hy,hu1,hh]
  unfold array
  simpa only [zero_add,zero_sub,sub_zero] using
    ((((power_tendsto hu.le h1).add (power_tendsto hu.le h2)).sub
      (tendsto_const_nhds (x := (1 : ℂ)))).sub (power_tendsto hu.le h3))

/-- The continuous Selberg test also has vanishing normalized trace
error, with all low logged orders retained. -/
theorem full_trace_tendsto {u y : ℝ} (hu : 0<u) (hu1 : u<1) (hy : 54≤|y|) :
    Tendsto (ZetaRieszSignedSelbergPayment.traceError (array u y)) atTop (𝓝 0) :=
  traceError_tendsto _ (array_tendsto hu hu1 hy)

/-- The unchanged full central/successor/logged/trace functional fails
the proposed floor in this positive rational test. This is not a
counterexample to an ordinary-prime or literal carrier theorem. -/
theorem eventually_joined_gt_target {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∀ᶠ N : ℕ in atTop,(399/5000 : ℝ)<(harmonicEvaluation (array u y) u N).re := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (harmonicEvaluation_tendsto _ (array_tendsto (by linarith only [hu])
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]) hy)
      (by linarith only [hu]) (by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]))
  simp only [Complex.ofReal_re] at ht
  exact ht.eventually_const_lt (by
    linarith only [ZetaRieszEndgameSlack.retainedCost_upper hu hU])

/-- A vanishing error on a cofinal subsequence does not fix this
generic Selberg argument. Actual ordinary-integer arithmetic is still
required; the test does not supply a new unpaid carrier hypothesis. -/
theorem cofinal_generic_floor_impossible {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (err : ℕ→ℝ) (he : Tendsto err atTop (𝓝 0))
    (hb : ∃ᶠ N : ℕ in atTop,(harmonicEvaluation (array u y) u N).re≤399/5000+err N) : False := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (harmonicEvaluation_tendsto _ (array_tendsto (by linarith only [hu])
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]) hy)
      (by linarith only [hu]) (by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]))
  simp only [Complex.ofReal_re] at ht
  have hs : 1-ZetaRieszMaskSupport.retainedCost u-0≤(399/5000 : ℝ) :=
    le_of_tendsto_of_frequently (ht.sub he) (hb.mono fun N hN => by
      dsimp only [Function.comp_def]
      linarith only [hN])
  linarith only [hs,ZetaRieszEndgameSlack.retainedCost_upper hu hU]

/-- Exact distinction from the ordinary-integer count transform.
Its extra real pole and residue cannot silently be normalized away. -/
theorem countSymbol_eq_one_add {u y : ℝ} {s : ℂ}
    (h1 : s-1≠0) (h2 : s-extraPole u≠0) :
    countSymbol u y s=1+((y : ℂ)^2+((u : ℂ)-1/2)^2)/((s-1)*(s-extraPole u)) := by
  have hc : star (testZero u y)=(3/2-(u : ℂ))-Complex.I*y := by
    simp [testZero]
    ring
  unfold countSymbol
  rw [hc]
  unfold testZero
  field_simp [h1,h2]
  unfold extraPole
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- The model number-count residue is dramatically different from one
at the present radius/height. This is why it is not literal arithmetic. -/
theorem count_normalization_mismatch {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    (29160000 : ℝ)≤(y^2+(u-1/2)^2)/(2*u-1) := by
  have hp : 0<2*u-1 := by linarith only [hu]
  have hU' : 2*u-1≤(1/10000 : ℝ) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  have hs : (2916 : ℝ)≤y^2 := by nlinarith only [hy,sq_abs y]
  apply (le_div_iff₀ hp).mpr
  nlinarith only [hU',hs,sq_nonneg (u-1/2)]

end RiemannGaussian.ZetaRieszSelbergRenewalAudit
