/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingOrderCancellation
import RiemannGaussian.ZetaRieszPairFloorAllMultiplicity

/-!
# A gate for a generic positivity/common-phase ceiling

This is a continuous density, NOT the ordinary-prime measure. Its leading
prime-density normalization is one, it has one common phase at every
factorial order, and its logged moments converge to -2. Evaluating the
EXISTING joined Selberg/pair expression gives a value above 42/25.

Thus positivity, smooth-density normalization and adjacent-order coupling
do not suffice for the arithmetic ceiling. This does not refute that
ceiling for actual primes, pay any carrier error, or supply a zero exclusion.
All logged orders, including zero, are retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Real Filter Topology MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingDensityAudit
open ZetaRieszPositiveDensityAudit ZetaRieszSelbergSourceAudit
open ZetaRieszSignedSelbergPayment ZetaRieszPairFloorAllMultiplicity

/-- Positive past a fixed threshold, with the usual leading density.
The factor four gives the selected logged source -2. -/
def doubleDensity (u y t : ℝ) : ℝ :=
  (exp t-4*exp ((3/2-u)*t)*cos (y*t))/t

/-- No additional real exponential channel was added to achieve positivity. -/
theorem doubleDensity_pos {u y t : ℝ} (ht : 0<t) (hgap : 2≤(u-1/2)*t) :
    0<doubleDensity u y t := by
  have h1 : (2 : ℝ)<exp 1 := by
    have h := add_one_lt_exp (by norm_num : (1 : ℝ)≠0)
    norm_num at h
    exact h
  have h2 : (4 : ℝ)<exp 2 := by
    rw [show (2 : ℝ)=1+1 by norm_num,exp_add]
    nlinarith only [h1]
  have hg := h2.trans_le (exp_le_exp.mpr hgap)
  have hs : exp t=exp ((3/2-u)*t)*exp ((u-1/2)*t) := by
    rw [←exp_add]; congr 1; ring
  have hc := cos_le_one (y*t)
  have hp := exp_pos ((3/2-u)*t)
  unfold doubleDensity
  apply div_pos _ ht
  rw [hs]
  nlinarith only [hg,hc,hp]

/-- At the current radius ceiling this is positive at every height on
the entire half-line starting at 40000. It is not a prime-count theorem. -/
theorem doubleDensity_ceiling_pos (y : ℝ) {t : ℝ} (ht : 40000≤t) :
    0<doubleDensity (10001/20000) y t := by
  apply doubleDensity_pos (by linarith only [ht])
  norm_num
  linarith only [ht]

/-- Exact density normalization, with the small oscillatory term retained. -/
theorem doubleDensity_relative_eq (u y : ℝ) {t : ℝ} (ht : t≠0) :
    t*doubleDensity u y t/exp t-1=
      -4*exp (-(u-1/2)*t)*cos (y*t) := by
  have hs : exp ((3/2-u)*t)=exp t*exp (-(u-1/2)*t) := by
    rw [←exp_add]; congr 1; ring
  unfold doubleDensity
  rw [hs]
  field_simp [ht,(exp_pos t).ne']
  ring

/-- A correct leading density and a power-sized relative ripple still
permit the double source in this continuous model. -/
theorem doubleDensity_relative_abs_le (u y : ℝ) {t : ℝ} (ht : t≠0) :
    |t*doubleDensity u y t/exp t-1|≤4*exp (-(u-1/2)*t) := by
  rw [doubleDensity_relative_eq u y ht,abs_mul,abs_mul]
  norm_num only [abs_neg,abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one (y*t))

private theorem density_split (u y t : ℝ) :
    doubleDensity u y t=2*density u y t-exp t/t := by
  unfold doubleDensity density
  ring

/-- Exact physical common-phase moment, retaining the finite lower log
threshold and every logged order. No source limit defines this array. -/
def doubleMoment (u y B : ℝ) (k : ℕ) : ℂ :=
  ∫ t : ℝ in Ioi B,(u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
    Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(doubleDensity u y t : ℂ)

private theorem moment_split_integrand (u y : ℝ) (k : ℕ) {t : ℝ} (ht : 0<t) :
    (u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(doubleDensity u y t : ℂ)=
    2*((u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ))-
      (u : ℂ)^(k+1)*integrand (1/2+Complex.I*y) k t := by
  have he : Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*Complex.exp (t : ℂ)=
      Complex.exp (-(1/2+Complex.I*y)*(t : ℂ)) := by
    rw [←Complex.exp_add]; congr 1; ring
  have ht0 : (t : ℂ)≠0 := by exact_mod_cast ht.ne'
  have hf : (u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(Complex.exp (t : ℂ)/(t : ℂ))=
        (u : ℂ)^(k+1)*integrand (1/2+Complex.I*y) k t := by
    calc
      _ = (u : ℂ)^(k+1)*(t : ℂ)^k/(k.factorial : ℂ)*
          (Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*Complex.exp (t : ℂ)) := by
        rw [pow_succ]
        field_simp [ht0]
        ring
      _ = _ := by rw [he]; unfold integrand; ring
  rw [density_split]
  push_cast
  calc
    _ = 2*((u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
        Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*(density u y t : ℂ))-
        (u : ℂ)^(k+1)*(t : ℂ)^(k+1)/(k.factorial : ℂ)*
        Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))*
          (Complex.exp (t : ℂ)/(t : ℂ)) := by ring
    _ = _ := by rw [hf]

/-- Exact integral identity; the lower-threshold unshifted channel is
retained rather than discarded before forming the joined expression. -/
theorem doubleMoment_eq (u y B : ℝ) (hu : 0<u) (hB : 0≤B) (k : ℕ) :
    doubleMoment u y B k=2*densityMoment u y B k-
      tailLeg u (1/2+Complex.I*y) B k := by
  have hi := densityMoment_integrable hu hB y k
  have hj := (integrand_integrable (z:=1/2+Complex.I*y) (by norm_num) hB k).const_mul
    ((u : ℂ)^(k+1))
  unfold doubleMoment
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => moment_split_integrand u y k (lt_of_le_of_lt hB ht))]
  rw [integral_sub (hi.const_mul (2 : ℂ)) hj,integral_const_mul,integral_const_mul]
  rfl

/-- The one common-phase positive density gives logged source -2.
This is a countertest of a generic method, not an actual-zeta hypothesis. -/
theorem doubleMoment_tendsto {u y B : ℝ} (hu : 0<u) (hu1 : u<1)
    (hB : 0≤B) (hy : 1≤|y|) :
    Tendsto (doubleMoment u y B) atTop (𝓝 (-2)) := by
  have hp : |y|≤‖(1/2 : ℂ)+Complex.I*y‖ := by
    simpa using Complex.abs_im_le_norm ((1/2 : ℂ)+Complex.I*y)
  have hj := tailLeg_tendsto_zero hu.le hB (z:=1/2+Complex.I*y)
    (by norm_num) (lt_of_lt_of_le hu1 (hy.trans hp))
  have hi := (densityMoment_tendsto hu hu1 hB hy).const_mul (2 : ℂ)
  norm_num only at hi
  simpa only [sub_zero] using
    (hi.sub hj).congr (fun k => (doubleMoment_eq u y B hu hB k).symm)

/-- The CURRENT joined Selberg/pair upper expression, expressed using
its existing trace and harmonic API. This equality changes no weights. -/
theorem current_join_eq (a : ℕ→ℂ) (u : ℝ) {N : ℕ} (hN : 0<N) :
    -traceError a (N-1)-harmonicEvaluation a u N=
      a N-(∑ k∈ZetaRieszPairPrefixConvolution.centralOrders (N+1) (13*N/32),
        a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
      ((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)*
        (∑ k∈Finset.Icc 1 (N+1-13*N/32),
          a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)) := by
  have hn : N-1+1=N := by omega
  unfold traceError harmonicEvaluation
  rw [hn]
  ring

/-- A generic array with limit -2 has a joined source exceeding the
ceiling, even though its adjacent-order differences tend to zero. -/
theorem joined_double_tendsto (a : ℕ→ℂ) (ha : Tendsto a atTop (𝓝 (-2)))
    {u : ℝ} (hu : 0<u) (hU : u≤3/5) :
    Tendsto (fun N => -traceError a (N-1)-harmonicEvaluation a u N) atTop
      (𝓝 ((-2+4*ZetaRieszMaskSupport.retainedCost u : ℝ) : ℂ)) := by
  let b : ℕ→ℂ := fun k => a k/2
  have hb : Tendsto b atTop (𝓝 (-1)) := by
    simpa only [b,show (-2 : ℂ)/2=-1 by norm_num] using ha.div_const (2 : ℂ)
  have he (k : ℕ) : a k=2*b k := by dsimp [b]; ring
  have ht : Tendsto (traceError a) atTop (𝓝 (-2)) := by
    have hh := (traceError_tendsto b hb).const_mul (4 : ℂ) |>.add
      ((hb.comp (tendsto_add_atTop_nat 1)).const_mul (2 : ℂ))
    norm_num only at hh
    apply hh.congr
    intro N
    simp only [Function.comp_def]
    unfold traceError
    simp_rw [he]
    have hm k : (2*b k)*(2*b (N-k))=4*(b k*b (N-k)) := by ring
    simp_rw [hm]
    rw [←Finset.mul_sum]
    ring
  have hh : Tendsto (harmonicEvaluation a u) atTop
      (𝓝 (4*((1-ZetaRieszMaskSupport.retainedCost u : ℝ) : ℂ))) := by
    have hh := (harmonicEvaluation_tendsto b hb hu hU).const_mul (4 : ℂ)
    exact hh.congr (fun N => by
      simpa only [show (2 : ℂ)^2=4 by norm_num,←he] using
        (harmonicEvaluation_mul b 2 u N).symm)
  convert ((ht.comp (tendsto_sub_atTop_nat 1)).neg.sub hh) using 1
  · rfl
  · push_cast
    ring

/-- A strict reverse inequality for the continuous countertest. It is
NOT a reverse inequality for the literal arithmetic carrier. -/
theorem eventually_double_join_gt_ceiling {y : ℝ} (hy : 1≤|y|) :
    ∀ᶠ N in atTop,(42/25 : ℝ)<
      (-traceError (doubleMoment (10001/20000) y 40000) (N-1)-
        harmonicEvaluation (doubleMoment (10001/20000) y 40000) (10001/20000) N).re := by
  have ht := joined_double_tendsto _
    (doubleMoment_tendsto (u:=10001/20000) (B:=40000)
      (by norm_num) (by norm_num) (by norm_num) hy)
      (u:=10001/20000) (by norm_num) (by norm_num)
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u:=10001/20000) (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp only [Complex.ofReal_re] at hr
  exact hr.eventually_const_lt (by linarith only [hc])

/-- Even a cofinal subsequence and a vanishing two-sided tolerance do
not rescue the generic ceiling for this model. No literal prime packet
is identified with the model by this theorem. -/
theorem double_cofinal_ceiling_impossible {y : ℝ} (hy : 1≤|y|)
    (orders : ℕ→ℕ) (horders : Tendsto orders atTop atTop)
    (err : ℕ→ℝ) (he : Tendsto err atTop (𝓝 0))
    (hceiling : ∃ᶠ j in atTop,
      (-traceError (doubleMoment (10001/20000) y 40000) (orders j-1)-
        harmonicEvaluation (doubleMoment (10001/20000) y 40000)
          (10001/20000) (orders j)).re≤42/25+err j) : False := by
  have ht := joined_double_tendsto _
    (doubleMoment_tendsto (u:=10001/20000) (B:=40000)
      (by norm_num) (by norm_num) (by norm_num) hy)
      (u:=10001/20000) (by norm_num) (by norm_num)
  have hr := (Complex.continuous_re.continuousAt.tendsto.comp ht).comp horders
  simp only [Complex.ofReal_re] at hr
  have hlimit : (-2+4*ZetaRieszMaskSupport.retainedCost (10001/20000))-0≤
      (42/25 : ℝ) := le_of_tendsto_of_frequently (hr.sub he)
        (hceiling.mono fun j hj => by
          dsimp only [Function.comp_def]
          linarith only [hj])
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u:=10001/20000) (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  linarith only [hlimit,hc]

end RiemannGaussian.ZetaRieszCeilingDensityAudit
