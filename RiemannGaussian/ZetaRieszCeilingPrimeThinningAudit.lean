/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingIntegerAudit
import RiemannGaussian.ZetaSignedPoleControl

/-!
# Genuine prime support is not complete prime coverage

This is a detector control, not an estimate for the complete ordinary-prime
carrier. Removing a nonnegative damped cosine weight from genuine primes
can create the double source in the SAME joined evaluator. Clipping that
weight to [0,1] changes only a finite head and leaves the source unchanged.

Every order, including zero and one, is kept. No conclusion below removes
an unpaid subset from the arithmetic proof chain.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Complex Filter Topology Metric Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingPrimeThinningAudit
open ZetaRieszCeilingDensityAudit ZetaRieszSelbergSourceAudit
open ZetaRieszSignedSelbergPayment ZetaRieszJoinedPhaseRadius

/-- The actual ordinary-prime moment at the tilted Euler centre. -/
def tiltedMoment (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (1+u+Complex.I*y)

private theorem filled_analytic_closed (u y : ℝ) :
    AnalyticOnNhd ℂ (logDeriv riemannZeta₁)
      (closedBall (1+u+Complex.I*y) u) := by
  intro s hs
  have hd : ‖s-(1+u+Complex.I*y)‖≤u := by
    simpa only [mem_closedBall,dist_eq_norm] using hs
  have hr : 1≤(s : ℂ).re := by
    have hl := (abs_le.mp ((Complex.abs_re_le_norm (s-(1+u+Complex.I*y))).trans hd)).1
    simp only [sub_re,add_re,one_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,
      zero_mul,one_mul,sub_zero,add_zero] at hl
    linarith only [hl]
  have ha := differentiable_riemannZeta₁.analyticAt s
  exact ha.deriv.div ha (riemannZeta₁_ne_zero_of_one_le_re hr)

/-- Compactness supplies a radius beyond the genuine pole distance
for the FILLED zeta remainder. No unproved zero gap is assumed. -/
theorem exists_filled_radius (u y : ℝ) (hu : 0<u) :
    ∃ R : ℝ,u<R ∧ AnalyticOnNhd ℂ (logDeriv riemannZeta₁)
      (closedBall (1+u+Complex.I*y) R) := by
  let f : ℂ→ℂ := logDeriv riemannZeta₁
  let c : ℂ := 1+u+Complex.I*y
  have hb : closedBall c u⊆{s | AnalyticAt ℂ f s} := filled_analytic_closed u y
  obtain ⟨δ,hδ,hd⟩ := (isCompact_closedBall c u).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) hb
  refine ⟨u+δ/2,by linarith only [hδ],?_⟩
  intro s hs
  apply hd
  rw [cthickening_closedBall hδ.le hu.le]
  exact (closedBall_subset_closedBall (by linarith only [hδ])) hs

private theorem full_moment_split (u y : ℝ) (hu : 0<u) (k : ℕ) :
    zetaPrimeLogMoment k (1+u+Complex.I*y)=
      (((u : ℂ)+Complex.I*y)⁻¹)^(k+1)-
      signedTaylorMoment k (logDeriv riemannZeta₁) (1+u+Complex.I*y) := by
  let c : ℂ := 1+u+Complex.I*y
  have hc : 1<c.re := by dsimp [c]; simp; linarith only [hu]
  have h1 : c≠1 := by intro he; rw [he] at hc; norm_num at hc
  have hz := riemannZeta_ne_zero_of_one_le_re hc.le
  have ha : AnalyticAt ℂ (fun s : ℂ => (s-1)⁻¹) c :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h1)
  have hb : AnalyticAt ℂ (logDeriv riemannZeta₁) c := (differentiable_riemannZeta₁.analyticAt c).deriv.div
    (differentiable_riemannZeta₁.analyticAt c) (riemannZeta₁_ne_zero_of_one_le_re hc.le)
  have he : (fun s : ℂ => -logDeriv riemannZeta s)=ᶠ[𝓝 c]
      (fun s => (s-1)⁻¹-logDeriv riemannZeta₁ s) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hc] with s hs
    have hs1 : s≠1 := by intro hh; rw [hh] at hs; norm_num at hs
    simpa only [one_div] using neg_logDeriv_riemannZeta_eq_pole_sub hs1
      (riemannZeta_ne_zero_of_one_le_re hs.le)
  rw [zetaPrimeLogMoment,signedTaylorMoment_congr k he,
    signedTaylorMoment_sub k ha hb,signedTaylorMoment_inv_sub_one]
  dsimp only [c]
  congr 2
  ring

/-- Exact pole plus a decaying FILLED-zeta remainder and independently
decaying proper powers, at every fixed tilted Euler centre. -/
theorem tiltedMoment_sub_pole_tendsto (u y : ℝ) (hu : 0<u) :
    Tendsto (fun k => tiltedMoment u y k-
      ((u : ℂ)/((u : ℂ)+Complex.I*y))^(k+1)) atTop (𝓝 0) := by
  obtain ⟨R,hR,ha⟩ := exists_filled_radius u y hu
  obtain ⟨B,hB⟩ := ((isCompact_closedBall (1+u+Complex.I*y) R).image_of_continuousOn
    ha.continuousOn).isBounded.exists_norm_le
  let M : ℝ := max B 0+1
  have hM : 0<M := by dsimp [M]; linarith only [le_max_right B 0]
  have hm (k : ℕ) :
      ‖signedTaylorMoment k (logDeriv riemannZeta₁) (1+u+Complex.I*y)‖≤M/R^k := by
    apply norm_signedTaylorMoment_le (by linarith only [hu,hR])
      (ha.differentiableOn.diffContOnCl_ball (by intro s hs; exact hs))
    intro s hs
    have hh := hB _ (mem_image_of_mem _ (sphere_subset_closedBall hs))
    exact hh.trans (by dsimp [M]; linarith only [le_max_left B 0])
  have hR0 : 0<R := lt_trans hu hR
  have hr0 : 0≤u/R := div_nonneg hu.le hR0.le
  have hr1 : u/R<1 := (div_lt_one₀ (by linarith only [hu,hR])).mpr hR
  have hreg : Tendsto (fun k => (u : ℂ)^(k+1)*
      signedTaylorMoment k (logDeriv riemannZeta₁) (1+u+Complex.I*y))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun k => u*M*(u/R)^k) _
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (u*M))
    intro k
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
    calc
      _ ≤ u^(k+1)*(M/R^k) := mul_le_mul_of_nonneg_left (hm k) (by positivity)
      _ = _ := by rw [pow_succ,div_pow]; ring
  let q : ℝ := u+1/4
  have hq : 0<q := by dsimp [q]; linarith only [hu]
  have huq : u/q<1 := (div_lt_one₀ hq).mpr (by dsimp [q]; linarith)
  let P : ℝ := zetaProperPrimePowerExpMass (1+u-q)
  have hmass : Summable (fun m => zetaProperPrimePowerCoefficient m*
      zetaPrimeExpWeight ((1+u+Complex.I*y).re-q) m) := by
    apply summable_zetaProperPrimePowerExpMass
    simp [q]; linarith
  have hp (k : ℕ) : ‖zetaProperPrimePowerMoment k (1+u+Complex.I*y)‖≤
      q⁻¹^k*P := by
    simpa only [zetaProperPrimePowerMoment,P,zetaProperPrimePowerExpMass,
      add_re,one_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,
      zero_mul,one_mul,sub_zero,add_zero] using
      norm_tsum_mul_zetaPrimeLogKernel_le _ zetaProperPrimePowerCoefficient_nonneg
        k (1+u+Complex.I*y) hq hmass
  have hpow : Tendsto (fun k => (u : ℂ)^(k+1)*
      zetaProperPrimePowerMoment k (1+u+Complex.I*y)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun k => u*P*(u/q)^k) _
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg hu.le hq.le) huq).const_mul (u*P))
    intro k
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
    calc
      _ ≤ u^(k+1)*(q⁻¹^k*P) :=
        mul_le_mul_of_nonneg_left (hp k) (by positivity)
      _ = _ := by rw [pow_succ,div_pow,inv_pow]; ring
  have he (k : ℕ) : tiltedMoment u y k-
      ((u : ℂ)/((u : ℂ)+Complex.I*y))^(k+1)=
      -((u : ℂ)^(k+1)*signedTaylorMoment k (logDeriv riemannZeta₁)
        (1+u+Complex.I*y))-
      (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (1+u+Complex.I*y) := by
    have hs : 1<(1+u+Complex.I*(y : ℂ)).re := by simp; linarith only [hu]
    have hh := zetaPrimeLogMoment_eq_prime_add_proper k hs
    rw [full_moment_split u y hu k] at hh
    unfold tiltedMoment
    rw [show zetaOrdinaryPrimeLogMoment k (1+u+Complex.I*y)=
      (((u : ℂ)+Complex.I*y)⁻¹)^(k+1)-
      signedTaylorMoment k (logDeriv riemannZeta₁) (1+u+Complex.I*y)-
      zetaProperPrimePowerMoment k (1+u+Complex.I*y) by linear_combination -hh]
    rw [div_pow,div_eq_mul_inv,←inv_pow]
    ring
  have ht : Tendsto (fun k =>
      -((u : ℂ)^(k+1)*signedTaylorMoment k (logDeriv riemannZeta₁)
        (1+u+Complex.I*y))-
      (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (1+u+Complex.I*y)) atTop (𝓝 0) := by
    simpa only [neg_zero,sub_zero] using hreg.neg.sub hpow
  exact ht.congr (fun k => (he k).symm)

/-- The genuine simple pole, not an invented density channel. -/
theorem tiltedMoment_zero_height (u : ℝ) (hu : 0<u) :
    Tendsto (tiltedMoment u 0) atTop (𝓝 1) := by
  have h := tiltedMoment_sub_pole_tendsto u 0 hu
  have he (k : ℕ) : ((u : ℂ)/((u : ℂ)+Complex.I*(0 : ℝ)))^(k+1)=1 := by
    simp [hu.ne']
  simp_rw [he] at h
  simpa using (h.add tendsto_const_nhds).congr (fun k => sub_add_cancel _ _)

/-- Every fixed nonzero phase at the tilted centre has a strict pole
ratio below one; this uses the proved zero-free line. -/
theorem tiltedMoment_nonzero_height (u y : ℝ) (hu : 0<u) (hy : y≠0) :
    Tendsto (tiltedMoment u y) atTop (𝓝 0) := by
  have hn : ‖(u : ℂ)/((u : ℂ)+Complex.I*y)‖<1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hu.le]
    have hs : u<‖(u : ℂ)+Complex.I*y‖ := by
      rw [Complex.norm_def]
      apply (lt_sqrt hu.le).mpr
      simp only [normSq_apply,add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,
        I_re,I_im,zero_mul,one_mul,sub_zero,add_zero]
      nlinarith only [sq_pos_of_ne_zero hy]
    exact (div_lt_one₀ (by linarith only [hu,hs])).mpr hs
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).comp
    (tendsto_add_atTop_nat 1)
  simpa only [zero_add] using ((tiltedMoment_sub_pole_tendsto u y hu).add ht).congr
    (fun k => sub_add_cancel _ _)

/-- Nonnegative removal density on GENUINE primes. It is clipped below
before defining the retained fractional prime measure. -/
def rawWeight (u y : ℝ) (p : ℕ) : ℝ :=
  4*Real.exp (-(u-1/2)*Real.log p)*(1+Real.cos (y*Real.log p))

/-- Clip the removal weight, not an arithmetic proof error, to [0,1]. -/
def clippedWeight (u y : ℝ) (p : ℕ) : ℝ := min 1 (rawWeight u y p)

theorem rawWeight_nonneg (u y : ℝ) (p : ℕ) : 0≤rawWeight u y p := by
  have hc := neg_one_le_cos (y*Real.log p)
  unfold rawWeight
  exact mul_nonneg (mul_nonneg (by norm_num) (exp_pos _).le) (by linarith only [hc])

theorem rawWeight_le (u y : ℝ) (p : ℕ) :
    rawWeight u y p≤8*Real.exp (-(u-1/2)*Real.log p) := by
  have hc := cos_le_one (y*Real.log p)
  have he := exp_pos (-(u-1/2)*Real.log p)
  unfold rawWeight
  nlinarith only [hc,he]

/-- The retained actual-prime weights are between zero and one. -/
theorem clippedWeight_bounds (u y : ℝ) (p : ℕ) :
    0≤clippedWeight u y p ∧ clippedWeight u y p≤1 := by
  exact ⟨le_min (by norm_num) (rawWeight_nonneg u y p),min_le_left _ _⟩

/-- The damped cosine is EXACTLY three tilted ordinary-prime channels,
at each literal prime and factorial order, with the original phase kept. -/
theorem rawWeight_kernel (u y : ℝ) (k p : ℕ) :
    (rawWeight u y p : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*y) p=
      4*zetaPrimeLogKernel k (1+u+Complex.I*y) p+
      2*zetaPrimeLogKernel k (1+u) p+
      2*zetaPrimeLogKernel k (1+u+Complex.I*(2*y)) p := by
  let t : ℝ := Real.log p
  have hc : 2*(Real.cos (y*t) : ℂ)=
      Complex.exp (Complex.I*y*(t : ℂ))+Complex.exp (-Complex.I*y*(t : ℂ)) := by
    calc
      _ = Complex.exp (((y*t : ℝ) : ℂ)*Complex.I)+
          Complex.exp (-((y*t : ℝ) : ℂ)*Complex.I) := by
        simpa only [Complex.ofReal_cos] using Complex.two_cos ((y*t : ℝ) : ℂ)
      _ = _ := by congr 2 <;> push_cast <;> ring
  have h0 : Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))=
      Complex.exp (-(1+u+Complex.I*y)*(t : ℂ)) := by
    rw [←Complex.exp_add]; congr 1; push_cast; ring
  have h1 : Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)*
      Complex.exp (Complex.I*y*(t : ℂ))*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))=
      Complex.exp (-(1+u)*(t : ℂ)) := by
    rw [←Complex.exp_add,←Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)*
      Complex.exp (-Complex.I*y*(t : ℂ))*
      Complex.exp (-(3/2+Complex.I*y)*(t : ℂ))=
      Complex.exp (-(1+u+Complex.I*(2*y))*(t : ℂ)) := by
    rw [←Complex.exp_add,←Complex.exp_add]; congr 1; push_cast; ring
  have hw : (rawWeight u y p : ℂ)=
      4*Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)+
      2*Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)*Complex.exp (Complex.I*y*(t : ℂ))+
      2*Complex.exp (-((u-1/2 : ℝ) : ℂ)*t)*Complex.exp (-Complex.I*y*(t : ℂ)) := by
    unfold rawWeight
    change ((4*Real.exp (-(u-1/2)*t)*(1+Real.cos (y*t)) : ℝ) : ℂ)=_
    push_cast at hc
    push_cast
    linear_combination 2*Complex.exp (-(u-1/2)*(t : ℂ))*hc
  rw [hw]
  unfold zetaPrimeLogKernel zetaPrimeFeature
  push_cast at h0 h1 h2 ⊢
  simp only [neg_mul] at h0 h1 h2 ⊢
  dsimp only [t] at h0 h1 h2 ⊢
  simp only [←Complex.natCast_log,mul_assoc] at h0 h1 h2 ⊢
  linear_combination
    4*((Real.log p : ℂ)^k/(k.factorial : ℂ))*h0+
    2*((Real.log p : ℂ)^k/(k.factorial : ℂ))*h1+
    2*((Real.log p : ℂ)^k/(k.factorial : ℂ))*h2

/-- Raw weighted ordinary-prime removal. This definition is arithmetic,
not a sequence defined by its desired limiting source. -/
def rawRemovedMoment (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' p : ℕ, if p.Prime then
    (rawWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
      zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0

private theorem raw_summable (u y : ℝ) (hu : 0<u) (k : ℕ) :
    Summable (fun p : ℕ => if p.Prime then
      (rawWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0) := by
  have hs (t : ℝ) : 1<(1+u+Complex.I*t).re := by simp; linarith only [hu]
  have h0 := (summable_zetaOrdinaryPrimeLogMoment k (hs y)).mul_left (4 : ℂ)
  have h1 := (summable_zetaOrdinaryPrimeLogMoment k (hs 0)).mul_left (2 : ℂ)
  have h2 := (summable_zetaOrdinaryPrimeLogMoment k (hs (2*y))).mul_left (2 : ℂ)
  apply (h0.add h1 |>.add h2).congr
  intro p
  by_cases hp : p.Prime
  · simp only [hp,ite_true]
    have ht := congrArg (fun z => (ArithmeticFunction.vonMangoldt p : ℂ)*z)
      (rawWeight_kernel u y k p).symm
    simp only [Complex.ofReal_zero,mul_zero,add_zero,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_add] at ht ⊢
    linear_combination ht
  · simp [hp]

/-- The exact THREE complete series, before any norm or source limit. -/
theorem rawRemovedMoment_eq (u y : ℝ) (hu : 0<u) (k : ℕ) :
    rawRemovedMoment u y k=4*tiltedMoment u y k+
      2*tiltedMoment u 0 k+2*tiltedMoment u (2*y) k := by
  have hs (t : ℝ) : 1<(1+u+Complex.I*t).re := by simp; linarith only [hu]
  have h0 := (summable_zetaOrdinaryPrimeLogMoment k (hs y)).mul_left (4 : ℂ)
  have h1 := (summable_zetaOrdinaryPrimeLogMoment k (hs 0)).mul_left (2 : ℂ)
  have h2 := (summable_zetaOrdinaryPrimeLogMoment k (hs (2*y))).mul_left (2 : ℂ)
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at h2
  have he : (∑' p : ℕ, if p.Prime then
      (rawWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0)=
      4*zetaOrdinaryPrimeLogMoment k (1+u+Complex.I*y)+
      2*zetaOrdinaryPrimeLogMoment k (1+u+Complex.I*(0 : ℝ))+
      2*zetaOrdinaryPrimeLogMoment k (1+u+Complex.I*(2*y)) := by
    rw [zetaOrdinaryPrimeLogMoment,zetaOrdinaryPrimeLogMoment,zetaOrdinaryPrimeLogMoment,
      ←tsum_mul_left,←tsum_mul_left,←tsum_mul_left,←h0.tsum_add h1,←(h0.add h1).tsum_add h2]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime
    · simp only [hp,ite_true]
      have ht := congrArg (fun z => (ArithmeticFunction.vonMangoldt p : ℂ)*z)
        (rawWeight_kernel u y k p)
      simp only [Complex.ofReal_zero,mul_zero,add_zero,mul_add] at ht ⊢
      linear_combination ht
    · simp [hp]
  unfold rawRemovedMoment tiltedMoment
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at he ⊢
  rw [he]
  ring

/-- The removed source is +2. Its density can be small while its joined
factorial source is not negligible. No actual-prime discrepancy is paid. -/
theorem rawRemovedMoment_tendsto (u y : ℝ) (hu : 0<u) (hy : y≠0) :
    Tendsto (rawRemovedMoment u y) atTop (𝓝 2) := by
  have h0 := (tiltedMoment_nonzero_height u y hu hy).const_mul (4 : ℂ)
  have h1 := (tiltedMoment_zero_height u hu).const_mul (2 : ℂ)
  have h2 := (tiltedMoment_nonzero_height u (2*y) hu
    (mul_ne_zero (by norm_num) hy)).const_mul (2 : ℂ)
  simpa using (h0.add h1 |>.add h2).congr (fun k => (rawRemovedMoment_eq u y hu k).symm)

/-- Clipping affects only a finite prime head, even at the target's
very small positive horizontal damping. Its size need not be enumerated. -/
theorem clippedWeight_eq_raw_eventually (u y : ℝ) (hu : 1/2<u) :
    ∀ᶠ p : ℕ in atTop,clippedWeight u y p=rawWeight u y p := by
  have hd : 0<u-1/2 := by linarith only [hu]
  have ht := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (Real.log 8/(u-1/2))
  filter_upwards [ht] with p hp
  have hlog : Real.log 8≤(u-1/2)*Real.log p := by
    exact (div_le_iff₀ hd).mp hp |>.trans_eq (mul_comm _ _)
  have hr : rawWeight u y p≤1 := by
    calc
      _ ≤ 8*Real.exp (-(u-1/2)*Real.log p) := rawWeight_le u y p
      _ ≤ 8*Real.exp (-Real.log 8) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hlog])) (by norm_num)
      _ = 1 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<8)]; norm_num
  exact min_eq_right hr

private theorem normalizedKernel_tendsto (u : ℝ) (s : ℂ) (p : ℕ)
    (hu : 0≤u) (hU : u<1) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+1)*zetaPrimeLogKernel k s p) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a:=fun k => u*zetaPrimeExpWeight (s.re-1) p*u^k) _
    (by simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hu hU).const_mul
      (u*zetaPrimeExpWeight (s.re-1) p)))
  intro k
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  have hk := norm_zetaPrimeLogKernel_le k s p (by norm_num : (0 : ℝ)<1)
  simpa only [inv_one,one_pow,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm] using
    mul_le_mul_of_nonneg_left hk (pow_nonneg hu (k+1))

/-- Complete arithmetic removal with a bounded fractional prime weight. -/
def clippedRemovedMoment (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' p : ℕ, if p.Prime then
    (clippedWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
      zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0

private theorem clipped_summable (u y : ℝ) (k : ℕ) :
    Summable (fun p : ℕ => if p.Prime then
      (clippedWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0) := by
  have hs := (summable_zetaOrdinaryPrimeLogMoment k
    (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)).norm
  apply hs.of_norm_bounded
  intro p
  by_cases hp : p.Prime
  · simp only [hp,ite_true,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (clippedWeight_bounds u y p).1]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (clippedWeight_bounds u y p).2
        (norm_nonneg (ArithmeticFunction.vonMangoldt p)))
      (norm_nonneg (zetaPrimeLogKernel k (3/2+Complex.I*y) p))).trans_eq (by ring)
  · simp [hp]

/-- Exact finite head difference. This error contains all clipped prime
orders and does not stand in for an ordinary-prime density discrepancy. -/
theorem clippedRemovedMoment_sub_raw_eq (u y : ℝ) (hu : 0<u) (M : ℕ)
    (hM : ∀ p,M≤p→clippedWeight u y p=rawWeight u y p) (k : ℕ) :
    clippedRemovedMoment u y k-rawRemovedMoment u y k=
      ∑ p∈Finset.range M,
        (u : ℂ)^(k+1)*(if p.Prime then
          ((clippedWeight u y p-rawWeight u y p : ℝ) : ℂ)*
          (ArithmeticFunction.vonMangoldt p : ℂ)*
          zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0) := by
  unfold clippedRemovedMoment rawRemovedMoment
  rw [←mul_sub,←(clipped_summable u y k).tsum_sub (raw_summable u y hu k)]
  have hterm p : (if p.Prime then
      (clippedWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0)-
      (if p.Prime then (rawWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0)=
      (if p.Prime then ((clippedWeight u y p-rawWeight u y p : ℝ) : ℂ)*
        (ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0) := by
    by_cases hp : p.Prime <;> simp [hp,sub_mul]
  simp_rw [hterm]
  rw [tsum_eq_sum (s:=Finset.range M) (by
    intro p hp
    have hh := hM p (by simpa using hp)
    simp [hh])]
  rw [Finset.mul_sum]

/-- Fractional actual-prime removal has source +2 unconditionally. The
finite clipping head is proved negligible, not assumed negligible. -/
theorem clippedRemovedMoment_tendsto (u y : ℝ) (hu : 1/2<u) (hU : u<1) (hy : y≠0) :
    Tendsto (clippedRemovedMoment u y) atTop (𝓝 2) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (clippedWeight_eq_raw_eventually u y hu)
  have hu0 : 0<u := by linarith only [hu]
  have he : Tendsto (fun k => clippedRemovedMoment u y k-rawRemovedMoment u y k)
      atTop (𝓝 0) := by
    have ht : Tendsto (fun k => ∑ p∈Finset.range M,
        (u : ℂ)^(k+1)*(if p.Prime then
          ((clippedWeight u y p-rawWeight u y p : ℝ) : ℂ)*
          (ArithmeticFunction.vonMangoldt p : ℂ)*
          zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0)) atTop
        (𝓝 (∑ _p∈Finset.range M,(0 : ℂ))) := by
      apply tendsto_finsetSum
      intro p _
      by_cases hp : p.Prime
      · simp only [hp,ite_true]
        have h := (normalizedKernel_tendsto u (3/2+Complex.I*y) p hu0.le hU).const_mul
          (((clippedWeight u y p-rawWeight u y p : ℝ) : ℂ)*
            (ArithmeticFunction.vonMangoldt p : ℂ))
        simpa only [mul_zero,zero_mul,mul_assoc,mul_comm,mul_left_comm] using h
      · simpa only [hp,ite_false,mul_zero] using (tendsto_const_nhds (x:=(0 : ℂ)))
    simp only [Finset.sum_const_zero] at ht
    exact ht.congr (fun k => (clippedRemovedMoment_sub_raw_eq u y hu0 M hM k).symm)
  simpa only [zero_add] using (he.add (rawRemovedMoment_tendsto u y hu0 hy)).congr
    (fun k => sub_add_cancel _ _)

/-- Literal fractional THINNING of ordinary primes. This is not the
complete ordinary-prime measure used by the actual endgame carrier. -/
def retainedMoment (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' p : ℕ, if p.Prime then
    ((1-clippedWeight u y p : ℝ) : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
      zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0

theorem retainedWeight_bounds (u y : ℝ) (p : ℕ) :
    0≤1-clippedWeight u y p ∧ 1-clippedWeight u y p≤1 := by
  have hh := clippedWeight_bounds u y p
  constructor <;> linarith only [hh.1,hh.2]

/-- Exact prime completeness ledger. The removed term is not an error
merely because the remaining labels are also genuine primes. -/
theorem retainedMoment_add_removed (u y : ℝ) (k : ℕ) :
    retainedMoment u y k+clippedRemovedMoment u y k=
      ZetaRieszPairPrimePowerPayment.ordinaryArray u y k := by
  have hs := summable_zetaOrdinaryPrimeLogMoment k
    (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)
  unfold retainedMoment clippedRemovedMoment ZetaRieszPairPrimePowerPayment.ordinaryArray
  rw [←mul_add]
  have he : (∑' p : ℕ,if p.Prime then
      ((1-clippedWeight u y p : ℝ) : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
        zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0)=
      zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)-
        ∑' p : ℕ,if p.Prime then
          (clippedWeight u y p : ℂ)*(ArithmeticFunction.vonMangoldt p : ℂ)*
            zetaPrimeLogKernel k (3/2+Complex.I*y) p else 0 := by
    rw [zetaOrdinaryPrimeLogMoment,←hs.tsum_sub (clipped_summable u y k)]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime <;> simp [hp,sub_mul]
  rw [he,sub_add_cancel]

private theorem original_target_moment_tendsto :
    Tendsto (ZetaRieszPairPrimePowerPayment.ordinaryArray (10001/20000) 54)
      atTop (𝓝 0) := by
  have hlog : Real.log (|(54 : ℝ)|+3)≤1800 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<57)
    norm_num at hh ⊢
    linarith only [hh]
  obtain ⟨C,hC,hbound⟩ := exists_ordinary_bound_concrete_height
    (y:=54) (by norm_num) hlog
  apply squeeze_zero_norm (a:=fun k => (10001/20000 : ℝ)*C*
      (100010/100011 : ℝ)^k) _
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ)≤100010/100011)
      (by norm_num : (100010/100011 : ℝ)<1)).const_mul ((10001/20000 : ℝ)*C))
  intro k
  unfold ZetaRieszPairPrimePowerPayment.ordinaryArray
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤10001/20000)]
  calc
    _ ≤ (10001/20000 : ℝ)^(k+1)*(C/(100011/200000)^k) :=
      mul_le_mul_of_nonneg_left (hbound k) (by positivity)
    _ = (10001/20000 : ℝ)*C*((10001/20000)^k/(100011/200000)^k) := by
      rw [pow_succ]
      ring
    _ = (10001/20000 : ℝ)*C*((10001/20000)/(100011/200000))^k :=
      congrArg (fun x : ℝ => (10001/20000 : ℝ)*C*x)
        (div_pow (10001/20000 : ℝ) (100011/200000 : ℝ) k).symm
    _ = _ := by norm_num

/-- An UNCONDITIONAL genuine-prime fractional control at the original
radius and a fixed admissible height. No hypothetical zero is assumed. -/
theorem retainedMoment_target_tendsto :
    Tendsto (retainedMoment (10001/20000) 54) atTop (𝓝 (-2)) := by
  have he (k : ℕ) : retainedMoment (10001/20000) 54 k=
      ZetaRieszPairPrimePowerPayment.ordinaryArray (10001/20000) 54 k-
        clippedRemovedMoment (10001/20000) 54 k := by
    have hh := retainedMoment_add_removed (10001/20000) 54 k
    linear_combination hh
  have ht := original_target_moment_tendsto.sub
    (clippedRemovedMoment_tendsto (10001/20000) 54 (by norm_num) (by norm_num) (by norm_num))
  simpa only [zero_sub] using ht.congr (fun k => (he k).symm)

/-- The unchanged JOINED evaluator exceeds 42/25 for the fractional
prime thinning. This refutes support-only detector reasoning, NOT the
arithmetic ceiling for the complete prime carrier. -/
theorem retained_join_exceeds_ceiling :
    ∀ᶠ N in atTop,(42/25 : ℝ)<
      (-traceError (retainedMoment (10001/20000) 54) (N-1)-
        harmonicEvaluation (retainedMoment (10001/20000) 54) (10001/20000) N).re := by
  have ht := joined_double_tendsto _ retainedMoment_target_tendsto
    (u:=10001/20000) (by norm_num) (by norm_num)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp only [Complex.ofReal_re] at hr
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u:=10001/20000) (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  exact hr.eventually_const_lt (by linarith only [hc])

/-- Literal cumulative clipped removal, indexed by INTEGER labels.
Its increments vanish at composites; no continuous density is rounded. -/
def primePrefix (u y : ℝ) (M : ℕ) : ℝ :=
  ∑ p∈Finset.range M,if p.Prime then clippedWeight u y p else 0

/-- Cumulative rounding on integer labels gives unit ordinary-prime atoms. -/
def binaryPrimeAtom (u y : ℝ) (p : ℕ) : ℕ :=
  ⌊primePrefix u y (p+1)⌋₊-⌊primePrefix u y p⌋₊

private theorem prefix_nonneg (u y : ℝ) (M : ℕ) : 0≤primePrefix u y M := by
  apply Finset.sum_nonneg
  intro p _
  by_cases hp : p.Prime <;> simp only [hp,ite_true,ite_false]
  · exact (clippedWeight_bounds u y p).1
  · norm_num

private theorem prefix_step (u y : ℝ) (p : ℕ) :
    primePrefix u y (p+1)=primePrefix u y p+
      (if p.Prime then clippedWeight u y p else 0) := by
  exact Finset.sum_range_succ (fun q : ℕ => if q.Prime then clippedWeight u y q else 0) p

private theorem prefix_mono_step (u y : ℝ) (p : ℕ) :
    primePrefix u y p≤primePrefix u y (p+1) := by
  rw [prefix_step]
  by_cases hp : p.Prime <;> simp only [hp,ite_true,ite_false]
  · linarith only [(clippedWeight_bounds u y p).1]
  · exact le_add_of_nonneg_right (le_refl (0 : ℝ))

/-- Binary support really consists of ordinary primes. This is a
finite exact statement, not an infinite moment-comparison premise. -/
theorem binaryPrimeAtom_composite (u y : ℝ) {p : ℕ} (hp : ¬p.Prime) :
    binaryPrimeAtom u y p=0 := by
  simp [binaryPrimeAtom,prefix_step,hp]

theorem binaryPrimeAtom_zero_or_one (u y : ℝ) (p : ℕ) :
    binaryPrimeAtom u y p=0 ∨ binaryPrimeAtom u y p=1 := by
  have hs : primePrefix u y (p+1)≤primePrefix u y p+1 := by
    rw [prefix_step]
    by_cases hp : p.Prime <;> simp only [hp,ite_true,ite_false]
    · linarith only [(clippedWeight_bounds u y p).2]
    · linarith
  have hl := Nat.floor_mono hs
  rw [Nat.floor_add_one (prefix_nonneg u y p)] at hl
  unfold binaryPrimeAtom
  omega

/-- Complete finite cumulative bookkeeping, including the initial
endpoint. This is what the optional binary prime probe rounds. -/
theorem binaryPrimeAtom_sum (u y : ℝ) (M : ℕ) :
    (∑ p∈Finset.range M,(binaryPrimeAtom u y p : ℝ))=
      (⌊primePrefix u y M⌋₊ : ℝ) := by
  induction M with
  | zero => simp [primePrefix]
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,binaryPrimeAtom,
      Nat.cast_sub (Nat.floor_mono (prefix_mono_step u y M))]
    ring

theorem binaryPrimeAtom_prefix_error (u y : ℝ) (M : ℕ) :
    |(∑ p∈Finset.range M,(binaryPrimeAtom u y p : ℝ))-primePrefix u y M|<1 := by
  rw [binaryPrimeAtom_sum,abs_of_nonpos
    (sub_nonpos.mpr (Nat.floor_le (prefix_nonneg u y M)))]
  have hh := Nat.lt_floor_add_one (primePrefix u y M)
  linarith only [hh]

end RiemannGaussian.ZetaRieszCeilingPrimeThinningAudit
