/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusWronskianArithmetic
import RiemannGaussian.ZetaFiniteDirichlet
import RiemannGaussian.ZetaReciprocalGeometry
import RiemannGaussian.GaussianXiDivisorContour
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Converse ordinary-prime moment coherence

The converse uses the ordinary-prime generating series and Abel convergence,
not a Riesz carrier or an exposure hypothesis. The right-half restriction
`0 < u < 1` keeps the proper-prime-power correction analytic at the candidate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Complex Filter Metric Set Topology
open scoped BigOperators Classical NNReal ENNReal
namespace RiemannGaussian.ZetaPrimeMomentCoherence

/-- The safe Euler center at a fixed real height. -/
def center (y : ℝ) : ℂ := 3/2+I*y
/-- The point selected by the horizontal source radius. -/
def candidate (u y : ℝ) : ℂ := center y-u
/-- The actual complete ordinary-prime logarithmic moment at source scale. -/
def moments (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*zetaOrdinaryPrimeLogMoment k (center y)
/-- The moment power series, absolutely convergent on the unit disk under coherence. -/
def generating (u y : ℝ) (z : ℂ) : ℂ := ∑' k, moments u y k*z^k

@[simp] theorem center_re (y : ℝ) : (center y).re=3/2 := by simp [center]
@[simp] theorem candidate_re (u y : ℝ) : (candidate u y).re=3/2-u := by
  simp [candidate]
@[simp] theorem candidate_im (u y : ℝ) : (candidate u y).im=y := by
  simp [candidate,center]

/-- Convergent coefficients are bounded, so their generating series is
genuinely absolutely convergent throughout the open unit disk. -/
theorem summable_of_tendsto {a : ℕ → ℂ} {l z : ℂ}
    (ha : Tendsto a atTop (𝓝 l)) (hz : ‖z‖ < 1) :
    Summable (fun k => a k*z^k) := by
  obtain ⟨C,hC⟩ := ha.cauchySeq.isBounded_range.exists_norm_le
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C)
  intro k
  rw [norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_right (hC _ (mem_range_self k))
    (pow_nonneg (norm_nonneg z) k)

/-- Abel averaging of a convergent coefficient sequence. No convergence
of its unweighted infinite sum is assumed. -/
theorem tendsto_abel_of_tendsto {a : ℕ → ℂ} {l : ℂ}
    (ha : Tendsto a atTop (𝓝 l)) :
    Tendsto (fun r : ℝ => (1-(r : ℂ))*∑' k, a k*(r : ℂ)^k)
      (𝓝[<] 1) (𝓝 l) := by
  let f : ℕ → ℂ := fun k => if k=0 then a 0 else a k-a (k-1)
  have hs (n : ℕ) : ∑ k∈Finset.range (n+1), f k = a n := by
    induction n with
    | zero => simp [f]
    | succ n ih => rw [Finset.sum_range_succ,ih]; simp [f]
  have ht : Tendsto (fun n => ∑ k∈Finset.range n, f k) atTop (𝓝 l) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [hs] using ha
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt ht
  have hab' : Tendsto (fun r : ℝ => ∑' k, f k*(r : ℂ)^k) (𝓝[<] 1) (𝓝 l) :=
    hab.comp (tendsto_map : Tendsto Complex.ofReal (𝓝[<] (1 : ℝ))
      ((𝓝[<] (1 : ℝ)).map Complex.ofReal))
  apply hab'.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with r hr
  have hz : ‖(r : ℂ)‖<1 := by simpa [abs_of_pos hr.1] using hr.2
  have hsa := summable_of_tendsto ha hz
  have hsf := summable_powerSeries_of_norm_lt_one ht.cauchySeq hz
  rw [←hsf.sum_add_tsum_nat_add 1,←hsa.sum_add_tsum_nat_add 1]
  have h1 : (∑' k, f (k+1)*(r : ℂ)^(k+1))=
      (∑' k, a (k+1)*(r : ℂ)^(k+1))-(r : ℂ)*∑' k,a k*(r : ℂ)^k := by
    have he : (fun k => f (k+1)*(r : ℂ)^(k+1))=fun k =>
        a (k+1)*(r : ℂ)^(k+1)-(r : ℂ)*(a k*(r : ℂ)^k) := by
      funext k
      simp only [f,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,
        Nat.add_sub_cancel,sub_mul,pow_succ]
      ring
    have hshift : Summable (fun k => a (k+1)*(r : ℂ)^(k+1)) :=
      (summable_nat_add_iff 1).mpr hsa
    have hmul : Summable (fun k => (r : ℂ)*(a k*(r : ℂ)^k)) :=
      hsa.mul_left (r : ℂ)
    rw [he,hshift.tsum_sub hmul,tsum_mul_left]
  rw [h1]
  simp only [Finset.sum_range_one,pow_zero,mul_one,f,↓reduceIte]
  have he : (∑' k,a k*(r : ℂ)^k)=a 0+∑' k,a (k+1)*(r : ℂ)^(k+1) := by
    simpa using (hsa.sum_add_tsum_nat_add 1).symm
  rw [he]
  ring

/-- Coefficient convergence supplies analyticity of the whole generating
series, including every low factorial order. -/
theorem analyticOnNhd_generating {u y : ℝ} {l : ℂ}
    (ha : Tendsto (moments u y) atTop (𝓝 l)) :
    AnalyticOnNhd ℂ (generating u y) (ball 0 1) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (moments u y)
  have hr : (1 : ℝ≥0∞) ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    apply p.le_radius_of_summable_norm
    simpa [p,FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg r.coe_nonneg] using
      (summable_of_tendsto ha (z := (r : ℂ)) (by simpa using hr)).norm
  intro z hz
  have hze : z∈Metric.eball (0 : ℂ) p.radius := by
    apply lt_of_lt_of_le _ hr
    have hz' : ‖z‖ < 1 := by simpa using hz
    simpa [edist_dist,dist_zero_right,enorm_eq_nnnorm] using
      (show (‖z‖₊ : ℝ≥0∞)<1 from by exact_mod_cast hz')
  have he : p.sum=generating u y := by
    funext w
    simpa [p,FormalMultilinearSeries.ofScalarsSum,smul_eq_mul,generating] using
      FormalMultilinearSeries.ofScalars_sum_eq (moments u y) w
  rw [←he]
  exact p.analyticOnNhd z hze

private def primeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then ArithmeticFunction.vonMangoldt n else 0

private theorem primeCoefficient_nonneg (n : ℕ) : 0 ≤ primeCoefficient n := by
  unfold primeCoefficient
  split_ifs <;> positivity

private theorem primeCoefficient_summable {σ : ℝ} (hσ : 1<σ) :
    Summable (fun n => primeCoefficient n*zetaPrimeExpWeight σ n) := by
  apply summable_zetaPrimeExpWeight_mul _ (by simp [primeCoefficient])
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ)) (by simpa using hσ)).indicator {n | n.Prime}
  apply h.congr
  intro n
  by_cases hp : n.Prime <;>
    simp [Set.indicator,LSeries.term,primeCoefficient,hp]

private theorem moment_eq_tsum (u y : ℝ) (k : ℕ) :
    moments u y k = ∑' n, (u : ℂ)^(k+1)*(primeCoefficient n : ℂ)*
      zetaPrimeLogKernel k (center y) n := by
  unfold moments zetaOrdinaryPrimeLogMoment
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hp : n.Prime <;> simp [primeCoefficient,hp,mul_assoc]

/-- Exact ordinary-prime exponential generating identity in the Euler
half-plane. The double series is absolutely summable before it is exchanged. -/
theorem generating_eq_primeSeries {u y : ℝ} (hu : 0<u) {z : ℂ}
    (hz : u*‖z‖<1/2) :
    generating u y z = (u : ℂ)*zetaOrdinaryPrimeLogMoment 0 (center y-u*z) := by
  obtain ⟨q,hzq,hq⟩ := exists_between hz
  have hq0 : 0<q := lt_of_le_of_lt (mul_nonneg hu.le (norm_nonneg z)) hzq
  let f : ℕ → ℕ → ℂ := fun k n =>
    (u : ℂ)^(k+1)*(primeCoefficient n : ℂ)*zetaPrimeLogKernel k (center y) n*z^k
  let g : ℕ×ℕ → ℝ := fun kn =>
    (u*‖z‖/q)^kn.1*(u*(primeCoefficient kn.2*zetaPrimeExpWeight (3/2-q) kn.2))
  have hg : Summable g := by
    have hg0 (kn : ℕ×ℕ) : 0 ≤ g kn := by
      have hc := primeCoefficient_nonneg kn.2
      dsimp [g,zetaPrimeExpWeight]
      positivity
    apply (summable_prod_of_nonneg hg0).mpr
    refine ⟨fun k => ?_,?_⟩
    · exact ((primeCoefficient_summable (σ := 3/2-q) (by linarith)).mul_left u).mul_left
        ((u*‖z‖/q)^k)
    · simp only [g,tsum_mul_left]
      exact (summable_geometric_of_lt_one (by positivity)
        ((div_lt_one hq0).mpr hzq)).mul_right _
  have hfg (kn : ℕ×ℕ) : ‖f kn.1 kn.2‖ ≤ g kn := by
    dsimp [f,g]
    rw [norm_mul,norm_mul,norm_mul,norm_pow,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg hu.le,Complex.norm_real,
      Real.norm_of_nonneg (primeCoefficient_nonneg _)]
    have hk := norm_zetaPrimeLogKernel_le kn.1 (center y) kn.2 hq0
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk
        (mul_nonneg (pow_nonneg hu.le (kn.1+1)) (primeCoefficient_nonneg kn.2)))
      (pow_nonneg (norm_nonneg z) kn.1)
    apply hp.trans_eq
    rw [center_re]
    rw [div_pow,mul_pow,inv_pow,pow_succ]
    ring
  have hf : Summable (Function.uncurry f) := Summable.of_norm_bounded hg hfg
  have hn (n : ℕ) : ∑' k,f k n =
      (u : ℂ)*(primeCoefficient n : ℂ)*zetaPrimeFeature (center y-u*z) n := by
    have hex := (NormedSpace.expSeries_div_hasSum_exp
      ((u : ℂ)*z*(Real.log n : ℂ))).mul_left
      ((u : ℂ)*(primeCoefficient n : ℂ)*zetaPrimeFeature (center y) n)
    have he : (fun k => f k n) = fun k =>
        (u : ℂ)*(primeCoefficient n : ℂ)*zetaPrimeFeature (center y) n*
          (((u : ℂ)*z*(Real.log n : ℂ))^k/(k.factorial : ℂ)) := by
      funext k
      dsimp [f,zetaPrimeLogKernel]
      rw [mul_pow,mul_pow,pow_succ]
      ring
    rw [he,hex.tsum_eq]
    unfold zetaPrimeFeature
    rw [←Complex.exp_eq_exp_ℂ]
    rw [mul_assoc,←Complex.exp_add]
    congr 2
    ring
  unfold generating
  simp_rw [moment_eq_tsum,←tsum_mul_right]
  change (∑' k,∑' n,f k n)=_
  rw [←hf.tsum_comm]
  simp_rw [hn]
  unfold zetaOrdinaryPrimeLogMoment
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hp : n.Prime <;> simp [primeCoefficient,hp,zetaPrimeLogKernel,mul_assoc]

/-- Literal prime Dirichlet series on the real Euler segment. Outside
this segment the proof uses `generating_cleared`, not this series. -/
theorem generating_eq_prime_dirichlet {u y r : ℝ} (hu : 0<u) (hr : 0≤r)
    (hur : u*r<1/2) :
    generating u y r = (u : ℂ)*∑' p : ℕ,
      if p.Prime then (Real.log p : ℂ)/(p : ℂ)^(center y-(u : ℂ)*r) else 0 := by
  rw [generating_eq_primeSeries hu (by simpa [abs_of_nonneg hr] using hur)]
  congr 1
  unfold zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro p
  by_cases hp : p.Prime
  · simp only [hp,↓reduceIte,ArithmeticFunction.vonMangoldt_apply_prime hp,
      zetaPrimeLogKernel,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one]
    rw [zetaPrimeFeature,Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero),
      ←Complex.natCast_log,div_eq_mul_inv,←Complex.exp_neg]
    congr 2
    ring
  · simp [hp]

private theorem primeSeries_eq {s : ℂ} (hs : 1<s.re) :
    zetaOrdinaryPrimeLogMoment 0 s =
      -(logDeriv riemannZeta s+zetaProperPrimePowerSeries s) := by
  have h := (LSeriesHasSum_zetaMoebiusPrimeDerivative hs).neg
  have he : -(fun n => if n.Prime then zetaMoebiusDerivativeCoefficient n else 0)=
      fun n => (primeCoefficient n : ℂ) := by
    funext n
    by_cases hp : n.Prime <;>
      simp [primeCoefficient,zetaMoebiusDerivativeCoefficient,hp,
        ArithmeticFunction.moebius_apply_prime,ArithmeticFunction.vonMangoldt_apply_prime]
  rw [he] at h
  have ht := h.tsum_eq
  simp_rw [LSeries_term_eq_zetaPrimeFeature (fun n => (primeCoefficient n : ℂ))
    (by norm_num [primeCoefficient])] at ht
  rw [←ht]
  unfold zetaOrdinaryPrimeLogMoment
  apply tsum_congr
  intro n
  by_cases hp : n.Prime <;> simp [zetaPrimeLogKernel,
    primeCoefficient,hp]

/-- A pole-cleared analytic identity. It continues the generating series
across the Euler boundary without asserting prime-series convergence there. -/
theorem generating_cleared {u y : ℝ} (hu : 0<u) (hu1 : u<1) {l : ℂ}
    (ha : Tendsto (moments u y) atTop (𝓝 l)) {z : ℂ} (hz : ‖z‖<1) :
    let s := center y-(u : ℂ)*z
    (s-1)*riemannZeta₁ s*(generating u y z+(u : ℂ)*zetaProperPrimePowerSeries s)+
      (u : ℂ)*(s-1)*deriv riemannZeta₁ s-(u : ℂ)*riemannZeta₁ s=0 := by
  let s : ℂ → ℂ := fun z => center y-(u : ℂ)*z
  let F : ℂ → ℂ := fun z =>
    (s z-1)*riemannZeta₁ (s z)*
      (generating u y z+(u : ℂ)*zetaProperPrimePowerSeries (s z))+
      (u : ℂ)*(s z-1)*deriv riemannZeta₁ (s z)-(u : ℂ)*riemannZeta₁ (s z)
  have hs (w : ℂ) : AnalyticAt ℂ s w := by dsimp [s]; fun_prop
  have hpos {w : ℂ} (hw : w∈ball (0 : ℂ) 1) : 1/2<(s w).re := by
    have hw' : ‖w‖<1 := by simpa using hw
    have hre := Complex.re_le_norm w
    have hb : u*w.re<1 := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hre hu.le) (by nlinarith)
    simp only [s,Complex.sub_re,center_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    linarith
  have hF : AnalyticOnNhd ℂ F (ball 0 1) := by
    intro w hw
    have hg := (differentiable_riemannZeta₁.analyticAt (s w)).comp (hs w)
    have hd := (differentiable_riemannZeta₁.analyticAt (s w)).deriv.comp (hs w)
    have hQ := (analyticAt_zetaProperPrimePowerSeries (hpos hw)).comp (hs w)
    exact (((hs w).sub analyticAt_const).mul hg).mul
      ((analyticOnNhd_generating ha w hw).add (analyticAt_const.mul hQ)) |>.add
        ((analyticAt_const.mul ((hs w).sub analyticAt_const)).mul hd) |>.sub
        (analyticAt_const.mul hg)
  have hF0 : F =ᶠ[𝓝 0] (fun _ => 0) := by
    have hopen : IsOpen {w : ℂ | u*‖w‖<1/2} := isOpen_lt
      (continuous_const.mul continuous_norm) continuous_const
    filter_upwards [hopen.mem_nhds (by simp : u*‖(0 : ℂ)‖<1/2)] with w hw
    have he : 1<(s w).re := by
      have hb := mul_le_mul_of_nonneg_left (Complex.re_le_norm w) hu.le
      simp only [s,Complex.sub_re,center_re,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      linarith
    have h1 : s w≠1 := by intro hh; simp [hh] at he
    have hne := riemannZeta_ne_zero_of_one_lt_re he
    have hg := riemannZeta₁_ne_zero_of_one_le_re he.le
    have hp := neg_logDeriv_riemannZeta_eq_pole_sub h1 hne
    dsimp [F]
    rw [generating_eq_primeSeries hu hw,primeSeries_eq he]
    change (s w-1)*riemannZeta₁ (s w)*
      ((u : ℂ)*(-(logDeriv riemannZeta (s w)+zetaProperPrimePowerSeries (s w)))+
        (u : ℂ)*zetaProperPrimePowerSeries (s w))+
      (u : ℂ)*(s w-1)*deriv riemannZeta₁ (s w)-(u : ℂ)*riemannZeta₁ (s w)=0
    have halg : (u : ℂ)*(-(logDeriv riemannZeta (s w)+zetaProperPrimePowerSeries (s w)))+
        (u : ℂ)*zetaProperPrimePowerSeries (s w)=
        (u : ℂ)*(-logDeriv riemannZeta (s w)) := by ring
    rw [halg,hp,logDeriv_apply]
    field_simp [sub_ne_zero.mpr h1,hg]
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball (0 : ℂ) 1).isPreconnected (by simp) hF0 (by simpa using hz)

/-- The real radial approach from the safe center to the candidate point. -/
def path (u y : ℝ) (r : ℝ) : ℂ := center y-(u : ℂ)*(r : ℂ)

theorem tendsto_path (u y : ℝ) :
    Tendsto (path u y) (𝓝[<] 1) (𝓝 (candidate u y)) := by
  have h : Continuous (path u y) := by unfold path; fun_prop
  simpa [path,candidate] using (h.continuousAt (x := (1 : ℝ))).tendsto.mono_left
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)

theorem path_sub_candidate (u y r : ℝ) :
    path u y r-candidate u y=(u : ℂ)*(1-(r : ℂ)) := by
  unfold path candidate
  ring

private theorem tendsto_one_sub :
    Tendsto (fun r : ℝ => 1-(r : ℂ)) (𝓝[<] 1) (𝓝 (0 : ℂ)) := by
  simpa using ((tendsto_const_nhds (x := (1 : ℂ))).sub
    ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)))

private theorem boundary_regular_limits {u y : ℝ} (hu1 : u<1) :
    Tendsto (fun r => riemannZeta₁ (path u y r)) (𝓝[<] 1)
      (𝓝 (riemannZeta₁ (candidate u y))) ∧
    Tendsto (fun r => deriv riemannZeta₁ (path u y r)) (𝓝[<] 1)
      (𝓝 (deriv riemannZeta₁ (candidate u y))) ∧
    Tendsto (fun r => zetaProperPrimePowerSeries (path u y r)) (𝓝[<] 1)
      (𝓝 (zetaProperPrimePowerSeries (candidate u y))) := by
  have hg := differentiable_riemannZeta₁.analyticAt (candidate u y)
  exact ⟨hg.continuousAt.tendsto.comp (tendsto_path u y),
    hg.deriv.continuousAt.tendsto.comp (tendsto_path u y),
    (analyticAt_zetaProperPrimePowerSeries (by simp; linarith)).continuousAt.tendsto.comp
      (tendsto_path u y)⟩

private theorem source_forces_cleared_zero {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {l : ℂ} (ha : Tendsto (moments u y) atTop (𝓝 l)) (hl : l≠0) :
    (candidate u y-1)*riemannZeta₁ (candidate u y)=0 := by
  obtain ⟨hg,hd,hQ⟩ := boundary_regular_limits (y := y) hu1
  have hs := (tendsto_path u y).sub_const 1
  have hA := tendsto_abel_of_tendsto ha
  change Tendsto (fun r : ℝ => (1-(r : ℂ))*generating u y r) _ _ at hA
  have hB := ((hs.mul hg).mul (hQ.const_mul (u : ℂ))).add
    ((hs.const_mul (u : ℂ)).mul hd) |>.sub (hg.const_mul (u : ℂ))
  have hlim := ((hs.mul hg).mul hA).add (tendsto_one_sub.mul hB)
  have he : (fun r : ℝ => (path u y r-1)*riemannZeta₁ (path u y r)*
        ((1-(r : ℂ))*generating u y r)+(1-(r : ℂ))*
        ((path u y r-1)*riemannZeta₁ (path u y r)*
          ((u : ℂ)*zetaProperPrimePowerSeries (path u y r))+
          (u : ℂ)*(path u y r-1)*deriv riemannZeta₁ (path u y r)-
          (u : ℂ)*riemannZeta₁ (path u y r))) =ᶠ[𝓝[<] 1] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with r hr
    have hc := generating_cleared hu hu1 ha
      (z := (r : ℂ)) (by simpa [abs_of_pos hr.1] using hr.2)
    change (path u y r-1)*riemannZeta₁ (path u y r)*
      (generating u y r+(u : ℂ)*zetaProperPrimePowerSeries (path u y r))+
      (u : ℂ)*(path u y r-1)*deriv riemannZeta₁ (path u y r)-
      (u : ℂ)*riemannZeta₁ (path u y r)=0 at hc
    linear_combination (1-(r : ℂ))*hc
  have h0 := tendsto_nhds_unique (hlim.congr' he) tendsto_const_nhds
  simp only [zero_mul,add_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_right hl

/-- A negative coherent source cannot be zeta's positive pole at one. -/
theorem candidate_ne_one_of_source {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {m : ℕ} (hm : 0<m) (ha : Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    candidate u y≠1 := by
  intro h1
  obtain ⟨hg,hd,hQ⟩ := boundary_regular_limits (y := y) hu1
  have hp := tendsto_path u y
  have hA := (tendsto_abel_of_tendsto ha).const_mul (u : ℂ)
  change Tendsto (fun r : ℝ => (u : ℂ)*((1-(r : ℂ))*generating u y r)) _ _ at hA
  have hs := hp.sub_const 1
  have hlim := (hg.mul hA).add ((hs.mul hg).mul (hQ.const_mul (u : ℂ))) |>.add
    ((hs.const_mul (u : ℂ)).mul hd) |>.sub (hg.const_mul (u : ℂ))
  have he : (fun r : ℝ => riemannZeta₁ (path u y r)*
        ((u : ℂ)*((1-(r : ℂ))*generating u y r))+
        (path u y r-1)*riemannZeta₁ (path u y r)*
          ((u : ℂ)*zetaProperPrimePowerSeries (path u y r))+
        (u : ℂ)*(path u y r-1)*deriv riemannZeta₁ (path u y r)-
        (u : ℂ)*riemannZeta₁ (path u y r)) =ᶠ[𝓝[<] 1] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with r hr
    have hc := generating_cleared hu hu1 ha
      (z := (r : ℂ)) (by simpa [abs_of_pos hr.1] using hr.2)
    have hsub : path u y r-1=(u : ℂ)*(1-(r : ℂ)) := by
      simpa only [h1] using path_sub_candidate u y r
    change (path u y r-1)*riemannZeta₁ (path u y r)*
      (generating u y r+(u : ℂ)*zetaProperPrimePowerSeries (path u y r))+
      (u : ℂ)*(path u y r-1)*deriv riemannZeta₁ (path u y r)-
      (u : ℂ)*riemannZeta₁ (path u y r)=0 at hc
    linear_combination hc-riemannZeta₁ (path u y r)*generating u y r*hsub
  have h0 := tendsto_nhds_unique (hlim.congr' he) tendsto_const_nhds
  simp only [h1,riemannZeta₁_one,sub_self,one_mul,zero_mul,mul_zero,add_zero] at h0
  have hu0 : (u : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hm0 : (0 : ℝ)<m := by exact_mod_cast hm
  have heq : -(m : ℂ)=1 := by
    apply mul_left_cancel₀ hu0
    linear_combination h0
  have := congrArg Complex.re heq
  norm_num at this
  linarith

/-- Coherence forces a genuine nontrivial zero, with no exposure or
Riesz hypothesis. The proper powers are analytic because `u<1`. -/
theorem isNontrivialZetaZero_of_tendsto {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {m : ℕ} (hm : 0<m) (ha : Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    IsNontrivialZetaZero (candidate u y) := by
  have h1 := candidate_ne_one_of_source hu hu1 hm ha
  have hc := source_forces_cleared_zero hu hu1 ha
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne'))
  have hg := (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr h1)
  exact isNontrivialZetaZero_of_poleRemoved_eq_zero (by simp; linarith) hg

/-- The continued prime series has exactly the zeta logarithmic residue
along the approach to its candidate zero. -/
theorem tendsto_logDeriv_source {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {m : ℕ} (hm : 0<m) (ha : Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    Tendsto (fun r : ℝ => (path u y r-candidate u y)*
      (-logDeriv riemannZeta (path u y r))) (𝓝[<] 1) (𝓝 (-(m : ℂ))) := by
  let rho : NontrivialZetaZero := ⟨candidate u y,isNontrivialZetaZero_of_tendsto hu hu1 hm ha⟩
  have hp : Tendsto (path u y) (𝓝[<] 1) (𝓝[≠] rho.1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_path u y,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r (hr : r<1)
    change path u y r≠candidate u y
    intro he
    have hh := path_sub_candidate u y r
    rw [he,sub_self] at hh
    have hh' := congrArg Complex.re hh
    simp only [Complex.zero_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,
      zero_mul,sub_zero] at hh'
    nlinarith
  have hf := analyticAt_riemannZeta_nontrivialZero rho
  have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hz : ∀ᶠ s in 𝓝[≠] rho.1, riemannZeta s≠0 :=
    hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun he => hfinite (analyticOrderAt_eq_top.mpr he))
  have h1 : ∀ᶠ s in 𝓝[≠] rho.1, s≠1 :=
    (eventually_ne_nhds rho.2.2.2).filter_mono nhdsWithin_le_nhds
  have hQ := (boundary_regular_limits (y := y) hu1).2.2
  have hlim := (tendsto_abel_of_tendsto ha).add
    ((tendsto_one_sub.mul hQ).const_mul (u : ℂ))
  simp only [zero_mul,mul_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hp.eventually hz,hp.eventually h1,
    Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with r hzr h1r hr
  have hc := generating_cleared hu hu1 ha
    (z := (r : ℂ)) (by simpa [abs_of_pos hr.1] using hr.2)
  change (path u y r-1)*riemannZeta₁ (path u y r)*
    (generating u y r+(u : ℂ)*zetaProperPrimePowerSeries (path u y r))+
    (u : ℂ)*(path u y r-1)*deriv riemannZeta₁ (path u y r)-
    (u : ℂ)*riemannZeta₁ (path u y r)=0 at hc
  have hg : riemannZeta₁ (path u y r)≠0 := by
    rw [riemannZeta₁_eq_sub_one_mul h1r]
    exact mul_ne_zero (sub_ne_zero.mpr h1r) hzr
  have he : generating u y r+(u : ℂ)*zetaProperPrimePowerSeries (path u y r)=
      (u : ℂ)*(-logDeriv riemannZeta (path u y r)) := by
    rw [neg_logDeriv_riemannZeta_eq_pole_sub h1r hzr,logDeriv_apply]
    apply (mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr h1r) hg))
    field_simp [sub_ne_zero.mpr h1r,hg]
    linear_combination hc
  change (1-(r : ℂ))*generating u y r+
    (u : ℂ)*((1-(r : ℂ))*zetaProperPrimePowerSeries (path u y r))=_
  rw [path_sub_candidate]
  linear_combination (1-(r : ℂ))*he

/-- The assumed negative integer limit identifies the actual analytic
multiplicity, not a synthetically assigned zero weight. Exposure is absent. -/
theorem multiplicity_eq_of_tendsto (rho : NontrivialZetaZero) {u y : ℝ}
    (hu : 0<u) (hu1 : u<1) (hrho : rho.1=candidate u y)
    {m : ℕ} (hm : 0<m) (ha : Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    analyticZetaZeroMultiplicity rho=m := by
  have hp : Tendsto (path u y) (𝓝[<] 1) (𝓝[≠] rho.1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [hrho] using tendsto_path u y,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r (hr : r<1)
    change path u y r≠rho.1
    rw [hrho]
    intro he
    have hh := path_sub_candidate u y r
    rw [he,sub_self] at hh
    have hh' := congrArg Complex.re hh
    simp only [Complex.zero_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,
      zero_mul,sub_zero] at hh'
    nlinarith
  have hres := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg.comp hp
  have hgiven := tendsto_logDeriv_source hu hu1 hm ha
  have hres' : Tendsto (fun r => (path u y r-candidate u y)*
      (-logDeriv riemannZeta (path u y r))) (𝓝[<] 1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
    simpa only [hrho,analyticZetaZeroMultiplicity,Function.comp_def,mul_neg] using hres
  have he := neg_injective (tendsto_nhds_unique hres' hgiven)
  exact_mod_cast he

/-- Terminal converse: an actual zero at the specified coordinate with
exactly the integer multiplicity recovered from prime-moment coherence. -/
theorem exists_zero_multiplicity_of_tendsto {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {m : ℕ} (hm : 0<m) (ha : Tendsto (moments u y) atTop (𝓝 (-(m : ℂ)))) :
    ∃ rho : NontrivialZetaZero, rho.1=candidate u y ∧ analyticZetaZeroMultiplicity rho=m := by
  let rho : NontrivialZetaZero := ⟨candidate u y,isNontrivialZetaZero_of_tendsto hu hu1 hm ha⟩
  exact ⟨rho,rfl,multiplicity_eq_of_tendsto rho hu hu1 rfl hm ha⟩

end RiemannGaussian.ZetaPrimeMomentCoherence
