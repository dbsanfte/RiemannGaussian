/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSelbergControlAudit
import RiemannGaussian.SuzukiConvolutionSource
import RiemannGaussian.ZetaExposedPrimeFilter
import RiemannGaussian.ZetaSignedPoleControl
import RiemannGaussian.HarmonicProductContinuity

/-!
# Signed Selberg source and the unit-prime collapse gate

The COMPLETE signed word `Lambda log - Lambda * Lambda` has double-zero
source `-m-m^2`, including simple zeros. Multiplication by `s-1` removes
its density pole without removing that source. Its exact factorial
convolution has the same source law for ANY coherent moment array.
In particular the genuine unit-prime Euler control passes this gate.

This freezes convolution/support/positivity-only estimation of this
complete word. The unaltered Mobius/Gamma constraint, physical-mask
completion and actual signed distinct-prime inequalities remain open.
-/

namespace RiemannGaussian.ArithmeticOperatorSelbergSourceAudit
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical
open ArithmeticOperatorSelbergControlAudit

/-- The prime-minus-pair Euler response; the sign is not the simple-zero
cancelling PLUS Selberg word. -/
def response (s : ℂ) : ℂ :=
  deriv (logDeriv riemannZeta) s-(logDeriv riemannZeta s)^2

/-- Genuine convergent Euler series, retaining all powers and phases. -/
theorem response_euler {s : ℂ} (hs : 1<s.re) :
    LSeriesHasSum (selbergWord (-1) mangoldt) s (response s) := by
  have h := (LSeriesHasSum_vonMangoldt_center 0 hs).sub
    (LSeriesHasSum_zetaPrimePairArithmetic hs)
  convert h using 1
  · funext n
    simp [selbergWord_minus_mangoldt]
  · simp [response]

/-- Local source from the ACTUAL divisor, not a synthetic linear-mode
inference for a masked nonlinear statistic. -/
theorem actual_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s => (s-rho.1)^2*response s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)-
        (analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  have hlin := AnalyticAt.tendsto_logarithmicPrime_source
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
    (w := fun _ => 1) (r := fun _ => 0) (v := 1) (b := 0)
    tendsto_const_nhds (by simp)
  have hsq := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).pow 2
  convert hlin.sub hsq using 1
  · funext s
    simp only [response]
    ring
  · simp [analyticZetaZeroMultiplicity]

/-- The pole-clearing factor retains a nonzero source at every actual
nontrivial zero, with its entire analytic multiplicity. -/
theorem actual_centered_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s => (s-rho.1)^2*((s-1)*response s)) (𝓝[≠] rho.1)
      (𝓝 ((rho.1-1)*(-(analyticZetaZeroMultiplicity rho : ℂ)-
        (analyticZetaZeroMultiplicity rho : ℂ)^2))) := by
  have hs : Tendsto (fun s : ℂ => s-1) (𝓝[≠] rho.1) (𝓝 (rho.1-1)) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  convert hs.mul (actual_zero_source rho) using 1
  funext s
  ring

theorem centered_zero_source_ne_zero (rho : NontrivialZetaZero) :
    (rho.1-1)*(-(analyticZetaZeroMultiplicity rho : ℂ)-
      (analyticZetaZeroMultiplicity rho : ℂ)^2) ≠ 0 := by
  apply mul_ne_zero (sub_ne_zero.mpr rho.2.2.2)
  have hm := analyticZetaZeroMultiplicity_positive rho
  have hr : (0 : ℝ)<analyticZetaZeroMultiplicity rho := by exact_mod_cast hm
  have hn : -((analyticZetaZeroMultiplicity rho : ℝ))-
      (analyticZetaZeroMultiplicity rho : ℝ)^2≠0 := by nlinarith [sq_nonneg (analyticZetaZeroMultiplicity rho : ℝ)]
  exact_mod_cast hn

/-- The density pole is removed as an ACTUAL local analytic germ. The
regular cross-term is retained; cancelling only its double pole is not enough. -/
theorem centered_response_analytic_at_pole :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E 1 ∧
      (fun s => (s-1)*response s) =ᶠ[𝓝[≠] (1 : ℂ)] E := by
  let H : ℂ → ℂ := logDeriv riemannZeta₁
  have hH : AnalyticAt ℂ H 1 := by
    exact ((differentiable_riemannZeta₁).analyticAt 1).deriv.div
      ((differentiable_riemannZeta₁).analyticAt 1) (by simp)
  have hne : ∀ᶠ s in 𝓝 (1 : ℂ), riemannZeta₁ s≠0 :=
    (differentiable_riemannZeta₁ 1).continuousAt.eventually_ne (by simp)
  have he : logDeriv riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => -1/(s-1)+H s := by
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with s hns (hs : s≠1)
    have hz : riemannZeta s≠0 := by
      rw [riemannZeta_eq_inv_sub_mul hs]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs)) hns
    have h := neg_logDeriv_riemannZeta_eq_pole_sub hs hz
    dsimp [H]
    linear_combination -h
  refine ⟨fun s => 2*H s+(s-1)*(deriv H s-(H s)^2),
    (analyticAt_const.mul hH).add ((analyticAt_id.sub analyticAt_const).mul
      (hH.deriv.sub (hH.pow 2))),?_⟩
  filter_upwards [he,he.nhdsNE_deriv,
    hH.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with s hs hds hHs (hs1 : s≠1)
  have hd := ((hasDerivAt_const s (-1 : ℂ)).fun_div
    ((hasDerivAt_id s).sub_const 1) (sub_ne_zero.mpr hs1)).fun_add
      hHs.differentiableAt.hasDerivAt
  have hd' : deriv (logDeriv riemannZeta) s = 1/(s-1)^2+deriv H s := by
    rw [hds]
    simpa only [id_eq,zero_mul,mul_one,zero_sub,neg_neg] using hd.deriv
  rw [response,hd',hs]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- The complete factorial pair convolution retains every endpoint. -/
def convolutionAverage (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ k∈Finset.range (N+1),a k*a (N-k))/((N+1 : ℕ) : ℂ)

/-- Signed complete derivative-minus-square coefficient. -/
def signedTrace (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  a (N+1)-convolutionAverage a N

/-- Exact complete Taylor coefficient of the signed arithmetic word.
This does not complete or alter ANY physical-mask carrier. -/
theorem response_moment {s : ℂ} (hs : 1<s.re) (N : ℕ) :
    signedTaylorMoment N response s=
      ((N+1 : ℕ) : ℂ)*zetaPrimeLogMoment (N+1) s-
        ∑ k∈Finset.range (N+1),zetaPrimeLogMoment k s*zetaPrimeLogMoment (N-k) s := by
  have hs1 : s≠1 := by intro h; simp [h] at hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hf : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    (analyticOn_riemannZeta s (by simpa using hs1)).deriv.div
      (analyticOn_riemannZeta s (by simpa using hs1)) hz
  have hneg (k : ℕ) : signedTaylorMoment k (logDeriv riemannZeta) s=
      -zetaPrimeLogMoment k s := by
    have hh := iteratedDeriv_neg k (logDeriv riemannZeta) s
    change iteratedDeriv k (fun z => -logDeriv riemannZeta z) s=
      -iteratedDeriv k (logDeriv riemannZeta) s at hh
    simp only [zetaPrimeLogMoment,signedTaylorMoment,hh]
    ring
  have hsquare : signedTaylorMoment N (fun z => (logDeriv riemannZeta z)^2) s=
      ∑ k∈Finset.range (N+1),zetaPrimeLogMoment k s*zetaPrimeLogMoment (N-k) s := by
    simp only [pow_two]
    rw [signedTaylorMoment_mul hf hf]
    simp_rw [hneg,neg_mul_neg]
  unfold response
  rw [signedTaylorMoment_sub N (f := deriv (logDeriv riemannZeta))
    (g := fun z => (logDeriv riemannZeta z)^2) hf.deriv (hf.pow 2),
    signedTaylorMoment_deriv,hneg,hsquare]
  ring

/-- Every moment on the Euler half-plane is the GENUINELY CONVERGENT
literal prime-minus-pair series, including its factorial and phase. -/
theorem response_moment_hasSum {s : ℂ} (hs : 1<s.re) (N : ℕ) :
    HasSum (fun n => selbergWord (-1) mangoldt n*zetaPrimeLogKernel N s n)
      (signedTaylorMoment N response s) := by
  have hb : LSeries.abscissaOfAbsConv (selbergWord (-1) mangoldt)≤1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    intro x hx
    exact (response_euler (s := x) (by simpa using hx)).LSeriesSummable
  have he : response =ᶠ[𝓝 s] LSeries (selbergWord (-1) mangoldt) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (response_euler hz).LSeries_eq.symm
  rw [signedTaylorMoment_congr N he]
  simpa only [zetaPrimeLogKernel,mul_assoc] using
    hasSum_signedTaylorMoment_LSeries (selbergWord (-1) mangoldt)
      (by simp [selbergWord,convolution,mangoldt]) (lt_of_le_of_lt hb (by exact_mod_cast hs)) N

/-- Full factorial joining identifies the normalized COMPLETE trace.
Neither a native mask nor an unpaid completion error is silently replaced. -/
theorem scaled_response_moment_eq_trace (u : ℂ) {s : ℂ} (hs : 1<s.re) (N : ℕ) :
    u^(N+2)*signedTaylorMoment N response s/((N+1 : ℕ) : ℂ)=
      signedTrace (fun k => u^(k+1)*zetaPrimeLogMoment k s) N := by
  have hsum : (∑ k∈Finset.range (N+1),
      (u^(k+1)*zetaPrimeLogMoment k s)*(u^(N-k+1)*zetaPrimeLogMoment (N-k) s))=
      u^(N+2)*(∑ k∈Finset.range (N+1),zetaPrimeLogMoment k s*zetaPrimeLogMoment (N-k) s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k≤N := by simpa using Finset.mem_range.mp hk
    have he : u^(k+1)*u^(N-k+1)=u^(N+2) := by
      rw [←pow_add]
      congr 1
      omega
    calc
      _ = (u^(k+1)*u^(N-k+1))*(zetaPrimeLogMoment k s*zetaPrimeLogMoment (N-k) s) := by ring
      _ = _ := by rw [he]
  rw [response_moment hs,signedTrace,convolutionAverage,hsum]
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp [hn]

theorem convolutionAverage_constant (ell : ℂ) (N : ℕ) :
    convolutionAverage (fun _ => ell) N=ell^2 := by
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  simp only [convolutionAverage,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp [hn]

/-- Quantitative finite continuity is used to transfer a source, not to
claim an independent bound on the actual-prime arithmetic. -/
theorem norm_convolutionAverage_sub_square_le (a : ℕ → ℂ) (ell : ℂ)
    {C : ℝ} (ha : ∀ k, ‖a k‖≤C) (hell : ‖ell‖≤C) (N : ℕ) :
    ‖convolutionAverage a N-ell^2‖≤
      2*C*((((N+1 : ℕ) : ℝ))⁻¹*∑ k∈Finset.range (N+1),‖a k-ell‖) := by
  have hterms k : ‖a k*a (N-k)-ell^2‖≤C*(‖a k-ell‖+‖a (N-k)-ell‖) :=
    HarmonicProductContinuity.norm_product_sub_square (ha (N-k)) hell
  have href : (∑ k∈Finset.range (N+1),‖a (N-k)-ell‖)=
      ∑ k∈Finset.range (N+1),‖a k-ell‖ := by
    simpa using Finset.sum_range_reflect (fun k => ‖a k-ell‖) (N+1)
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  have he : convolutionAverage a N-ell^2=
      (∑ k∈Finset.range (N+1),(a k*a (N-k)-ell^2))/((N+1 : ℕ) : ℂ) := by
    simp only [convolutionAverage,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_range,nsmul_eq_mul]
    field_simp [hn]
  rw [he,norm_div,Complex.norm_natCast]
  calc
    _ ≤ (∑ k∈Finset.range (N+1),C*(‖a k-ell‖+‖a (N-k)-ell‖))/((N+1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun k _ => hterms k))) (Nat.cast_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib,href]; ring

/-- Any complete coherent array has the same quadratic source. -/
theorem convolutionAverage_tendsto {a : ℕ → ℂ} {ell : ℂ}
    (ha : Tendsto a atTop (𝓝 ell)) :
    Tendsto (convolutionAverage a) atTop (𝓝 (ell^2)) := by
  obtain ⟨B,hB,hab⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  let C : ℝ := B+‖ell‖
  have hac k : ‖a k‖≤C := by
    have h := hab (a k) (Set.mem_range_self k)
    dsimp [C]
    linarith [norm_nonneg ell]
  have hc : ‖ell‖≤C := by dsimp [C]; linarith
  have he : Tendsto (fun k => ‖a k-ell‖) atTop (𝓝 0) := by
    simpa using (ha.sub_const ell).norm
  have havg := he.cesaro.comp (tendsto_add_atTop_nat 1)
  have hb := havg.const_mul (2*C)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => norm_convolutionAverage_sub_square_le a ell hac hc N)
  simpa only [Function.comp_def,mul_zero] using hb

theorem signedTrace_tendsto {a : ℕ → ℂ} {ell : ℂ}
    (ha : Tendsto a atTop (𝓝 ell)) :
    Tendsto (signedTrace a) atTop (𝓝 (ell-ell^2)) :=
  (ha.comp (tendsto_add_atTop_nat 1)).sub (convolutionAverage_tendsto ha)

/-- Coefficient action of the SAME pole-clearing affine symbol. -/
def centeredTrace (c u : ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  c*(1+(((N+1 : ℕ) : ℂ))⁻¹)*signedTrace a (N+1)-u*signedTrace a N

/-- The actual pole-clearing operation does not remove a coherent zero
source. This statement needs no exposure or arithmetic approximation. -/
theorem centeredTrace_tendsto (c u : ℂ) {a : ℕ → ℂ} {ell : ℂ}
    (ha : Tendsto a atTop (𝓝 ell)) :
    Tendsto (centeredTrace c u a) atTop (𝓝 ((c-u)*(ell-ell^2))) := by
  have hi : Tendsto (fun N : ℕ => (((N+1 : ℕ) : ℂ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have ht := signedTrace_tendsto ha
  have h := ((tendsto_const_nhds (x := c)).mul
    ((tendsto_const_nhds (x := (1 : ℂ))).add hi)).mul
      (ht.comp (tendsto_add_atTop_nat 1)) |>.sub ((tendsto_const_nhds (x := u)).mul ht)
  convert h using 1
  · rfl
  · ring

/-- The pure density factorial array is cancelled EXACTLY, at every
order, before any absolute estimate. -/
theorem signedTrace_geometric (q : ℂ) (N : ℕ) :
    signedTrace (fun k => q^(k+1)) N=0 := by
  have he : ∀ k∈Finset.range (N+1),q^(k+1)*q^(N-k+1)=q^(N+2) := by
    intro k hk
    have hkn : k≤N := by simpa using Finset.mem_range.mp hk
    rw [←pow_add]
    congr 1
    omega
  simp only [signedTrace,convolutionAverage,Finset.sum_congr rfl he,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn : ((N+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp [hn]
  ring

theorem centeredTrace_geometric (c u q : ℂ) (N : ℕ) :
    centeredTrace c u (fun k => q^(k+1)) N=0 := by
  simp [centeredTrace,signedTrace_geometric]

/-- The already-proved actual exposed prime source passes the same
complete factorial quadratic with EVERY analytic multiplicity. -/
theorem actual_exposed_trace_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Tendsto (signedTrace (fun k => ((3/2-rho.1.re : ℝ) : ℂ)^(k+1)*
      zetaPrimeLogMoment k (3/2+Complex.I*(rho.1.im : ℂ)))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)-
        (analyticZetaZeroMultiplicity rho : ℂ)^2)) := by
  have ha := ZetaExposedPrimeFilter.tendsto_primeFilter_one_exposed rho hrho hexposed
  have hfilter (k : ℕ) : zetaPrimeLogFilter 1 k (3/2+Complex.I*(rho.1.im : ℂ))=
      zetaPrimeLogMoment k (3/2+Complex.I*(rho.1.im : ℂ)) := by
    change (∑ i∈(Polynomial.C (1 : ℂ)).support,
      (Polynomial.C (1 : ℂ)).coeff i*zetaPrimeLogMoment (k+i) _) = _
    rw [Polynomial.support_C (one_ne_zero : (1 : ℂ)≠0)]
    simp
  simp_rw [hfilter] at ha
  simpa using signedTrace_tendsto ha

/-- The exact UNIT-prime Euler control passes this source gate too. -/
theorem unit_control_trace_source :
    Tendsto (signedTrace (fun k => ((10001/20000 : ℝ) : ℂ)^(k+1)*∑' n,
      ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*
        (ArithmeticFunction.vonMangoldt n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*54) n))
      atTop (𝓝 (-6)) := by
  convert signedTrace_tendsto ArithmeticOperatorBinaryEulerControl.euler_control_source using 1
  norm_num

/-- Support, positive complete convolution and the source gate do not
give a decay theorem: the literal unit-Euler control is a counterexample. -/
theorem unit_control_trace_not_zero :
    ¬Tendsto (signedTrace (fun k => ((10001/20000 : ℝ) : ℂ)^(k+1)*∑' n,
      ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*
        (ArithmeticFunction.vonMangoldt n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*54) n))
      atTop (𝓝 0) := by
  intro hh
  have h := tendsto_nhds_unique unit_control_trace_source hh
  norm_num at h

/-- The pole-centered complete word still detects the coherent unit
Euler control. Its source is nonzero; pole centering alone adds no
independent restriction on the actual prime sequence. -/
theorem unit_control_centered_trace_source :
    Tendsto (centeredTrace (1/2+Complex.I*54) (10001/20000)
      (fun k => ((10001/20000 : ℝ) : ℂ)^(k+1)*∑' n,
        ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*
          (ArithmeticFunction.vonMangoldt n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*54) n))
      atTop (𝓝 ((1/2+Complex.I*54-(10001/20000 : ℂ))*(-6))) := by
  convert centeredTrace_tendsto (1/2+Complex.I*54) (10001/20000)
    ArithmeticOperatorBinaryEulerControl.euler_control_source using 1
  norm_num

theorem unit_control_centered_trace_not_zero :
    ¬Tendsto (centeredTrace (1/2+Complex.I*54) (10001/20000)
      (fun k => ((10001/20000 : ℝ) : ℂ)^(k+1)*∑' n,
        ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*
          (ArithmeticFunction.vonMangoldt n : ℂ)*zetaPrimeLogKernel k (3/2+Complex.I*54) n))
      atTop (𝓝 0) := by
  intro hh
  have h := congrArg Complex.im (tendsto_nhds_unique unit_control_centered_trace_source hh)
  norm_num [Complex.mul_im,Complex.add_im,Complex.sub_im] at h

end
end RiemannGaussian.ArithmeticOperatorSelbergSourceAudit
