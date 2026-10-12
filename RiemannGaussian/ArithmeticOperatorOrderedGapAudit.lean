/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorOrderedGapGeometry
import RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit

/-!
# One-step native ordered gaps: source and whole-mask collapse audit

The denominator dictionary is proved from actual reduced fractions and
their literal no-intermediate-fraction condition. Complete native gap
COUNT is exactly the old totient prefix; its phased increments retain
every actual zero multiplicity, with the density pole separable.

EVERY joined complex two-denominator mask is kept before the Mobius sum
is reindexed. Its arbitrary-inverse-array counterpart is one signed
scalar kernel. Free arrays are NOT granted actual rational adjacency,
Gamma observations or generalized-prime arithmetic. Native unsmoothed
count norm payment is false beyond every head. Prescribed signed/mixed
gap constraints, higher correlations and boundary-aware smoothing remain
separate open candidates; no RH-strength estimate is proved here.
-/

namespace RiemannGaussian.ArithmeticOperatorOrderedGapAudit
noncomputable section
open Complex Filter Topology
open ArithmeticOperatorOrderedGapGeometry ArithmeticOperatorGcdAudit
open ArithmeticOperatorMoebiusCoprimeAudit SuzukiCarryCorrelation
open scoped BigOperators Classical

/-- Complete literal adjacent-denominator sum. W may include both
original phases, hard masks, prime qualities and factorial/radial weights. -/
def pairs (N : ℕ) (W : ℕ → ℕ → ℂ) : ℂ :=
  ∑ q∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,
    if N<q+r ∧ q.Coprime r then W q r else 0

/-- Arbitrary inverse-weight control for the collapse audit ONLY.
It is not an actual Farey walk unless the column is actual Mobius. -/
def freePairs (N : ℕ) (w : ℕ → ℂ) (W : ℕ → ℕ → ℂ) : ℂ :=
  ∑ q∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,
    if N<q+r then W q r*gcdKernel w q r else 0

/-- The entire structured mask remains at its ORIGINAL physical pair,
including the strict sloping boundary and both divisor incidences. -/
def joinedKernel (N : ℕ) (W : ℕ → ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ q∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,
    if N<q+r ∧ d∣q ∧ d∣r then W q r else 0

/-- Exact actual-Mobius specialization. Every diagonal, unit endpoint
and nonsquarefree denominator is retained. -/
theorem pairs_eq_actual_inverse (N : ℕ) (W : ℕ → ℕ → ℂ) :
    pairs N W=freePairs N (column 0) W := by
  unfold pairs freePairs
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  rw [untwisted_entry]
  by_cases h : N<q+r <;> by_cases hc : q.Coprime r <;> simp [h,hc]

/-- ALL native masks and correlated weights are joined before any
estimate. The same algebra holds for a free inverse array, without
asserting that array has actual primitive counts or Gamma data. -/
theorem freePairs_eq_scalar (N : ℕ) (w : ℕ → ℂ) (W : ℕ → ℕ → ℂ) :
    freePairs N w W=∑ d∈Finset.Icc 1 N,w d*joinedKernel N W d := by
  have hterm (q : ℕ) (hq : q∈Finset.Icc 1 N)
      (r : ℕ) :
      (if N<q+r then W q r*gcdKernel w q r else 0)=
        ∑ d∈Finset.Icc 1 N,w d*(if N<q+r ∧ d∣q ∧ d∣r then W q r else 0) := by
    rw [gcdKernel_eq_incidence (Finset.mem_Icc.mp hq).1
      (Finset.mem_Icc.mp hq).2 w]
    by_cases ht : N<q+r
    · rw [ite_eq_left ht,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [divisorFeature]
      by_cases hq' : d∣q <;> by_cases hr' : d∣r <;> simp [ht,hq',hr']
      ring
    · simp [ht]
  have he : freePairs N w W=
      ∑ q∈Finset.Icc 1 N,∑ d∈Finset.Icc 1 N,∑ r∈Finset.Icc 1 N,
        w d*(if N<q+r ∧ d∣q ∧ d∣r then W q r else 0) := by
    unfold freePairs
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_congr rfl (fun r _ => hterm q hq r),Finset.sum_comm]
  rw [he,Finset.sum_comm]
  simp only [joinedKernel,Finset.mul_sum]

/-- The ENTIRE free-array signed bound is equivalent to a ZERO joined
kernel. Geometry/reindexing alone adds no uniform source-scale estimate. -/
theorem free_bound_iff (N : ℕ) (W : ℕ → ℕ → ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ,‖freePairs N w W‖≤B) ↔
      0≤B ∧ ∀ d∈Finset.Icc 1 N,joinedKernel N W d=0 := by
  simp only [freePairs_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

/-- Number of actual unique adjacent gaps, from the proved native chart. -/
def count (N : ℕ) : ℂ := pairs N (fun _ _ => 1)

/-- For each first denominator the second denominator runs through
exactly ONE complete residue period. All sloping-boundary endpoints stay. -/
theorem row_count {N q : ℕ} (hq : q∈Finset.Icc 1 N) :
    (∑ r∈Finset.Icc 1 N,if N<q+r ∧ q.Coprime r then (1 : ℂ) else 0)=q.totient := by
  obtain ⟨hq0,hqN⟩ := Finset.mem_Icc.mp hq
  have he : (Finset.Icc 1 N).filter (fun r => N<q+r ∧ q.Coprime r)=
      (Finset.Ico (N-q+1) (N+1)).filter (fun r => q.Coprime r) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ico]
    omega
  have hs : N-q+1+q=N+1 := by omega
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one,he,←hs,
    Nat.filter_coprime_Ico_eq_totient]

/-- Native order has not supplied a new count constraint: this is
EXACTLY the old actual totient prefix, not an asymptotic. -/
theorem count_eq_totient_prefix (N : ℕ) :
    count N=∑ q∈Finset.Icc 1 N,(q.totient : ℂ) := by
  unfold count pairs
  exact Finset.sum_congr rfl (fun q hq => row_count hq)

theorem count_step (N : ℕ) : count (N+1)-count N=(N+1).totient := by
  rw [count_eq_totient_prefix,count_eq_totient_prefix,
    Finset.sum_Icc_succ_top (by omega)]
  ring

/-- Matched phase stays on each literal NATIVE cutoff increment. -/
def increment (y : ℝ) (n : ℕ) : ℂ := (count n-count (n-1))*primePhase y n

theorem increment_eq (y : ℝ) (n : ℕ) :
    increment y n=(n.totient : ℂ)*primePhase y n := by
  cases n with
  | zero => simp [increment,count,pairs]
  | succ n => simpa only [increment,Nat.add_sub_cancel] using
      congrArg (fun z : ℂ => z*primePhase y (n+1)) (count_step n)

private theorem shell_zero_eq (n : ℕ) : shell 0 n=2*(n.totient : ℂ) := by
  by_cases hn : n=0
  · simp [hn,shell]
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n : ℕ => (n.totient : ℂ)) (g := fun n : ℕ => (n : ℂ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n) n (Nat.pos_of_ne_zero hn)
  have hc : column 0=mu := by funext d; simp [column,primePhase]
  rw [shell,hc,LSeries.convolution_def]
  calc
    _ = 2*∑ da∈n.divisorsAntidiagonal,(ArithmeticFunction.moebius da.1 : ℂ)*(da.2 : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by simp only [twoIndex,mu]; ring)
    _ = _ := by rw [hi]

/-- Exact complete response of native increments. The defining series
is asserted only on Re(s)>2; all proper denominator powers remain. -/
def countResponse (z : ℂ) : ℂ := riemannZeta (z-1)/riemannZeta z

theorem increment_euler_response (y : ℝ) {s : ℂ} (hs : 2<s.re) :
    LSeries (increment y) s=countResponse (s+I*y) := by
  have he : increment y=fun n => ((1/2 : ℂ)*shell 0 n)*primePhase y n := by
    funext n
    rw [increment_eq,shell_zero_eq]
    ring
  rw [he,ArithmeticOperatorGammaTwistAudit.LSeries_primePhase]
  have hscale : (fun n => (1/2 : ℂ)*shell 0 n)=(1/2 : ℂ) • shell 0 := rfl
  rw [hscale,LSeries_smul,euler_response 0 (by simpa using hs)]
  simp only [response,countResponse,ofReal_zero,mul_zero,sub_zero,add_zero]
  ring

private theorem numerator_ne_zero (rho : NontrivialZetaZero) :
    riemannZeta (rho.1-1)≠0 := by
  intro hz
  let tau : NontrivialZetaZero := ⟨rho.1-1,hz,by
    rintro ⟨n,hn⟩
    have he := congrArg Complex.re hn
    norm_num [Complex.mul_re] at he
    nlinarith [Nat.cast_nonneg (α := ℝ) n,NontrivialZetaZero.zero_lt_re rho],by
    intro he
    have hh := congrArg Complex.re he
    simp only [sub_re,one_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]⟩
  have hh := NontrivialZetaZero.zero_lt_re tau
  change 0<(rho.1-1).re at hh
  simp only [sub_re,one_re] at hh
  linarith [NontrivialZetaZero.re_lt_one rho]

/-- Genuine actual-zero gate: EVERY multiplicity is detected, without
exposure, rightmost selection, or a diagnostic nonlinear-source inference.
This is an analytic response theorem, NOT a native cutoff asymptotic. -/
theorem actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*countResponse z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨g,hg,hg0,he⟩ := (analyticAt_riemannZeta_nontrivialZero rho).analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have hn : rho.1-1≠1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [sub_re,one_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hA : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z-1)) rho.1 :=
    AnalyticAt.comp (analyticOn_riemannZeta _ hn) (analyticAt_id.sub analyticAt_const)
  have ha : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z-1)/g z) rho.1 := hA.div hg hg0
  refine ⟨riemannZeta (rho.1-1)/g rho.1,div_ne_zero (numerator_ne_zero rho) hg0,?_⟩
  have heq : (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*countResponse z)
      =ᶠ[𝓝[≠] rho.1] fun z => riemannZeta (z-1)/g z := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      hg.continuousAt.eventually_ne hg0 |>.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hgz (hzn : z≠rho.1)
    rw [countResponse,hz]
    simp only [smul_eq_mul]
    change (z-rho.1)^(analyticZetaZeroMultiplicity rho)*
      (riemannZeta (z-1)/((z-rho.1)^(analyticZetaZeroMultiplicity rho)*g z))=_
    field_simp [pow_ne_zero _ (sub_ne_zero.mpr hzn),hgz]
  exact (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Remove the TWO-dimensional density pole, keeping the actual source. -/
def centeredCountResponse (z : ℂ) : ℂ := (z-2)*countResponse z

theorem centered_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 2 ∧
      centeredCountResponse=ᶠ[𝓝[≠] (2 : ℂ)] E := by
  obtain ⟨E,hE,he⟩ := ArithmeticOperatorMoebiusCoprimeAudit.centered_density_analytic 0
  refine ⟨fun z => (1/2 : ℂ)*E z,analyticAt_const.mul (by simpa using hE),?_⟩
  simp only [ofReal_zero,mul_zero,add_zero] at he
  filter_upwards [he] with z hz
  rw [←hz]
  unfold centeredCountResponse centeredResponse countResponse response
  simp only [ofReal_zero,mul_zero,add_zero,sub_zero]
  ring

theorem centered_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun z : ℂ => (z-rho.1)^(analyticZetaZeroMultiplicity rho)*centeredCountResponse z)
      (𝓝[≠] rho.1) (𝓝 v) := by
  obtain ⟨v,hv,ht⟩ := actual_zero_source rho
  have hc : rho.1-2≠0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.sub_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  refine ⟨(rho.1-2)*v,mul_ne_zero hc hv,?_⟩
  have hx : Tendsto (fun z : ℂ => z-2) (𝓝[≠] rho.1) (𝓝 (rho.1-2)) :=
    (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  convert hx.mul ht using 1
  funext z
  unfold centeredCountResponse
  ring

/-- A genuine punctured analytic extension, not evaluation of the
totalized quotient at its zero denominator. -/
def RemovableAt (s : ℂ) : Prop :=
  ∃ g : ℂ → ℂ,AnalyticAt ℂ g s ∧ g=ᶠ[𝓝[≠] s] centeredCountResponse

/-- Even after exact density-pole removal, analytic regularization of
the complete native count response is EXACTLY strip nonvanishing.
This is a strength audit, not an imported arithmetic estimate. -/
theorem centered_removable_iff {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    RemovableAt s ↔ riemannZeta s≠0 := by
  constructor
  · rintro ⟨g,hg,he⟩ hz
    let rho : NontrivialZetaZero := ⟨s,hz,by
      rintro ⟨n,hn⟩
      have h := congrArg Complex.re hn
      norm_num [Complex.mul_re] at h
      nlinarith [Nat.cast_nonneg (α := ℝ) n],by
      intro h
      rw [h] at hs1
      norm_num at hs1⟩
    obtain ⟨v,hv,ht⟩ := centered_actual_zero_source rho
    have hzlim : Tendsto (fun z : ℂ => (z-s)^(analyticZetaZeroMultiplicity rho)*g z)
        (𝓝[≠] s) (𝓝 0) := by
      have hsub : Tendsto (fun z : ℂ => z-s) (𝓝[≠] s) (𝓝 0) := by
        have hc : Continuous (fun z : ℂ => z-s) := by fun_prop
        simpa only [sub_self] using hc.continuousAt (x := s) |>.tendsto.mono_left
          nhdsWithin_le_nhds
      have hh := (hsub.pow (analyticZetaZeroMultiplicity rho)).mul
        (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simpa [zero_pow (analyticZetaZeroMultiplicity_positive rho).ne'] using hh
    have hj : (fun z : ℂ => (z-s)^(analyticZetaZeroMultiplicity rho)*g z)=ᶠ[𝓝[≠] s]
        fun z => (z-s)^(analyticZetaZeroMultiplicity rho)*centeredCountResponse z := by
      filter_upwards [he] with z hz
      rw [hz]
    exact hv (tendsto_nhds_unique ht (hzlim.congr' hj))
  · intro hs
    have hn : s≠1 := by intro h; rw [h] at hs1; norm_num at hs1
    have hn1 : s-1≠1 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [sub_re,one_re] at hr
      linarith
    have hA : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z-1)) s :=
      AnalyticAt.comp (analyticOn_riemannZeta _ hn1) (analyticAt_id.sub analyticAt_const)
    exact ⟨centeredCountResponse,
      (analyticAt_id.sub analyticAt_const).mul (hA.div (analyticOn_riemannZeta _ hn) hs),
      Filter.EventuallyEq.rfl⟩

/-- Native phased count discrepancy, with the SAME discrete density
and endpoints as the earlier complete primitive population. -/
def countError (c y : ℝ) (N : ℕ) : ℂ :=
  ∑ n∈Finset.Icc 1 N,(increment y n-(c : ℂ)*n*primePhase y n)

theorem countError_eq_old (c y : ℝ) (N : ℕ) :
    countError c y N=ArithmeticOperatorPrimitiveCountAudit.error c y N := by
  rw [ArithmeticOperatorPrimitiveCountAudit.error_eq]
  simp only [countError,increment_eq]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The complete unsmoothed ordered count remains linearly costly
BEYOND EVERY head, with every prime power and the full height preserved. -/
theorem exists_native_linear_cost {c : ℝ} (hc : c≤2/3) (y : ℝ) (B : ℕ) :
    ∃ N : ℕ,B≤N ∧ 0<N ∧ (N : ℝ)/8≤‖countError c y N‖ := by
  simpa only [countError_eq_old] using
    ArithmeticOperatorPrimitiveCountAudit.exists_native_linear_cost hc y B

/-- Thus no GLOBAL sublinear norm envelope can pay this native count.
Selected subsequences, signed smoothing and extra gap constraints are
NOT refuted by this theorem. -/
theorem not_eventually_subsource_bound {c : ℝ} (hc : c≤2/3) (y : ℝ)
    {beta : ℝ} (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ N : ℕ in atTop,‖countError c y N‖≤C*(N : ℝ)^beta := by
  simpa only [countError_eq_old] using
    ArithmeticOperatorPrimitiveCountAudit.not_eventually_subsource_bound hc y hb C

end
end RiemannGaussian.ArithmeticOperatorOrderedGapAudit
