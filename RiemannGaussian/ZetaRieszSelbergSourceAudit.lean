/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveDensityAudit
import RiemannGaussian.ZetaRieszPairJointQuadratic
import RiemannGaussian.ZetaRieszEndgameSlack
import RiemannGaussian.HarmonicIntervalLimit
import RiemannGaussian.ZetaRieszLengthAsymptotic

/-!
# Audit the full signed quadratic against the continuous source model

This leaf tests a proposed GENERIC moment argument, not the ordinary-prime
floor. All four factorial terms and all low logged orders are retained.
The strictly positive common-phase density also passes the normalized
Selberg trace test. This does not assert the arithmetic Selberg identity
for that density, nor transport it to ordinary primes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSelbergSourceAudit
open ZetaRieszPositiveDensityAudit ZetaRieszSignedSelbergPayment
open ZetaRieszPairPrefixConvolution ZetaRieszLengthAsymptotic
open HarmonicIntervalLimit

/-- The normalized Selberg source cancellation holds for ANY convergent
unit negative moment array, including the continuous positive model. -/
theorem traceError_tendsto (a : ℕ → ℂ) (ha : Tendsto a atTop (𝓝 (-1))) :
    Tendsto (traceError a) atTop (𝓝 0) := by
  obtain ⟨B, hB, haB⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hab : ∀ k, ‖a k‖ ≤ B+1 := fun k =>
    (haB (a k) (Set.mem_range_self k)).trans (by linarith only [hB])
  exact squeeze_zero_norm (fun N => norm_traceError_le a (by linarith : 1≤B+1) hab N)
    (traceBudget_tendsto a ha (B+1))

/-- The positive density passes this exact normalized trace test with its
full phase and finite lower threshold, without any zero hypothesis. -/
theorem density_traceError_tendsto {u B y : ℝ} (hu : 0<u) (hu1 : u<1)
    (hB : 0≤B) (hy : 1≤|y|) :
    Tendsto (traceError (densityMoment u y B)) atTop (𝓝 0) :=
  traceError_tendsto _ (densityMoment_tendsto hu hu1 hB hy)

private theorem marginal_sums (e : ℕ → ℝ) (he : ∀ n, 0≤e n) (t : ℕ)
    (S : Finset ℕ) (hS : ∀ k∈S, 0<k ∧ k≤t) :
    (∑ k∈S,e (k-1))≤∑ j∈Finset.range (t+1),e j ∧
    (∑ k∈S,e (t-k))≤∑ j∈Finset.range (t+1),e j := by
  have hl : S.image (fun k => k-1)⊆Finset.range (t+1) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have := hS k hk
    exact Finset.mem_range.mpr (by omega)
  have hr : S.image (fun k => t-k)⊆Finset.range (t+1) := by
    intro j hj
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hil : Set.InjOn (fun k : ℕ => k-1) S := by
    intro k hk l hl h
    have := hS k hk
    have := hS l hl
    dsimp only at h
    omega
  have hir : Set.InjOn (fun k : ℕ => t-k) S := by
    intro k hk l hl h
    have := hS k hk
    have := hS l hl
    dsimp only at h
    omega
  constructor
  · rw [←Finset.sum_image hil]
    exact Finset.sum_le_sum_of_subset_of_nonneg hl (fun j _ _ => he j)
  · rw [←Finset.sum_image hir]
    exact Finset.sum_le_sum_of_subset_of_nonneg hr (fun j _ _ => he j)

/-- The entire reflected harmonic product error, not independently
replaced atoms. Its two marginals include order zero exactly once. -/
private theorem norm_product_error_le (a : ℕ → ℂ) {C : ℝ}
    (hC : 1≤C) (ha : ∀ k, ‖a k‖≤C) (t : ℕ) (S : Finset ℕ)
    (hS : ∀ k∈S, 0<k ∧ 4*k≤3*(t+1)) :
    ‖∑ k∈S,(a (k-1)*a (t-k)-1)/((t+1-k : ℕ) : ℂ)‖≤
      8*C*(((t+1 : ℕ) : ℝ)⁻¹*∑ k∈Finset.range (t+1),‖a k+1‖) := by
  have hsel : ∀ k∈S, 0<k ∧ k≤t := by
    intro k hk
    have := hS k hk
    omega
  have hm := marginal_sums (fun k => ‖a k+1‖) (fun k => norm_nonneg _) t S hsel
  have ht : (0 : ℝ)<((t+1 : ℕ) : ℝ) := by positivity
  have hp k (hk : k∈S) :
      ‖(a (k-1)*a (t-k)-1)/((t+1-k : ℕ) : ℂ)‖≤
        (4*C/((t+1 : ℕ) : ℝ))*(‖a (k-1)+1‖+‖a (t-k)+1‖) := by
    have hh := hS k hk
    have hden : (0 : ℝ)<((t+1-k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0<t+1-k)
    have hfour : ((t+1 : ℕ) : ℝ)≤4*((t+1-k : ℕ) : ℝ) := by
      exact_mod_cast (by omega : t+1≤4*(t+1-k))
    have hi : (1 : ℝ)/((t+1-k : ℕ) : ℝ)≤4/((t+1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hden ht).mpr
      linarith only [hfour]
    have hprod : ‖a (k-1)*a (t-k)-1‖≤C*(‖a (k-1)+1‖+‖a (t-k)+1‖) := by
      simpa using HarmonicProductContinuity.norm_product_sub_square
        (a := (-1 : ℂ)) (ha (t-k)) (by simpa using hC)
    rw [norm_div,Complex.norm_natCast,div_eq_mul_inv]
    exact (mul_le_mul hprod (by simpa only [one_div] using hi)
      (by positivity) (by positivity)).trans_eq (by ring)
  calc
    _ ≤ ∑ k∈S,(4*C/((t+1 : ℕ) : ℝ))*(‖a (k-1)+1‖+‖a (t-k)+1‖) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (4*C/((t+1 : ℕ) : ℝ))*
        ((∑ k∈S,‖a (k-1)+1‖)+∑ k∈S,‖a (t-k)+1‖) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left (add_le_add hm.1 hm.2)
        (by positivity : 0≤4*C/((t+1 : ℕ) : ℝ))).trans_eq (by ring)

private theorem product_error_tendsto (a : ℕ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    (S : ℕ → Finset ℕ) (hS : ∀ᶠ t in atTop,∀ k∈S t,0<k ∧ 4*k≤3*(t+1)) :
    Tendsto (fun t => ∑ k∈S t,(a (k-1)*a (t-k)-1)/((t+1-k : ℕ) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨B,hB,haB⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hab : ∀ k, ‖a k‖≤B+1 := fun k =>
    (haB (a k) (Set.mem_range_self k)).trans (by linarith only [hB])
  have he : Tendsto (fun k => ‖a k+1‖) atTop (𝓝 0) := by simpa using (ha.add_const 1).norm
  have hc := (he.cesaro.comp (tendsto_add_atTop_nat 1)).const_mul (8*(B+1))
  apply squeeze_zero_norm' (by
    filter_upwards [hS] with t ht
    exact norm_product_error_le a (by linarith : 1≤B+1) hab t (S t) ht)
  simpa only [Function.comp_def,mul_zero] using hc

private theorem lower_ratio :
    Tendsto (fun N : ℕ => ((13*N/32 : ℕ) : ℝ)/(N+1)) atTop (𝓝 (13/32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun N : ℕ => ((13*N/32 : ℕ) : ℝ)/(N+1)-13/32)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (2 : ℝ)/(N+1)) ?_ (hm.const_div_atTop 2)
    intro N
    have hlo : 13*(N+1)≤32*(13*N/32)+64 := by omega
    have hhi : 32*(13*N/32)≤13*(N+1)+64 := by omega
    have hlor : (13 : ℝ)*(N+1)≤32*((13*N/32 : ℕ) : ℝ)+64 := by exact_mod_cast hlo
    have hhir : 32*((13*N/32 : ℕ) : ℝ)≤(13 : ℝ)*(N+1)+64 := by exact_mod_cast hhi
    have hm0 : (0 : ℝ)<N+1 := by positivity
    have hb : |((13*N/32 : ℕ) : ℝ)-13/32*(N+1)|≤2 :=
      abs_le.mpr ⟨by linarith only [hlor],by linarith only [hhir]⟩
    rw [Real.norm_eq_abs]
    calc
      _ = |((13*N/32 : ℕ) : ℝ)-13/32*(N+1)|/(N+1) := by
        rw [show ((13*N/32 : ℕ) : ℝ)/(N+1)-13/32=
          (((13*N/32 : ℕ) : ℝ)-13/32*(N+1))/(N+1) by field_simp,
          abs_div,abs_of_pos hm0]
      _ ≤ _ := div_le_div_of_nonneg_right hb hm0.le
  convert! he.add_const (13/32 : ℝ) using 1
  · funext N; ring
  · norm_num

private theorem complement_ratio :
    Tendsto (fun N : ℕ => ((N-13*N/32 : ℕ) : ℝ)/(N+1)) atTop (𝓝 (19/32)) := by
  have hm : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one,Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hm.const_div_atTop 1)).sub lower_ratio
  norm_num only at h
  apply h.congr'
  filter_upwards [] with N
  have he : ((13*N/32 : ℕ) : ℝ)+((N-13*N/32 : ℕ) : ℝ)=N := by
    exact_mod_cast (show 13*N/32+(N-13*N/32)=N by omega)
  have hm0 : (N : ℝ)+1≠0 := by positivity
  field_simp
  linarith only [he]

private theorem reciprocal_interval (a b : ℕ) (hab : a≤b) :
    (∑ k∈Finset.Icc (a+1) b,(1 : ℝ)/k)=(harmonic b : ℝ)-(harmonic a : ℝ) := by
  have hsub : Finset.Icc 1 a⊆Finset.Icc 1 b := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hs : Finset.Icc 1 b\Finset.Icc 1 a=Finset.Icc (a+1) b := by
    ext k
    simp only [Finset.mem_sdiff,Finset.mem_Icc]
    omega
  have hh := Finset.sum_sdiff (f := fun k : ℕ => (1 : ℝ)/k) hsub
  rw [hs] at hh
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  simpa only [one_div] using (eq_sub_iff_add_eq.mpr hh)

private theorem central_reciprocal (N : ℕ) :
    (∑ k∈centralOrders (N+1) (13*N/32),(1 : ℝ)/((N+1-k : ℕ) : ℝ))=
      (harmonic (N-13*N/32) : ℝ)-(harmonic (13*N/32) : ℝ) := by
  have he : centralOrders (N+1) (13*N/32)=Finset.Icc (13*N/32+1) (N-13*N/32) := by
    ext k
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [he]
  have href : (∑ k∈Finset.Icc (13*N/32+1) (N-13*N/32),
      (1 : ℝ)/((N+1-k : ℕ) : ℝ))=
      ∑ k∈Finset.Icc (13*N/32+1) (N-13*N/32),(1 : ℝ)/k := by
    apply Finset.sum_bij (fun k _ => N+1-k)
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb h
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨N+1-k,?_,?_⟩
      · rw [Finset.mem_Icc] at hk ⊢
        omega
      · rw [Finset.mem_Icc] at hk
        omega
    · intro k _; rfl
  rw [href,reciprocal_interval _ _ (by omega)]

private theorem prefix_reciprocal (N : ℕ) :
    (∑ k∈Finset.Icc 1 (N+1-13*N/32),(1 : ℝ)/((N+2-k : ℕ) : ℝ))=
      (harmonic (N+1) : ℝ)-(harmonic (13*N/32) : ℝ) := by
  have href : (∑ k∈Finset.Icc 1 (N+1-13*N/32),
      (1 : ℝ)/((N+2-k : ℕ) : ℝ))=
      ∑ k∈Finset.Icc (13*N/32+1) (N+1),(1 : ℝ)/k := by
    apply Finset.sum_bij (fun k _ => N+2-k)
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb h
      rw [Finset.mem_Icc] at ha hb
      omega
    · intro k hk
      refine ⟨N+2-k,?_,?_⟩
      · rw [Finset.mem_Icc] at hk ⊢
        omega
      · rw [Finset.mem_Icc] at hk
        omega
    · intro k _; rfl
  rw [href,reciprocal_interval _ _ (by omega)]

private theorem central_reciprocal_tendsto :
    Tendsto (fun N => ∑ k∈centralOrders (N+1) (13*N/32),
      (1 : ℝ)/((N+1-k : ℕ) : ℝ)) atTop (𝓝 (log (19/13))) := by
  have hK : Tendsto (fun N : ℕ => 13*N/32) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3*b)] with N hN
    omega
  have hB : Tendsto (fun N : ℕ => N-13*N/32) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3*b)] with N hN
    omega
  have hr := complement_ratio.div lower_ratio (by norm_num : (13/32 : ℝ)≠0)
  norm_num only at hr
  have hr' : Tendsto (fun N : ℕ => ((N-13*N/32 : ℕ) : ℝ)/((13*N/32 : ℕ) : ℝ))
      atTop (𝓝 (19/13)) := by
    apply hr.congr'
    filter_upwards [] with N
    dsimp only [Pi.div_apply]
    exact div_div_div_cancel_right₀ (by positivity : (N : ℝ)+1≠0) _ _
  exact (tendsto_harmonic_difference _ _ hB hK (by norm_num) hr').congr
    (fun N => (central_reciprocal N).symm)

private theorem prefix_reciprocal_tendsto :
    Tendsto (fun N => ∑ k∈Finset.Icc 1 (N+1-13*N/32),
      (1 : ℝ)/((N+2-k : ℕ) : ℝ)) atTop (𝓝 (log (32/13))) := by
  have hK : Tendsto (fun N : ℕ => 13*N/32) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [eventually_ge_atTop (3*b)] with N hN
    omega
  have hr := lower_ratio.inv₀ (by norm_num : (13/32 : ℝ)≠0)
  norm_num only at hr
  have hr' : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)/((13*N/32 : ℕ) : ℝ))
      atTop (𝓝 (32/13)) := by simpa only [inv_div,Nat.cast_add,Nat.cast_one] using hr
  exact (tendsto_harmonic_difference _ _ (tendsto_add_atTop_nat 1) hK
    (by norm_num) hr').congr (fun N => (prefix_reciprocal N).symm)

/-- Regression evaluation of the joined normalized factorial polynomial.
It is not a new arithmetic carrier: the central/successor/logged/trace
slots are collected algebraically below. All array indices start at zero. -/
def harmonicEvaluation (a : ℕ → ℂ) (u : ℝ) (N : ℕ) : ℂ :=
  (∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ)+
    (∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))-
    ((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)*
      (∑ k∈Finset.Icc 1 (N+1-13*N/32),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))

/-- The positive model has the SAME obstructive limit for the joined
signed polynomial, not just for its independently inspected moments. -/
theorem harmonicEvaluation_tendsto (a : ℕ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    {u : ℝ} (hu : 0<u) (huq : u≤3/5) :
    Tendsto (harmonicEvaluation a u) atTop
      (𝓝 ((1-ZetaRieszMaskSupport.retainedCost u : ℝ) : ℂ)) := by
  have ht : Tendsto (fun N : ℕ => (∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ))
      atTop (𝓝 1) := by
    have hh := ((ha.comp (tendsto_add_atTop_nat 1)).neg.sub
      (traceError_tendsto a ha)).comp (tendsto_sub_atTop_nat 1)
    norm_num only at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : N-1+1=N := by omega
    simp only [Function.comp_def,traceError,hn]
    ring
  have ec := product_error_tendsto a ha (fun t => centralOrders (t+1) (13*t/32)) (by
    filter_upwards [] with t
    intro k hk
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
    omega)
  have ep0 := product_error_tendsto a ha
    (fun t => Finset.Icc 1 (t-13*(t-1)/32)) (by
      filter_upwards [eventually_ge_atTop 8] with t ht
      intro k hk
      rw [Finset.mem_Icc] at hk
      have ht' : t-1+1=t := by omega
      omega)
  have ep := ep0.comp (tendsto_add_atTop_nat 1)
  have hrc := Complex.continuous_ofReal.continuousAt.tendsto.comp central_reciprocal_tendsto
  have hrp := Complex.continuous_ofReal.continuousAt.tendsto.comp prefix_reciprocal_tendsto
  have hc : Tendsto (fun N : ℕ => ∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ)) atTop (𝓝 (log (19/13) : ℂ)) := by
    have hh := ec.add hrc
    simp only [zero_add] at hh
    apply hh.congr
    intro N
    simp only [Function.comp_def,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast,
      ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp : Tendsto (fun N : ℕ => ∑ k∈Finset.Icc 1 (N+1-13*N/32),
      a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)) atTop (𝓝 (log (32/13) : ℂ)) := by
    have hh := ep.add hrp
    simp only [zero_add] at hh
    apply hh.congr
    intro N
    simp only [Function.comp_def,show N+1-1=N by omega,
      Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_natCast,
      ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_head_length_factor hu huq)
  have hh := (ht.add hc).sub (hf.mul hp)
  convert! hh using 1
  · funext N
    dsimp only [Function.comp_def,harmonicEvaluation]
    push_cast
    rfl
  · unfold ZetaRieszMaskSupport.retainedCost
    push_cast
    ring

/-- The four already-existing factorial slots, evaluated on an arbitrary
unlogged moment array. This is an audit evaluator, not a replacement
for the literal prime carrier. -/
def momentPolynomial (P : ℕ → ℂ) (N : ℕ) (L : ℝ) : ℂ :=
  (N+1 : ℂ)/2*(∑ k∈centralOrders (N+1) (13*N/32),P k*P (N+1-k))-
    (N+1 : ℂ)*(N+2)/(2*(L : ℂ))*
      (∑ k∈centralOrders (N+2) (13*N/32),P k*P (N+2-k))-
    (N+1 : ℂ)/(L : ℂ)*(∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
      (k : ℂ)*P k*P (N+2-k))+
    (∑ k∈Finset.range N,((k+1 : ℕ) : ℂ)*((N-k : ℕ) : ℂ)*P (k+1)*P (N-k))/(N : ℂ)

/-- The evaluator matches the actual finite prime quadratic exactly.
This equality supplies no independent bound on either side. -/
theorem factorialQuadratic_eq_polynomial (A : Finset ℕ) (N : ℕ) (L : ℝ) (s : ℂ) :
    ZetaRieszPairJointQuadratic.factorialQuadratic A N L s=
      momentPolynomial (fun k => ZetaRieszPrimePairConvolution.finiteMoment A k s) N L := by
  unfold ZetaRieszPairJointQuadratic.factorialQuadratic momentPolynomial
  rw [ZetaRieszPairJointQuadratic.selbergTrace_eq_weighted_orders]

/-- Recover ordinary factorial moments from a normalized logged array.
Order zero is not used in the endpoint-cancelled polynomial. Logged order
zero is retained and enters at ordinary order one. -/
def modelMoment (a : ℕ → ℂ) (u : ℝ) (k : ℕ) : ℂ :=
  a (k-1)/((k : ℂ)*(u : ℂ)^k)

private theorem model_product (a : ℕ → ℂ) {u : ℝ} (hu : u≠0)
    {M k : ℕ} (hk : 0<k) (hkM : k<M) :
    (u : ℂ)^M*(modelMoment a u k*modelMoment a u (M-k))=
      a (k-1)*a (M-k-1)/((k : ℂ)*((M-k : ℕ) : ℂ)) := by
  have huk : (u : ℂ)≠0 := by exact_mod_cast hu
  have hkc : (k : ℂ)≠0 := by exact_mod_cast hk.ne'
  have hmc : ((M-k : ℕ) : ℂ)≠0 := by exact_mod_cast (by omega : M-k≠0)
  have hp : (u : ℂ)^M=(u : ℂ)^k*(u : ℂ)^(M-k) := by
    rw [←pow_add,show k+(M-k)=M by omega]
  unfold modelMoment
  rw [hp]
  field_simp [huk,hkc,hmc]

private theorem central_reflect (M K : ℕ) (f : ℕ → ℂ) :
    (∑ k∈centralOrders M K,f (M-k))=∑ k∈centralOrders M K,f k := by
  apply Finset.sum_bij (fun k _ => M-k)
  · intro k hk
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk ⊢
    omega
  · intro a ha b hb h
    simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at ha hb
    omega
  · intro k hk
    refine ⟨M-k,?_,?_⟩
    · simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk ⊢
      omega
    · simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
      omega
  · intro k _; rfl

private theorem central_partial_fractions (a : ℕ → ℂ) (M K : ℕ) :
    (M : ℂ)/2*(∑ k∈centralOrders M K,
      a (k-1)*a (M-k-1)/((k : ℂ)*((M-k : ℕ) : ℂ)))=
      ∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/((M-k : ℕ) : ℂ) := by
  have hp : (M : ℂ)*(∑ k∈centralOrders M K,
      a (k-1)*a (M-k-1)/((k : ℂ)*((M-k : ℕ) : ℂ)))=
      (∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/(k : ℂ))+
        ∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/((M-k : ℕ) : ℂ) := by
    rw [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := Finset.mem_filter.mp hk
    have hkM : k<M := by omega
    have hkc : (k : ℂ)≠0 := by exact_mod_cast (show k≠0 by omega)
    have hmc : ((M-k : ℕ) : ℂ)≠0 := by exact_mod_cast (show M-k≠0 by omega)
    have hadd : (k : ℂ)+((M-k : ℕ) : ℂ)=(M : ℂ) := by
      exact_mod_cast (show k+(M-k)=M by omega)
    field_simp [hkc,hmc]
    linear_combination -(a (k-1)*a (M-k-1))*hadd
  have hr : (∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/(k : ℂ))=
      ∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/((M-k : ℕ) : ℂ) := by
    rw [←central_reflect M K (fun k => a (k-1)*a (M-k-1)/(k : ℂ))]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := Finset.mem_filter.mp hk
    have hs : M-(M-k)=k := by omega
    simp only [hs,mul_comm]
  rw [hr] at hp
  linear_combination hp/2

private theorem central_model (a : ℕ → ℂ) {u : ℝ} (hu : u≠0) (M K : ℕ) :
    (u : ℂ)^M*((M : ℂ)/2*
      ∑ k∈centralOrders M K,modelMoment a u k*modelMoment a u (M-k))=
      ∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/((M-k : ℕ) : ℂ) := by
  rw [mul_left_comm,Finset.mul_sum]
  have hs : (∑ k∈centralOrders M K,(u : ℂ)^M*
      (modelMoment a u k*modelMoment a u (M-k)))=
      ∑ k∈centralOrders M K,a (k-1)*a (M-k-1)/((k : ℂ)*((M-k : ℕ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hh := Finset.mem_filter.mp hk
    exact model_product a hu (by omega) (by omega)
  rw [hs,central_partial_fractions]

private theorem successor_partition (a : ℕ → ℂ) (N : ℕ) :
    (∑ k∈centralOrders (N+2) (13*N/32),a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))+
      (∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))=
      ∑ k∈Finset.Icc 1 (N+1-13*N/32),a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ) := by
  have hl : (Finset.Icc 1 (N+1-13*N/32)).filter (fun k => k≤13*N/32)=
      (Finset.range (13*N/32+1)).filter (fun k => 0<k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    omega
  have hh : (Finset.Icc 1 (N+1-13*N/32)).filter (fun k => ¬k≤13*N/32)=
      centralOrders (N+2) (13*N/32) := by
    ext k
    simp only [centralOrders,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    omega
  rw [←hl,←hh,add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Exact collection of all four signed slots. No asymptotic order
selection, phase replacement, or discarded low-order atom is used. -/
theorem model_polynomial_eq_harmonic (a : ℕ → ℂ) {u : ℝ} (hu : u≠0) (N : ℕ) :
    (u : ℂ)^(N+1)*momentPolynomial (modelMoment a u) N
      (SquarefreeVaughanLogSource.length u N)=harmonicEvaluation a u N := by
  let L := SquarefreeVaughanLogSource.length u N
  have huC : (u : ℂ)≠0 := by exact_mod_cast hu
  have hL : (L : ℂ)≠0 := by exact_mod_cast (SquarefreeVaughanLogSource.length_pos u N).ne'
  have hc := central_model a hu (N+1) (13*N/32)
  have hn : (u : ℂ)^(N+1)*((N+1 : ℂ)*(N+2)/(2*(L : ℂ))*
      ∑ k∈centralOrders (N+2) (13*N/32),modelMoment a u k*modelMoment a u (N+2-k))=
      (N+1 : ℂ)/((u : ℂ)*(L : ℂ))*
        ∑ k∈centralOrders (N+2) (13*N/32),a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ) := by
    have hc' := central_model a hu (N+2) (13*N/32)
    have he : ∀ k, N+2-k-1=N+1-k := by omega
    simp only [he] at hc'
    rw [←hc',show N+2=(N+1)+1 by omega,pow_succ]
    simp only [pow_succ,Nat.cast_add,Nat.cast_one]
    field_simp [huC,hL]
    ring
  have hl : (u : ℂ)^(N+1)*((N+1 : ℂ)/(L : ℂ)*
      ∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
        (k : ℂ)*modelMoment a u k*modelMoment a u (N+2-k))=
      (N+1 : ℂ)/((u : ℂ)*(L : ℂ))*
        ∑ k∈(Finset.range (13*N/32+1)).filter (fun k => 0<k),
          a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hkR,hk0⟩ := Finset.mem_filter.mp hk
    have hkM : k<N+2 := by have := Finset.mem_range.mp hkR; omega
    have hh := model_product a hu hk0 hkM
    have hkc : (k : ℂ)≠0 := by exact_mod_cast hk0.ne'
    have hm : ((N+2-k : ℕ) : ℂ)≠0 := by exact_mod_cast (by omega : N+2-k≠0)
    rw [show N+2-k-1=N+1-k by omega,show N+2=(N+1)+1 by omega,pow_succ] at hh
    field_simp [huC,hL,hkc,hm] at hh ⊢
    simp only [pow_succ] at hh
    linear_combination hh
  have ht : (u : ℂ)^(N+1)*
      ((∑ k∈Finset.range N,((k+1 : ℕ) : ℂ)*((N-k : ℕ) : ℂ)*
        modelMoment a u (k+1)*modelMoment a u (N-k))/(N : ℂ))=
      (∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ) := by
    rw [←mul_div_assoc,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkM : k+1<N+1 := by have := Finset.mem_range.mp hk; omega
    have hh := model_product a hu (Nat.succ_pos k) hkM
    have hNk : N+1-(k+1)=N-k := by omega
    have he : N-k-1=N-1-k := by omega
    simp only [hNk,he,Nat.succ_sub_one] at hh
    have hkc : ((k+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero k
    have hmc : ((N-k : ℕ) : ℂ)≠0 := by exact_mod_cast (by omega : N-k≠0)
    field_simp [hkc,hmc] at hh
    linear_combination hh
  simp only [Nat.cast_add,Nat.cast_one] at hc
  unfold momentPolynomial
  rw [mul_add,mul_sub,mul_sub,hc,hn,hl,ht]
  have hs : ∀ k,N+1-k-1=N-k := by omega
  simp only [hs]
  unfold harmonicEvaluation
  rw [←successor_partition a N]
  dsimp only [L]
  push_cast
  ring

/-- Full four-term model evaluation converges to the obstructive source.
The proof collects factorial slots before using array convergence. -/
theorem model_polynomial_tendsto (a : ℕ → ℂ) (ha : Tendsto a atTop (𝓝 (-1)))
    {u : ℝ} (hu : 0<u) (huq : u≤3/5) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*momentPolynomial (modelMoment a u) N
      (SquarefreeVaughanLogSource.length u N)) atTop
      (𝓝 ((1-ZetaRieszMaskSupport.retainedCost u : ℝ) : ℂ)) :=
  (harmonicEvaluation_tendsto a ha hu huq).congr
    (fun N => (model_polynomial_eq_harmonic a hu.ne' N).symm)

/-- This is a genuinely positive common-phase density, not merely the
constant limiting array: all lower-threshold heads are retained. -/
theorem density_polynomial_tendsto {y : ℝ} (hy : 1≤|y|) :
    Tendsto (fun N : ℕ => (((10001/20000 : ℝ) : ℂ))^(N+1)*
      momentPolynomial (modelMoment (densityMoment (10001/20000) y 20000) (10001/20000)) N
        (SquarefreeVaughanLogSource.length (10001/20000) N)) atTop
      (𝓝 ((1-ZetaRieszMaskSupport.retainedCost (10001/20000) : ℝ) : ℂ)) :=
  model_polynomial_tendsto (densityMoment (10001/20000) y 20000)
    (density_ceiling_moment_tendsto hy) (u := (10001/20000 : ℝ)) (by norm_num) (by norm_num)

/-- A cofinal, kernel-checked countertest for the generic density/trace
method. This does NOT refute an ordinary-prime bound or assert a zero. -/
theorem eventually_density_polynomial_gt_target {y : ℝ} (hy : 1≤|y|) :
    ∀ᶠ N : ℕ in atTop,(399/5000 : ℝ)<
      ((((10001/20000 : ℝ) : ℂ))^(N+1)*
        momentPolynomial (modelMoment (densityMoment (10001/20000) y 20000) (10001/20000)) N
          (SquarefreeVaughanLogSource.length (10001/20000) N)).re := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (density_polynomial_tendsto hy)
  simp only [Complex.ofReal_re] at hs
  exact hs.eventually_const_lt (by
    linarith only [ZetaRieszEndgameSlack.retainedCost_upper
      (by norm_num : (1/2 : ℝ)≤10001/20000)
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (10001/20000 : ℝ)≤ZetaRieszWideOwnerAudit.radiusCeiling)])

/-- Even a vanishing additive budget cannot rescue that generic bound
on a cofinal subsequence. Literal ordinary-prime correlations remain an
additional arithmetic requirement, not an omitted error in this test. -/
theorem density_cofinal_floor_impossible {y : ℝ} (hy : 1≤|y|)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hf : ∃ᶠ N : ℕ in atTop,
      ((((10001/20000 : ℝ) : ℂ))^(N+1)*
        momentPolynomial (modelMoment (densityMoment (10001/20000) y 20000) (10001/20000)) N
          (SquarefreeVaughanLogSource.length (10001/20000) N)).re≤399/5000+err N) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (density_polynomial_tendsto hy)
  simp only [Complex.ofReal_re] at hs
  have hh : 1-ZetaRieszMaskSupport.retainedCost (10001/20000)-0≤(399/5000 : ℝ) :=
    le_of_tendsto_of_frequently (hs.sub he) (hf.mono fun N hN => by
      dsimp only [Function.comp_def]
      linarith only [hN])
  have hc := ZetaRieszEndgameSlack.retainedCost_upper
    (by norm_num : (1/2 : ℝ)≤10001/20000)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      (10001/20000 : ℝ)≤ZetaRieszWideOwnerAudit.radiusCeiling)
  linarith only [hh,hc]

/-- The same positive source model has relative error smaller than any
fixed stretched exponential, beyond an explicit threshold. This is a
model statement, not a prime-density approximation theorem. -/
theorem relative_density_stretched_exponential {c y t : ℝ} (hc : 0≤c)
    (ht : 40000≤t) (hs : (40000*c)^2≤t) :
    |t*density (10001/20000) y t/exp t-1|≤exp (-c*sqrt t) := by
  have ht0 : 0≤t := by linarith only [ht]
  have hsq := sq_sqrt ht0
  have hr0 := sqrt_nonneg t
  have hr : 40000*c ≤ sqrt t := by
    apply (sq_le_sq₀ (by positivity : 0≤40000*c) hr0).mp
    simpa only [hsq] using hs
  have hp := mul_le_mul_of_nonneg_right hr hr0
  have hneg : 1-t/20000≤-c*sqrt t := by nlinarith only [hp,hsq,ht]
  have he : (2 : ℝ)<exp 1 := by
    have hh := add_one_lt_exp (by norm_num : (1 : ℝ)≠0)
    norm_num at hh
    exact hh
  calc
    _ ≤ 2*exp (-t/20000) := by
      convert! relative_density_abs_le (10001/20000) y (by linarith : t≠0) using 1
      congr 1
      ring
    _ ≤ exp 1*exp (-t/20000) := mul_le_mul_of_nonneg_right he.le (exp_pos _).le
    _ = exp (1-t/20000) := by rw [←exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr hneg

end RiemannGaussian.ZetaRieszSelbergSourceAudit
