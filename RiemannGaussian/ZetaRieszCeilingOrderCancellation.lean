/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPhaseRadius

/-!
# A joined upper inequality for the central factorial orders

The Selberg trace must remain joined at higher multiplicity. Its complete
trace cancels the trace in `harmonicEvaluation`. Before estimating the two
remaining adjacent-order central sums, collect their common product. Its
absolute coefficient is at most 2/11 of the separate coefficients.

Only the adjacent-order difference is priced as an error. The ordinary-prime
term and the entire outer-order sum remain signed. This gives a concrete
global central saving, not the independent numerical ceiling 42/25.
No literal mask is removed without its existing geometric payment.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCeilingOrderCancellation
open ZetaRieszPairPrefixConvolution ZetaRieszSelbergSourceAudit
open ZetaRieszPairPrimePowerPayment ZetaRieszJoinedPhaseRadius
open ZetaRieszSignedSelbergPayment ZetaRieszPairPrefixPayment
open ZetaRieszLowCountSignedBoundary ZetaRieszPrimeCountFrequency

/-- The exact lower-prefix orders and the single upper endpoint not in
the common central interval. No low order or endpoint is discarded. -/
def exteriorOrders (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N+1-13*N/32)\centralOrders (N+1) (13*N/32)

/-- Only the change in the second logged order is priced here. -/
def centralStepMass (a : ℕ→ℂ) (N : ℕ) : ℝ :=
  ∑ k∈centralOrders (N+1) (13*N/32),
    ‖a (k-1)‖*‖a (N+1-k)-a (N-k)‖/((N+2-k : ℕ) : ℝ)

/-- The separate central price, for comparison with the checked 9/11
coefficient saving. This is not a proposed whole-carrier majorant. -/
def separateCentralPrice (a : ℕ→ℂ) (N : ℕ) (lam : ℝ) : ℝ :=
  ∑ k∈centralOrders (N+1) (13*N/32),
    (lam/((N+2-k : ℕ) : ℝ)+1/((N+1-k : ℕ) : ℝ))*
      ‖a (k-1)*a (N-k)‖

private theorem central_subset (N : ℕ) :
    centralOrders (N+1) (13*N/32)⊆Finset.Icc 1 (N+1-13*N/32) := by
  intro k hk
  simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
  rw [Finset.mem_Icc]
  omega

private theorem prefix_partition (a : ℕ→ℂ) (N : ℕ) :
    (∑ k∈Finset.Icc 1 (N+1-13*N/32),
      a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))=
      (∑ k∈centralOrders (N+1) (13*N/32),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))+
      ∑ k∈exteriorOrders N,a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ) := by
  simpa only [exteriorOrders,add_comm] using
    (Finset.sum_sdiff (f:=fun k =>
      a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)) (central_subset N)).symm

/-- Exact adjacent-order collection, before any phase or norm estimate. -/
theorem central_adjacent_eq (a : ℕ→ℂ) (N : ℕ) (lam : ℝ) :
    -(∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
      (lam : ℂ)*(∑ k∈Finset.Icc 1 (N+1-13*N/32),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))=
    (∑ k∈centralOrders (N+1) (13*N/32),
      ((lam : ℂ)/((N+2-k : ℕ) : ℂ)-1/((N+1-k : ℕ) : ℂ))*
        (a (k-1)*a (N-k)))+
    (lam : ℂ)*(∑ k∈exteriorOrders N,
      a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))+
    (lam : ℂ)*(∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*(a (N+1-k)-a (N-k))/((N+2-k : ℕ) : ℂ)) := by
  rw [prefix_partition,mul_add]
  have he : (∑ k∈centralOrders (N+1) (13*N/32),
      (
      - (a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
        (lam : ℂ)*(a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))))=
    ∑ k∈centralOrders (N+1) (13*N/32),
      (((lam : ℂ)/((N+2-k : ℕ) : ℂ)-1/((N+1-k : ℕ) : ℂ))*
        (a (k-1)*a (N-k))+
      (lam : ℂ)*(a (k-1)*(a (N+1-k)-a (N-k))/((N+2-k : ℕ) : ℂ))) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.mul_sum] at he
  linear_combination he

/-- Uniform contraction of the coefficient, not an assumed contraction
of the prime phases. The second order differs by EXACTLY one. -/
theorem adjacent_coefficient_price {d lam : ℝ} (hd : 3≤d)
    (hl : 1≤lam) (hu : lam≤13/9) :
    |lam/(d+1)-1/d|≤(2/11)*(lam/(d+1)+1/d) := by
  have hd0 : 0<d := by linarith
  have hs0 : 0<d+1 := by linarith
  have h1 : 9*(lam/(d+1))≤13*(1/d) := by
    have ht : (9*lam)/(d+1)≤(13 : ℝ)/d :=
      (div_le_div_iff₀ hs0 hd0).mpr (by nlinarith only [hu,hd0])
    simpa only [←mul_div_assoc,mul_one] using ht
  have h2 : 9*(1/d)≤13*(lam/(d+1)) := by
    have hh := mul_le_mul_of_nonneg_right hl hd0.le
    have hmul : 9*(d+1)≤13*lam*d := by nlinarith only [hh,hd]
    have ht : (9 : ℝ)/d≤(13*lam)/(d+1) :=
      (div_le_div_iff₀ hd0 hs0).mpr hmul
    simpa only [←mul_div_assoc,mul_one] using ht
  apply abs_le.mpr
  constructor <;> linarith only [h1,h2]

private theorem norm_central_step_le (a : ℕ→ℂ) (N : ℕ) :
    ‖∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*(a (N+1-k)-a (N-k))/((N+2-k : ℕ) : ℂ)‖≤centralStepMass a N := by
  apply (norm_sum_le _ _).trans
  simp only [centralStepMass,norm_div,norm_mul,Complex.norm_natCast]
  exact le_refl _

/-- Stronger signed version: take no norm or positive part of either
main sum. Only the joined adjacent-order difference receives a price. -/
theorem central_adjacent_signed_upper (a : ℕ→ℂ) (N : ℕ) {lam : ℝ}
    (hl : 0≤lam) :
    (-(∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
      (lam : ℂ)*(∑ k∈Finset.Icc 1 (N+1-13*N/32),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))).re≤
    (∑ k∈centralOrders (N+1) (13*N/32),
      ((lam : ℂ)/((N+2-k : ℕ) : ℂ)-1/((N+1-k : ℕ) : ℂ))*
        (a (k-1)*a (N-k))).re+
    lam*(∑ k∈exteriorOrders N,a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)).re+
      lam*centralStepMass a N := by
  rw [central_adjacent_eq,Complex.add_re,Complex.add_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he := (Complex.re_le_norm (∑ k∈centralOrders (N+1) (13*N/32),
    a (k-1)*(a (N+1-k)-a (N-k))/((N+2-k : ℕ) : ℂ))).trans
      (norm_central_step_le a N)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he hl)

/-- A one-sided estimate for ALL central orders together. The outer
orders retain their signed common phase, including logged order zero. -/
theorem central_adjacent_upper (a : ℕ→ℂ) {N : ℕ} (hN : 8≤N)
    {lam : ℝ} (hl : 1≤lam) (hu : lam≤13/9) :
    (-(∑ k∈centralOrders (N+1) (13*N/32),
      a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
      (lam : ℂ)*(∑ k∈Finset.Icc 1 (N+1-13*N/32),
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))).re≤
    (2/11)*separateCentralPrice a N lam+
      lam*(∑ k∈exteriorOrders N,
        a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)).re+
      lam*centralStepMass a N := by
  have hl0 : 0≤lam := by linarith only [hl]
  have hc : ‖∑ k∈centralOrders (N+1) (13*N/32),
      ((lam : ℂ)/((N+2-k : ℕ) : ℂ)-1/((N+1-k : ℕ) : ℂ))*
        (a (k-1)*a (N-k))‖≤(2/11)*separateCentralPrice a N lam := by
    apply (norm_sum_le _ _).trans
    rw [separateCentralPrice,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hd : 3≤N+1-k := by
      simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
      omega
    have he : N+2-k=N+1-k+1 := by
      simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk
      omega
    have hb := adjacent_coefficient_price (d:=((N+1-k : ℕ) : ℝ))
      (by exact_mod_cast hd) hl hu
    rw [he]
    push_cast
    rw [norm_mul]
    have hn : ‖((lam : ℂ)/((N+1-k : ℕ) +1)-1/((N+1-k : ℕ) : ℂ))‖=
        |lam/(((N+1-k : ℕ) : ℝ)+1)-1/((N+1-k : ℕ) : ℝ)| := by
      simpa only [Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_add,
        Complex.ofReal_one,Complex.ofReal_natCast,Real.norm_eq_abs] using
        Complex.norm_real (lam/(((N+1-k : ℕ) : ℝ)+1)-1/((N+1-k : ℕ) : ℝ))
    rw [hn]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (by ring)
  rw [central_adjacent_eq,Complex.add_re,Complex.add_re]
  have he := Complex.re_le_norm (∑ k∈centralOrders (N+1) (13*N/32),
    ((lam : ℂ)/((N+2-k : ℕ) : ℂ)-1/((N+1-k : ℕ) : ℂ))*(a (k-1)*a (N-k)))
  have hs := Complex.re_le_norm (∑ k∈centralOrders (N+1) (13*N/32),
    a (k-1)*(a (N+1-k)-a (N-k))/((N+2-k : ℕ) : ℂ))
  have hm := mul_le_mul_of_nonneg_left (hs.trans (norm_central_step_le a N)) hl0
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  linarith only [he,hc,hm]

/-- The adjacent-order price uses ONE injective high-order marginal;
there is no extra count, prime-pair or positive whole-core envelope. -/
theorem centralStepMass_le_cesaro (a : ℕ→ℂ) {C : ℝ} (hC : 0≤C)
    (ha : ∀ k,‖a k‖≤C) (N : ℕ) :
    centralStepMass a N≤4*C*((((N+2 : ℕ) : ℝ))⁻¹*
      ∑ k∈Finset.range (N+2),‖a (k+1)-a k‖) := by
  let S := centralOrders (N+1) (13*N/32)
  let e := fun k => ‖a (k+1)-a k‖
  have hS : ∀ k∈S,k≤N ∧ N+2≤4*(N+2-k) := by
    intro k hk
    simp only [S,centralOrders,Finset.mem_filter,Finset.mem_range] at hk
    omega
  have hp k (hk : k∈S) :
      ‖a (k-1)‖*‖a (N+1-k)-a (N-k)‖/((N+2-k : ℕ) : ℝ)≤
        (4*C/((N+2 : ℕ) : ℝ))*e (N-k) := by
    have hs := hS k hk
    have he : N+1-k=N-k+1 := by omega
    have hd : (0 : ℝ)<((N+2-k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0<N+2-k)
    have hn : (0 : ℝ)<((N+2 : ℕ) : ℝ) := by positivity
    have hden : (1 : ℝ)/((N+2-k : ℕ) : ℝ)≤4/((N+2 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hd hn).mpr
      norm_num only [one_mul]
      exact_mod_cast hs.2
    rw [he,div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (ha (k-1)) (norm_nonneg _))
      (by simpa only [one_div] using hden) (by positivity) (by positivity)).trans_eq (by
        dsimp only [e]
        ring)
  have hsub : S.image (fun k => N-k)⊆Finset.range (N+2) := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    have := hS k hk
    exact Finset.mem_range.mpr (by omega)
  have hi : Set.InjOn (fun k : ℕ => N-k) S := by
    intro k hk l hl he
    have := hS k hk
    have := hS l hl
    dsimp only at he
    omega
  have hm : (∑ k∈S,e (N-k))≤∑ k∈Finset.range (N+2),e k := by
    rw [←Finset.sum_image hi]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => norm_nonneg _)
  calc
    centralStepMass a N≤∑ k∈S,(4*C/((N+2 : ℕ) : ℝ))*e (N-k) :=
      Finset.sum_le_sum hp
    _ = (4*C/((N+2 : ℕ) : ℝ))*∑ k∈S,e (N-k) := by rw [Finset.mul_sum]
    _ ≤ (4*C/((N+2 : ℕ) : ℝ))*∑ k∈Finset.range (N+2),e k :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by dsimp only [e]; ring

/-- At any convergent complete-prime source, including multiplicity>=2,
the entire adjacent-order price vanishes. The source itself stays in the
signed central and outer sums, so this is not a ceiling by 42/25. -/
theorem centralStepMass_tendsto (a : ℕ→ℂ) {v : ℂ}
    (ha : Tendsto a atTop (𝓝 v)) :
    Tendsto (centralStepMass a) atTop (𝓝 0) := by
  obtain ⟨C,hC,haC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hb : ∀ k,‖a k‖≤C := fun k => haC (a k) (Set.mem_range_self k)
  have hd : Tendsto (fun k => ‖a (k+1)-a k‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,Function.comp_def] using
      ((ha.comp (tendsto_add_atTop_nat 1)).sub ha).norm
  have ht := ((hd.cesaro.comp (tendsto_add_atTop_nat 2)).const_mul (4*C))
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (a:=fun N => 4*C*((((N+2 : ℕ) : ℝ))⁻¹*
    ∑ k∈Finset.range (N+2),‖a (k+1)-a k‖)) ?_ ?_
  · intro N
    rw [Real.norm_of_nonneg (by
      unfold centralStepMass
      exact Finset.sum_nonneg (fun k _ => by positivity))]
    exact centralStepMass_le_cesaro a hC.le hb N
  · simpa only [Function.comp_def] using ht

/-- The actual floor-defined moving length supplies the coefficient
range. The integer cutoff and its added two are retained by the existing
length theorems. This assertion is uniform in height and needs no zero. -/
theorem length_factor_bounds {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    1≤(N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N) ∧
      (N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N)≤13/9 := by
  have hu0 : 0<u := by linarith only [hu]
  have huhi : u≤3/5 := hU.trans (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hup := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2≤N)
  have hlog2 : log 2≤3/4 := by linarith [log_two_lt_d9]
  have hlogN := mul_le_mul_of_nonneg_right hlog2 (Nat.cast_nonneg (α:=ℝ) N)
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  have hprod := mul_nonneg (show 0≤u-1/2 by linarith only [hu]) hL.le
  have humax := mul_le_mul_of_nonneg_right huhi hL.le
  constructor
  · apply (le_div_iff₀ (mul_pos hu0 hL)).mpr
    nlinarith only [hup,hlogN,humax,hNr]
  · apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
    nlinarith only [hlo,hprod,hNr]

/-- The full Selberg trace cancels exactly at EVERY multiplicity, not
only at a simple zero. Its ordinary-prime term and ONE diagonal remain. -/
theorem complete_selberg_join (u y : ℝ) {N : ℕ} (hN : 0<N) :
    (u : ℂ)^(N+1)*completeSelberg (N-1) y+
      harmonicEvaluation (ordinaryArray u y) u N=
    -ordinaryArray u y N+
      (∑ k∈centralOrders (N+1) (13*N/32),
        ordinaryArray u y (k-1)*ordinaryArray u y (N-k)/((N+1-k : ℕ) : ℂ))-
      (((N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ)*
        (∑ k∈Finset.Icc 1 (N+1-13*N/32),
          ordinaryArray u y (k-1)*ordinaryArray u y (N+1-k)/((N+2-k : ℕ) : ℂ))+
      (u : ℂ)^(N+1)*squareMoment N y/2 := by
  have he := scaled_completeSelberg_eq u y (N-1)
  have hn : N-1+1=N := by omega
  have hn2 : N-1+2=N+1 := by omega
  rw [hn,hn2] at he
  change _=traceError (ordinaryArray u y) (N-1)+_ at he
  rw [he]
  unfold traceError harmonicEvaluation
  rw [hn]
  push_cast
  ring

/-- Only geometric old mask, diagonal and radial errors enter this
budget. No Selberg-source or positive central allowance is paid twice. -/
def ceilingTransferBudget (u y : ℝ) (j : ℕ) : ℝ :=
  nativeSignedPeriodBudget u y j+prefixBudget (dyadicMomentOrder j)+
    ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*selbergEdgeConstant+
    ZetaRieszPairWholeCompletion.wholeCompletionBudget (dyadicMomentOrder j)+
    ZetaRieszPairJointQuadratic.squareBudget u (dyadicMomentOrder j)+
    (4*u/3)^(dyadicMomentOrder j)*(u*squareMass/2)

theorem ceilingTransferBudget_tendsto {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (ceilingTransferBudget u y) atTop (𝓝 0) := by
  have he := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    ZetaRieszLargeOrderCore.rate_bounds.1.le ZetaRieszLargeOrderCore.rate_bounds.2).mul_const
      selbergEdgeConstant).comp tendsto_dyadicMomentOrder
  have hr : 4*u/3<1 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  have hd := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0≤4*u/3) hr).mul_const
    (u*squareMass/2)).comp tendsto_dyadicMomentOrder
  have ht := (((((nativeSignedPeriodBudget_tendsto u y).add
    (prefixBudget_tendsto.comp tendsto_dyadicMomentOrder)).add he).add
    (ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto.comp tendsto_dyadicMomentOrder)).add
    ((ZetaRieszPairJointQuadratic.squareBudget_tendsto hu hU).comp tendsto_dyadicMomentOrder)).add hd
  convert ht using 1
  · rfl
  · norm_num

/-- The whole native carrier has a direct one-sided bound by its joined
prime and two adjacent factorial sums. The FULL trace is absent from the
price. This is an independent arithmetic inequality, not a source limit. -/
theorem eventually_native_joined_ceiling {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      let N := dyadicMomentOrder j
      let a := ordinaryArray u y
      let lam := (N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N)
      ((u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N
        (ZetaRieszNearCriticalCountPayment.countCeiling j)).re≤
      (a N-(∑ k∈centralOrders (N+1) (13*N/32),
        a (k-1)*a (N-k)/((N+1-k : ℕ) : ℂ))+
        (lam : ℂ)*(∑ k∈Finset.Icc 1 (N+1-13*N/32),
          a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))).re+
        ceilingTransferBudget u y j := by
  filter_upwards [eventually_native_signed_period_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
      with j hj hN
  dsimp only
  let N := dyadicMomentOrder j
  let a := ordinaryArray u y
  let c := (u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N
    (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hN0 : 0<N := by dsimp [N]; omega
  have hp := norm_literalPairDefect_sub_prefix_le hu.le hU hN hy
  have hh := norm_prefix_sub_ordinary_le hu.le hU hy hN
  have hs := (Classical.choose_spec exists_literalSelberg_completion_bound).2
    u y hu.le hU hy (N-1) (by dsimp [N]; omega)
  have hn1 : N-1+1=N := by omega
  have hn2 : N-1+2=N+1 := by omega
  rw [hn1,hn2] at hs
  have hsq := scaled_squareMoment_bound (by linarith only [hu] : 0≤u) y (N-1)
  rw [hn1,hn2] at hsq
  rw [lowCountPeriods_eq] at hj
  change |c.re+((literalSelberg u y N).re+(literalPairDefect u y N).re)|≤_ at hj
  have ep := (Complex.abs_re_le_norm (literalPairDefect u y N-prefixPairDefect u y N)).trans hp
  have eh := (Complex.abs_re_le_norm (prefixPairDefect u y N-harmonicEvaluation a u N)).trans hh
  have es := (Complex.abs_re_le_norm
    ((u : ℂ)^(N+1)*completeSelberg (N-1) y-literalSelberg u y N)).trans hs
  have ed := (Complex.abs_re_le_norm ((u : ℂ)^(N+1)*squareMoment N y/2)).trans hsq
  have he := complete_selberg_join u y hN0
  change _+harmonicEvaluation a u N=_ at he
  have her := congrArg Complex.re he
  simp only [Complex.sub_re,Complex.add_re,Complex.neg_re] at ep eh es her
  unfold ceilingTransferBudget
  change c.re≤_
  simp only [Complex.add_re,Complex.sub_re]
  dsimp only [selbergEdgeConstant,N,a] at ep eh es ed her ⊢
  linarith only [(abs_le.mp hj).2,(abs_le.mp ep).1,(abs_le.mp eh).1,
    (abs_le.mp es).2,(abs_le.mp ed).1,her]

/-- The checked 9/11 central coefficient saving is spent INSIDE
the whole native upper inequality. Ordinary-prime and outer-order terms
remain signed. Bounding their joint total by 42/25 is still OPEN. -/
theorem eventually_native_ceiling_central_saving {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      let N := dyadicMomentOrder j
      let a := ordinaryArray u y
      let lam := (N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N)
      ((u : ℂ)^(N+1)*ZetaRieszParityPacket.coreResponse u y N
        (ZetaRieszNearCriticalCountPayment.countCeiling j)).re≤
      (a N).re+(2/11)*separateCentralPrice a N lam+
        lam*(∑ k∈exteriorOrders N,a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)).re+
        lam*centralStepMass a N+ceilingTransferBudget u y j := by
  filter_upwards [eventually_native_joined_ceiling hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
    with j hj hN
  dsimp only at hj ⊢
  obtain ⟨hl,hh⟩ := length_factor_bounds hu.le hU hN
  have hc := central_adjacent_upper (ordinaryArray u y) (by omega : 8≤dyadicMomentOrder j) hl hh
  have he : (ordinaryArray u y (dyadicMomentOrder j)-
      (∑ k∈centralOrders (dyadicMomentOrder j+1) (13*dyadicMomentOrder j/32),
        ordinaryArray u y (k-1)*ordinaryArray u y (dyadicMomentOrder j-k)/
          ((dyadicMomentOrder j+1-k : ℕ) : ℂ))+
      (((dyadicMomentOrder j+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) : ℝ) : ℂ)*
        (∑ k∈Finset.Icc 1 (dyadicMomentOrder j+1-13*dyadicMomentOrder j/32),
          ordinaryArray u y (k-1)*ordinaryArray u y (dyadicMomentOrder j+1-k)/
            ((dyadicMomentOrder j+2-k : ℕ) : ℂ))).re=
      (ordinaryArray u y (dyadicMomentOrder j)).re+
      (-(∑ k∈centralOrders (dyadicMomentOrder j+1) (13*dyadicMomentOrder j/32),
        ordinaryArray u y (k-1)*ordinaryArray u y (dyadicMomentOrder j-k)/
          ((dyadicMomentOrder j+1-k : ℕ) : ℂ))+
      (((dyadicMomentOrder j+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) : ℝ) : ℂ)*
        (∑ k∈Finset.Icc 1 (dyadicMomentOrder j+1-13*dyadicMomentOrder j/32),
          ordinaryArray u y (k-1)*ordinaryArray u y (dyadicMomentOrder j+1-k)/
            ((dyadicMomentOrder j+2-k : ℕ) : ℂ))).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.neg_re]
    ring
  rw [he] at hj
  linarith only [hj,hc]

/-- The current endgame carrier pays only the original count and physical
bridges on top of the preceding jointly spent mask costs. -/
def physicalCeilingBudget (u y : ℝ) (j : ℕ) : ℝ :=
  ceilingTransferBudget u y j+ZetaRieszNearCriticalCountPayment.allowance j+
    2*(19/20 : ℝ)^(dyadicMomentOrder j)*zetaMoebiusLogMajorantMass (1+1/256)

theorem physicalCeilingBudget_tendsto {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (physicalCeilingBudget u y) atTop (𝓝 0) := by
  have hb := (((tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ)≤19/20) (by norm_num : (19/20 : ℝ)<1)).const_mul 2).mul_const
      (zetaMoebiusLogMajorantMass (1+1/256))).comp tendsto_dyadicMomentOrder
  have ht := ((ceilingTransferBudget_tendsto hu hU y).add
    ZetaRieszNearCriticalCountPayment.tendsto_allowance).add hb
  convert ht using 1
  · rfl
  · norm_num

/-- The actual source-equivalent `joinedPhysical` receives the 9/11
central-price saving, at all counts and every fixed admissible height.
The ordinary-prime and outer-order aggregate is still signed and unpaid;
this theorem does NOT bound it by the required constant 42/25. -/
theorem eventually_joinedPhysical_ceiling {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      let N := dyadicMomentOrder j
      let a := ordinaryArray u y
      let lam := (N+1 : ℝ)/(u*SquarefreeVaughanLogSource.length u N)
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re≤
      (a N).re+(2/11)*separateCentralPrice a N lam+
        lam*(∑ k∈exteriorOrders N,a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ)).re+
        lam*centralStepMass a N+physicalCeilingBudget u y j := by
  filter_upwards [eventually_native_ceiling_central_saving hu hU hy,
    ZetaRieszNearCriticalCountPayment.eventually_norm_core_count_change_le,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))]
    with j hj hcount hN
  dsimp only at hj ⊢
  have hc := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    (ZetaRieszParityPacket.coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszParityPacket.coreResponse u y (dyadicMomentOrder j)
        (ZetaRieszNearCriticalCountPayment.countCeiling j)))).trans
          (hcount u y (by linarith only [hu] : 0≤u) hU)
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith only [hu] : 0<u) hU
  have hL : (11/8 : ℝ)*dyadicMomentOrder j≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) (dyadicMomentOrder j)]
  have hp := (Complex.abs_re_le_norm ((u : ℂ)^(dyadicMomentOrder j+1)*
    (ZetaRieszParityPacket.coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)))).trans
      (ZetaRieszGammaJoint.core_joined_bound (by linarith only [hu] : 0≤u) hU _ _ y hL)
  rw [mul_sub,Complex.sub_re] at hc hp
  unfold physicalCeilingBudget
  linarith only [hj,(abs_le.mp hc).2,(abs_le.mp hp).1]

end RiemannGaussian.ZetaRieszCeilingOrderCancellation
