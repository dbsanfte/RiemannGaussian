/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairPhaseCreditGrowth
import RiemannGaussian.ZetaSignedPoleZeroFree
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# An independent fixed-height radius for the joined signed main

The actual zero-free line supplies a Cauchy radius strictly larger than
one half at every fixed nonzero height. The radius is not claimed to
exceed the requested source radius. Keeping the correlated total order
in each of the four joined slots gives a bound with rate `u/R`, before
any favorable credit is separated. Decay needs the additional `u<R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology Metric Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJoinedPhaseRadius
open ZetaRieszPairPrimePowerPayment ZetaRieszSelbergSourceAudit
open ZetaRieszPairPrefixPayment ZetaRieszHeadOrders
open ZetaRieszPairPrefixConvolution

private theorem analytic_closed_half {y : ℝ} (hy : 54≤|y|) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) (1/2)) := by
  intro s hs
  have hd : ‖s-(3/2+Complex.I*y)‖≤(1/2 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hs
  have hr : 1 ≤ s.re := by
    have hl := (abs_le.mp ((Complex.abs_re_le_norm (s-(3/2+Complex.I*y))).trans hd)).1
    norm_num at hl
    linarith only [hl]
  have hs1 : s≠1 := by
    intro he
    have hi := (Complex.abs_im_le_norm (s-(3/2+Complex.I*y))).trans hd
    rw [he] at hi
    norm_num at hi
    linarith only [hi,hy]
  have ha := analyticOn_riemannZeta s (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact (ha.deriv.div ha (riemannZeta_ne_zero_of_one_le_re hr)).neg

/-- Compactness enlarges the ACTUAL zero-free boundary disk. No
exposed zero, rightmost assumption or local artificial mode is used.
The new margin can depend on height and has no uniform lower bound here. -/
theorem exists_analytic_radius {y : ℝ} (hy : 54≤|y|) :
    ∃ R : ℝ,1/2<R ∧ R<3/4 ∧
      AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
        (closedBall (3/2+Complex.I*y) R) := by
  let f := fun s : ℂ => -logDeriv riemannZeta s
  let c : ℂ := 3/2+Complex.I*y
  have hbase : closedBall c (1/2)⊆{s | AnalyticAt ℂ f s} := analytic_closed_half hy
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_closedBall c (1/2)).exists_cthickening_subset_open
    (isOpen_analyticAt ℂ f) hbase
  let e := min (δ/2) (1/8)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have hed : e≤δ/2 := min_le_left _ _
  have he8 : e≤1/8 := min_le_right _ _
  refine ⟨1/2+e,by linarith only [he],by linarith only [he8],?_⟩
  intro s hs
  apply hthick
  rw [cthickening_closedBall hδ.le (by norm_num)]
  exact (closedBall_subset_closedBall (by linarith only [hed,hδ])) hs

/-- Cauchy bounds for the actual ordinary-prime moments from an
independently proved analytic disk. All logged orders, including zero,
are retained; the proper-prime-power radius has the same exact rate. -/
theorem ordinary_moment_bound_of_analytic_radius {R y : ℝ}
    (hRl : 1/2<R) (hRu : R<3/4)
    (ha : AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) R)) :
    ∃ C : ℝ,0<C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k := by
  obtain ⟨B,hB⟩ := ((isCompact_closedBall (3/2+Complex.I*y) R).image_of_continuousOn
    ha.continuousOn).isBounded.exists_norm_le
  let M := max B 0+1
  let P := zetaProperPrimePowerExpMass (3/2-R)
  have hM : 0<M := by dsimp only [M]; linarith only [le_max_right B 0]
  have hP : 0≤P := zetaProperPrimePowerExpMass_nonneg _
  refine ⟨M+P,by linarith only [hM,hP],?_⟩
  intro k
  have hfull : ‖zetaPrimeLogMoment k (3/2+Complex.I*y)‖≤M/R^k := by
    apply norm_signedTaylorMoment_le (by linarith only [hRl])
      (ha.differentiableOn.diffContOnCl_ball (by intro s hs; exact hs))
    intro s hs
    have hb := hB _ (mem_image_of_mem _ (sphere_subset_closedBall hs))
    exact hb.trans (show B≤M by dsimp only [M]; linarith only [le_max_left B 0])
  have hpower := norm_zetaProperPrimePowerMoment_le k y
    (show 0<R by linarith only [hRl]) (show R<1 by linarith only [hRu])
  have he := zetaPrimeLogMoment_eq_prime_add_proper k
    (by norm_num : 1<(3/2+Complex.I*(y : ℂ)).re)
  have ho : zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)=
      zetaPrimeLogMoment k (3/2+Complex.I*y)-zetaProperPrimePowerMoment k (3/2+Complex.I*y) := by
    rw [he,add_sub_cancel_right]
  rw [ho]
  apply ((norm_sub_le _ _).trans (add_le_add hfull hpower)).trans_eq
  dsimp only [P]
  rw [div_eq_mul_inv,div_eq_mul_inv,inv_pow]
  ring

/-- A single independent geometric bound for ALL complete ordinary-prime
logged orders. The radius is actual, not an assumed exposed spectral gap
or a uniform radius beyond `u`. -/
theorem exists_ordinary_moment_bound {y : ℝ} (hy : 54≤|y|) :
    ∃ R C : ℝ,1/2<R ∧ R<3/4 ∧ 0<C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k := by
  obtain ⟨R,hRl,hRu,ha⟩ := exists_analytic_radius hy
  obtain ⟨C,hC,hm⟩ := ordinary_moment_bound_of_analytic_radius hRl hRu ha
  exact ⟨R,C,hRl,hRu,hC,hm⟩

/-- The existing signed-pole region supplies a concrete disk on this
height range. These heights are ALREADY zero-free in the candidate strip;
this theorem transfers their existing coverage, not a new exclusion. -/
theorem analytic_concrete_radius_of_log_height {y : ℝ} (hy : 54≤|y|)
    (hlog : log (|y|+3)≤1800) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (3/2+Complex.I*y) (100011/200000)) := by
  intro s hs
  have hd : ‖s-(3/2+Complex.I*y)‖≤(100011/200000 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hs
  have hr : (1-11/200000 : ℝ) ≤ s.re := by
    have hl := (abs_le.mp ((Complex.abs_re_le_norm (s-(3/2+Complex.I*y))).trans hd)).1
    norm_num at hl
    linarith only [hl]
  have hi : |s.im-y|≤(100011/200000 : ℝ) := by
    have hh := (Complex.abs_im_le_norm (s-(3/2+Complex.I*y))).trans hd
    norm_num at hh
    exact hh
  have hyb : |s.im|+2≤|y|+3 := by
    have hh := abs_add_le (s.im-y) y
    rw [sub_add_cancel] at hh
    linarith only [hh,hi]
  have hls : log (|s.im|+2)≤1800 :=
    (Real.log_le_log (by positivity) hyb).trans hlog
  have hw : (11/200000 : ℝ)<zetaSignedPoleZeroMargin s.im := by
    unfold zetaSignedPoleZeroMargin
    apply (lt_div_iff₀ (zetaSignedPole_denominator_pos s.im)).mpr
    linarith only [hls]
  have hs1 : s≠1 := by
    intro he
    rw [he] at hi
    norm_num at hi
    linarith only [hi,hy]
  have ha := analyticOn_riemannZeta s
    (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact (ha.deriv.div ha (riemannZeta_ne_zero_of_signedPole_margin hs1
    (by linarith only [hr,hw]))).neg

/-- A numerical Cauchy rate for ALL logged ordinary-prime orders at
each fixed height in the region already covered by signed-pole bounds.
The unspecified constant depends on height, not on radius or order. -/
theorem exists_ordinary_bound_concrete_height {y : ℝ} (hy : 54≤|y|)
    (hlog : log (|y|+3)≤1800) :
    ∃ C : ℝ,0<C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤
        C/(100011/200000 : ℝ)^k :=
  ordinary_moment_bound_of_analytic_radius (by norm_num) (by norm_num)
    (analytic_concrete_radius_of_log_height hy hlog)

private theorem correlated_product (a : ℕ→ℂ) {D r : ℝ} (hD : 0≤D) (hr : 0≤r)
    (ha : ∀ k,‖a k‖≤D*r^k) (i j : ℕ) :
    ‖a i*a j‖≤D^2*r^(i+j) := by
  rw [norm_mul]
  exact (mul_le_mul (ha i) (ha j) (norm_nonneg _) (by positivity)).trans_eq
    (by rw [pow_add]; ring)

private theorem harmonic_slot_bound (a : ℕ→ℂ) {D r : ℝ} (hD : 0≤D) (hr : 0≤r)
    (ha : ∀ k,‖a k‖≤D*r^k) {N : ℕ} (hN : 0<N) (t : ℕ) (S : Finset ℕ)
    (hcard : S.card≤2*N) (hS : ∀ k∈S,0<k ∧ k≤t ∧ N≤4*(t+1-k)) :
    ‖∑ k∈S,a (k-1)*a (t-k)/((t+1-k : ℕ) : ℂ)‖≤8*D^2*r^(t-1) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hp k (hk : k∈S) :
      ‖a (k-1)*a (t-k)/((t+1-k : ℕ) : ℂ)‖≤
        (4/(N : ℝ))*(D^2*r^(t-1)) := by
    obtain ⟨hk0,hkt,hden⟩ := hS k hk
    have hd : (0 : ℝ)<((t+1-k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0<t+1-k)
    have hdiv : (1 : ℝ)/((t+1-k : ℕ) : ℝ)≤4/(N : ℝ) :=
      (div_le_div_iff₀ hd hNr).mpr (by
        simpa only [one_mul] using
          (show (N : ℝ)≤4*((t+1-k : ℕ) : ℝ) by exact_mod_cast hden))
    have hh := correlated_product a hD hr ha (k-1) (t-k)
    rw [show k-1+(t-k)=t-1 by omega] at hh
    rw [norm_div,Complex.norm_natCast,div_eq_mul_inv]
    exact (mul_le_mul hh (by simpa only [one_div] using hdiv)
      (by positivity) (by positivity)).trans_eq (by ring)
  have hcr : (S.card : ℝ)≤2*(N : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ ∑ _k∈S,(4/(N : ℝ))*(D^2*r^(t-1)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hp)
    _ = (S.card : ℝ)*((4/(N : ℝ))*(D^2*r^(t-1))) := by simp
    _ ≤ (2*(N : ℝ))*((4/(N : ℝ))*(D^2*r^(t-1))) :=
      mul_le_mul_of_nonneg_right hcr (by positivity)
    _ = _ := by field_simp; ring

private theorem length_factor {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) :
    ‖((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)‖≤3/2 := by
  have hu0 : 0<u := by linarith only [hu]
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  have hprod := mul_nonneg (show 0≤u-1/2 by linarith only [hu]) hL.le
  have hNr : (65536 : ℝ)≤N := by exact_mod_cast hN
  rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_real,
    Real.norm_of_nonneg hu0.le,Complex.norm_real,Real.norm_of_nonneg hL.le]
  apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
  push_cast
  nlinarith only [hlo,hprod,hNr]

/-- Preserve each correlated TOTAL order before bounding the joined
four slots. A radius estimate loses neither a second exponent nor any
logged order-zero channel. This is a bound for the existing evaluator. -/
theorem norm_harmonicEvaluation_le_geometric (a : ℕ→ℂ) {D r u : ℝ}
    (hD : 0≤D) (hr : 2/3≤r) (ha : ∀ k,‖a k‖≤D*r^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536≤N) :
    ‖harmonicEvaluation a u N‖≤26*D^2*r^N := by
  have hr0 : 0≤r := by linarith only [hr]
  have hN0 : 0<N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN0
  have ht : ‖(∑ k∈Finset.range N,a k*a (N-1-k))/(N : ℂ)‖≤D^2*r^(N-1) := by
    rw [norm_div,Complex.norm_natCast]
    calc
      _ ≤ (∑ _k∈Finset.range N,D^2*r^(N-1))/(N : ℝ) := by
        apply div_le_div_of_nonneg_right _ hNr.le
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hh := correlated_product a hD hr0 ha k (N-1-k)
        simpa only [show k+(N-1-k)=N-1 by have := Finset.mem_range.mp hk; omega] using hh
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; field_simp
  have hc := harmonic_slot_bound a hD hr0 ha hN0 N (centralOrders (N+1) (13*N/32))
    ((Finset.card_filter_le _ _).trans (by simp only [Finset.card_range]; omega))
    (by intro k hk; simp only [centralOrders,Finset.mem_filter,Finset.mem_range] at hk; omega)
  have hp := harmonic_slot_bound a hD hr0 ha hN0 (N+1)
    (Finset.Icc 1 (N+1-13*N/32))
    (by simp only [Nat.card_Icc]; omega)
    (by intro k hk; rw [Finset.mem_Icc] at hk; omega)
  rw [Nat.add_sub_cancel] at hp
  have hf : ‖((N+1 : ℕ) : ℂ)/((u : ℂ)*SquarefreeVaughanLogSource.length u N)*
      (∑ k∈Finset.Icc 1 (N+1-13*N/32),a (k-1)*a (N+1-k)/((N+2-k : ℕ) : ℂ))‖≤
      12*D^2*r^N := by
    rw [norm_mul]
    exact (mul_le_mul (length_factor hu hU hN) hp (norm_nonneg _) (by norm_num)).trans_eq
      (by ring)
  have hpow : r^(N-1)≤(3/2 : ℝ)*r^N := by
    have he : r^N=r^(N-1)*r := by rw [←pow_succ,show N-1+1=N by omega]
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left (show 1≤(3/2 : ℝ)*r by linarith only [hr])
      (pow_nonneg hr0 (N-1))
    simpa only [mul_one,mul_comm,mul_left_comm,mul_assoc] using hmul
  unfold harmonicEvaluation
  apply (norm_sub_le _ _).trans
  apply ((add_le_add ((norm_add_le _ _).trans (add_le_add ht hc)) hf)).trans
  have hsave := mul_le_mul_of_nonneg_left hpow (show 0≤9*D^2 by positivity)
  have hn : 0≤D^2*r^N := by positivity
  nlinarith only [hsave,hn]

/-- Apply the actual Cauchy moment bound to the WHOLE ordinary-prime
quadratic. The new rate is `u/R`, not `2*u`; it need not be below one. -/
theorem norm_joined_ordinary_le {R C u y : ℝ} (hRl : 1/2<R) (hRu : R<3/4)
    (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {N : ℕ} (hN : 65536≤N) :
    ‖harmonicEvaluation (ordinaryArray u y) u N‖≤26*C^2*(u/R)^N := by
  have hR : 0<R := by linarith only [hRl]
  have hu0 : 0≤u := by linarith only [hu]
  have hur : (2/3 : ℝ)≤u/R := (le_div_iff₀ hR).mpr (by linarith only [hRu,hu])
  have ha k : ‖ordinaryArray u y k‖≤(C*u)*(u/R)^k := by
    unfold ordinaryArray
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
    apply (mul_le_mul_of_nonneg_left (hm k) (pow_nonneg hu0 (k+1))).trans_eq
    rw [div_pow,pow_succ]
    ring
  have hb := norm_harmonicEvaluation_le_geometric (ordinaryArray u y)
    (mul_nonneg hC hu0) hur ha hu hU hN
  have hu1 : u≤1 := by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU; linarith only [hU]
  have hCu := mul_le_mul_of_nonneg_left hu1 hC
  have hs : (C*u)^2≤C^2 := pow_le_pow_left₀ (mul_nonneg hC hu0) (by simpa only [mul_one] using hCu) 2
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ)≤26)) (by positivity))

/-- Expose the already-paid whole-support/square bridge WITHOUT the
exposed-array hypotheses needed by the separate proper-power payment. -/
theorem norm_prefix_sub_ordinary_le {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    {N : ℕ} (hN : 65536≤N) :
    ‖prefixPairDefect u y N-harmonicEvaluation (ordinaryArray u y) u N‖≤
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N := by
  have hu0 : u≠0 := by linarith only [hu]
  have ht := ((tendsto_const_nhds (x := prefixPairDefect u y N)).sub
    (finite_quadratic_tendsto hu0 y N)).norm
  exact le_of_tendsto ht
    (ZetaRieszPairJointQuadratic.eventually_norm_prefix_sub_quadratic_le hu hU hy hN)

/-- An independent bound for the ENTIRE literal retained signed main.
All favorable and unfavorable terms stay joined. Only the two existing
geometric mask/diagonal errors appear; no source hypothesis is used. -/
theorem norm_prefix_le_radius {R C u y : ℝ} (hRl : 1/2<R) (hRu : R<3/4)
    (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N : ℕ} (hN : 65536≤N) :
    ‖prefixPairDefect u y N‖≤26*C^2*(u/R)^N+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N := by
  have he : prefixPairDefect u y N=
      harmonicEvaluation (ordinaryArray u y) u N+
        (prefixPairDefect u y N-harmonicEvaluation (ordinaryArray u y) u N) := by ring
  rw [he]
  exact ((norm_add_le _ _).trans
    (add_le_add (norm_joined_ordinary_le hRl hRu hC hm hu hU hN)
      (norm_prefix_sub_ordinary_le hu hU hy hN))).trans_eq (by ring)

/-- A strictly improved actual-phase exponent at every fixed height.
This does NOT say that `R>u` for the full requested radius interval. -/
theorem exists_global_signed_radius_bound {y : ℝ} (hy : 54≤|y|) :
    ∃ R C : ℝ,1/2<R ∧ R<3/4 ∧ 0<C ∧ ∀ u : ℝ,
      1/2≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ,65536≤N →
      ‖prefixPairDefect u y N‖≤26*C^2*(u/R)^N+
        ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
          ZetaRieszPairJointQuadratic.squareBudget u N := by
  obtain ⟨R,C,hRl,hRu,hC,hm⟩ := exists_ordinary_moment_bound hy
  exact ⟨R,C,hRl,hRu,hC,fun _ hu hU _ hN => norm_prefix_le_radius hRl hRu hC.le hm hu hU hy hN⟩

/-- The signed rest and its ENTIRE exact favorable credit satisfy the
radius bound TOGETHER. No termwise norm is taken on either population. -/
theorem joint_rest_sub_credit_le_radius {R C u y : ℝ} (hRl : 1/2<R) (hRu : R<3/4)
    (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N : ℕ} (hN : 65536≤N) :
    ((u : ℂ)^(N+1)*∑ n∈
      ((ZetaRieszGlobalPeriodEdgePayment.completePeriodLabels
        (ZetaRieszLowCountSignedBoundary.joinedLabels u N) N y).filter (fun n => ¬n.Prime))\
          ZetaRieszJoinedPairSignCover.favorableLabels u y N,
      (prefixCoefficient u N n-ZetaRieszLowCountSelbergAudit.selbergCoefficient n)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      ZetaRieszJoinedPairSignCover.exactSignCredit u y N≤26*C^2*(u/R)^N+
        ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
          ZetaRieszPairJointQuadratic.squareBudget u N := by
  rw [←ZetaRieszJoinedPairSignCover.prefix_eq_rest_sub_exact_credit]
  exact (Complex.re_le_norm _).trans (norm_prefix_le_radius hRl hRu hC hm hu hU hy hN)

/-- The explicit whole-main bound tends to zero exactly in the
source-subcritical radius regime. No zero/source hypothesis is added. -/
theorem prefix_tendsto_zero_of_radius {R C u y : ℝ} (hRl : 1/2<R) (hRu : R<3/4)
    (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (hur : u<R) : Tendsto (prefixPairDefect u y) atTop (𝓝 0) := by
  have hR : 0<R := by linarith only [hRl]
  have hr : u/R<1 := (div_lt_one hR).mpr hur
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (by linarith only [hu]) hR.le) hr).const_mul (26*C^2)
  have hlim : Tendsto (fun N => 26*C^2*(u/R)^N+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (ht.add ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto).add
        (ZetaRieszPairJointQuadratic.squareBudget_tendsto (by linarith only [hu]) hU)
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN =>
    norm_prefix_le_radius hRl hRu hC hm hu hU hy hN) hlim

/-- Uniformity over a whole source-radius interval follows from one
strict analytic margin `v<R`. The original masks and moving length are
retained for every radius, not merely at one chosen endpoint. -/
theorem eventually_uniform_prefix_small {R C v y : ℝ} (hRl : 1/2<R) (hRu : R<3/4)
    (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hv : 1/2≤v) (hvU : v≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    (hvr : v<R) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ u : ℝ,1/2≤u → u≤v → ‖prefixPairDefect u y N‖<ε := by
  have hR : 0<R := by linarith only [hRl]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg (by linarith only [hv]) hR.le) ((div_lt_one hR).mpr hvr)).const_mul (26*C^2)
  have hs := ZetaRieszPairJointQuadratic.squareBudget_tendsto
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]) le_rfl
  have hlim : Tendsto (fun N => 26*C^2*(v/R)^N+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget ZetaRieszWideOwnerAudit.radiusCeiling N)
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (ht.add ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto).add hs
  filter_upwards [hlim.eventually_lt_const hε,eventually_ge_atTop (65536 : ℕ)] with N hsmall hN u hu huv
  have hU := huv.trans hvU
  have hp := norm_prefix_le_radius hRl hRu hC hm hu hU hy hN
  have hgeom : 26*C^2*(u/R)^N≤26*C^2*(v/R)^N := by
    gcongr
  have hsq : ZetaRieszPairJointQuadratic.squareBudget u N≤
      ZetaRieszPairJointQuadratic.squareBudget ZetaRieszWideOwnerAudit.radiusCeiling N := by
    simpa only [ZetaRieszPairJointQuadratic.squareBudget,
      show 4*ZetaRieszWideOwnerAudit.radiusCeiling/3=(10001/15000 : ℝ) by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]] using
      ZetaRieszPairJointQuadratic.squareBudget_le_uniform (by linarith only [hu]) hU N
  exact (hp.trans (add_le_add (add_le_add hgeom le_rfl) hsq)).trans_lt hsmall

/-- A genuine independent cofinal bound for the retained signed main on
a NONEMPTY, height-dependent radius interval. It does not certify that
this interval reaches `10001/20000` at every height. -/
theorem exists_height_local_joint_floor {y : ℝ} (hy : 54≤|y|) :
    ∃ v : ℝ,1/2<v ∧ v≤ZetaRieszWideOwnerAudit.radiusCeiling ∧
      ∀ᶠ N : ℕ in atTop,∀ u : ℝ,1/2≤u → u≤v →
        (prefixPairDefect u y N).re<(399/5000 : ℝ) := by
  obtain ⟨R,C,hRl,hRu,hC,hm⟩ := exists_ordinary_moment_bound hy
  let v := min ((R+1/2)/2) ZetaRieszWideOwnerAudit.radiusCeiling
  have hv : 1/2<v := lt_min (by linarith only [hRl])
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have hvU : v≤ZetaRieszWideOwnerAudit.radiusCeiling := min_le_right _ _
  have hvr : v<R := (min_le_left _ _).trans_lt (by linarith only [hRl])
  refine ⟨v,hv,hvU,?_⟩
  filter_upwards [eventually_uniform_prefix_small hRl hRu hC.le hm hv.le hvU hy hvr
    (by norm_num : (0 : ℝ)<399/5000)] with N hN u hu huv
  exact (Complex.re_le_norm _).trans_lt (hN u hu huv)

/-- A concrete geometric bound for the WHOLE signed sum over the entire
requested radius interval, at heights ALREADY covered by the project's
signed-pole region. No entry order or numerical size for `C` is asserted. -/
theorem exists_concrete_height_joint_bound {y : ℝ} (hy : 54≤|y|)
    (hlog : log (|y|+3)≤1800) :
    ∃ C : ℝ,0<C ∧ ∀ u : ℝ,1/2≤u →
      u≤ZetaRieszWideOwnerAudit.radiusCeiling → ∀ N : ℕ,65536≤N →
      ‖prefixPairDefect u y N‖≤26*C^2*(100010/100011 : ℝ)^N+
        ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
          ZetaRieszPairJointQuadratic.squareBudget u N := by
  obtain ⟨C,hC,hm⟩ := exists_ordinary_bound_concrete_height hy hlog
  refine ⟨C,hC,?_⟩
  intro u hu hU N hN
  have hb := norm_prefix_le_radius (by norm_num : (1/2 : ℝ)<100011/200000)
    (by norm_num : (100011/200000 : ℝ)<3/4) hC.le hm hu hU hy hN
  have hr : u/(100011/200000 : ℝ)≤100010/100011 := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  exact hb.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hr N) (by positivity)) le_rfl) le_rfl)

/-- An independent cofinal 399/5000 bound, uniform over ALL requested
radii, on this already-excluded height range. This is a carrier estimate,
not a new zero-free region or the all-height floor. -/
theorem eventually_concrete_height_joint_floor {y : ℝ} (hy : 54≤|y|)
    (hlog : log (|y|+3)≤1800) :
    ∀ᶠ N : ℕ in atTop,∀ u : ℝ,1/2≤u →
      u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      (prefixPairDefect u y N).re<(399/5000 : ℝ) := by
  obtain ⟨C,hC,hm⟩ := exists_ordinary_bound_concrete_height hy hlog
  have hb := eventually_uniform_prefix_small
    (by norm_num : (1/2 : ℝ)<100011/200000)
    (by norm_num : (100011/200000 : ℝ)<3/4) hC.le hm
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling]) le_rfl hy
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
      ZetaRieszWideOwnerAudit.radiusCeiling<(100011/200000 : ℝ))
    (by norm_num : (0 : ℝ)<399/5000)
  filter_upwards [hb] with N hN u hu hU
  exact (Complex.re_le_norm _).trans_lt (hN u hu hU)

/-- Quantitative GLOBAL cancellation relative to the ENTIRE exact
favorable credit. Even if `u/R` is not below one, the cancellation rate
`1/(2*R)` is. This does not claim source-scale decay of the main. -/
theorem exists_joint_credit_cancellation_rate {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∃ R D : ℝ,1/2<R ∧ R<3/4 ∧ 0<D ∧
      ∀ᶠ N : ℕ in atTop,
        ‖prefixPairDefect u y N‖≤
          D*((N : ℝ)+1)^3*(1/(2*R))^N*
            ZetaRieszJoinedPairSignCover.exactSignCredit u y N+
          (ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
            ZetaRieszPairJointQuadratic.squareBudget u N) := by
  obtain ⟨R,C,hRl,hRu,hC,hm⟩ := exists_ordinary_moment_bound hy
  obtain ⟨c,hc,hcredit⟩ := ZetaRieszPairPhaseCreditGrowth.eventually_exactSignCredit_growth
    hu hU hy
  let D := 26*C^2/c
  have hD : 0<D := by dsimp only [D]; positivity
  have hR : 0<R := by linarith only [hRl]
  have hu0 : 0<u := by linarith only [hu]
  refine ⟨R,D,hRl,hRu,hD,?_⟩
  filter_upwards [hcredit,eventually_ge_atTop (65536 : ℕ)] with N hcr hN
  have hid : 26*C^2*(u/R)^N=
      (D*((N : ℝ)+1)^3*(1/(2*R))^N)*(c*(2*u)^N/((N : ℝ)+1)^3) := by
    dsimp only [D]
    rw [div_pow,div_pow,mul_pow,mul_pow]
    field_simp
    ring
  have hg : 26*C^2*(u/R)^N≤D*((N : ℝ)+1)^3*(1/(2*R))^N*
      ZetaRieszJoinedPairSignCover.exactSignCredit u y N := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hcr (by positivity)
  exact (norm_prefix_le_radius hRl hRu hC.le hm hu.le hU hy hN).trans
    (by linarith only [hg])

/-- The whole main, divided by the full growing actual-prime credit,
tends to zero at EVERY fixed height. Thus the signed rest matches that
credit in relative size; the absolute 399/5000 target can still be open. -/
theorem prefix_div_exact_credit_tendsto_zero {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun N => ‖prefixPairDefect u y N‖/
      ZetaRieszJoinedPairSignCover.exactSignCredit u y N) atTop (𝓝 0) := by
  obtain ⟨R,D,hRl,_hRu,hD,hbound⟩ := exists_joint_credit_cancellation_rate hu hU hy
  have hR : 0<R := by linarith only [hRl]
  have hr0 : 0<(1/(2*R) : ℝ) := by positivity
  have hr1 : (1/(2*R) : ℝ)<1 := (div_lt_one (by positivity)).mpr
    (by linarith only [hRl])
  have hgeom : Tendsto (fun N : ℕ => D*((N : ℝ)+1)^3*(1/(2*R))^N) atTop (𝓝 0) := by
    simpa only [mul_assoc,mul_zero] using
      (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3 hr0 hr1).const_mul D
  have hcredit := ZetaRieszPairPhaseCreditGrowth.exactSignCredit_tendsto_atTop hu hU hy
  have herror := (ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto.add
    (ZetaRieszPairJointQuadratic.squareBudget_tendsto
      (by linarith only [hu] : 0≤u) hU)).div_atTop hcredit
  have ht : Tendsto (fun N : ℕ => D*((N : ℝ)+1)^3*(1/(2*R))^N+
      (ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N)/
          ZetaRieszJoinedPairSignCover.exactSignCredit u y N) atTop (𝓝 0) := by
    simpa only [add_zero] using hgeom.add herror
  apply squeeze_zero' _ _ ht
  · filter_upwards [hcredit.eventually_gt_atTop 0] with N hpos
    exact div_nonneg (norm_nonneg _) hpos.le
  · filter_upwards [hbound,hcredit.eventually_gt_atTop 0] with N hb hpos
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ _ := hb
      _ = _ := by field_simp

/-- The literal signed rest and the ENTIRE actual-prime favorable credit
match in relative size. This is global across the retained support; it
does not control the absolute signed difference by 399/5000. -/
theorem signed_rest_div_exact_credit_tendsto_one {u y : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun N =>
      ((u : ℂ)^(N+1)*∑ n∈
        ((ZetaRieszGlobalPeriodEdgePayment.completePeriodLabels
          (ZetaRieszLowCountSignedBoundary.joinedLabels u N) N y).filter (fun n => ¬n.Prime))\
            ZetaRieszJoinedPairSignCover.favorableLabels u y N,
        (prefixCoefficient u N n-ZetaRieszLowCountSelbergAudit.selbergCoefficient n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re/
        ZetaRieszJoinedPairSignCover.exactSignCredit u y N) atTop (𝓝 1) := by
  have hc := ZetaRieszPairPhaseCreditGrowth.exactSignCredit_tendsto_atTop hu hU hy
  have hr : Tendsto (fun N => (prefixPairDefect u y N).re/
      ZetaRieszJoinedPairSignCover.exactSignCredit u y N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (prefix_div_exact_credit_tendsto_zero hu hU hy)
    filter_upwards [hc.eventually_gt_atTop 0] with N hpos
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hpos.le
  have ht : Tendsto (fun N => (prefixPairDefect u y N).re/
      ZetaRieszJoinedPairSignCover.exactSignCredit u y N+1) atTop (𝓝 1) := by
    simpa only [zero_add] using hr.add tendsto_const_nhds
  apply ht.congr'
  filter_upwards [hc.eventually_gt_atTop 0] with N hpos
  rw [ZetaRieszJoinedPairSignCover.prefix_eq_rest_sub_exact_credit]
  field_simp
  ring

/-- A nonzero ordinary-prime source prevents moving the Cauchy radius
beyond its source radius. Relative cancellation is still compatible with
that source. Thus assuming `R>u` is not a legitimate new endgame payment. -/
theorem radius_le_of_nonzero_ordinary_source {R C u y : ℝ} {a : ℂ}
    (hR : 0<R) (hu : 0<u)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+Complex.I*y)‖≤C/R^k)
    (hsource : Tendsto (ordinaryArray u y) atTop (𝓝 a)) (ha : a≠0) : R≤u := by
  by_contra hn
  have hur : u<R := lt_of_not_ge hn
  have hb k : ‖ordinaryArray u y k‖≤(C*u)*(u/R)^k := by
    unfold ordinaryArray
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
    apply (mul_le_mul_of_nonneg_left (hm k) (pow_nonneg hu.le (k+1))).trans_eq
    rw [div_pow,pow_succ]
    ring
  have ht : Tendsto (fun k : ℕ => (C*u)*(u/R)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hu.le hR.le) ((div_lt_one hR).mpr hur)).const_mul (C*u)
  have hzero : Tendsto (ordinaryArray u y) atTop (𝓝 0) := squeeze_zero_norm hb ht
  exact ha (tendsto_nhds_unique hsource hzero)

end RiemannGaussian.ZetaRieszJoinedPhaseRadius
