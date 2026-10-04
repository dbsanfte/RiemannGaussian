/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelbergSignedBoundary
import RiemannGaussian.ZetaRieszJoinedPhaseRadius

/-!
# Signed cancellation between the unchanged balanced mask and its literal rest

The two terms below are precisely the two existing pieces of
`prefixPairDefect`. No completion, phase replacement or prime subdivision is
made on either piece. The whole-support radius estimate is applied only after
their exact sum has been restored.

At the test height `19*pi`, the balanced term tends to positive infinity and
its actual native mask complement tends to negative infinity, whereas their
sum tends to zero geometrically. The height is not asserted to be a zero
ordinate. This tests the necessity of a JOINT signed boundary estimate; it
does not provide the all-height exposed-source ceiling.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open Complex (I)
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSelbergMaskCancellation
open ZetaRieszSelbergAdjacentOrders ZetaRieszSelbergSignedBoundary
open ZetaRieszGlobalHeadPriceAudit ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszLowCountSignedBoundary ZetaRieszLowCountSelbergAudit
open ZetaRieszPairPrefixPayment ZetaRieszJoinedPhaseRadius

/-- The whole original balanced contribution, including both signed prefixes. -/
def balancedPrefix (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ e∈balancedPairs N,
    (prefixCoefficient u N (e.1*e.2)-selbergCoefficient (e.1*e.2))*
      zetaPrimeLogKernel N (3/2+I*y) (e.1*e.2)

/-- Its exact existing native complement; none of its conditions is removed. -/
def maskRest (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈
    ((completePeriodLabels (joinedLabels u N) N y).filter (fun n=>¬n.Prime))\
      balancedProducts N,
    (prefixCoefficient u N n-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+I*y) n

/-- The signed ledger contains no error and no moving-mask commutator. -/
theorem balanced_add_rest {u y : ℝ} {N : ℕ} (hN : 65536≤N) (hy : 54≤|y|) :
    balancedPrefix u y N+maskRest u y N=prefixPairDefect u y N := by
  have hS : balancedProducts N⊆
      (completePeriodLabels (joinedLabels u N) N y).filter (fun n=>¬n.Prime) := by
    intro n hn
    refine Finset.mem_filter.mpr ⟨balancedProducts_subset_periods hN hy hn,?_⟩
    obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hq,_⟩ := balanced_pair_data he
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  have he := Finset.sum_sdiff
    (f:=fun n=> (prefixCoefficient u N n-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+I*y) n) hS
  rw [sum_balancedProducts] at he
  unfold balancedPrefix maskRest prefixPairDefect
  rw [←mul_add]
  congr 1
  simpa only [add_comm] using he

/-- Whole-support completion is used on the UNION, never on one masked piece.
The two existing mask and diagonal budgets are included once. -/
theorem norm_balanced_add_rest_le_radius {R C u y : ℝ}
    (hRl : 1/2<R) (hRu : R<3/4) (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|y|) {N : ℕ} (hN : 65536≤N) :
    ‖balancedPrefix u y N+maskRest u y N‖≤26*C^2*(u/R)^N+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N := by
  rw [balanced_add_rest hN hy]
  exact norm_prefix_le_radius hRl hRu hC hm hu hU hy hN

/-- Both inequalities concern the JOINED real contribution. Neither signed
piece receives an absolute price. The rate need not be subcritical at a zero. -/
theorem signed_balanced_add_rest_bounds {R C u y : ℝ}
    (hRl : 1/2<R) (hRu : R<3/4) (hC : 0≤C)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+I*y)‖≤C/R^k)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|y|) {N : ℕ} (hN : 65536≤N) :
    |(balancedPrefix u y N).re+(maskRest u y N).re|≤26*C^2*(u/R)^N+
      ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
        ZetaRieszPairJointQuadratic.squareBudget u N := by
  simpa only [Complex.add_re] using
    (Complex.abs_re_le_norm _).trans
      (norm_balanced_add_rest_le_radius hRl hRu hC hm hu hU hy hN)

private theorem test_height_eligible : 54≤|testHeight| := by
  rw [abs_of_pos (by linarith only [testHeight_bounds.1] : 0<testHeight)]
  exact testHeight_bounds.1.le

private theorem test_height_log : log (|testHeight|+3)≤1800 := by
  have ht : 0<testHeight := by linarith only [testHeight_bounds.1]
  rw [abs_of_pos ht]
  have hh := log_le_sub_one_of_pos (show 0<testHeight+3 by linarith only [ht])
  linarith only [hh,testHeight_bounds.2]

/-- A decay budget for the TEST height, in the already proved zero-free range.
The coefficient constant is existential; no numerical entry order is claimed. -/
def testJointBudget (u C : ℝ) (N : ℕ) : ℝ :=
  26*C^2*(100010/100011 : ℝ)^N+
    ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
      ZetaRieszPairJointQuadratic.squareBudget u N

theorem testJointBudget_tendsto {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (C : ℝ) :
    Tendsto (testJointBudget u C) atTop (𝓝 0) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ)≤100010/100011)
    (by norm_num : (100010/100011 : ℝ)<1)).const_mul (26*C^2)
  change Tendsto (fun N=>26*C^2*(100010/100011 : ℝ)^N+
    ZetaRieszPairWholeCompletion.wholeCompletionBudget N+
      ZetaRieszPairJointQuadratic.squareBudget u N) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using
    (ht.add ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto).add
      (ZetaRieszPairJointQuadratic.squareBudget_tendsto hu hU)

/-- Actual-prime joint cancellation throughout the original radius interval
at this test height. The individual pieces are allowed to grow without bound. -/
theorem exists_test_joint_bound :
    ∃ C : ℝ,0<C ∧ ∀ u : ℝ,1/2≤u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      ∀ N : ℕ,65536≤N →
        ‖balancedPrefix u testHeight N+maskRest u testHeight N‖≤testJointBudget u C N := by
  obtain ⟨C,hC,h⟩ := exists_concrete_height_joint_bound
    test_height_eligible test_height_log
  exact ⟨C,hC,fun u hu hU N hN=> by
    rw [balanced_add_rest hN test_height_eligible]
    exact h u hu hU N hN⟩

/-- Signed aggregate tends to zero, despite the two endpoint divergences. -/
theorem test_joined_tendsto {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>balancedPrefix u testHeight N+maskRest u testHeight N)
      atTop (𝓝 0) := by
  obtain ⟨C,_hC,h⟩ := exists_test_joint_bound
  exact squeeze_zero_norm' ((eventually_ge_atTop 65536).mono
    (fun N hN=>h u hu hU N hN))
    (testJointBudget_tendsto (by linarith only [hu] : 0≤u) hU C)

/-- The retained positive endpoint growth is the actual prefix contribution. -/
theorem test_balanced_re_tendsto {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>(balancedPrefix u testHeight N).re) atTop atTop := by
  simpa only [balancedPrefix] using balanced_literal_prefix_tendsto_atTop hu hU

/-- The complementary ORIGINAL mask supplies an equal, divergent negative
contribution. It is not a small error, favorable credit or a new sector. -/
theorem test_rest_re_tendsto {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>(maskRest u testHeight N).re) atTop atBot := by
  have hsum := Complex.continuous_re.tendsto 0 |>.comp
    (test_joined_tendsto (by linarith only [hu]) hU)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (balancedPrefix u testHeight N+maskRest u testHeight N).re<1 :=
    hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))
  refine tendsto_atBot.2 (fun M=>?_)
  filter_upwards [hsmall,(test_balanced_re_tendsto hu hU).eventually_gt_atTop (1-M)]
    with N hN hB
  rw [Complex.add_re] at hN
  linarith only [hN,hB]

/-- Taking the norm BEFORE recombination destroys the proved cancellation. -/
theorem test_balanced_norm_tendsto {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>‖balancedPrefix u testHeight N‖) atTop atTop :=
  tendsto_atTop_mono (fun _=>Complex.re_le_norm _)
    (test_balanced_re_tendsto hu hU)

theorem test_rest_norm_tendsto {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>‖maskRest u testHeight N‖) atTop atTop := by
  have ht : Tendsto (fun N=> -(maskRest u testHeight N).re) atTop atTop := by
    simpa only [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (test_rest_re_tendsto hu hU)
  apply tendsto_atTop_mono (fun _=>?_) ht
  exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)

/-- The sum of two separately priced absolute masses also diverges. -/
theorem test_separate_price_tendsto {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N=>‖balancedPrefix u testHeight N‖+‖maskRest u testHeight N‖)
      atTop atTop := by
  exact tendsto_atTop_mono (fun N=>le_add_of_nonneg_right (norm_nonneg _))
    (test_balanced_norm_tendsto hu hU)

/-- On the original dyadic orders the rest cannot receive a separate fixed
cofinal FLOOR. This is a test-height audit, never an exposed-zero claim. -/
theorem not_frequently_native_rest_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (M : ℝ) :
    ¬∃ᶠ j : ℕ in atTop,
      M≤(maskRest u testHeight (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)).re := by
  intro h
  have ht := (test_rest_re_tendsto hu hU).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  obtain ⟨j,hge,hlt⟩ := (h.and_eventually (ht.eventually_lt_atBot M)).exists
  exact hlt.not_ge hge

/-- A nonzero genuine source rules out the strict radius margin used above.
Thus the test-height joint payment may not be transplanted to an exposed
zero by omitting its selected mode. This is a LIMIT obstruction, not an
assumed arithmetic cancellation hypothesis. -/
theorem radius_le_source_of_nonzero_limit {u R C y : ℝ} {v : ℂ}
    (hu : 0<u) (hR : 0<R)
    (hm : ∀ k,‖zetaOrdinaryPrimeLogMoment k (3/2+I*y)‖≤C/R^k)
    (hv : v≠0)
    (ha : Tendsto (ZetaRieszPairPrimePowerPayment.ordinaryArray u y) atTop (𝓝 v)) :
    R≤u := by
  by_contra! hur
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hu.le hR.le) ((div_lt_one hR).mpr hur)).const_mul (C*u)
  have hz : Tendsto (ZetaRieszPairPrimePowerPayment.ordinaryArray u y) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k=>?_) (by simpa only [mul_zero] using ht)
    unfold ZetaRieszPairPrimePowerPayment.ordinaryArray
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu.le]
    apply (mul_le_mul_of_nonneg_left (hm k) (pow_nonneg hu.le _)).trans_eq
    rw [div_pow,pow_succ]
    ring
  exact hv (tendsto_nhds_unique ha hz)

end RiemannGaussian.ZetaRieszSelbergMaskCancellation
