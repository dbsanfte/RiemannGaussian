import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGap

/-!
# The explicit alternating interval structure of the eta gaps

The preceding support--gap decomposition defined the gaps as the complement
of the paired-eta support.  This module identifies that complement with the
explicit alternating logarithmic intervals

`(log (2n+2), log (2n+3)]`.

It then decomposes the gap measure into the sum of the corresponding interval
restrictions and rewrites its Laplace transform as a literal infinite series
of elementary interval transforms.  This is the termwise arithmetic form
needed for quantitative estimates of the exact gap target.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The `n`th omitted logarithmic interval between consecutive paired-eta
support intervals. -/
def pairedEtaLogGapInterval (n : ℕ) : Set ℝ :=
  Ioc (Real.log (2 * n + 2)) (Real.log (2 * n + 3))

/-- The explicit union of all omitted logarithmic intervals. -/
def pairedEtaExplicitLogGapSupport : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogGapInterval n

/-- Every positive logarithmic time lies in one unique consecutive
integer-log interval. -/
theorem iUnion_logSuccInterval_eq_Ioi_zero :
    (⋃ n : ℕ,
      Ioc (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))) =
      Ioi 0 := by
  have hmin : ∀ n : ℕ,
      Real.log (((⊥ : ℕ) : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := by
    intro n
    simpa [Nat.bot_eq_zero] using
      (Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by
        have hn : 0 ≤ (n : ℝ) := by positivity
        linarith))
  have htop : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1))
      atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop)
  have hunbounded : ¬ BddAbove
      (range fun n : ℕ ↦ Real.log ((n : ℝ) + 1)) :=
    not_bddAbove_of_tendsto_atTop htop
  have hcover := iUnion_Ioc_map_succ_eq_Ioi
    (f := fun n : ℕ ↦ Real.log ((n : ℝ) + 1)) hmin hunbounded
  have hnext : ∀ n : ℕ,
      Real.log ((n : ℝ) + 1 + 1) = Real.log ((n : ℝ) + 2) := by
    intro n
    congr 1
    ring
  simpa [hnext] using hcover

/-- The explicit gap intervals lie in positive logarithmic time. -/
theorem pairedEtaExplicitLogGapSupport_subset_Ioi_zero :
    pairedEtaExplicitLogGapSupport ⊆ Ioi 0 := by
  intro t ht
  rw [pairedEtaExplicitLogGapSupport, mem_iUnion] at ht
  obtain ⟨n, hn⟩ := ht
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogLower : Real.log (2 : ℝ) ≤ Real.log (2 * n + 2) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast (show 2 ≤ 2 * n + 2 by omega)
  exact hlogTwoPos.trans_le hlogLower |>.trans hn.1

/-- The paired-eta intervals and the explicit omitted intervals together
cover the full positive half-line. -/
theorem pairedEtaLogSupport_union_explicitGapSupport :
    pairedEtaLogSupport ∪ pairedEtaExplicitLogGapSupport = Ioi 0 := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    rcases ht with ht | ht
    · exact pairedEtaLogSupport_subset_Ioi_zero ht
    · exact pairedEtaExplicitLogGapSupport_subset_Ioi_zero ht
  · intro ht
    have hcover : t ∈ ⋃ k : ℕ,
        Ioc (Real.log ((k : ℝ) + 1)) (Real.log ((k : ℝ) + 2)) := by
      rw [iUnion_logSuccInterval_eq_Ioi_zero]
      exact ht
    rw [mem_iUnion] at hcover
    obtain ⟨k, hk⟩ := hcover
    obtain ⟨n, hEven | hOdd⟩ := k.even_or_odd'
    · left
      rw [pairedEtaLogSupport, mem_iUnion]
      refine ⟨n, ?_⟩
      subst k
      simpa [pairedEtaLogInterval] using hk
    · right
      rw [pairedEtaExplicitLogGapSupport, mem_iUnion]
      refine ⟨n, ?_⟩
      subst k
      norm_num [add_assoc] at hk
      simpa [pairedEtaLogGapInterval] using hk

/-- Distinct explicit logarithmic gap intervals are disjoint. -/
theorem pairwise_disjoint_pairedEtaLogGapInterval :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogGapInterval n) (pairedEtaLogGapInterval m)) := by
  suffices hordered : ∀ {n m : ℕ}, n < m →
      Disjoint (pairedEtaLogGapInterval n) (pairedEtaLogGapInterval m) by
    intro n m hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact hordered hnm
    · exact (hordered hmn).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t htn htm
  have harg : (2 : ℝ) * n + 3 < 2 * m + 2 := by
    exact_mod_cast (show 2 * n + 3 < 2 * m + 2 by omega)
  have hlog : Real.log (2 * n + 3) < Real.log (2 * m + 2) :=
    Real.log_lt_log (by positivity) harg
  exact (not_lt_of_ge htn.2) (hlog.trans htm.1)

/-- The paired-eta support is disjoint from the explicit logarithmic gap
support. -/
theorem disjoint_pairedEtaLogSupport_explicitGapSupport :
    Disjoint pairedEtaLogSupport pairedEtaExplicitLogGapSupport := by
  apply Set.disjoint_left.mpr
  intro t htSupport htGap
  rw [pairedEtaLogSupport, mem_iUnion] at htSupport
  rw [pairedEtaExplicitLogGapSupport, mem_iUnion] at htGap
  obtain ⟨m, hm⟩ := htSupport
  obtain ⟨n, hn⟩ := htGap
  by_cases hmn : m ≤ n
  · have harg : (2 : ℝ) * m + 2 ≤ 2 * n + 2 := by
      exact_mod_cast (show 2 * m + 2 ≤ 2 * n + 2 by omega)
    have hlog : Real.log (2 * m + 2) ≤ Real.log (2 * n + 2) :=
      Real.log_le_log (by positivity) harg
    exact (not_lt_of_ge (hm.2.trans hlog)) hn.1
  · have hnm : n < m := lt_of_not_ge hmn
    have harg : (2 : ℝ) * n + 3 ≤ 2 * m + 1 := by
      exact_mod_cast (show 2 * n + 3 ≤ 2 * m + 1 by omega)
    have hlog : Real.log (2 * n + 3) ≤ Real.log (2 * m + 1) :=
      Real.log_le_log (by positivity) harg
    exact (not_lt_of_ge (hn.2.trans hlog)) hm.1

/-- The abstract complement gap support is exactly the explicit union of
alternating logarithmic intervals. -/
theorem pairedEtaLogGapSupport_eq_explicit :
    pairedEtaLogGapSupport = pairedEtaExplicitLogGapSupport := by
  apply Set.Subset.antisymm
  · intro t ht
    have hu : t ∈ pairedEtaLogSupport ∪
        pairedEtaExplicitLogGapSupport := by
      rw [pairedEtaLogSupport_union_explicitGapSupport]
      exact ht.1
    rcases hu with hs | hg
    · exact (ht.2 hs).elim
    · exact hg
  · intro t ht
    refine ⟨pairedEtaExplicitLogGapSupport_subset_Ioi_zero ht, ?_⟩
    intro hs
    exact Set.disjoint_left.mp
      disjoint_pairedEtaLogSupport_explicitGapSupport hs ht

/-- The abstract arithmetic gap measure is the countable sum of its explicit
interval restrictions. -/
theorem pairedEtaLogGapMeasure_eq_sum_restrict :
    pairedEtaLogGapMeasure =
      Measure.sum fun n : ℕ ↦ volume.restrict (pairedEtaLogGapInterval n) := by
  unfold pairedEtaLogGapMeasure
  rw [pairedEtaLogGapSupport_eq_explicit]
  unfold pairedEtaExplicitLogGapSupport
  exact Measure.restrict_iUnion
    pairwise_disjoint_pairedEtaLogGapInterval
    (fun _ ↦ by
      unfold pairedEtaLogGapInterval
      exact measurableSet_Ioc)

/-- Every explicit logarithmic gap interval has positive length. -/
theorem pairedEtaLogGapInterval_pos (n : ℕ) :
    Real.log (2 * n + 2) < Real.log (2 * n + 3) := by
  apply Real.log_lt_log
  · positivity
  · exact_mod_cast (show 2 * n + 2 < 2 * n + 3 by omega)

/-- The gap measure is dominated by Lebesgue measure on the positive
half-line. -/
theorem pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero :
    pairedEtaLogGapMeasure ≤ volume.restrict (Ioi 0) := by
  unfold pairedEtaLogGapMeasure pairedEtaLogGapSupport
  exact Measure.restrict_mono sdiff_subset le_rfl

/-- A positive-real-part exponential is integrable against the complete gap
measure. -/
theorem integrable_exp_neg_mul_pairedEtaLogGapMeasure
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      pairedEtaLogGapMeasure := by
  have hfull : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t))
      (Ioi 0) := by
    have h := integrableOn_exp_mul_complex_Ioi (a := -s) (by
      norm_num
      linarith) 0
    simpa using h
  exact Integrable.mono_measure hfull
    pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero

/-- One explicit arithmetic-gap Laplace interval. -/
def pairedEtaGapLaplaceInterval (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 2)..Real.log (2 * n + 3),
    Complex.exp (-s * t)

/-- The complete intervalwise Laplace series of the arithmetic gaps. -/
def pairedEtaGapLaplacePartition (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaGapLaplaceInterval s n

/-- The elementary even-odd Dirichlet difference carried by the `n`th gap. -/
def pairedEtaGapCoreSummand (s : ℂ) (n : ℕ) : ℂ :=
  ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) -
    ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s)

/-- One even-odd gap difference is `s` times its positive logarithmic-time
Laplace interval. -/
theorem pairedEtaGapCoreSummand_eq_mul_logLaplaceInterval
    (s : ℂ) (n : ℕ) :
    pairedEtaGapCoreSummand s n =
      s * pairedEtaGapLaplaceInterval s n := by
  by_cases hs : s = 0
  · subst s
    simp [pairedEtaGapCoreSummand, pairedEtaGapLaplaceInterval]
  · have hlowerNonneg : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by
      positivity
    have hupperNonneg : (0 : ℝ) ≤ ((2 * n + 3 : ℕ) : ℝ) := by
      positivity
    have hlower : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)
    have hupper : ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 3 ≠ 0 by omega)
    have hlowerPow :
        Complex.exp (-s * Real.log (2 * n + 2)) =
          ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hlower,
        ← Complex.ofReal_log hlowerNonneg]
      congr 1
      push_cast
      ring
    have hupperPow :
        Complex.exp (-s * Real.log (2 * n + 3)) =
          ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero hupper,
        ← Complex.ofReal_log hupperNonneg]
      congr 1
      push_cast
      ring
    unfold pairedEtaGapLaplaceInterval
    rw [integral_exp_mul_complex (c := -s) (neg_ne_zero.mpr hs)]
    rw [hlowerPow, hupperPow]
    unfold pairedEtaGapCoreSummand
    field_simp [hs]
    abel

/-- The explicit gap-interval Laplace transforms are absolutely summable
throughout the positive half-plane. -/
theorem summable_pairedEtaGapLaplaceInterval
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaGapLaplaceInterval s) := by
  have hint := integrable_exp_neg_mul_pairedEtaLogGapMeasure hs
  rw [pairedEtaLogGapMeasure_eq_sum_restrict] at hint
  have hnorm := hint.summable_integral
  apply hnorm.of_norm_bounded
  intro n
  unfold pairedEtaGapLaplaceInterval pairedEtaLogGapInterval
  rw [intervalIntegral.integral_of_le
    (pairedEtaLogGapInterval_pos n).le]
  exact norm_integral_le_integral_norm _

/-- The elementary even-odd gap Dirichlet differences are absolutely
summable throughout the positive half-plane. -/
theorem summable_pairedEtaGapCoreSummand
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaGapCoreSummand s) := by
  have hmul := (summable_pairedEtaGapLaplaceInterval hs).mul_left s
  apply hmul.congr
  intro n
  exact (pairedEtaGapCoreSummand_eq_mul_logLaplaceInterval s n).symm

/-- The complete even-odd Dirichlet series carried by the arithmetic gaps. -/
def pairedEtaGapCore (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaGapCoreSummand s n

/-- Multiplication by `s` converts the explicit gap Laplace partition into
its literal even-odd Dirichlet-difference series. -/
theorem pairedEtaGapCore_eq_mul_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaGapCore s = s * pairedEtaGapLaplacePartition s := by
  unfold pairedEtaGapCore pairedEtaGapLaplacePartition
  calc
    ∑' n : ℕ, pairedEtaGapCoreSummand s n =
        ∑' n : ℕ, s * pairedEtaGapLaplaceInterval s n := by
      apply tsum_congr
      intro n
      exact pairedEtaGapCoreSummand_eq_mul_logLaplaceInterval s n
    _ = s * ∑' n : ℕ, pairedEtaGapLaplaceInterval s n :=
      (summable_pairedEtaGapLaplaceInterval hs).tsum_mul_left s

/-- The gap-measure Laplace integral is exactly its explicit intervalwise
arithmetic series. -/
theorem integral_exp_neg_mul_pairedEtaLogGapMeasure_eq_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogGapMeasure) =
      pairedEtaGapLaplacePartition s := by
  have hint := integrable_exp_neg_mul_pairedEtaLogGapMeasure hs
  rw [pairedEtaLogGapMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogGapMeasure_eq_sum_restrict, integral_sum_measure hint]
  unfold pairedEtaGapLaplacePartition pairedEtaGapLaplaceInterval
    pairedEtaLogGapInterval
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (pairedEtaLogGapInterval_pos n).le).symm

/-- The explicit gap partition is the full positive-half-line transform minus
the paired-eta support partition. -/
theorem pairedEtaGapLaplacePartition_eq_inv_sub_pairedEtaLaplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaGapLaplacePartition s =
      s⁻¹ - pairedEtaLaplacePartition s := by
  have hsupport := integrable_exp_neg_mul_pairedEtaLogMeasure hs
  have hgap := integrable_exp_neg_mul_pairedEtaLogGapMeasure hs
  have hsplit :
      (∫ t : ℝ, Complex.exp (-s * t) ∂volume.restrict (Ioi 0)) =
        (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) +
          ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogGapMeasure := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
      integral_add_measure hsupport hgap]
  have hfull :
      (∫ t : ℝ, Complex.exp (-s * t) ∂volume.restrict (Ioi 0)) =
        s⁻¹ := by
    simpa only [Complex.re_add_im] using
      (integral_cexp_neg_sigma_add_I_mul_Ioi_zero hs s.im)
  rw [hfull,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hs,
    integral_exp_neg_mul_pairedEtaLogGapMeasure_eq_laplacePartition hs]
      at hsplit
  rw [hsplit]
  abel

/-- The complete gap Dirichlet series is exactly one minus the paired-eta
core throughout the positive half-plane. -/
theorem pairedEtaGapCore_eq_one_sub_pairedEtaCore
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaGapCore s = 1 - pairedEtaCore s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  rw [pairedEtaGapCore_eq_mul_laplacePartition hs,
    pairedEtaGapLaplacePartition_eq_inv_sub_pairedEtaLaplacePartition hs,
    pairedEtaCore_eq_mul_laplacePartition hs]
  field_simp [hs0]

/-- At every nontrivial zeta zero, the literal arithmetic gap series equals
the reciprocal spectral parameter. -/
theorem pairedEtaGapLaplacePartition_eq_inv_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaGapLaplacePartition rho.1 = rho.1⁻¹ := by
  rw [pairedEtaGapLaplacePartition_eq_inv_sub_pairedEtaLaplacePartition
      (NontrivialZetaZero.zero_lt_re rho),
    pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho, sub_zero]

/-- Equivalently, every nontrivial zeta zero makes the literal even-odd gap
Dirichlet-difference series sum exactly to one. -/
theorem pairedEtaGapCore_eq_one_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaGapCore rho.1 = 1 := by
  have hre := NontrivialZetaZero.zero_lt_re rho
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      hre rho.2.2.2, rho.2.1, mul_zero]
  rw [pairedEtaGapCore_eq_one_sub_pairedEtaCore hre, hcore, sub_zero]

/-- The horizontal-defect gap transform is literally the difference of the
two complementary, absolutely convergent arithmetic-gap interval series. -/
theorem pairedEtaPositiveHorizontalDefectGapTransform_eq_gapSeries
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaPositiveHorizontalDefectGapTransform a y =
      -(a : ℂ) *
        (pairedEtaGapLaplacePartition
            (((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I) -
          pairedEtaGapLaplacePartition
            (((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp := integrable_exp_neg_mul_pairedEtaLogGapMeasure
    (s := (((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      exact hplus)
  have hm := integrable_exp_neg_mul_pairedEtaLogGapMeasure
    (s := (((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      linarith)
  unfold pairedEtaPositiveHorizontalDefectGapTransform
    pairedEtaPositiveHorizontalDefectFourierKernel
  rw [integral_const_mul, integral_sub hp hm,
    integral_exp_neg_mul_pairedEtaLogGapMeasure_eq_laplacePartition
      (s := (((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
        norm_num
        exact hplus),
    integral_exp_neg_mul_pairedEtaLogGapMeasure_eq_laplacePartition
      (s := (((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
        norm_num
        linarith)]

/-- At a zeta zero, the complementary arithmetic gap series reduce to the
two explicit reciprocal spectral parameters. -/
theorem nontrivialZetaZero_etaHorizontalDefectGapTransform_eq_inv_sub_inv
    (rho : NontrivialZetaZero) :
    pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im =
      -((rho.1.re - 1 / 2 : ℝ) : ℂ) *
        (rho.1⁻¹ - (NontrivialZetaZero.conjugatePartner rho).1⁻¹) := by
  have hrePos := NontrivialZetaZero.zero_lt_re rho
  have hreLt := NontrivialZetaZero.re_lt_one rho
  let a : ℝ := rho.1.re - 1 / 2
  have ha : |a| < 1 / 2 := by
    dsimp [a]
    rw [abs_lt]
    constructor <;> linarith
  let qplus : ℂ := (((1 / 2 + a : ℝ) : ℂ) +
    (rho.1.im : ℂ) * Complex.I)
  let qminus : ℂ := (((1 / 2 - a : ℝ) : ℂ) +
    (rho.1.im : ℂ) * Complex.I)
  have hqplus : qplus = rho.1 := by
    apply Complex.ext <;> simp [qplus, a]
  have hqminus : qminus =
      (NontrivialZetaZero.conjugatePartner rho).1 := by
    apply Complex.ext
    · simp [qminus, a, NontrivialZetaZero.conjugatePartner_coe]
      ring
    · simp [qminus, a, NontrivialZetaZero.conjugatePartner_coe]
  rw [show rho.1.re - 1 / 2 = a by rfl,
    pairedEtaPositiveHorizontalDefectGapTransform_eq_gapSeries ha]
  change -(a : ℂ) *
      (pairedEtaGapLaplacePartition qplus -
        pairedEtaGapLaplacePartition qminus) = _
  rw [hqplus, hqminus,
    pairedEtaGapLaplacePartition_eq_inv_of_nontrivialZetaZero,
    pairedEtaGapLaplacePartition_eq_inv_of_nontrivialZetaZero]

/-- Every hypothetical off-critical zero therefore forces two literal
even-odd gap series to sum to one and their complementary interval transforms
to produce the already-proved nonzero horizontal target. -/
theorem nontrivialZetaZero_offCritical_etaGapArithmeticSeries_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    (pairedEtaGapCore rho.1 = 1 ∧
      pairedEtaGapCore (NontrivialZetaZero.conjugatePartner rho).1 = 1) ∧
    (pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im =
      -((rho.1.re - 1 / 2 : ℝ) : ℂ) *
        (rho.1⁻¹ - (NontrivialZetaZero.conjugatePartner rho).1⁻¹) ∧
      pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im ≠ 0) := by
  exact ⟨⟨pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho,
      pairedEtaGapCore_eq_one_of_nontrivialZetaZero
        (NontrivialZetaZero.conjugatePartner rho)⟩,
    ⟨nontrivialZetaZero_etaHorizontalDefectGapTransform_eq_inv_sub_inv rho,
      nontrivialZetaZero_offCritical_etaHorizontalDefectGapTransform_ne_zero
        rho hoff⟩⟩

end

end RiemannGaussian
