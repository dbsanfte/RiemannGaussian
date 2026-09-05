import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapArithmetic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Arithmetic displacement of the literal eta logarithmic support

The positive eta measure alternates at the logarithms of consecutive integers.
Small displacements therefore have an exact finite boundary decomposition below
a cutoff. The complex phase is retained before estimating the omitted tail.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real indicator of the actual infinite paired-eta support. -/
def pairedEtaLogIndicator (t : ℝ) : ℝ :=
  pairedEtaLogSupport.indicator (fun _ ↦ 1) t

/-- One consecutive integer-log cell, with the same endpoint convention as
the existing eta support and gap measures. -/
def pairedEtaLogCell (n : ℕ) : Set ℝ :=
  Ioc (Real.log ((n : ℝ) + 1)) (Real.log ((n : ℝ) + 2))

/-- The alternating colour of a consecutive integer-log cell. -/
def pairedEtaLogCellColour (n : ℕ) : ℝ :=
  if Even n then 1 else 0

/-- The literal eta indicator is measurable. -/
theorem measurable_pairedEtaLogIndicator : Measurable pairedEtaLogIndicator := by
  exact measurable_const.indicator measurableSet_pairedEtaLogSupport

/-- Each value of the literal eta indicator is zero or one. -/
theorem pairedEtaLogIndicator_eq_zero_or_one (t : ℝ) :
    pairedEtaLogIndicator t = 0 ∨ pairedEtaLogIndicator t = 1 := by
  by_cases ht : t ∈ pairedEtaLogSupport
  · right
    simp [pairedEtaLogIndicator, ht]
  · left
    simp [pairedEtaLogIndicator, ht]

/-- The support indicator has the prescribed alternating colour throughout
each cell, including its right endpoint. -/
theorem pairedEtaLogIndicator_eq_cellColour {n : ℕ} {t : ℝ}
    (ht : t ∈ pairedEtaLogCell n) :
    pairedEtaLogIndicator t = pairedEtaLogCellColour n := by
  obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
  · have hmem : t ∈ pairedEtaLogSupport := by
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      simpa [pairedEtaLogCell, pairedEtaLogInterval] using ht
    simp [pairedEtaLogIndicator, pairedEtaLogCellColour, hmem]
  · have hgap : t ∈ pairedEtaExplicitLogGapSupport := by
      apply mem_iUnion.mpr
      refine ⟨k, ?_⟩
      norm_num [pairedEtaLogCell, pairedEtaLogGapInterval, add_assoc] at ht ⊢
      exact ht
    have hnot : t ∉ pairedEtaLogSupport := fun hmem ↦
      Set.disjoint_left.mp disjoint_pairedEtaLogSupport_explicitGapSupport hmem hgap
    simp [pairedEtaLogIndicator, pairedEtaLogCellColour, hnot]

/-- Consecutive cells have complementary colours. -/
theorem pairedEtaLogCellColour_succ (n : ℕ) :
    pairedEtaLogCellColour (n + 1) = 1 - pairedEtaLogCellColour n := by
  by_cases hn : Even n <;> simp [pairedEtaLogCellColour, Nat.even_add_one, hn]

/-- Squaring the difference of adjacent cell colours gives exactly one. -/
theorem pairedEtaLogCellColour_succ_sub_sq (n : ℕ) :
    (pairedEtaLogCellColour (n + 1) - pairedEtaLogCellColour n) ^ 2 = 1 := by
  rw [pairedEtaLogCellColour_succ]
  by_cases hn : Even n <;> simp [pairedEtaLogCellColour, hn]

/-- The logarithmic spacing of consecutive positive real numbers decreases
with the starting point. -/
theorem log_succ_ratio_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log ((b + 1) / b) ≤ Real.log ((a + 1) / a) := by
  have hb : 0 < b := ha.trans_le hab
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hb ha).2
  nlinarith

/-- A displacement bounded by the last logarithmic spacing is bounded by
every earlier spacing. -/
theorem log_nat_add_shift_le_log_succ {M n : ℕ} {r : ℝ}
    (hn : 1 ≤ n) (hnM : n ≤ M)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    Real.log (n : ℝ) + r ≤ Real.log ((n : ℝ) + 1) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hgap := log_succ_ratio_antitone hnpos (show (n : ℝ) ≤ M by exact_mod_cast hnM)
  rw [Real.log_div (by positivity) (ne_of_gt hnpos)] at hgap
  linarith

/-- Distinct consecutive integer-log cells are disjoint. -/
theorem pairwise_disjoint_pairedEtaLogCell :
    Pairwise (fun n m : ℕ ↦ Disjoint (pairedEtaLogCell n) (pairedEtaLogCell m)) := by
  suffices hord : ∀ {n m : ℕ}, n < m →
      Disjoint (pairedEtaLogCell n) (pairedEtaLogCell m) by
    intro n m hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hord h
    · exact (hord h).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t htn htm
  have hlog : Real.log ((n : ℝ) + 2) ≤ Real.log ((m : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show n + 2 ≤ m + 1 by omega)
  exact (not_lt_of_ge (htn.2.trans hlog)) htm.1

/-- Every positive time has a consecutive integer-log cell. -/
theorem exists_pairedEtaLogCell {t : ℝ} (ht : 0 < t) :
    ∃ n : ℕ, t ∈ pairedEtaLogCell n := by
  have hcover : t ∈ ⋃ n : ℕ, pairedEtaLogCell n := by
    simpa [pairedEtaLogCell, iUnion_logSuccInterval_eq_Ioi_zero] using ht
  exact mem_iUnion.mp hcover

/-- A cell meeting the interval up to `log M` has its right endpoint at an
integer no larger than `M`. -/
theorem pairedEtaLogCell_index_le {M n : ℕ} {t : ℝ}
    (hM : 0 < M) (ht : t ∈ pairedEtaLogCell n) (htM : t ≤ Real.log (M : ℝ)) :
    n + 2 ≤ M := by
  have hlt : Real.log ((n : ℝ) + 1) < Real.log (M : ℝ) := ht.1.trans_le htM
  have hnM : (n : ℝ) + 1 < M :=
    (Real.log_lt_log_iff (by positivity) (by exact_mod_cast hM)).mp hlt
  have : n + 1 < M := by exact_mod_cast hnM
  omega

/-- The squared support mismatch retains the actual arithmetic support. -/
def pairedEtaLogShiftMismatch (r t : ℝ) : ℝ :=
  (pairedEtaLogIndicator (t + r) - pairedEtaLogIndicator t) ^ 2

/-- The mismatch is measurable in displacement and observation time. -/
theorem measurable_pairedEtaLogShiftMismatch :
    Measurable (fun p : ℝ × ℝ ↦ pairedEtaLogShiftMismatch p.1 p.2) := by
  exact ((measurable_pairedEtaLogIndicator.comp (measurable_snd.add measurable_fst)).sub
    (measurable_pairedEtaLogIndicator.comp measurable_snd)).pow_const 2

/-- The support mismatch is nonnegative. -/
theorem pairedEtaLogShiftMismatch_nonneg (r t : ℝ) :
    0 ≤ pairedEtaLogShiftMismatch r t := sq_nonneg _

/-- The support mismatch is bounded by one without discarding its definition. -/
theorem pairedEtaLogShiftMismatch_le_one (r t : ℝ) :
    pairedEtaLogShiftMismatch r t ≤ 1 := by
  rcases pairedEtaLogIndicator_eq_zero_or_one (t + r) with h₁ | h₁ <;>
    rcases pairedEtaLogIndicator_eq_zero_or_one t with h₂ | h₂ <;>
    simp [pairedEtaLogShiftMismatch, h₁, h₂]

/-- The times whose positive displacement crosses the boundary at `log n`. -/
def pairedEtaLogCrossingStrip (r : ℝ) (n : ℕ) : Set ℝ :=
  Ioc (Real.log (n : ℝ) - r) (Real.log (n : ℝ))

/-- Before the last resolved boundary, a crossing strip lies in the cell
immediately preceding that boundary. -/
theorem pairedEtaLogCrossingStrip_subset_cell {M n : ℕ} {r : ℝ}
    (hnM : n + 2 ≤ M) (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    pairedEtaLogCrossingStrip r (n + 2) ⊆ pairedEtaLogCell n := by
  have hspacing := log_nat_add_shift_le_log_succ (n := n + 1) (by omega)
    (show n + 1 ≤ M by omega) hr
  simp only [Nat.cast_add, Nat.cast_one] at hspacing
  have harg : (n : ℝ) + 1 + 1 = n + 2 := by ring
  rw [harg] at hspacing
  intro t ht
  simp only [pairedEtaLogCrossingStrip, mem_Ioc, Nat.cast_add, Nat.cast_ofNat] at ht
  exact ⟨by linarith [ht.1], ht.2⟩

/-- On a resolved cell, the squared mismatch is exactly the indicator of
its right boundary's crossing strip. -/
theorem pairedEtaLogShiftMismatch_eq_crossingStrip_indicator
    {M n : ℕ} {r t : ℝ} (hnM : n + 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) (ht : t ∈ pairedEtaLogCell n) :
    pairedEtaLogShiftMismatch r t =
      (pairedEtaLogCrossingStrip r (n + 2)).indicator (fun _ ↦ (1 : ℝ)) t := by
  have hspacing := log_nat_add_shift_le_log_succ (n := n + 2) (by omega) hnM hr
  simp only [Nat.cast_add, Nat.cast_ofNat] at hspacing
  have harg : (n : ℝ) + 2 + 1 = n + 3 := by ring
  rw [harg] at hspacing
  by_cases hcross : Real.log ((n : ℝ) + 2) < t + r
  · have hnext : t + r ∈ pairedEtaLogCell (n + 1) := by
      norm_num [pairedEtaLogCell, add_assoc]
      refine ⟨?_, ?_⟩
      · simpa using hcross
      · linarith [ht.2]
    have hstrip : t ∈ pairedEtaLogCrossingStrip r (n + 2) := by
      simp only [pairedEtaLogCrossingStrip, mem_Ioc, Nat.cast_add, Nat.cast_ofNat]
      exact ⟨by linarith, ht.2⟩
    rw [indicator_of_mem hstrip]
    unfold pairedEtaLogShiftMismatch
    rw [pairedEtaLogIndicator_eq_cellColour hnext,
      pairedEtaLogIndicator_eq_cellColour ht, pairedEtaLogCellColour_succ_sub_sq]
  · have hsame : t + r ∈ pairedEtaLogCell n :=
      ⟨ht.1.trans (lt_add_of_pos_right t hrpos),
        le_of_not_gt hcross⟩
    have hnot : t ∉ pairedEtaLogCrossingStrip r (n + 2) := by
      simp only [pairedEtaLogCrossingStrip, mem_Ioc, Nat.cast_add, Nat.cast_ofNat]
      intro h
      exact hcross (by linarith [h.1])
    rw [indicator_of_notMem hnot]
    simp [pairedEtaLogShiftMismatch, pairedEtaLogIndicator_eq_cellColour hsame,
      pairedEtaLogIndicator_eq_cellColour ht]

/-- Below the arithmetic cutoff, the actual mismatch is the finite sum of
the resolved boundary indicators, with no endpoint exceptions. -/
theorem pairedEtaLogShiftMismatch_eq_sum_crossingStrip
    {M : ℕ} {r t : ℝ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M))
    (ht : t ∈ Ioc 0 (Real.log (M : ℝ))) :
    pairedEtaLogShiftMismatch r t =
      ∑ n ∈ Finset.Icc 2 M,
        (pairedEtaLogCrossingStrip r n).indicator (fun _ ↦ (1 : ℝ)) t := by
  obtain ⟨n, htn⟩ := exists_pairedEtaLogCell ht.1
  have hnM := pairedEtaLogCell_index_le (show 0 < M by omega) htn ht.2
  rw [pairedEtaLogShiftMismatch_eq_crossingStrip_indicator hnM hrpos hr htn]
  symm
  apply Finset.sum_eq_single (n + 2)
  · intro j hj hjn
    apply indicator_of_notMem
    intro htj
    have hjM := Finset.mem_Icc.mp hj
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hjM.1
    have hjk : j = k + 2 := by omega
    clear hk
    subst j
    have hkn : k ≠ n := by omega
    exact Set.disjoint_left.mp (pairwise_disjoint_pairedEtaLogCell hkn)
      (pairedEtaLogCrossingStrip_subset_cell hjM.2 hr htj) htn
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨by omega, hnM⟩)).elim

/-- Every resolved crossing strip is inside the positive-time cutoff. -/
theorem pairedEtaLogCrossingStrip_subset_cutoff {M n : ℕ} {r : ℝ}
    (hn : n ∈ Finset.Icc 2 M) (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    pairedEtaLogCrossingStrip r n ⊆ Ioc 0 (Real.log (M : ℝ)) := by
  have hnM := Finset.mem_Icc.mp hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnM.1
  have hnk : n = k + 2 := by omega
  clear hk
  subst n
  intro t ht
  have hcell := pairedEtaLogCrossingStrip_subset_cell hnM.2 hr ht
  refine ⟨?_, ?_⟩
  · exact (Real.log_nonneg
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ k + 1)).trans_lt hcell.1
  · exact ht.2.trans (Real.log_le_log (by positivity) (by exact_mod_cast hnM.2))

/-- Fixing the displacement gives a measurable arithmetic mismatch. -/
theorem measurable_pairedEtaLogShiftMismatch_time (r : ℝ) :
    Measurable (pairedEtaLogShiftMismatch r) := by
  exact measurable_pairedEtaLogShiftMismatch.comp (measurable_const.prodMk measurable_id)

/-- Multiplication by the arithmetic mismatch preserves genuine integrability. -/
theorem integrableOn_pairedEtaLogShiftMismatch_mul {f : ℝ → ℂ} {s : Set ℝ}
    (hf : IntegrableOn f s) (r : ℝ) :
    IntegrableOn (fun t ↦ (pairedEtaLogShiftMismatch r t : ℂ) * f t) s := by
  apply hf.bdd_mul (measurable_pairedEtaLogShiftMismatch_time r).complex_ofReal.aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg r t)] using
        pairedEtaLogShiftMismatch_le_one r t

/-- The exact finite boundary expansion for an arbitrary integrable complex
weight, keeping the unresolved arithmetic tail as a complex integral. -/
theorem pairedEtaLogShiftMismatch_integral_eq_boundary_add_tail
    {M : ℕ} {r : ℝ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M))
    {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    (∫ t in Ioi 0, (pairedEtaLogShiftMismatch r t : ℂ) * f t) =
      (∑ n ∈ Finset.Icc 2 M, ∫ t in pairedEtaLogCrossingStrip r n, f t) +
        ∫ t in Ioi (Real.log (M : ℝ)),
          (pairedEtaLogShiftMismatch r t : ℂ) * f t := by
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hMreal
  have hfm := integrableOn_pairedEtaLogShiftMismatch_mul hf r
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfm
    (hfm.mono_set (Ioi_subset_Ioi hlog))
  rw [intervalIntegral.integral_of_le hlog] at hsplit
  rw [← hsplit]
  congr 1
  calc
    (∫ t in Ioc 0 (Real.log (M : ℝ)), (pairedEtaLogShiftMismatch r t : ℂ) * f t) =
        ∫ t in Ioc 0 (Real.log (M : ℝ)),
          ∑ n ∈ Finset.Icc 2 M, (pairedEtaLogCrossingStrip r n).indicator f t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [pairedEtaLogShiftMismatch_eq_sum_crossingStrip hM hrpos hr ht,
        Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : t ∈ pairedEtaLogCrossingStrip r n <;> simp [hn]
    _ = ∑ n ∈ Finset.Icc 2 M,
        ∫ t in Ioc 0 (Real.log (M : ℝ)), (pairedEtaLogCrossingStrip r n).indicator f t := by
      apply integral_finsetSum
      intro n _
      exact (hf.mono_set Ioc_subset_Ioi_self).indicator measurableSet_Ioc
    _ = ∑ n ∈ Finset.Icc 2 M, ∫ t in pairedEtaLogCrossingStrip r n, f t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [setIntegral_indicator (show MeasurableSet (pairedEtaLogCrossingStrip r n)
          from measurableSet_Ioc),
        inter_eq_right.mpr (pairedEtaLogCrossingStrip_subset_cutoff hn hr)]

/-- The exponentially tilted complex phase increment used in the arithmetic
displacement integral. -/
def pairedEtaShiftPhaseKernel (sigma : ℝ) (phi : ℝ → ℝ) (r t : ℝ) : ℂ :=
  (Real.exp (-(2 * sigma) * t) : ℂ) *
    Complex.exp (((phi (t + r) - phi t : ℝ) : ℂ) * Complex.I)

/-- The complex phase has unit modulus, so the kernel norm is exactly its
exponential envelope. -/
theorem norm_pairedEtaShiftPhaseKernel (sigma : ℝ) (phi : ℝ → ℝ) (r t : ℝ) :
    ‖pairedEtaShiftPhaseKernel sigma phi r t‖ = Real.exp (-(2 * sigma) * t) := by
  unfold pairedEtaShiftPhaseKernel
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- A measurable real phase gives a measurable tilted phase kernel. -/
theorem measurable_pairedEtaShiftPhaseKernel {phi : ℝ → ℝ}
    (hphi : Measurable phi) (sigma r : ℝ) :
    Measurable (pairedEtaShiftPhaseKernel sigma phi r) := by
  have hphase := Complex.continuous_exp.measurable.comp
    (((hphi.comp (measurable_id.add_const r)).sub hphi).complex_ofReal.mul_const Complex.I)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.complex_ofReal).mul
    hphase

/-- Positive tilt makes the full phase kernel integrable on every right
half-line, with no growth assumptions on the real phase. -/
theorem integrableOn_pairedEtaShiftPhaseKernel {sigma : ℝ} (hsigma : 0 < sigma)
    {phi : ℝ → ℝ} (hphi : Measurable phi) (r a : ℝ) :
    IntegrableOn (pairedEtaShiftPhaseKernel sigma phi r) (Ioi a) := by
  apply (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) a).mono'
    (measurable_pairedEtaShiftPhaseKernel hphi sigma r).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ (norm_pairedEtaShiftPhaseKernel sigma phi r t).le

/-- The complete, phase-resolved displacement of the literal eta support. -/
def pairedEtaPhaseMismatch (sigma : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℂ :=
  ∫ t in Ioi 0,
    (pairedEtaLogShiftMismatch r t : ℂ) * pairedEtaShiftPhaseKernel sigma phi r t

/-- The retained complex tail beyond a logarithmic boundary cutoff. -/
def pairedEtaPhaseMismatchTail (sigma : ℝ) (phi : ℝ → ℝ) (r : ℝ) (M : ℕ) : ℂ :=
  ∫ t in Ioi (Real.log (M : ℝ)),
    (pairedEtaLogShiftMismatch r t : ℂ) * pairedEtaShiftPhaseKernel sigma phi r t

/-- The exact phase-resolved arithmetic boundary expansion. -/
theorem pairedEtaPhaseMismatch_eq_boundary_add_tail
    {sigma r : ℝ} (hsigma : 0 < sigma) {phi : ℝ → ℝ} (hphi : Measurable phi)
    {M : ℕ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    pairedEtaPhaseMismatch sigma phi r =
      (∑ n ∈ Finset.Icc 2 M,
        ∫ t in pairedEtaLogCrossingStrip r n, pairedEtaShiftPhaseKernel sigma phi r t) +
      pairedEtaPhaseMismatchTail sigma phi r M := by
  exact pairedEtaLogShiftMismatch_integral_eq_boundary_add_tail hM hrpos hr
    (integrableOn_pairedEtaShiftPhaseKernel hsigma hphi r 0)

/-- The phase-resolved arithmetic tail is bounded by an explicit exponential
mass. The bound does not depend on the phase or displacement. -/
theorem norm_pairedEtaPhaseMismatchTail_le {sigma : ℝ} (hsigma : 0 < sigma)
    (phi : ℝ → ℝ) (r : ℝ) {M : ℕ} (hM : 0 < M) :
    ‖pairedEtaPhaseMismatchTail sigma phi r M‖ ≤
      (M : ℝ) ^ (-(2 * sigma)) / (2 * sigma) := by
  have henv := integrableOn_exp_mul_Ioi (a := -(2 * sigma))
    (by linarith) (Real.log (M : ℝ))
  calc
    ‖pairedEtaPhaseMismatchTail sigma phi r M‖ ≤
        ∫ t in Ioi (Real.log (M : ℝ)), Real.exp (-(2 * sigma) * t) := by
      apply norm_integral_le_of_norm_le henv
      exact Eventually.of_forall fun t ↦ by
        rw [norm_mul, norm_pairedEtaShiftPhaseKernel, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (pairedEtaLogShiftMismatch_nonneg r t)]
        exact mul_le_of_le_one_left (Real.exp_pos _).le (pairedEtaLogShiftMismatch_le_one r t)
    _ = (M : ℝ) ^ (-(2 * sigma)) / (2 * sigma) := by
      rw [integral_exp_mul_Ioi (by linarith), neg_div_neg_eq,
        Real.rpow_def_of_pos (by exact_mod_cast hM)]
      congr 2
      ring

/-- Uniform phase-sensitive error bound for the finite arithmetic boundary
expansion of the actual eta support. -/
theorem pairedEtaPhaseMismatch_boundary_error_le
    {sigma r : ℝ} (hsigma : 0 < sigma) {phi : ℝ → ℝ} (hphi : Measurable phi)
    {M : ℕ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    ‖pairedEtaPhaseMismatch sigma phi r -
      ∑ n ∈ Finset.Icc 2 M,
        ∫ t in pairedEtaLogCrossingStrip r n, pairedEtaShiftPhaseKernel sigma phi r t‖ ≤
      (M : ℝ) ^ (-(2 * sigma)) / (2 * sigma) := by
  rw [pairedEtaPhaseMismatch_eq_boundary_add_tail hsigma hphi hM hrpos hr,
    add_sub_cancel_left]
  exact norm_pairedEtaPhaseMismatchTail_le hsigma phi r (by omega)

/-- The exact boundary expansion also holds for real integrable weights. -/
theorem pairedEtaLogShiftMismatch_real_integral_eq_boundary_add_tail
    {M : ℕ} {r : ℝ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M))
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    (∫ t in Ioi 0, pairedEtaLogShiftMismatch r t * f t) =
      (∑ n ∈ Finset.Icc 2 M, ∫ t in pairedEtaLogCrossingStrip r n, f t) +
        ∫ t in Ioi (Real.log (M : ℝ)), pairedEtaLogShiftMismatch r t * f t := by
  have h := pairedEtaLogShiftMismatch_integral_eq_boundary_add_tail hM hrpos hr
    (f := fun t ↦ (f t : ℂ))
    (hf.ofReal (𝕜 := ℂ))
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sum,
    ← Complex.ofReal_add, Complex.ofReal_inj] using h

/-- The uncoloured displacement of the literal eta support. -/
def pairedEtaMismatch (sigma r : ℝ) : ℝ :=
  ∫ t in Ioi 0, pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t)

/-- The uncoloured omitted tail, still on the actual arithmetic support. -/
def pairedEtaMismatchTail (sigma r : ℝ) (M : ℕ) : ℝ :=
  ∫ t in Ioi (Real.log (M : ℝ)),
    pairedEtaLogShiftMismatch r t * Real.exp (-(2 * sigma) * t)

/-- Zero phase recovers the uncoloured real integral exactly. -/
theorem pairedEtaPhaseMismatch_zero (sigma r : ℝ) :
    pairedEtaPhaseMismatch sigma (fun _ ↦ 0) r = (pairedEtaMismatch sigma r : ℂ) := by
  unfold pairedEtaPhaseMismatch pairedEtaShiftPhaseKernel pairedEtaMismatch
  simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    ← Complex.ofReal_mul, integral_complex_ofReal]

/-- Zero phase also recovers the retained real arithmetic tail. -/
theorem pairedEtaPhaseMismatchTail_zero (sigma r : ℝ) (M : ℕ) :
    pairedEtaPhaseMismatchTail sigma (fun _ ↦ 0) r M =
      (pairedEtaMismatchTail sigma r M : ℂ) := by
  unfold pairedEtaPhaseMismatchTail pairedEtaShiftPhaseKernel pairedEtaMismatchTail
  simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    ← Complex.ofReal_mul, integral_complex_ofReal]

/-- Uncoloured mismatch is nonnegative at every tilt and displacement. -/
theorem pairedEtaMismatch_nonneg (sigma r : ℝ) : 0 ≤ pairedEtaMismatch sigma r := by
  exact integral_nonneg fun t ↦
    mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le

/-- The uncoloured omitted arithmetic tail is nonnegative. -/
theorem pairedEtaMismatchTail_nonneg (sigma r : ℝ) (M : ℕ) :
    0 ≤ pairedEtaMismatchTail sigma r M := by
  exact integral_nonneg fun t ↦
    mul_nonneg (pairedEtaLogShiftMismatch_nonneg r t) (Real.exp_pos _).le

/-- The uncoloured omitted tail has the same explicit, uniform mass bound. -/
theorem pairedEtaMismatchTail_le {sigma : ℝ} (hsigma : 0 < sigma)
    (r : ℝ) {M : ℕ} (hM : 0 < M) :
    pairedEtaMismatchTail sigma r M ≤ (M : ℝ) ^ (-(2 * sigma)) / (2 * sigma) := by
  have h := norm_pairedEtaPhaseMismatchTail_le hsigma (fun _ ↦ 0) r hM
  rwa [pairedEtaPhaseMismatchTail_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pairedEtaMismatchTail_nonneg sigma r M)] at h

/-- The exact exponential mass of one resolved logarithmic crossing strip. -/
theorem integral_exp_pairedEtaLogCrossingStrip {sigma r : ℝ} (hsigma : 0 < sigma)
    (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) :
    (∫ t in pairedEtaLogCrossingStrip r n, Real.exp (-(2 * sigma) * t)) =
      (Real.exp (2 * sigma * r) - 1) / (2 * sigma) * (n : ℝ) ^ (-(2 * sigma)) := by
  have hle : Real.log (n : ℝ) - r ≤ Real.log (n : ℝ) := by linarith
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith)
      (Real.log (n : ℝ) - r)) hle
  rw [intervalIntegral.integral_of_le hle] at h
  unfold pairedEtaLogCrossingStrip
  rw [← h, integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith)]
  simp only [neg_div_neg_eq]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  rw [show -(2 * sigma) * (Real.log (n : ℝ) - r) =
      Real.log (n : ℝ) * (-(2 * sigma)) + 2 * sigma * r by ring,
    Real.exp_add,
    show -(2 * sigma) * Real.log (n : ℝ) = Real.log (n : ℝ) * (-(2 * sigma)) by ring]
  ring

/-- Exact weighted boundary sum plus the nonnegative actual-support tail. -/
theorem pairedEtaMismatch_eq_boundaryMass_add_tail
    {sigma r : ℝ} (hsigma : 0 < sigma) {M : ℕ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    pairedEtaMismatch sigma r =
      (Real.exp (2 * sigma * r) - 1) / (2 * sigma) *
        (∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-(2 * sigma))) +
      pairedEtaMismatchTail sigma r M := by
  have h := pairedEtaLogShiftMismatch_real_integral_eq_boundary_add_tail hM hrpos hr
    (integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) 0)
  change pairedEtaMismatch sigma r = _ + pairedEtaMismatchTail sigma r M at h
  rw [h, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_exp_pairedEtaLogCrossingStrip hsigma hrpos.le
    (by have := (Finset.mem_Icc.mp hn).1; omega)

/-- Two-sided arithmetic estimate by the resolved weighted boundary sum. -/
theorem pairedEtaMismatch_boundaryMass_error_bounds
    {sigma r : ℝ} (hsigma : 0 < sigma) {M : ℕ} (hM : 2 ≤ M) (hrpos : 0 < r)
    (hr : r ≤ Real.log (((M : ℝ) + 1) / M)) :
    let main := (Real.exp (2 * sigma * r) - 1) / (2 * sigma) *
      (∑ n ∈ Finset.Icc 2 M, (n : ℝ) ^ (-(2 * sigma)))
    0 ≤ pairedEtaMismatch sigma r - main ∧
      pairedEtaMismatch sigma r - main ≤ (M : ℝ) ^ (-(2 * sigma)) / (2 * sigma) := by
  dsimp only
  rw [pairedEtaMismatch_eq_boundaryMass_add_tail hsigma hM hrpos hr, add_sub_cancel_left]
  exact ⟨pairedEtaMismatchTail_nonneg sigma r M, pairedEtaMismatchTail_le hsigma r (by omega)⟩

end

end RiemannGaussian
