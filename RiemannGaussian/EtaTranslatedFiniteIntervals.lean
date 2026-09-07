import RiemannGaussian.EtaTranslatedResidual

/-!
# Exact finite interval arithmetic for eta translates

Below the original odd eta endpoint every nonnegative translate is exactly
its finite interval prefix. Overlap masses retain both translated endpoints
and the common physical cutoff. Their exponential integrals evaluate in
finite elementary arithmetic, including empty intersections.
-/

open Complex Filter MeasureTheory Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- One translated original eta interval, with unchanged endpoint convention. -/
def pairedEtaTranslatedInterval (a : ℝ) (n : ℕ) : Set ℝ :=
  Ioc (a + Real.log (2 * n + 1)) (a + Real.log (2 * n + 2))

/-- The finite prefix consists of the original translated interval indicators. -/
def pairedEtaTranslatedColourPrefix (N : ℕ) (a t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (pairedEtaTranslatedInterval a n).indicator (fun _ ↦ 1) t

/-- Interval membership preserves the exact original translation. -/
theorem mem_pairedEtaTranslatedInterval (a t : ℝ) (n : ℕ) :
    t ∈ pairedEtaTranslatedInterval a n ↔ t - a ∈ pairedEtaLogInterval n := by
  simp only [pairedEtaTranslatedInterval, pairedEtaLogInterval, mem_Ioc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- No eta interval at or beyond the finite prefix meets its original odd cutoff. -/
theorem pairedEtaLogInterval_index_lt_of_le_odd {N n : ℕ} {t : ℝ}
    (ht : t ∈ pairedEtaLogInterval n) (hT : t ≤ Real.log (2 * N + 1 : ℝ)) : n < N := by
  have hlog : Real.log (2 * n + 1 : ℝ) < Real.log (2 * N + 1 : ℝ) := ht.1.trans_le hT
  have hlt := (Real.log_lt_log_iff (by positivity : 0 < (2 * n + 1 : ℝ))
    (by positivity : 0 < (2 * N + 1 : ℝ))).mp hlog
  exact_mod_cast (by linarith : (n : ℝ) < N)

/-- The full infinite eta indicator is exactly a finite disjoint sum below the original odd endpoint. -/
theorem pairedEtaLogIndicator_eq_sum_intervals {N : ℕ} {t : ℝ}
    (hT : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaLogIndicator t = ∑ n ∈ Finset.range N, (pairedEtaLogInterval n).indicator (fun _ ↦ (1 : ℝ)) t := by
  by_cases ht : t ∈ pairedEtaLogSupport
  · obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    have hnN := pairedEtaLogInterval_index_lt_of_le_odd hn hT
    rw [pairedEtaLogIndicator, indicator_of_mem ht]
    symm
    rw [Finset.sum_eq_single n]
    · exact indicator_of_mem hn _
    · intro k _ hkn
      apply indicator_of_notMem
      exact fun hk ↦ (Set.disjoint_left.mp (pairwise_disjoint_pairedEtaLogInterval hkn)) hk hn
    · intro hnmem
      exact (hnmem (Finset.mem_range.mpr hnN)).elim
  · rw [pairedEtaLogIndicator, indicator_of_notMem ht]
    symm
    apply Finset.sum_eq_zero
    intro n _
    apply indicator_of_notMem
    exact fun hn ↦ ht (mem_iUnion.mpr ⟨n, hn⟩)

/-- Every nonnegative translated colour agrees with its finite prefix throughout the same physical cutoff. -/
theorem pairedEtaTranslatedColour_eq_prefix {N : ℕ} {a t : ℝ} (ha : 0 ≤ a)
    (hT : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaTranslatedColour a t = pairedEtaTranslatedColourPrefix N a t := by
  rw [pairedEtaTranslatedColour, pairedEtaLogIndicator_eq_sum_intervals (by linarith : t - a ≤ Real.log (2 * N + 1 : ℝ))]
  unfold pairedEtaTranslatedColourPrefix
  apply Finset.sum_congr rfl
  intro n _
  by_cases ht : t ∈ pairedEtaTranslatedInterval a n
  · simp only [indicator_of_mem ht, indicator_of_mem ((mem_pairedEtaTranslatedInterval a t n).mp ht)]
  · simp only [indicator_of_notMem ht, indicator_of_notMem (fun h ↦ ht ((mem_pairedEtaTranslatedInterval a t n).mpr h))]

/-- The exact positive exponential mass of an interval, with empty intervals included. -/
def etaProjectionIntervalMass (l u : ℝ) : ℝ := max 0 (Real.exp (-l) - Real.exp (-u))

/-- The whole positive exponential tail evaluates at its original endpoint. -/
theorem integral_Ioi_exp_neg_eq (a : ℝ) : (∫ t : ℝ in Ioi a, Real.exp (-t)) = Real.exp (-a) := by
  simpa only [neg_one_mul, neg_div_neg_eq, div_one] using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) a

/-- Each finite interval mass has its exact elementary value with no ordering hypothesis. -/
theorem integral_Ioc_exp_neg_eq_intervalMass (l u : ℝ) :
    (∫ t : ℝ in Ioc l u, Real.exp (-t)) = etaProjectionIntervalMass l u := by
  by_cases hlu : l ≤ u
  · have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi l) := by
      simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) l
    have h := intervalIntegral.integral_Ioi_sub_Ioi hi hlu
    rw [intervalIntegral.integral_of_le hlu, integral_Ioi_exp_neg_eq, integral_Ioi_exp_neg_eq] at h
    rw [← h, etaProjectionIntervalMass, max_eq_right]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hlu), setIntegral_empty, etaProjectionIntervalMass, max_eq_left]
    exact sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))

/-- The finite exponential overlap mass retains both original intervals and the common cutoff. -/
def pairedEtaTranslatedOverlapMass (T a b : ℝ) (n m : ℕ) : ℝ :=
  etaProjectionIntervalMass
    (max 0 (max (a + Real.log (2 * n + 1)) (b + Real.log (2 * m + 1))))
    (min T (min (a + Real.log (2 * n + 2)) (b + Real.log (2 * m + 2))))

/-- A finite translate Gram entry is an explicit double sum of all interval overlaps. -/
def pairedEtaTranslatedFiniteGram (N : ℕ) (T a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, pairedEtaTranslatedOverlapMass T a b n m

end

end RiemannGaussian
