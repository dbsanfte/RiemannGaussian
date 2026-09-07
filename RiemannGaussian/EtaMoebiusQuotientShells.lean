import RiemannGaussian.EtaMoebiusBoundaryFibreDecay

/-!
# The full quadratic form of complete dyadic quotient shells

After the single clipped fibre is removed, each quotient block is complete.
Dyadic shells group these exact complex blocks, with the actual cutoff
retained by zero extension. The whole mean square is the sum of every
shell-to-shell correlation, including all cross terms. Its proved source
limit identifies a uniform sub-source bound as the remaining sufficient
target; no such arithmetic bound is asserted here.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A dyadic shell of complete quotient blocks, with the original phases and the exact moving quotient cut. -/
def pairedEtaCompletedMoebiusQuotientShell (rho : NontrivialZetaZero) (D M j : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q

private theorem sum_dyadicIntervals (f : ℕ → ℂ) (J : ℕ) :
    (∑ j ∈ Finset.range J, ∑ q ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f q) =
      ∑ q ∈ Finset.Ico 1 (2 ^ J), f q := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have hp : 0 < (2 : ℕ) ^ J := pow_pos (by norm_num) J
    exact Finset.sum_Ico_consecutive f hp (by rw [pow_succ]; omega)

/-- Any enclosing dyadic quotient range reconstructs the surviving complete-block carrier exactly, before taking a norm or discarding any cross terms. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_shells
    (rho : NontrivialZetaZero) (M D J : ℕ) (hQ : M / (D + 1) < 2 ^ J) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D =
      ∑ j ∈ Finset.range J, pairedEtaCompletedMoebiusQuotientShell rho D M j := by
  have hs : Finset.Icc 1 (M / (D + 1)) ⊆ Finset.Ico 1 (2 ^ J) := by
    intro q hq
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hq
    exact Finset.mem_Ico.mpr ⟨hl, hu.trans_lt hQ⟩
  calc
    _ = ∑ q ∈ Finset.Icc 1 (M / (D + 1)), pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [pairedEtaCompletedMoebiusLargeQuotientFamily, if_pos (Finset.mem_Icc.mp hq).2]
    _ = ∑ q ∈ Finset.Ico 1 (2 ^ J), pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q := by
      apply Finset.sum_subset hs
      intro q hq hn
      have hl := (Finset.mem_Ico.mp hq).1
      have hnot : ¬q ≤ M / (D + 1) := by simpa only [Finset.mem_Icc, hl, true_and] using hn
      simp only [pairedEtaCompletedMoebiusLargeQuotientFamily, if_neg hnot]
    _ = _ := (sum_dyadicIntervals _ J).symm

/-- On the cubic dyadic schedule, exactly `k+1` dyadic shells suffice for every retained complete quotient block. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_twoThirds_eq_shells
    (rho : NontrivialZetaZero) (k : ℕ) {M : ℕ} (hM : M < 2 * (2 ^ k) ^ 3) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M ((2 ^ k) ^ 2) =
      ∑ j ∈ Finset.range (k + 1), pairedEtaCompletedMoebiusQuotientShell rho ((2 ^ k) ^ 2) M j := by
  apply pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_shells
  simpa only [pow_succ, mul_comm] using moebiusTwoThirds_quotient_lt_twice hM

/-- Full complex correlation of two complete quotient shells on the original physical window. -/
def pairedEtaCompletedMoebiusQuotientShellCorrelation
    (rho : NontrivialZetaZero) (A L D j l : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L, pairedEtaCompletedMoebiusQuotientShell rho D (A + n) j *
    starRingEnd ℂ (pairedEtaCompletedMoebiusQuotientShell rho D (A + n) l)) / L

/-- Each shell correlation is itself the exact sum of the original complete quotient-block correlations; no off-diagonal arithmetic is removed by grouping. -/
theorem pairedEtaCompletedMoebiusQuotientShellCorrelation_eq_blockCorrelations
    (rho : NontrivialZetaZero) (A L D j l : ℕ) :
    pairedEtaCompletedMoebiusQuotientShellCorrelation rho A L D j l =
      ∑ q ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), ∑ r ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)),
        pairedEtaCompletedMoebiusQuotientBlockCorrelation rho D A L q r := by
  unfold pairedEtaCompletedMoebiusQuotientShellCorrelation pairedEtaCompletedMoebiusQuotientShell
    pairedEtaCompletedMoebiusQuotientBlockCorrelation
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  calc
    _ = ∑ r ∈ Finset.Ico (2 ^ l) (2 ^ (l + 1)), ∑ q ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
        ∑ n ∈ Finset.range L, pairedEtaCompletedMoebiusLargeQuotientFamily rho D (A + n) q *
          starRingEnd ℂ (pairedEtaCompletedMoebiusLargeQuotientFamily rho D (A + n) r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- At every point of the actual cubic window, the full complete-block square is the entire shell-to-shell form, retaining all phases and all cross terms. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_twoThirds_norm_sq_eq_shellPairs
    (rho : NontrivialZetaZero) (k : ℕ) {M : ℕ} (hM : M < 2 * (2 ^ k) ^ 3) :
    (‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M ((2 ^ k) ^ 2)‖ : ℂ) ^ 2 =
      ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
        pairedEtaCompletedMoebiusQuotientShell rho ((2 ^ k) ^ 2) M j *
          starRingEnd ℂ (pairedEtaCompletedMoebiusQuotientShell rho ((2 ^ k) ^ 2) M l) := by
  rw [← Complex.mul_conj', pairedEtaCompletedMoebiusCompleteQuotientAggregate_twoThirds_eq_shells rho k hM]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The actual complete-block mean square is exactly the full quadratic form of the dyadic quotient shells, with the physical averaging normalization unchanged. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_shellCorrelations
    (rho : NontrivialZetaZero) (k : ℕ) :
    (pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) : ℂ) =
      ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
        pairedEtaCompletedMoebiusQuotientShellCorrelation rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) j l := by
  unfold pairedEtaCompletedMoebiusCompleteQuotientMeanSquare pairedEtaCompletedMoebiusQuotientShellCorrelation
  push_cast
  simp only [← Finset.sum_div]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range ((2 ^ k) ^ 3), ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
        pairedEtaCompletedMoebiusQuotientShell rho ((2 ^ k) ^ 2) ((2 ^ k) ^ 3 + n) j *
          starRingEnd ℂ (pairedEtaCompletedMoebiusQuotientShell rho ((2 ^ k) ^ 2) ((2 ^ k) ^ 3 + n) l) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply pairedEtaCompletedMoebiusCompleteQuotientAggregate_twoThirds_norm_sq_eq_shellPairs
      have := Finset.mem_range.mp hn
      omega
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

/-- The whole shell form retains the nonzero source limit at a hypothetical right-half zero, after the boundary has been proved negligible. -/
theorem pairedEtaCompletedMoebiusQuotientShellForm_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun k ↦ (∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      pairedEtaCompletedMoebiusQuotientShellCorrelation rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) j l).re)
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  simp only [← pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_eq_shellCorrelations, Complex.ofReal_re]
  exact (pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_tendsto_source rho hrho).comp
    pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop

/-- Any fixed positive gap below the source square is eventually exceeded by the full shell form under the right-half-zero hypothesis. This identifies the uniform gap an independent arithmetic upper bound would have to contradict. -/
theorem pairedEtaCompletedMoebiusQuotientShellForm_eventually_above_sub_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 - δ <
      (∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
        pairedEtaCompletedMoebiusQuotientShellCorrelation rho ((2 ^ k) ^ 3) ((2 ^ k) ^ 3) ((2 ^ k) ^ 2) j l).re := by
  have hgap : ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 - δ < ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2 :=
    sub_lt_self _ hδ
  exact (pairedEtaCompletedMoebiusQuotientShellForm_tendsto_source rho hrho).eventually (lt_mem_nhds hgap)

end

end RiemannGaussian
