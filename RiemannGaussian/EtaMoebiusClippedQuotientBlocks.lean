import RiemannGaussian.EtaMoebiusHyperbolaSplit

/-!
# Exact quotient blocks at arbitrary divisor cuts

A divisor cut beyond the square root can bisect a quotient fibre. The
arithmetic block below retains the clipped lower endpoint as a maximum.
This gives exact finite reindexing at every cut, and a fixed cube-root
quotient range when the physical cutoff is cubic and the divisor cut
is quadratic. No boundary fibre is replaced by a whole block.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original complex Möbius weights in one quotient fibre after the literal large-divisor cutoff is imposed. -/
def complexMoebiusClippedDividedBlock (s : ℂ) (M D q : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Ioc D M).filter (fun d ↦ M / d = q), (μ d : ℂ) * (d : ℂ) ^ (-s)

/-- A clipped quotient fibre has the exact lower endpoint given by the maximum of the divisor cut and the complete fibre's lower endpoint. -/
theorem moebiusClippedDividedCutoff_filter_eq_Ioc (M D : ℕ) {q : ℕ} (hq : 0 < q) :
    (Finset.Ioc D M).filter (fun d ↦ M / d = q) =
      Finset.Ioc (max D (M / (q + 1))) (M / q) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, _⟩, he⟩
    have hd : 0 < d := by omega
    have hf := (moebius_dividedCutoff_eq_iff hq hd).mp he
    exact ⟨max_lt hl hf.1, hf.2⟩
  · rintro ⟨hl, hu⟩
    have hlD := (le_max_left D (M / (q + 1))).trans_lt hl
    have hlq := (le_max_right D (M / (q + 1))).trans_lt hl
    have hd : 0 < d := by omega
    exact ⟨⟨hlD, hu.trans (Nat.div_le_self M q)⟩,
      (moebius_dividedCutoff_eq_iff hq hd).mpr ⟨hlq, hu⟩⟩

/-- Every retained clipped arithmetic block is the difference of two actual finite prefixes, with the physical divisor cut included in the lower prefix. -/
theorem complexMoebiusClippedDividedBlock_eq_prefix_sub (s : ℂ) (M D : ℕ)
    {q : ℕ} (hq : 0 < q) (hcut : q ≤ M / (D + 1)) :
    complexMoebiusClippedDividedBlock s M D q =
      complexMoebiusFinitePrefix s (M / q) -
        complexMoebiusFinitePrefix s (max D (M / (q + 1))) := by
  have hprod : q * (D + 1) ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < D + 1)).mp hcut
  have hDq : D + 1 ≤ M / q := (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)
  have hLU : max D (M / (q + 1)) ≤ M / q :=
    max_le (by omega) (Nat.div_le_div_left (by omega : q ≤ q + 1) hq)
  have hs : Finset.Icc 1 (max D (M / (q + 1))) ⊆ Finset.Icc 1 (M / q) :=
    Finset.Icc_subset_Icc le_rfl hLU
  have he : Finset.Icc 1 (M / q) \ Finset.Icc 1 (max D (M / (q + 1))) =
      Finset.Ioc (max D (M / (q + 1))) (M / q) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  apply eq_sub_iff_add_eq.mpr
  rw [complexMoebiusClippedDividedBlock, moebiusClippedDividedCutoff_filter_eq_Ioc M D hq,
    complexMoebiusFinitePrefix_eq_sum_Icc, complexMoebiusFinitePrefix_eq_sum_Icc, ← he]
  exact Finset.sum_sdiff hs

/-- The actual completed quotient block with its large-divisor boundary clipped exactly. -/
def pairedEtaCompletedMoebiusClippedQuotientBlock (rho : NontrivialZetaZero) (M D q : ℕ) : ℂ :=
  complexMoebiusClippedDividedBlock rho.1 M D q *
    (pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix q rho.1)

/-- Exact factorization of the original completed terms over a clipped quotient fibre. -/
theorem sum_pairedEtaCompletedMoebiusTerm_eq_clippedQuotientBlock
    (rho : NontrivialZetaZero) (M D q : ℕ) :
    (∑ d ∈ (Finset.Ioc D M).filter (fun d ↦ M / d = q), pairedEtaCompletedMoebiusTerm rho M d) =
      pairedEtaCompletedMoebiusClippedQuotientBlock rho M D q := by
  rw [pairedEtaCompletedMoebiusClippedQuotientBlock, complexMoebiusClippedDividedBlock, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, (Finset.mem_filter.mp hd).2]

/-- The literal large-divisor range reindexes into clipped quotient blocks at every physical cutoff and every divisor cut. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_clippedQuotientBlocks
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      ∑ q ∈ Finset.Icc 1 (M / (D + 1)), pairedEtaCompletedMoebiusClippedQuotientBlock rho M D q := by
  have hmap : ∀ d ∈ Finset.Ioc D M, M / d ∈ Finset.Icc 1 (M / (D + 1)) := by
    intro d hd
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < d := by omega
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hu),
      Nat.div_le_div_left (by omega : D + 1 ≤ d) (by omega)⟩
  rw [pairedEtaCompletedMoebiusLargeAggregate, ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro q _
  exact sum_pairedEtaCompletedMoebiusTerm_eq_clippedQuotientBlock rho M D q

/-- The exact clipped blocks are already zero beyond the actual quotient boundary; no artificial extension changes the arithmetic. -/
theorem pairedEtaCompletedMoebiusClippedQuotientBlock_eq_zero_of_large
    (rho : NontrivialZetaZero) (M D : ℕ) {q : ℕ} (hq : M / (D + 1) < q) :
    pairedEtaCompletedMoebiusClippedQuotientBlock rho M D q = 0 := by
  have he : (Finset.Ioc D M).filter (fun d ↦ M / d = q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨hd, he⟩ := Finset.mem_filter.mp hd
    have hl := (Finset.mem_Ioc.mp hd).1
    have hdiv : M / d ≤ M / (D + 1) := Nat.div_le_div_left (by omega : D + 1 ≤ d) (by omega)
    omega
  simp only [pairedEtaCompletedMoebiusClippedQuotientBlock, complexMoebiusClippedDividedBlock,
    he, Finset.sum_empty, zero_mul]

/-- A quadratic divisor cut leaves fewer than twice the cube-root scale in quotient indices throughout the cubic physical window. -/
theorem moebiusTwoThirds_quotient_lt_twice {M D : ℕ} (hM : M < 2 * D ^ 3) :
    M / (D ^ 2 + 1) < 2 * D := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < D ^ 2 + 1)).mpr
  nlinarith

/-- The entire complement beyond `D²` is exactly a fixed family of at most `2D` clipped quotient blocks on the original cubic window. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_twoThirds_eq_fixedClippedQuotients
    (rho : NontrivialZetaZero) {M D : ℕ} (hM : M < 2 * D ^ 3) :
    pairedEtaCompletedMoebiusLargeAggregate rho M (D ^ 2) =
      ∑ q ∈ Finset.Icc 1 (2 * D), pairedEtaCompletedMoebiusClippedQuotientBlock rho M (D ^ 2) q := by
  have hq := moebiusTwoThirds_quotient_lt_twice hM
  have hs : Finset.Icc 1 (M / (D ^ 2 + 1)) ⊆ Finset.Icc 1 (2 * D) :=
    Finset.Icc_subset_Icc le_rfl hq.le
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_clippedQuotientBlocks]
  apply Finset.sum_subset hs
  intro q hmem hn
  have hlarge : M / (D ^ 2 + 1) < q := by
    have := (Finset.mem_Icc.mp hmem).1
    simp only [Finset.mem_Icc] at hn
    omega
  exact pairedEtaCompletedMoebiusClippedQuotientBlock_eq_zero_of_large rho M (D ^ 2) hlarge

end

end RiemannGaussian
