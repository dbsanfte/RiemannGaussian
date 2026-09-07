import RiemannGaussian.EtaMoebiusPhysicalFamily
import RiemannGaussian.EtaMoebiusDividedBlockCancellation

/-!
# The exact completed Möbius hyperbola split

The original source is separated into its small and large divisors. On
the square-root range `D² ≤ M`, the large part is exactly a sum of whole
quotient fibres: the cut cannot bisect a fibre. This extra hypothesis is
essential for the proposed full-block formula at a general divisor cut.
Every original complex coefficient and completed odd endpoint is retained.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The large divisors of the original completed Möbius aggregate, with a literal open lower cutoff. -/
def pairedEtaCompletedMoebiusLargeAggregate (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc D M, pairedEtaCompletedMoebiusTerm rho M d

/-- The small and large divisor pieces reconstruct the entire original carrier without an estimate. -/
theorem pairedEtaCompletedMoebiusPartial_add_large (rho : NontrivialZetaZero)
    {M D : ℕ} (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusPartialAggregate rho M D +
      pairedEtaCompletedMoebiusLargeAggregate rho M D =
        pairedEtaCompletedMoebiusTailAggregate rho M := by
  have hd : Disjoint (Finset.Icc 1 D) (Finset.Ioc D M) := by
    apply Finset.disjoint_left.mpr
    intro d hl hh
    have := Finset.mem_Icc.mp hl
    have := Finset.mem_Ioc.mp hh
    omega
  have hu : Finset.Icc 1 D ∪ Finset.Ioc D M = Finset.Icc 1 M := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [pairedEtaCompletedMoebiusPartialAggregate, pairedEtaCompletedMoebiusLargeAggregate,
    ← Finset.sum_union hd, hu, sum_pairedEtaCompletedMoebiusTerm]

/-- The actual large-divisor aggregate is the fixed nonzero source minus its small-divisor piece. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub (rho : NontrivialZetaZero)
    {M D : ℕ} (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      pairedEtaCompletedMoebiusSource rho - pairedEtaCompletedMoebiusPartialAggregate rho M D := by
  have h := pairedEtaCompletedMoebiusPartial_add_large rho hDM
  rw [pairedEtaCompletedMoebiusTailAggregate_eq_source rho hM] at h
  exact eq_sub_of_add_eq' h

/-- A complete quotient block retains its exact complex Möbius sum and the original completed eta prefix. -/
def pairedEtaCompletedMoebiusQuotientBlock (rho : NontrivialZetaZero) (M q : ℕ) : ℂ :=
  complexMoebiusDividedCutoffBlock rho.1 M q *
    (pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix q rho.1)

/-- The existing completed zero-order quotient factorization applies to the original terms themselves. -/
theorem sum_pairedEtaCompletedMoebiusTerm_eq_quotientBlock
    (rho : NontrivialZetaZero) (M q : ℕ) :
    (∑ d ∈ (Finset.Icc 1 M).filter (fun d ↦ M / d = q),
      pairedEtaCompletedMoebiusTerm rho M d) =
        pairedEtaCompletedMoebiusQuotientBlock rho M q := by
  simpa only [pairedEtaCompletedMomentMoebiusTerm_zero, pairedEtaCompletedMoebiusQuotientBlock]
    using sum_pairedEtaCompletedMomentMoebiusTerm_zero_divided_block rho 0 M q

/-- At or beyond the square of the divisor cut, consecutive divisors at that cut have distinct integer quotients. -/
theorem moebiusHyperbola_boundary_quotient_lt {M D : ℕ} (hD : 1 ≤ D) (hDM : D ^ 2 ≤ M) :
    M / (D + 1) < M / D := by
  have hq : D ≤ M / D := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith)
  have hr := Nat.mod_lt M hD
  have he := Nat.div_add_mod M D
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < D + 1)).mpr
  nlinarith

/-- Every quotient below the hyperbola boundary is already wholly in the large-divisor range; no partially cut fibre is silently inserted. -/
theorem moebiusHyperbola_large_filter_eq_full {M D q : ℕ}
    (hD : 1 ≤ D) (hDM : D ^ 2 ≤ M) (hq : q ≤ M / (D + 1)) :
    (Finset.Ioc D M).filter (fun d ↦ M / d = q) =
      (Finset.Icc 1 M).filter (fun d ↦ M / d = q) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hl, hu⟩, he⟩
    exact ⟨⟨by omega, hu⟩, he⟩
  · rintro ⟨⟨hl, hu⟩, he⟩
    refine ⟨⟨?_, hu⟩, he⟩
    by_contra hn
    have hdD : d ≤ D := by omega
    have hdiv : M / D ≤ M / d := Nat.div_le_div_left hdD hl
    have hstrict := moebiusHyperbola_boundary_quotient_lt hD hDM
    omega

/-- The large half on the square-root range equals the exact sum of its complete quotient blocks. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_quotientBlocks
    (rho : NontrivialZetaZero) {M D : ℕ} (hD : 1 ≤ D) (hDM : D ^ 2 ≤ M) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      ∑ q ∈ Finset.Icc 1 (M / (D + 1)), pairedEtaCompletedMoebiusQuotientBlock rho M q := by
  have hmap : ∀ d ∈ Finset.Ioc D M, M / d ∈ Finset.Icc 1 (M / (D + 1)) := by
    intro d hd
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < d := by omega
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hu),
      Nat.div_le_div_left (by omega : D + 1 ≤ d) (by omega)⟩
  rw [pairedEtaCompletedMoebiusLargeAggregate, ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro q hq
  rw [moebiusHyperbola_large_filter_eq_full hD hDM (Finset.mem_Icc.mp hq).2,
    sum_pairedEtaCompletedMoebiusTerm_eq_quotientBlock]

/-- The largest large-divisor quotient stays below twice the divisor cut on the actual dyadic square window. -/
theorem moebiusHyperbola_quotient_lt_twice {M D : ℕ} (hM : M < 2 * D ^ 2) :
    M / (D + 1) < 2 * D := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < D + 1)).mpr
  nlinarith

/-- The original quotient blocks extended by zero to a fixed-dimensional family on a square window. -/
def pairedEtaCompletedMoebiusLargeQuotientFamily (rho : NontrivialZetaZero) (D M q : ℕ) : ℂ :=
  if q ≤ M / (D + 1) then pairedEtaCompletedMoebiusQuotientBlock rho M q else 0

/-- The fixed quotient family reconstructs the literal large-divisor aggregate on every point of the dyadic square window. -/
theorem pairedEtaCompletedMoebiusLargeAggregate_eq_fixedQuotientFamily
    (rho : NontrivialZetaZero) {D M : ℕ} (hD : 1 ≤ D)
    (hMlo : D ^ 2 ≤ M) (hMhi : M < 2 * D ^ 2) :
    pairedEtaCompletedMoebiusLargeAggregate rho M D =
      ∑ q ∈ Finset.Icc 1 (2 * D), pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q := by
  have hq := moebiusHyperbola_quotient_lt_twice hMhi
  have hs : Finset.Icc 1 (M / (D + 1)) ⊆ Finset.Icc 1 (2 * D) :=
    Finset.Icc_subset_Icc le_rfl hq.le
  rw [pairedEtaCompletedMoebiusLargeAggregate_eq_quotientBlocks rho hD hMlo]
  calc
    _ = ∑ q ∈ Finset.Icc 1 (M / (D + 1)),
        pairedEtaCompletedMoebiusLargeQuotientFamily rho D M q := by
      apply Finset.sum_congr rfl
      intro q hmem
      simp only [pairedEtaCompletedMoebiusLargeQuotientFamily, if_pos (Finset.mem_Icc.mp hmem).2]
    _ = _ := by
      apply Finset.sum_subset hs
      intro q hmem hn
      have hnot : ¬q ≤ M / (D + 1) := by
        have := (Finset.mem_Icc.mp hmem).1
        simpa only [Finset.mem_Icc, this, true_and] using hn
      simp only [pairedEtaCompletedMoebiusLargeQuotientFamily, if_neg hnot]

end

end RiemannGaussian
