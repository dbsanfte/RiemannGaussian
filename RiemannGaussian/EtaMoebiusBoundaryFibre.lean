import RiemannGaussian.EtaMoebiusClippedQuotientBlocks

/-!
# Removing the single clipped quotient fibre

At an arbitrary divisor cut, completing the retained quotient blocks adds
only the part of the last fibre below that cut. The exact complex identity
is retained. On a cubic physical window with a quadratic divisor cut, this
boundary contains at most the cube-root scale in divisors.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Completing all retained quotient fibres moves the divisor cut downwards. -/
theorem moebiusQuotientBoundary_le (M D : ℕ) :
    M / (M / (D + 1) + 1) ≤ D := by
  have hM : M < (M / (D + 1) + 1) * (D + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < D + 1)).mp (Nat.lt_succ_self _)
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ _)).mpr (by nlinarith))

/-- A quotient prefix is exactly the original aggregate above its complete lower fibre boundary, at every cutoff. -/
theorem sum_pairedEtaCompletedMoebiusQuotientBlock_eq_large
    (rho : NontrivialZetaZero) (M Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, pairedEtaCompletedMoebiusQuotientBlock rho M q) =
      pairedEtaCompletedMoebiusLargeAggregate rho M (M / (Q + 1)) := by
  have hmap : ∀ d ∈ Finset.Ioc (M / (Q + 1)) M, M / d ∈ Finset.Icc 1 Q := by
    intro d hd
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hd
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hl
    have hprod : M < d * (Q + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp hl
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hu),
      Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hdpos).mpr (by nlinarith))⟩
  have hf : ∀ q ∈ Finset.Icc 1 Q,
      (Finset.Ioc (M / (Q + 1)) M).filter (fun d ↦ M / d = q) =
        (Finset.Icc 1 M).filter (fun d ↦ M / d = q) := by
    intro q hq
    obtain ⟨_, hqQ⟩ := Finset.mem_Icc.mp hq
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hl, hu⟩, he⟩
      exact ⟨⟨lt_of_le_of_lt (Nat.zero_le _) hl, hu⟩, he⟩
    · rintro ⟨⟨hl, hu⟩, he⟩
      have hdiv : M / d < Q + 1 := by omega
      have hprod := (Nat.div_lt_iff_lt_mul hl).mp hdiv
      exact ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith), hu⟩, he⟩
  rw [pairedEtaCompletedMoebiusLargeAggregate, ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro q hq
  rw [hf q hq, sum_pairedEtaCompletedMoebiusTerm_eq_quotientBlock]

/-- The added boundary retains the original completed complex terms, including their signs and phases. -/
def pairedEtaCompletedMoebiusBoundaryFibre (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc (M / (M / (D + 1) + 1)) D, pairedEtaCompletedMoebiusTerm rho M d

/-- The sum of complete quotient blocks selected by the actual divisor cut. -/
def pairedEtaCompletedMoebiusCompleteQuotientAggregate (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (M / (D + 1)), pairedEtaCompletedMoebiusQuotientBlock rho M q

/-- Completing the surviving blocks adds exactly the boundary fibre, with its full complex sign. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_boundary_add_large
    (rho : NontrivialZetaZero) {M D : ℕ} (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D =
      pairedEtaCompletedMoebiusBoundaryFibre rho M D +
        pairedEtaCompletedMoebiusLargeAggregate rho M D := by
  have hRD := moebiusQuotientBoundary_le M D
  have hd : Disjoint (Finset.Ioc (M / (M / (D + 1) + 1)) D) (Finset.Ioc D M) := by
    apply Finset.disjoint_left.mpr
    intro d hl hh
    have := Finset.mem_Ioc.mp hl
    have := Finset.mem_Ioc.mp hh
    omega
  have hu : Finset.Ioc (M / (M / (D + 1) + 1)) D ∪ Finset.Ioc D M =
      Finset.Ioc (M / (M / (D + 1) + 1)) M := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate,
    sum_pairedEtaCompletedMoebiusQuotientBlock_eq_large]
  simp only [pairedEtaCompletedMoebiusBoundaryFibre, pairedEtaCompletedMoebiusLargeAggregate]
  rw [← Finset.sum_union hd, hu]

/-- The added interval is contained in the single last retained quotient fibre, rather than several moving fibres. -/
theorem moebiusQuotientBoundary_filter_eq_Ioc {M D : ℕ} (hDM : D < M) :
    (Finset.Icc 1 D).filter (fun d ↦ M / d = M / (D + 1)) =
      Finset.Ioc (M / (M / (D + 1) + 1)) D := by
  have hq : 0 < M / (D + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hprod : M / (D + 1) * (D + 1) ≤ M := Nat.div_mul_le_self M (D + 1)
  have hupper : D + 1 ≤ M / (M / (D + 1)) :=
    (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, he⟩
    exact ⟨((moebius_dividedCutoff_eq_iff hq hl).mp he).1, hu⟩
  · rintro ⟨hl, hu⟩
    have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hl
    exact ⟨⟨hd, hu⟩, (moebius_dividedCutoff_eq_iff hq hd).mpr ⟨hl, by omega⟩⟩

/-- Only the last clipped quotient block changes when it is completed; the difference is the exact boundary carrier. -/
theorem pairedEtaCompletedMoebiusBoundaryFibre_eq_block_sub_clipped
    (rho : NontrivialZetaZero) {M D : ℕ} (hDM : D < M) :
    pairedEtaCompletedMoebiusBoundaryFibre rho M D =
      pairedEtaCompletedMoebiusQuotientBlock rho M (M / (D + 1)) -
        pairedEtaCompletedMoebiusClippedQuotientBlock rho M D (M / (D + 1)) := by
  have hs : Finset.Icc 1 D ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc le_rfl hDM.le
  have hf := Finset.filter_subset_filter (p := fun d ↦ M / d = M / (D + 1)) hs
  have he : (Finset.Icc 1 M).filter (fun d ↦ M / d = M / (D + 1)) \
      (Finset.Icc 1 D).filter (fun d ↦ M / d = M / (D + 1)) =
        (Finset.Ioc D M).filter (fun d ↦ M / d = M / (D + 1)) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff (f := pairedEtaCompletedMoebiusTerm rho M) hf
  rw [he, sum_pairedEtaCompletedMoebiusTerm_eq_clippedQuotientBlock,
    sum_pairedEtaCompletedMoebiusTerm_eq_quotientBlock,
    moebiusQuotientBoundary_filter_eq_Ioc hDM] at hsum
  exact eq_sub_of_add_eq' hsum

/-- On the cubic physical window, at most the cube-root scale of divisors is added by completing the last fibre. -/
theorem moebiusTwoThirds_boundary_card_le {M D : ℕ} (hD : 1 ≤ D) (hM : D ^ 3 ≤ M) :
    (Finset.Ioc (M / (M / (D ^ 2 + 1) + 1)) (D ^ 2)).card ≤ D := by
  have hsub : D - 1 + 1 = D := Nat.sub_add_cancel hD
  have hq : D - 1 ≤ M / (D ^ 2 + 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hprod : M / (D ^ 2 + 1) * (D ^ 2 + 1) ≤ M := Nat.div_mul_le_self M (D ^ 2 + 1)
  have hupper : M < (M / (M / (D ^ 2 + 1) + 1) + 1) * (M / (D ^ 2 + 1) + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self _)
  have hRD : D ^ 2 ≤ M / (M / (D ^ 2 + 1) + 1) + D := by
    by_contra hn
    have hr : M / (M / (D ^ 2 + 1) + 1) + 1 + D ≤ D ^ 2 := by omega
    have hp := Nat.mul_le_mul_right (M / (D ^ 2 + 1) + 1) hr
    nlinarith
  simpa only [Nat.card_Ioc] using (show D ^ 2 - M / (M / (D ^ 2 + 1) + 1) ≤ D by omega)

/-- The single boundary fibre has a uniform cube-root cardinality bound times the original physical decay; no Möbius cancellation is needed here. -/
theorem norm_pairedEtaCompletedMoebiusBoundaryFibre_twoThirds_le
    (rho : NontrivialZetaZero) {M D : ℕ} (hD : 1 ≤ D) (hM : D ^ 3 ≤ M) :
    ‖pairedEtaCompletedMoebiusBoundaryFibre rho M (D ^ 2)‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * (D : ℝ) ^ (1 - 3 * rho.1.re) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have h23 : D ^ 2 ≤ D ^ 3 := by nlinarith [Nat.mul_le_mul_left (D ^ 2) hD]
  have hc := (pairedEtaCompletedMoebiusTermConstant_pos rho).le
  have hcard : ((Finset.Ioc (M / (M / (D ^ 2 + 1) + 1)) (D ^ 2)).card : ℝ) ≤ D := by
    exact_mod_cast moebiusTwoThirds_boundary_card_le hD hM
  have hp : (M : ℝ) ^ (-rho.1.re) ≤ ((D : ℝ) ^ 3) ^ (-rho.1.re) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hM)
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  have he : (D : ℝ) * ((D : ℝ) ^ 3) ^ (-rho.1.re) = (D : ℝ) ^ (1 - 3 * rho.1.re) := by
    have hx : ((D : ℝ) ^ 3) ^ (-rho.1.re) = (D : ℝ) ^ (3 * (-rho.1.re)) := by
      simpa only [Real.rpow_ofNat] using (Real.rpow_mul hDR.le 3 (-rho.1.re)).symm
    rw [hx, show 1 - 3 * rho.1.re = 1 + 3 * (-rho.1.re) by ring,
      Real.rpow_add hDR, Real.rpow_one]
  unfold pairedEtaCompletedMoebiusBoundaryFibre
  calc
    _ ≤ ∑ d ∈ Finset.Ioc (M / (M / (D ^ 2 + 1) + 1)) (D ^ 2),
        pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hd
      exact norm_pairedEtaCompletedMoebiusTerm_le rho
        (Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hl, hu.trans (h23.trans hM)⟩)
    _ ≤ (D : ℝ) * (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    _ ≤ (D : ℝ) * (pairedEtaCompletedMoebiusTermConstant rho * ((D : ℝ) ^ 3) ^ (-rho.1.re)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hc) hDR.le
    _ = _ := by rw [← mul_assoc, mul_comm (D : ℝ), mul_assoc, he]

end

end RiemannGaussian
