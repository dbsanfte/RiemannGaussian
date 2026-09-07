import RiemannGaussian.EtaMoebiusBilinearEnergy
import RiemannGaussian.EtaWeightedDivisorSampling

/-!
# Physical estimates for selected original Möbius divisors

A fixed selection of divisor columns keeps its Möbius signs and complex
completion throughout a physical window. The original endpoint errors
and weighted Fourier sampler apply to this selection with their full
window loss. This will estimate the divisor annuli obtained by removing
an odd prime from the product index.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original completed divisor terms on a fixed finite selection. -/
def pairedEtaCompletedMoebiusSelectedAggregate (rho : NontrivialZetaZero)
    (S : Finset ℕ) (M : ℕ) : ℂ :=
  ∑ d ∈ S, pairedEtaCompletedMoebiusTerm rho M d

/-- Product grouping for a fixed selected divisor family retains the original signs, complex powers, completion, and all finite endpoints. -/
theorem pairedEtaCompletedMoebiusSelectedAggregate_eq_products
    (rho : NontrivialZetaZero) {S : Finset ℕ} {M : ℕ} (hS : S ⊆ Finset.Icc 1 M) :
    pairedEtaCompletedMoebiusSelectedAggregate rho S M =
      pairedEtaXiCompletionFactor rho.1 *
        ∑ n ∈ Finset.Icc 1 M,
          ((∑ a ∈ n.divisorsAntidiagonal.filter (fun a ↦ a.2 ∈ S),
            pairedEtaDirichletSign a.1 * μ a.2 : ℤ) : ℂ) * (n : ℂ) ^ (-rho.1) := by
  have hsel : (Finset.Icc 1 M).filter (fun d ↦ d ∈ S) = S := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hd ↦ ⟨hS hd, hd⟩⟩
  have he : (∑ n ∈ Finset.Icc 1 M,
      ((∑ a ∈ n.divisorsAntidiagonal.filter (fun a ↦ a.2 ∈ S),
        pairedEtaDirichletSign a.1 * μ a.2 : ℤ) : ℂ) * (n : ℂ) ^ (-rho.1)) =
      ∑ d ∈ S, (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
        pairedEtaUnpairedDirichletPrefix (M / d) rho.1 := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 M, ∑ a ∈ n.divisorsAntidiagonal,
          if a.2 ∈ S then (pairedEtaDirichletSign a.1 : ℂ) * (μ a.2 : ℂ) *
            ((a.1 * a.2 : ℕ) : ℂ) ^ (-rho.1) else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        rw [Int.cast_sum, Finset.sum_mul, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Nat.mem_divisorsAntidiagonal.mp ha).1]
        split_ifs <;> simp only [Int.cast_mul]
      _ = ∑ n ∈ Finset.Icc 1 M, ∑ a ∈ n.divisorsAntidiagonal,
          if a.1 ∈ S then (μ a.1 : ℂ) * (a.1 : ℂ) ^ (-rho.1) *
            ((pairedEtaDirichletSign a.2 : ℂ) * (a.2 : ℂ) ^ (-rho.1)) else 0 := by
        apply Finset.sum_congr rfl
        intro n _
        conv_lhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
        apply Finset.sum_congr rfl
        rintro ⟨d, q⟩ _
        change (if d ∈ S then (pairedEtaDirichletSign q : ℂ) * (μ d : ℂ) *
          ((q * d : ℕ) : ℂ) ^ (-rho.1) else 0) = _
        rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        split_ifs <;> ring
      _ = ∑ d ∈ Finset.Icc 1 M, ∑ q ∈ Finset.Icc 1 (M / d),
          if d ∈ S then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
            ((pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1)) else 0 :=
        sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix M
          (fun d q ↦ if d ∈ S then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
            ((pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1)) else 0)
      _ = ∑ d ∈ Finset.Icc 1 M, if d ∈ S then (μ d : ℂ) * (d : ℂ) ^ (-rho.1) *
          pairedEtaUnpairedDirichletPrefix (M / d) rho.1 else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : d ∈ S
        · simp only [if_pos hd, pairedEtaUnpairedDirichletPrefix, Finset.mul_sum]
        · simp only [if_neg hd, Finset.sum_const_zero]
      _ = _ := by rw [← Finset.sum_filter, hsel]
  rw [he, pairedEtaCompletedMoebiusSelectedAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix]
  ring

private theorem selected_parity_eq (rho : NontrivialZetaZero) {S : Finset ℕ} {D : ℕ}
    (hS : S ⊆ Finset.Icc 1 D) (M : ℕ) :
    (∑ d ∈ S, pairedEtaCompletedMoebiusParityPhase rho M d) =
      pairedEtaXiCompletionFactor rho.1 / 2 *
        pairedEtaWeightedDivisorParityFamily (fun d ↦ if d ∈ S then (μ d : ℝ) else 0) M D := by
  have he : (Finset.Icc 1 D).filter (fun d ↦ d ∈ S) = S := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hd ↦ ⟨hS hd, hd⟩⟩
  rw [pairedEtaWeightedDivisorParityFamily]
  simp only [apply_ite, Complex.ofReal_intCast, Complex.ofReal_zero, ite_mul, zero_mul,
    ← Finset.sum_filter, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold pairedEtaCompletedMoebiusParityPhase
  ring

/-- Both original complex normalization errors survive on a selected divisor family, with a uniform `D²/M` allowance. -/
theorem norm_pairedEtaCompletedMoebiusSelectedAggregate_physical_sub_parity_le
    (rho : NontrivialZetaZero) {S : Finset ℕ} {D M : ℕ}
    (hS : S ⊆ Finset.Icc 1 D) (hDM : D ≤ M) :
    ‖(M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusSelectedAggregate rho S M -
      pairedEtaXiCompletionFactor rho.1 / 2 *
        pairedEtaWeightedDivisorParityFamily (fun d ↦ if d ∈ S then (μ d : ℝ) else 0) M D‖ ≤
      (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
        2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) * (D : ℝ) ^ 2 / M := by
  let B := pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
    2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho,
      pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho]
  rw [← selected_parity_eq rho hS M, pairedEtaCompletedMoebiusSelectedAggregate,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ S, B * D / M := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp (hS hd)
      have hdM := Finset.mem_Icc.mpr ⟨hd1, hdD.trans hDM⟩
      have h := norm_sub_le_norm_sub_add_norm_sub ((M : ℂ) ^ rho.1 * pairedEtaCompletedMoebiusTerm rho M d)
        (pairedEtaCompletedMoebiusEndpointPhase rho M d)
        (pairedEtaCompletedMoebiusParityPhase rho M d)
      have hb := norm_pairedEtaCompletedMoebiusTerm_physical_sub_endpoint_le rho hdM
      have he := norm_pairedEtaCompletedMoebiusEndpointPhase_sub_parity_cutoff_le rho
        (hd1.trans (hdD.trans hDM)) hd1
      have hbd : B * d / (M : ℝ) ≤ B * D / M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hdD) hB)
          (Nat.cast_nonneg M)
      apply le_trans _ hbd
      apply (h.trans (add_le_add hb he)).trans_eq
      dsimp [B]
      ring
    _ ≤ (D : ℝ) * (B * D / M) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_le_card hS).trans_eq (by simp)
    _ = _ := by dsimp [B]; ring

private theorem selected_norm_sq_eq_physical (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 1 ≤ M) (z : ℂ) :
    ‖z‖ ^ 2 = (M : ℝ) ^ (-2 * rho.1.re) * ‖(M : ℂ) ^ rho.1 * z‖ ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hM, mul_pow]
  rw [← Real.rpow_mul_natCast hMR.le]
  norm_num only [Nat.cast_ofNat]
  rw [← mul_assoc, ← Real.rpow_add hMR,
    show -2 * rho.1.re + rho.1.re * 2 = 0 by ring, Real.rpow_zero, one_mul]

/-- The full physical-window estimate applies uniformly to every fixed selection of original Möbius divisors, including the prime-removal annuli. The sampling and endpoint costs are explicit. -/
theorem pairedEtaCompletedMoebiusSelectedAggregate_meanSquare_le_window
    (rho : NontrivialZetaZero) {S : Finset ℕ} {A L D : ℕ}
    (hS : S ⊆ Finset.Icc 1 D) (hA : 1 ≤ A) (hL : 0 < L) (hD : 1 ≤ D) (hDA : D ≤ A) :
    (∑ t ∈ Finset.range L, ‖pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)‖ ^ 2) / L ≤
      (A : ℝ) ^ (-2 * rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * finiteCircleSamplingConstant *
          ((4 * (D : ℝ) ^ 2 + L) / L) * (1 + Real.log D) ^ 2 * D +
          2 * (pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
            2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho) ^ 2 *
            (D : ℝ) ^ 4 / (A : ℝ) ^ 2) := by
  let w : ℕ → ℝ := fun d ↦ if d ∈ S then (μ d : ℝ) else 0
  let B := pairedEtaCompletedMoebiusPhysicalErrorConstant rho +
    2 * pairedEtaCompletedMoebiusPhaseErrorConstant rho
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [pairedEtaCompletedMoebiusPhysicalErrorConstant_nonneg rho,
      pairedEtaCompletedMoebiusPhaseErrorConstant_nonneg rho]
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hw : (∑ d ∈ Finset.Icc 1 D, w d ^ 2) ≤ (D : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hd : d ∈ S
        · simp only [w, if_pos hd]
          have hm : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
          simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr hm
        · simp [w, hd]
      _ = _ := by simp
  have hpoint (t : ℕ) :
      ‖pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)‖ ^ 2 ≤
        (A : ℝ) ^ (-2 * rho.1.re) *
          (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 *
            ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2 +
            2 * B ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2) := by
    let z := pairedEtaCompletedMoebiusSelectedAggregate rho S (A + t)
    let P := pairedEtaXiCompletionFactor rho.1 / 2 * pairedEtaWeightedDivisorParityFamily w (A + t) D
    have he : ‖((A + t : ℕ) : ℂ) ^ rho.1 * z - P‖ ≤ B * (D : ℝ) ^ 2 / A := by
      apply (norm_pairedEtaCompletedMoebiusSelectedAggregate_physical_sub_parity_le rho hS
        (hDA.trans (Nat.le_add_right A t))).trans
      exact div_le_div_of_nonneg_left (by positivity) hAR (by exact_mod_cast Nat.le_add_right A t)
    have hn := (norm_le_insert' (((A + t : ℕ) : ℂ) ^ rho.1 * z) P).trans (add_le_add le_rfl he)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    have hP : ‖P‖ ^ 2 = ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 4 *
        ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2 := by
      dsimp [P]
      rw [norm_mul, norm_div]
      norm_num only [norm_ofNat]
      ring
    have hsq : ‖((A + t : ℕ) : ℂ) ^ rho.1 * z‖ ^ 2 ≤
        ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 *
          ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2 +
          2 * B ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2 := by
      have hh : ‖((A + t : ℕ) : ℂ) ^ rho.1 * z‖ ^ 2 ≤
          2 * ‖P‖ ^ 2 + 2 * (B * (D : ℝ) ^ 2 / A) ^ 2 := by
        nlinarith [sq_nonneg (‖P‖ - B * (D : ℝ) ^ 2 / A)]
      apply hh.trans_eq
      rw [hP]
      ring
    rw [selected_norm_sq_eq_physical rho (hA.trans (Nat.le_add_right A t)) z]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos hAR (by exact_mod_cast Nat.le_add_right A t)
        (by linarith [NontrivialZetaZero.zero_lt_re rho])) hsq (sq_nonneg _) (by positivity)
  have hs := pairedEtaWeightedDivisorParityFamily_window_sq_le w A hD hL
  have hs' : (∑ t ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2) ≤
      finiteCircleSamplingConstant * (4 * (D : ℝ) ^ 2 + L) * ((1 + Real.log D) ^ 2 * D) :=
    hs.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (sq_nonneg _))
      (mul_nonneg finiteCircleSamplingConstant_pos.le (by positivity)))
  calc
    _ ≤ (∑ t ∈ Finset.range L, (A : ℝ) ^ (-2 * rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 *
          ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2 +
          2 * B ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2)) / (L : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun t _ ↦ hpoint t)) hLR.le
    _ = (A : ℝ) ^ (-2 * rho.1.re) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 *
          (∑ t ∈ Finset.range L, ‖pairedEtaWeightedDivisorParityFamily w (A + t) D‖ ^ 2) / (L : ℝ) +
          2 * B ^ 2 * (D : ℝ) ^ 4 / (A : ℝ) ^ 2) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ le_rfl
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2)) hLR.le
      convert h using 1
      ring

end

end RiemannGaussian
