import RiemannGaussian.EtaMoebiusQuarticBoundary
import RiemannGaussian.EtaMoebiusCoprimeFirstMean

/-!
# Completing quotient fibres after simultaneous prime exclusion

Every intersection in the odd-prime sieve is an original completed Möbius
term at a multiplied divisor. Consequently the single quartic boundary
costs at most `C_term * P * u^(2-4*Re(rho))`, uniformly in the modulus.
This cost vanishes on the existing growing sieve schedule. Completion
preserves the whole complex mean and its nonzero source; an independent
upper bound below that source is still required.
-/

open Complex Filter
open scoped Classical Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original divisor term with coprimality imposed on its eta index; the divisor's own coprimality is selected separately. -/
def pairedEtaCompletedMoebiusCoprimeTerm
    (rho : NontrivialZetaZero) (P M d : ℕ) : ℂ :=
  (μ d : ℂ) * (d : ℂ) ^ (-rho.1) * (pairedEtaXiCompletionFactor rho.1 *
    ∑ q ∈ (Finset.Icc 1 (M / d)).filter (fun q ↦ q.Coprime P),
      (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1))

/-- Every actual sieve intersection is exactly the original completed term at a multiplied divisor, including intersections beyond the physical cutoff. -/
theorem pairedEtaCompletedMoebiusCoprimeTerm_eq_sum_mul
    (rho : NontrivialZetaZero) {P d : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hd : d.Coprime P) (M : ℕ) :
    pairedEtaCompletedMoebiusCoprimeTerm rho P M d =
      ∑ e ∈ P.divisors, pairedEtaCompletedMoebiusTerm rho M (d * e) := by
  rw [pairedEtaCompletedMoebiusCoprimeTerm,
    pairedEtaUnpairedDirichletPrefix_coprime_eq_sieve rho.1 hP hodd]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hde : d.Coprime e := hd.of_dvd_right (Nat.dvd_of_mem_divisors he)
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hde,
    Int.cast_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
    Nat.div_div_eq_div_mul]
  ring

private theorem norm_term_le_all (rho : NontrivialZetaZero) {d : ℕ}
    (hd : 1 ≤ d) (M : ℕ) :
    ‖pairedEtaCompletedMoebiusTerm rho M d‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re) := by
  by_cases hdm : d ≤ M
  · exact norm_pairedEtaCompletedMoebiusTerm_le rho (Finset.mem_Icc.mpr ⟨hd, hdm⟩)
  · rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, Nat.div_eq_of_lt (by omega)]
    simp only [pairedEtaUnpairedDirichletPrefix, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty, mul_zero, norm_zero]
    exact mul_nonneg (pairedEtaCompletedMoebiusTermConstant_pos rho).le
      (Real.rpow_nonneg (Nat.cast_nonneg M) _)

/-- The sieve costs at most one copy of the physical term bound per divisor of its modulus, uniformly in the surviving divisor. -/
theorem norm_pairedEtaCompletedMoebiusCoprimeTerm_le
    (rho : NontrivialZetaZero) {P d : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hd : 1 ≤ d) (hc : d.Coprime P) (M : ℕ) :
    ‖pairedEtaCompletedMoebiusCoprimeTerm rho P M d‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * P * (M : ℝ) ^ (-rho.1.re) := by
  rw [pairedEtaCompletedMoebiusCoprimeTerm_eq_sum_mul rho hP hodd hc]
  calc
    _ ≤ ∑ e ∈ P.divisors,
        pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      exact norm_term_le_all rho (Nat.mul_pos hd (Nat.pos_of_mem_divisors he)) M
    _ ≤ (P : ℝ) * (pairedEtaCompletedMoebiusTermConstant rho * (M : ℝ) ^ (-rho.1.re)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self P)
      exact mul_nonneg (pairedEtaCompletedMoebiusTermConstant_pos rho).le
        (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = _ := by ring

/-- The single added boundary retains coprimality on both original factors and every complex sign. -/
def pairedEtaCompletedMoebiusCoprimeBoundaryFibre
    (rho : NontrivialZetaZero) (P M D : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Ioc (M / (M / (D + 1) + 1)) D).filter (fun d ↦ d.Coprime P),
    pairedEtaCompletedMoebiusCoprimeTerm rho P M d

/-- Completing the sieved quartic boundary costs at most a linear modulus factor, with no bound on the remaining quotient blocks assumed. -/
theorem norm_pairedEtaCompletedMoebiusCoprimeBoundaryFibre_quartic_le
    (rho : NontrivialZetaZero) {P M u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 1 ≤ u) (hM : u ^ 4 ≤ M) :
    ‖pairedEtaCompletedMoebiusCoprimeBoundaryFibre rho P M (u ^ 3)‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * P * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hC : 0 ≤ pairedEtaCompletedMoebiusTermConstant rho * P :=
    mul_nonneg (pairedEtaCompletedMoebiusTermConstant_pos rho).le (Nat.cast_nonneg P)
  have hcard : (((Finset.Ioc (M / (M / (u ^ 3 + 1) + 1)) (u ^ 3)).filter
      (fun d ↦ d.Coprime P)).card : ℝ) ≤ (u : ℝ) ^ 2 := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (moebiusQuartic_boundary_card_le hu hM)
  have hp : (M : ℝ) ^ (-rho.1.re) ≤ ((u : ℝ) ^ 4) ^ (-rho.1.re) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hM)
      (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)
  have he : (u : ℝ) ^ 2 * ((u : ℝ) ^ 4) ^ (-rho.1.re) = (u : ℝ) ^ (2 - 4 * rho.1.re) := by
    rw [← Real.rpow_natCast_mul huR.le,
      show 2 - 4 * rho.1.re = 2 + 4 * (-rho.1.re) by ring,
      Real.rpow_add huR, Real.rpow_ofNat]
    norm_num only [Nat.cast_ofNat]
  unfold pairedEtaCompletedMoebiusCoprimeBoundaryFibre
  calc
    _ ≤ ∑ d ∈ (Finset.Ioc (M / (M / (u ^ 3 + 1) + 1)) (u ^ 3)).filter (fun d ↦ d.Coprime P),
        pairedEtaCompletedMoebiusTermConstant rho * P * (M : ℝ) ^ (-rho.1.re) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdI, hdP⟩ := Finset.mem_filter.mp hd
      exact norm_pairedEtaCompletedMoebiusCoprimeTerm_le rho hP hodd
        (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hdI).1) hdP M
    _ ≤ (u : ℝ) ^ 2 * (pairedEtaCompletedMoebiusTermConstant rho * P * (M : ℝ) ^ (-rho.1.re)) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    _ ≤ (u : ℝ) ^ 2 * (pairedEtaCompletedMoebiusTermConstant rho * P * ((u : ℝ) ^ 4) ^ (-rho.1.re)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) (sq_nonneg _)
    _ = _ := by rw [← mul_assoc, mul_comm ((u : ℝ) ^ 2), mul_assoc, he]

private theorem coprime_low_eq_sum_terms (rho : NontrivialZetaZero) (P M D : ℕ) :
    pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M =
      ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d.Coprime P),
        pairedEtaCompletedMoebiusCoprimeTerm rho P M d := by
  unfold pairedEtaCompletedMoebiusCoprimeLowAggregate pairedEtaMoebiusCoprimeDivisors
    pairedEtaCompletedMoebiusCoprimeTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem sum_coprime_Ioc_add_Icc (f : ℕ → ℂ) (P : ℕ) {R D : ℕ} (hRD : R ≤ D) :
    (∑ d ∈ (Finset.Ioc R D).filter (fun d ↦ d.Coprime P), f d) +
      (∑ d ∈ (Finset.Icc 1 R).filter (fun d ↦ d.Coprime P), f d) =
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d.Coprime P), f d := by
  have hs : (Finset.Icc 1 R).filter (fun d ↦ d.Coprime P) ⊆
      (Finset.Icc 1 D).filter (fun d ↦ d.Coprime P) :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl hRD)
  have he : (Finset.Icc 1 D).filter (fun d ↦ d.Coprime P) \
      (Finset.Icc 1 R).filter (fun d ↦ d.Coprime P) =
        (Finset.Ioc R D).filter (fun d ↦ d.Coprime P) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← he]
  exact Finset.sum_sdiff hs

/-- Moving the original sieved product cutoff to the complete quotient boundary adds exactly the actual signed boundary fibre. -/
theorem pairedEtaCompletedMoebiusCoprimeAggregate_complete_eq_boundary_add
    (rho : NontrivialZetaZero) {P M D : ℕ} (hodd : Odd P) (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCoprimeAggregate rho P (M / (M / (D + 1) + 1)) M =
      pairedEtaCompletedMoebiusCoprimeBoundaryFibre rho P M D +
        pairedEtaCompletedMoebiusCoprimeAggregate rho P D M := by
  have hRD := moebiusQuotientBoundary_le M D
  have hlow : pairedEtaCompletedMoebiusCoprimeBoundaryFibre rho P M D +
      pairedEtaCompletedMoebiusCoprimeLowAggregate rho P (M / (M / (D + 1) + 1)) M =
        pairedEtaCompletedMoebiusCoprimeLowAggregate rho P D M := by
    simp only [pairedEtaCompletedMoebiusCoprimeBoundaryFibre, coprime_low_eq_sum_terms]
    exact sum_coprime_Ioc_add_Icc _ P hRD
  have hfull := pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd hM (hRD.trans hDM)
  have horig := pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd hM hDM
  linear_combination hfull - horig - hlow

private theorem coprime_high_eq_sum_terms (rho : NontrivialZetaZero) {P M D : ℕ}
    (hodd : Odd P) (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCoprimeAggregate rho P D M =
      ∑ d ∈ (Finset.Ioc D M).filter (fun d ↦ d.Coprime P),
        pairedEtaCompletedMoebiusCoprimeTerm rho P M d := by
  have hz : pairedEtaCompletedMoebiusCoprimeAggregate rho P M M = 0 := by
    unfold pairedEtaCompletedMoebiusCoprimeAggregate
    have hs : ∀ n ∈ (Finset.Icc 1 M).filter (fun n ↦ n.Coprime P),
        (pairedEtaMoebiusHighProductCoefficient M n : ℂ) * (n : ℂ) ^ (-rho.1) = 0 := by
      intro n hn
      rw [pairedEtaMoebiusHighProductCoefficient_eq_zero (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2]
      simp
    rw [Finset.sum_eq_zero hs, mul_zero]
  have htotal := pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd hM (le_refl M)
  have hcut := pairedEtaCompletedMoebiusCoprimeLow_add_coprime_eq_source rho hodd hM hDM
  rw [hz, add_zero] at htotal
  have hsplit := sum_coprime_Ioc_add_Icc (pairedEtaCompletedMoebiusCoprimeTerm rho P M) P hDM
  rw [← coprime_low_eq_sum_terms, ← coprime_low_eq_sum_terms] at hsplit
  linear_combination hcut - htotal - hsplit

/-- The changed product cutoff consists of complete quotient fibres, with both coprimality selections and all complex terms retained. -/
theorem pairedEtaCompletedMoebiusCoprimeAggregate_complete_eq_quotient_sum
    (rho : NontrivialZetaZero) {P M : ℕ} (hodd : Odd P) (hM : 2 ≤ M) (Q : ℕ) :
    pairedEtaCompletedMoebiusCoprimeAggregate rho P (M / (Q + 1)) M =
      ∑ q ∈ Finset.Icc 1 Q,
        ∑ d ∈ (Finset.Ioc (M / (q + 1)) (M / q)).filter (fun d ↦ d.Coprime P),
          pairedEtaCompletedMoebiusCoprimeTerm rho P M d := by
  have hmap : ∀ d ∈ (Finset.Ioc (M / (Q + 1)) M).filter (fun d ↦ d.Coprime P),
      M / d ∈ Finset.Icc 1 Q := by
    intro d hd
    obtain ⟨⟨hl, hu⟩, _⟩ := (Finset.mem_filter.trans (and_congr_left fun _ ↦ Finset.mem_Ioc)).mp hd
    have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hl
    have hprod : M < d * (Q + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp hl
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hdpos).mpr (by simpa using hu),
      Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hdpos).mpr (by nlinarith))⟩
  rw [coprime_high_eq_sum_terms rho hodd hM (Nat.div_le_self _ _),
    ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqpos, hqQ⟩ := Finset.mem_Icc.mp hq
  have hf : ((Finset.Ioc (M / (Q + 1)) M).filter (fun d ↦ d.Coprime P)).filter
      (fun d ↦ M / d = q) =
        (Finset.Ioc (M / (q + 1)) (M / q)).filter (fun d ↦ d.Coprime P) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hl, _⟩, hc⟩, he⟩
      exact ⟨(moebius_dividedCutoff_eq_iff hqpos (lt_of_le_of_lt (Nat.zero_le _) hl)).mp he, hc⟩
    · rintro ⟨⟨hl, hu⟩, hc⟩
      have hdpos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hl
      have hlQ := (Nat.div_le_div_left (Nat.succ_le_succ hqQ) (Nat.zero_lt_succ q)).trans_lt hl
      exact ⟨⟨⟨hlQ, hu.trans (Nat.div_le_self _ _)⟩, hc⟩,
        (moebius_dividedCutoff_eq_iff hqpos hdpos).mpr ⟨hl, hu⟩⟩
  rw [hf]

/-- Each complete coprime fibre factors into its actual signed Möbius block and the sieved eta prefix, retaining the completion phase. -/
theorem sum_pairedEtaCompletedMoebiusCoprimeTerm_fibre_eq_prefix_mul
    (rho : NontrivialZetaZero) (P M : ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ d ∈ (Finset.Ioc (M / (q + 1)) (M / q)).filter (fun d ↦ d.Coprime P),
      pairedEtaCompletedMoebiusCoprimeTerm rho P M d) =
        (∑ d ∈ (Finset.Ioc (M / (q + 1)) (M / q)).filter (fun d ↦ d.Coprime P),
          (μ d : ℂ) * (d : ℂ) ^ (-rho.1)) *
            (pairedEtaXiCompletionFactor rho.1 *
              ∑ r ∈ (Finset.Icc 1 q).filter (fun r ↦ r.Coprime P),
                (pairedEtaDirichletSign r : ℂ) * (r : ℂ) ^ (-rho.1)) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
  have hdiv := (moebius_dividedCutoff_eq_iff hq (lt_of_le_of_lt (Nat.zero_le _) hdI.1)).mpr hdI
  rw [pairedEtaCompletedMoebiusCoprimeTerm, hdiv]

/-- The quartic complex mean of the original coprime product prefix at the complete quotient cutoff. -/
def pairedEtaMoebiusCoprimeCompleteQuarticFirstMean
    (rho : NontrivialZetaZero) (P u : ℕ) : ℂ :=
  (∑ t ∈ Finset.range (u ^ 4), pairedEtaCompletedMoebiusCoprimeAggregate rho P
    ((u ^ 4 + t) / ((u ^ 4 + t) / (u ^ 3 + 1) + 1)) (u ^ 4 + t)) / (u ^ 4 : ℕ)

/-- Completing the sieved complex mean pays the linear modulus cost of the actual boundary, including every prime intersection. -/
theorem norm_pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_sub_original_le
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P) (hu : 2 ≤ u) :
    ‖pairedEtaMoebiusCoprimeCompleteQuarticFirstMean rho P u -
      pairedEtaMoebiusCoprimeQuarticFirstMean rho P u‖ ≤
        pairedEtaCompletedMoebiusTermConstant rho * P * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu.trans' (by norm_num : 0 < 2)
  have hM : 2 ≤ u ^ 4 := hu.trans (Nat.le_self_pow (by decide : 4 ≠ 0) u)
  have hD : u ^ 3 ≤ u ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  unfold pairedEtaMoebiusCoprimeCompleteQuarticFirstMean pairedEtaMoebiusCoprimeQuarticFirstMean
  simp_rw [pairedEtaCompletedMoebiusCoprimeAggregate_complete_eq_boundary_add rho hodd
    (hM.trans (Nat.le_add_right _ _)) (hD.trans (Nat.le_add_right _ _))]
  rw [Finset.sum_add_distrib, add_div, add_sub_cancel_right, norm_div, Complex.norm_natCast]
  have hsum := (norm_sum_le (Finset.range (u ^ 4))
    (fun t ↦ pairedEtaCompletedMoebiusCoprimeBoundaryFibre rho P (u ^ 4 + t) (u ^ 3))).trans
      (Finset.sum_le_sum (fun t _ ↦ norm_pairedEtaCompletedMoebiusCoprimeBoundaryFibre_quartic_le
        rho hP hodd (by omega : 1 ≤ u) (Nat.le_add_right (u ^ 4) t)))
  apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (u ^ 4))).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  field_simp

/-- The completed coprime mean retains the explicit source allowance, with both the whole low sieve and its boundary included. -/
theorem norm_pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_sub_source_le
    (rho : NontrivialZetaZero) {P u : ℕ} (hP : 0 < P) (hodd : Odd P)
    (hu : 2 ≤ u) (hPu : P ∣ u) :
    ‖pairedEtaMoebiusCoprimeCompleteQuarticFirstMean rho P u - pairedEtaCompletedMoebiusSource rho‖ ≤
      (pairedEtaCompletedMoebiusTermConstant rho + pairedEtaMoebiusFirstMeanConstant rho) *
        (P : ℝ) ^ 2 * (u : ℝ) ^ (2 - 4 * rho.1.re) := by
  have hP2 : (P : ℝ) ≤ (P : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) P
  have hbd := norm_pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_sub_original_le rho hP hodd hu
  have hbd' := hbd.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP2 (pairedEtaCompletedMoebiusTermConstant_pos rho).le) (by positivity))
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (pairedEtaMoebiusCoprimeCompleteQuarticFirstMean rho P u)
    (pairedEtaMoebiusCoprimeQuarticFirstMean rho P u) (pairedEtaCompletedMoebiusSource rho)
  exact (ht.trans (add_le_add hbd'
    (norm_pairedEtaMoebiusCoprimeQuarticFirstMean_sub_source_le rho hP hodd hu hPu))).trans_eq (by ring)

/-- On the explicit growing sieve schedule, completing all quotient fibres preserves the original nonzero complex source. -/
theorem pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_growing_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun v ↦ pairedEtaMoebiusCoprimeCompleteQuarticFirstMean rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v))
        atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  let a := 2 + (pairedEtaCoprimeScalePower rho : ℝ) * (2 - 4 * rho.1.re)
  have ha : a < 0 := pairedEtaCoprimeScalePower_firstMean_rate_neg rho hrho
  have hp : Tendsto (fun v ↦ (pairedEtaOddSieveModulus v : ℝ) ^ a) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp pairedEtaOddSieveModulus_tendsto_atTop)
  have hb : ∀ᶠ v in atTop, ‖pairedEtaMoebiusCoprimeCompleteQuarticFirstMean rho
      (pairedEtaOddSieveModulus v) (pairedEtaCoprimeScale rho v) - pairedEtaCompletedMoebiusSource rho‖ ≤
        (pairedEtaCompletedMoebiusTermConstant rho + pairedEtaMoebiusFirstMeanConstant rho) *
          (pairedEtaOddSieveModulus v : ℝ) ^ a := by
    filter_upwards [(pairedEtaCoprimeScale_tendsto_atTop rho).eventually (eventually_ge_atTop 2)] with v hv
    apply (norm_pairedEtaMoebiusCoprimeCompleteQuarticFirstMean_sub_source_le rho
      (pairedEtaOddSieveModulus_pos v) (pairedEtaOddSieveModulus_odd v) hv
      (pairedEtaOddSieveModulus_dvd_scale rho v)).trans_eq
    have hP : (0 : ℝ) < pairedEtaOddSieveModulus v := by exact_mod_cast pairedEtaOddSieveModulus_pos v
    dsimp only [a, pairedEtaCoprimeScale]
    simp only [Nat.cast_pow]
    rw [Real.rpow_add hP, Real.rpow_ofNat, Real.rpow_natCast_mul hP.le]
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) hb
  simpa only [mul_zero] using hp.const_mul
    (pairedEtaCompletedMoebiusTermConstant rho + pairedEtaMoebiusFirstMeanConstant rho)

end

end RiemannGaussian
