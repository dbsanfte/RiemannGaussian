import RiemannGaussian.EtaGammaDivisorTail
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Finite localization of the original gamma-smoothed high carrier

A summable physical dominator connects the full damped Möbius divisor
series to the original two-endpoint source. A logarithmic upper cutoff
then leaves a finite arithmetic band with an explicit vanishing tail
allowance. On the sixth/fifth-power schedule both removed ranges are
controlled and the finite band retains the nonzero source. An independent
upper bound below that source at a hypothetical right-half zero is open.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology Interval ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaGammaSmoothing

noncomputable section

private theorem original_selected_eq_min (rho : NontrivialZetaZero) (D M : ℕ) :
    pairedEtaCompletedMoebiusSelectedAggregate rho (Finset.Icc 1 D) M =
      pairedEtaCompletedMoebiusSelectedAggregate rho (Finset.Icc 1 (min D M)) M := by
  unfold pairedEtaCompletedMoebiusSelectedAggregate
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right (min_le_left D M))
  intro d hd hnot
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdD := (Finset.mem_Icc.mp hd).2
  have hdM : M < d := by
    simp only [Finset.mem_Icc, le_min_iff] at hnot
    omega
  rw [pairedEtaCompletedMoebiusTerm_eq_completed_prefix, Nat.div_eq_of_lt hdM]
  simp [pairedEtaUnpairedDirichletPrefix]

private theorem norm_original_selected_le (rho : NontrivialZetaZero) (D M : ℕ) :
    ‖pairedEtaCompletedMoebiusSelectedAggregate rho (Finset.Icc 1 D) M‖ ≤
      pairedEtaCompletedMoebiusTermConstant rho * M := by
  have hC := (pairedEtaCompletedMoebiusTermConstant_pos rho).le
  rw [original_selected_eq_min, pairedEtaCompletedMoebiusSelectedAggregate]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 (min D M), pairedEtaCompletedMoebiusTermConstant rho := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd1, hdm⟩ := Finset.mem_Icc.mp hd
      have hdM := hdm.trans (min_le_right D M)
      apply (norm_pairedEtaCompletedMoebiusTerm_le rho (Finset.mem_Icc.mpr ⟨hd1, hdM⟩)).trans
      exact mul_le_of_le_one_right hC
        (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1.trans hdM)
          (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le))
    _ ≤ _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [mul_comm _ (pairedEtaCompletedMoebiusTermConstant rho)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right D M) hC

private theorem summable_nat_mul_exp {x : ℝ} (hx : 0 < x) :
    Summable (fun M : ℕ ↦ (M : ℝ) * Real.exp (-(M : ℝ) * x)) := by
  have hq : ‖Real.exp (-x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  simpa only [pow_one, ← Real.exp_nat_mul, mul_neg, neg_mul] using
    summable_pow_mul_geometric_of_norm_lt_one 1 hq

/-- Increasing the divisor cutoff recovers the exact physical source under a proved summable dominator. -/
theorem gammaMoebiusSelected_tendsto_source (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun D : ℕ ↦ gammaMoebiusSelected rho (Finset.Icc 1 D) A)
      atTop (𝓝 (gammaMoebiusSource rho A)) := by
  let w : ℕ → ℝ := gammaPhysicalWeight A⁻¹
  let C : ℝ := pairedEtaCompletedMoebiusTermConstant rho
  let f : ℕ → ℕ → ℂ := fun D M ↦ (w M : ℂ) *
    pairedEtaCompletedMoebiusSelectedAggregate rho (Finset.Icc 1 D) M
  let g : ℕ → ℂ := fun M ↦ (w M : ℂ) * pairedEtaCompletedMoebiusTailAggregate rho M
  have hA0 : 0 < A⁻¹ := inv_pos.mpr hA
  have hsum : Summable (fun M : ℕ ↦ (4 * C) *
      ((M : ℝ) * Real.exp (-(M : ℝ) * (A⁻¹ / 2)))) :=
    (summable_nat_mul_exp (by positivity : 0 < A⁻¹ / 2)).mul_left _
  have hpoint (M : ℕ) : Tendsto (fun D ↦ f D M) atTop (𝓝 (g M)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop M] with D hD
    dsimp only [f, g]
    rw [original_selected_eq_min, min_eq_right hD]
    congr 1
  have hbound : ∀ᶠ D : ℕ in atTop, ∀ M, ‖f D M‖ ≤
      (4 * C) * ((M : ℝ) * Real.exp (-(M : ℝ) * (A⁻¹ / 2))) := by
    apply Eventually.of_forall
    intro D M
    have hw := (gammaPhysicalWeight_bounds hA0.le M).1
    have hwe := (gammaPhysicalWeight_bounds hA0.le M).2.trans
      (gammaSurvival_le_exp_half (by positivity))
    dsimp only [f, w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left (norm_original_selected_le rho D M) hw).trans
    apply (mul_le_mul_of_nonneg_right hwe
      (mul_nonneg (pairedEtaCompletedMoebiusTermConstant_pos rho).le (Nat.cast_nonneg M))).trans_eq
    dsimp only [C]
    rw [show -((M : ℝ) * A⁻¹) / 2 = -(M : ℝ) * (A⁻¹ / 2) by ring]
    ring
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have hf (D : ℕ) : (∑' M, f D M) = gammaMoebiusSelected rho (Finset.Icc 1 D) A :=
    (hasSum_gammaPhysicalWeight_moebiusSelected rho hA (fun _ hd ↦ (Finset.mem_Icc.mp hd).1)).tsum_eq
  have hg : (∑' M, g M) = gammaMoebiusSource rho A :=
    (hasSum_gammaPhysicalWeight_moebiusSource rho hA).tsum_eq
  simpa only [hf, hg] using hlim

private theorem sum_gammaMoebiusTerm_range (rho : NontrivialZetaZero) (A : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, gammaMoebiusTerm rho A (n + 1)) =
      gammaMoebiusSelected rho (Finset.Icc 1 N) A := by
  rw [gammaMoebiusSelected, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

/-- The complete absolutely convergent damped Möbius divisor series has the original two-endpoint source. -/
theorem hasSum_gammaMoebiusTerm (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) :
    HasSum (fun n : ℕ ↦ gammaMoebiusTerm rho A (n + 1)) (gammaMoebiusSource rho A) := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm (summable_norm_gammaMoebiusTerm rho hA)).mpr
  simpa only [sum_gammaMoebiusTerm_range] using gammaMoebiusSelected_tendsto_source rho hA

/-- Removing a finite divisor prefix retains the full remaining source exactly. -/
theorem hasSum_gammaMoebiusTerm_tail (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A) (R : ℕ) :
    HasSum (fun n : ℕ ↦ gammaMoebiusTerm rho A (R + n + 1))
      (gammaMoebiusSource rho A - gammaMoebiusSelected rho (Finset.Icc 1 R) A) := by
  have h := (hasSum_nat_add_iff' R).mpr (hasSum_gammaMoebiusTerm rho hA)
  simpa only [sum_gammaMoebiusTerm_range, Nat.add_comm _ R] using h

/-- The finite divisor prefix approximates the exact source with the complete exponential tail allowance. -/
theorem norm_gammaMoebiusSource_sub_selected_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {R : ℕ} (hR : 2 * A ≤ R) :
    ‖gammaMoebiusSource rho A - gammaMoebiusSelected rho (Finset.Icc 1 R) A‖ ≤
      16 * ‖pairedEtaXiCompletionFactor rho.1‖ * A * (R : ℝ) ^ (-rho.1.re) *
        Real.exp (-(R : ℝ) / (2 * A)) := by
  rw [← (hasSum_gammaMoebiusTerm_tail rho hA R).tsum_eq]
  exact norm_tsum_gammaMoebiusTerm_tail_le rho hA hR

/-- The entire original high-divisor physical average is the actual infinite damped Möbius tail. -/
theorem tsum_gammaPhysicalWeight_large_eq_gammaMoebiusTail (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) (D : ℕ) :
    (∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D) =
      ∑' n : ℕ, gammaMoebiusTerm rho A (D + n + 1) := by
  rw [(hasSum_gammaPhysicalWeight_moebiusLarge rho hA D).tsum_eq,
    (hasSum_gammaMoebiusTerm_tail rho hA D).tsum_eq]

/-- A finite divisor band is the exact difference of its two original damped prefixes. -/
theorem gammaMoebiusSelected_Ioc_eq_sub (rho : NontrivialZetaZero) (A : ℝ)
    {D R : ℕ} (hDR : D ≤ R) :
    gammaMoebiusSelected rho (Finset.Ioc D R) A =
      gammaMoebiusSelected rho (Finset.Icc 1 R) A - gammaMoebiusSelected rho (Finset.Icc 1 D) A := by
  have hd : Disjoint (Finset.Icc 1 D) (Finset.Ioc D R) := by
    apply Finset.disjoint_left.mpr
    intro d hl hh
    have := Finset.mem_Icc.mp hl
    have := Finset.mem_Ioc.mp hh
    omega
  have hu : Finset.Icc 1 D ∪ Finset.Ioc D R = Finset.Icc 1 R := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have he : gammaMoebiusSelected rho (Finset.Icc 1 D) A +
      gammaMoebiusSelected rho (Finset.Ioc D R) A = gammaMoebiusSelected rho (Finset.Icc 1 R) A := by
    rw [gammaMoebiusSelected, gammaMoebiusSelected, ← Finset.sum_union hd, hu]
    rfl
  exact eq_sub_of_add_eq' he

/-- Finite localization of the original signed high average loses exactly its upper damped divisor tail. -/
theorem gammaPhysicalHigh_sub_band_eq_tail (rho : NontrivialZetaZero) {A : ℝ} (hA : 0 < A)
    {D R : ℕ} (hDR : D ≤ R) :
    (∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D) -
      gammaMoebiusSelected rho (Finset.Ioc D R) A =
        ∑' n : ℕ, gammaMoebiusTerm rho A (R + n + 1) := by
  rw [(hasSum_gammaPhysicalWeight_moebiusLarge rho hA D).tsum_eq,
    gammaMoebiusSelected_Ioc_eq_sub rho A hDR, (hasSum_gammaMoebiusTerm_tail rho hA R).tsum_eq]
  ring

/-- The original high average is controlled by a finite arithmetic band plus the explicit infinite-tail error. -/
theorem norm_gammaPhysicalHigh_sub_band_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 0 < A) {D R : ℕ} (hDR : D ≤ R) (hR : 2 * A ≤ R) :
    ‖(∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D) -
      gammaMoebiusSelected rho (Finset.Ioc D R) A‖ ≤
        16 * ‖pairedEtaXiCompletionFactor rho.1‖ * A * (R : ℝ) ^ (-rho.1.re) *
          Real.exp (-(R : ℝ) / (2 * A)) := by
  rw [gammaPhysicalHigh_sub_band_eq_tail rho hA hDR]
  exact norm_tsum_gammaMoebiusTerm_tail_le rho hA hR

/-- A logarithmic upper divisor cutoff keeps the omitted arithmetic tail small. -/
def gammaDivisorCutoff (A : ℝ) : ℕ := ⌈2 * A * (1 + 2 * Real.log A)⌉₊

/-- The literal rounded cutoff satisfies both inequalities required by the exponential tail estimate. -/
theorem gammaDivisorCutoff_bounds {A : ℝ} (hA : 1 ≤ A) :
    2 * A ≤ gammaDivisorCutoff A ∧ 4 * A * Real.log A ≤ gammaDivisorCutoff A := by
  have hc : 2 * A * (1 + 2 * Real.log A) ≤ gammaDivisorCutoff A := Nat.le_ceil _
  have hlog := Real.log_nonneg hA
  constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ A) hlog]

/-- Logarithmic localization has an explicit inverse-scale error, retaining the divisor decay as well. -/
theorem norm_tsum_gammaMoebiusTerm_log_tail_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 1 ≤ A) :
    ‖∑' n : ℕ, gammaMoebiusTerm rho A (gammaDivisorCutoff A + n + 1)‖ ≤
      (16 * ‖pairedEtaXiCompletionFactor rho.1‖ / A) *
        (gammaDivisorCutoff A : ℝ) ^ (-rho.1.re) := by
  have hA0 : 0 < A := by linarith
  obtain ⟨hR, hRlog⟩ := gammaDivisorCutoff_bounds hA
  have hratio : 2 * Real.log A ≤ (gammaDivisorCutoff A : ℝ) / (2 * A) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have he : Real.exp (-(gammaDivisorCutoff A : ℝ) / (2 * A)) ≤ (A ^ 2)⁻¹ := by
    calc
      _ ≤ Real.exp (-(2 * Real.log A)) := by
        rw [neg_div]
        exact Real.exp_le_exp.mpr (neg_le_neg hratio)
      _ = _ := by
        rw [show -(2 * Real.log A) = -(Real.log A + Real.log A) by ring,
          Real.exp_neg, Real.exp_add, Real.exp_log hA0, pow_two]
  apply (norm_tsum_gammaMoebiusTerm_tail_le rho hA0 hR).trans
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
  field_simp

/-- The whole original high-divisor average is approximated by a finite logarithmic band with cost at most `16 norm(chi)/A`. -/
theorem norm_gammaPhysicalHigh_sub_logBand_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 1 ≤ A) {D : ℕ} (hD : D ≤ gammaDivisorCutoff A) :
    ‖(∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D) -
      gammaMoebiusSelected rho (Finset.Ioc D (gammaDivisorCutoff A)) A‖ ≤
        16 * ‖pairedEtaXiCompletionFactor rho.1‖ / A := by
  rw [gammaPhysicalHigh_sub_band_eq_tail rho (by linarith : 0 < A) hD]
  apply (norm_tsum_gammaMoebiusTerm_log_tail_le rho hA).trans
  apply mul_le_of_le_one_right (by positivity)
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · have hR := (gammaDivisorCutoff_bounds hA).1
    linarith
  · exact neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le

/-- The finite logarithmic band retains the nonzero source up to the paid low, high, and physical-endpoint errors. -/
theorem norm_gammaMoebiusLogBand_sub_source_le (rho : NontrivialZetaZero)
    {A : ℝ} (hA : 1 ≤ A) {D : ℕ} (hD : D ≤ gammaDivisorCutoff A) :
    ‖gammaMoebiusSelected rho (Finset.Ioc D (gammaDivisorCutoff A)) A -
        pairedEtaCompletedMoebiusSource rho‖ ≤
      gammaMoebiusConstant rho / A ^ 3 * (D : ℝ) ^ (4 - rho.1.re) +
        16 * ‖pairedEtaXiCompletionFactor rho.1‖ / A +
          ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / (6 * A ^ 3) := by
  let H : ℂ := ∑' M : ℕ, (gammaPhysicalWeight A⁻¹ M : ℂ) * pairedEtaCompletedMoebiusLargeAggregate rho M D
  let B : ℂ := gammaMoebiusSelected rho (Finset.Ioc D (gammaDivisorCutoff A)) A
  have hA0 : 0 < A := by linarith
  have hH : H = gammaMoebiusSource rho A - gammaMoebiusSelected rho (Finset.Icc 1 D) A :=
    (hasSum_gammaPhysicalWeight_moebiusLarge rho hA0 D).tsum_eq
  have he : B - pairedEtaCompletedMoebiusSource rho =
      (B - H) - gammaMoebiusSelected rho (Finset.Icc 1 D) A +
        (gammaMoebiusSource rho A - pairedEtaCompletedMoebiusSource rho) := by rw [hH]; ring
  change ‖B - pairedEtaCompletedMoebiusSource rho‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le (B - H) (gammaMoebiusSelected rho (Finset.Icc 1 D) A))
    (le_refl ‖gammaMoebiusSource rho A - pairedEtaCompletedMoebiusSource rho‖)).trans
  have hb : ‖B - H‖ ≤ 16 * ‖pairedEtaXiCompletionFactor rho.1‖ / A := by
    rw [norm_sub_rev]
    exact norm_gammaPhysicalHigh_sub_logBand_le rho hA hD
  have hl := norm_gammaMoebiusSelected_le rho hA0 (Finset.Subset.refl (Finset.Icc 1 D))
  have hs := norm_gammaMoebiusSource_sub_le rho hA0
  linarith

/-- The actual finite arithmetic band left on the sixth/fifth-power schedule. -/
def gammaMoebiusSixthBand (rho : NontrivialZetaZero) (u : ℕ) : ℂ :=
  gammaMoebiusSelected rho (Finset.Ioc (u ^ 5) (gammaDivisorCutoff ((u : ℝ) ^ 6))) ((u : ℝ) ^ 6)

private theorem sixth_band_admissible {u : ℕ} (hu : 1 ≤ u) :
    1 ≤ (u : ℝ) ^ 6 ∧ u ^ 5 ≤ gammaDivisorCutoff ((u : ℝ) ^ 6) := by
  have hA : 1 ≤ (u : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast hu)
  refine ⟨hA, ?_⟩
  have h56 : ((u ^ 5 : ℕ) : ℝ) ≤ (u : ℝ) ^ 6 := by
    exact_mod_cast Nat.pow_le_pow_right hu (by decide : 5 ≤ 6)
  have hR := (gammaDivisorCutoff_bounds hA).1
  exact_mod_cast h56.trans (by linarith : (u : ℝ) ^ 6 ≤ gammaDivisorCutoff ((u : ℝ) ^ 6))

/-- Both removed divisor ranges and both original source endpoints have explicit allowances at every positive schedule index. -/
theorem norm_gammaMoebiusSixthBand_sub_source_le (rho : NontrivialZetaZero)
    {u : ℕ} (hu : 1 ≤ u) :
    ‖gammaMoebiusSixthBand rho u - pairedEtaCompletedMoebiusSource rho‖ ≤
      gammaMoebiusConstant rho * (u : ℝ) ^ (2 - 5 * rho.1.re) +
        16 * ‖pairedEtaXiCompletionFactor rho.1‖ / (u : ℝ) ^ 6 +
          ‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) /
            (6 * ((u : ℝ) ^ 6) ^ 3) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  obtain ⟨hA, hD⟩ := sixth_band_admissible hu
  have h := norm_gammaMoebiusLogBand_sub_source_le rho hA hD
  have he : gammaMoebiusConstant rho / ((u : ℝ) ^ 6) ^ 3 *
      ((u ^ 5 : ℕ) : ℝ) ^ (4 - rho.1.re) =
        gammaMoebiusConstant rho * (u : ℝ) ^ (2 - 5 * rho.1.re) := by
    simp only [Nat.cast_pow]
    rw [← Real.rpow_natCast_mul huR.le, ← pow_mul,
      ← Real.rpow_natCast (u : ℝ) (6 * 3), div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub huR]
    congr 2
    norm_num
    ring
  simpa only [he, gammaMoebiusSixthBand] using h

/-- The finite band still tends to the nonzero source for `Re(rho)>2/5`; localization alone is not an upper bound below that source. -/
theorem gammaMoebiusSixthBand_tendsto_source (rho : NontrivialZetaZero)
    (hrho : (2 : ℝ) / 5 < rho.1.re) :
    Tendsto (gammaMoebiusSixthBand rho) atTop (𝓝 (pairedEtaCompletedMoebiusSource rho)) := by
  have hinv : Tendsto (fun u : ℕ ↦ (u : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp : Tendsto (fun u : ℕ ↦ (u : ℝ) ^ (2 - 5 * rho.1.re)) atTop (𝓝 0) := by
    convert! (tendsto_rpow_neg_atTop (by linarith : 0 < 5 * rho.1.re - 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    ext u
    simp only [Function.comp_apply]
    congr 1
    ring
  have h6 : Tendsto (fun u : ℕ ↦ 16 * ‖pairedEtaXiCompletionFactor rho.1‖ / (u : ℝ) ^ 6)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 6 ≠ 0), mul_zero] using
      (hinv.pow 6).const_mul (16 * ‖pairedEtaXiCompletionFactor rho.1‖)
  have h18 : Tendsto (fun u : ℕ ↦ ‖pairedEtaXiCompletionFactor rho.1‖ *
      (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / (6 * ((u : ℝ) ^ 6) ^ 3)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_inv, inv_pow, mul_assoc,
      zero_pow (by decide : 6 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero] using
      ((hinv.pow 6).pow 3).const_mul
        (‖pairedEtaXiCompletionFactor rho.1‖ * (1 + 16 * (2 : ℝ) ^ (-rho.1.re)) / 6)
  have herr := ((hp.const_mul (gammaMoebiusConstant rho)).add h6).add h18
  simp only [mul_zero, zero_add] at herr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    ((eventually_ge_atTop 1).mono fun _ hu ↦ norm_gammaMoebiusSixthBand_sub_source_le rho hu) herr

end

end RiemannGaussian.EtaGammaSmoothing
