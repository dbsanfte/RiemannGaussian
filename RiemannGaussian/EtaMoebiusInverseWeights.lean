import RiemannGaussian.EtaMoebiusParityInverse

/-!
# The explicit weight cost of reconstructing the original eta moments

The exact inverse is kept upstream. Taking norms term by term incurs the
sum of the original complex divisor-weight norms. That sum has a positive
power lower bound at every actual zero. Thus a uniform bound on the parity
aggregates does not give a uniform bound through this triangle estimate;
the inverse weights still require cancellation.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The absolute mass of the literal inverse divisor weights. -/
def pairedEtaOddInverseWeightMass (rho : NontrivialZetaZero) (M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter Odd, ‖(d : ℂ) ^ (-rho.1)‖

/-- The inverse weight mass is nonnegative. -/
theorem pairedEtaOddInverseWeightMass_nonneg (rho : NontrivialZetaZero) (M : ℕ) :
    0 ≤ pairedEtaOddInverseWeightMass rho M :=
  Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)

/-- The exact norm cost of substituting the complete odd-aggregate bound
into the original completed prefix reconstruction. -/
theorem norm_completed_pairedEtaUnpairedDirichletPrefix_le_oddInverseWeightMass
    (rho : NontrivialZetaZero) (M : ℕ) :
    ‖pairedEtaXiCompletionFactor rho.1 * pairedEtaUnpairedDirichletPrefix M rho.1‖ ≤
      pairedEtaCompletedMoebiusParityConstant rho * pairedEtaOddInverseWeightMass rho M := by
  rw [← sum_pairedEtaCompletedOddInverseTerm]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 M).filter Odd, ‖pairedEtaCompletedOddInverseTerm rho M d‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 M).filter Odd,
        ‖(d : ℂ) ^ (-rho.1)‖ * pairedEtaCompletedMoebiusParityConstant rho := by
      apply Finset.sum_le_sum
      intro d hd
      rw [pairedEtaCompletedOddInverseTerm, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_pairedEtaCompletedMoebiusOddAggregate_le rho (M / d))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

/-- The exact number of positive odd divisor indices at a physical cutoff. -/
theorem card_odd_Icc (M : ℕ) : ((Finset.Icc 1 M).filter Odd).card = (M + 1) / 2 := by
  rw [← Finset.card_range ((M + 1) / 2)]
  apply Finset.card_bij (fun d _ ↦ d / 2)
  · intro d hd
    obtain ⟨hdM, hdo⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp hdM
    have hmod := Nat.odd_iff.mp hdo
    apply Finset.mem_range.mpr
    omega
  · intro a ha b hb hab
    have hma := Nat.odd_iff.mp (Finset.mem_filter.mp ha).2
    have hmb := Nat.odd_iff.mp (Finset.mem_filter.mp hb).2
    omega
  · intro k hk
    have hkp := Finset.mem_range.mp hk
    refine ⟨2 * k + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      by exact Nat.odd_iff.mpr (by omega)⟩, by omega⟩

/-- The inverse weight mass grows at least as half the positive power
`M^(1-Re rho)`. Every actual divisor weight is included in this lower bound. -/
theorem pairedEtaOddInverseWeightMass_lower (rho : NontrivialZetaZero)
    {M : ℕ} (hM : 1 ≤ M) :
    (M : ℝ) ^ (1 - rho.1.re) / 2 ≤ pairedEtaOddInverseWeightMass rho M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hcard : (M : ℝ) / 2 ≤ ((M + 1) / 2 : ℕ) := by
    have hn : M ≤ 2 * ((M + 1) / 2) := by omega
    have hr : (M : ℝ) ≤ 2 * (((M + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  calc
    _ = ((M : ℝ) / 2) * (M : ℝ) ^ (-rho.1.re) := by
      rw [show 1 - rho.1.re = 1 + (-rho.1.re) by ring, Real.rpow_add hMp, Real.rpow_one]
      ring
    _ ≤ (((M + 1) / 2 : ℕ) : ℝ) * (M : ℝ) ^ (-rho.1.re) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hMp.le _)
    _ = ∑ _d ∈ (Finset.Icc 1 M).filter Odd, (M : ℝ) ^ (-rho.1.re) := by
      simp only [Finset.sum_const, nsmul_eq_mul, card_odd_Icc]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdp, hdM⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
      rw [Complex.norm_natCast_cpow_of_pos hdp, Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos hdR (by exact_mod_cast hdM) (neg_nonpos.mpr hs.le)

/-- The absolute inverse-weight mass diverges for every actual zero,
including zeros on the critical line. This diagnoses the loss in the
termwise triangle estimate, not divergence of the original signed current. -/
theorem pairedEtaOddInverseWeightMass_tendsto_atTop (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaOddInverseWeightMass rho) atTop atTop := by
  have hpow := ((tendsto_rpow_atTop (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho))).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  apply tendsto_atTop_mono' atTop _ hpow
  exact (eventually_ge_atTop 1).mono fun M hM ↦ by
    simpa only [Function.comp_apply, one_div, inv_mul_eq_div] using
      pairedEtaOddInverseWeightMass_lower rho hM

/-- A matching positive-power upper estimate for the inverse weight
mass, using the checked finite integral comparison, with explicit
dependence on the cutoff. -/
theorem pairedEtaOddInverseWeightMass_upper (rho : NontrivialZetaZero) (M : ℕ) :
    pairedEtaOddInverseWeightMass rho M ≤ (M + 1 : ℝ) ^ (1 - rho.1.re) / (1 - rho.1.re) := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 M, ‖(d : ℂ) ^ (-rho.1)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ norm_nonneg _)
    _ = ∑ d ∈ Finset.Icc 1 M, (d : ℝ) ^ (-rho.1.re) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Complex.norm_natCast_cpow_of_pos (Finset.mem_Icc.mp hd).1, Complex.neg_re]
    _ = ∑ n ∈ Finset.range M, (n + 1 : ℝ) ^ (-rho.1.re) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm 1]
    _ ≤ _ := by
      simpa only [neg_add_eq_sub] using sum_range_nat_add_one_rpow_le
        (by linarith [NontrivialZetaZero.re_lt_one rho] : -1 < -rho.1.re) (neg_nonpos.mpr hs.le) M

end

end RiemannGaussian
