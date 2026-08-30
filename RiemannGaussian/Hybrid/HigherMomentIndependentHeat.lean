import RiemannGaussian.Hybrid.HigherMomentHeatCeiling

/-!
# An independent heat channel separating the sharp moment ceiling

Heat-damping the sharp quadratic witness does not beat `13/18`, because the
adversarial model's two nonzero atoms are roots of that witness.  This module
therefore retains an independent channel: the ordinary weighted heat trace

`H₀(u) = sum_i w_i exp(-u x_i^2)`.

The first-moment normalization forces every degree-four model to carry some
strictly positive weight away from zero.  Consequently `H₀(u)` is strictly
larger than the zero-atom mass at every finite real scale, while it converges
to that mass as `u` tends to infinity.

Lean proves the exact separator criterion:

`13/18 < certificate` if and only if there is a nonnegative heat scale with
`H₀(u) < 5/36`.

For the sharp model, `H₀(u) > 5/36` at every finite scale.  Thus an
arithmetic upper bound crossing `5/36` would be genuinely new information and
would rigorously exclude the known adversary.  No eta theorem supplying that
bound is assumed here.
-/

open Finset Filter Topology
open scoped BigOperators Classical

namespace RiemannGaussian

noncomputable section

/-! ## Strict excess of ordinary heat over the zero mass -/

/-- The ordinary heat mass carried by nonzero atoms. -/
def DegreeFourMomentModel.independentHeatExcess
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) : ℝ :=
  ∑ i, if M.node i = 0 then 0
    else M.weight i * Real.exp (-u * M.node i ^ 2)

/-- Every degree-four model has a positive-weight nonzero atom.  This follows
already from its first moment being one. -/
theorem DegreeFourMomentModel.exists_weight_pos_and_node_ne_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    ∃ i, 0 < M.weight i ∧ M.node i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hweightZero : ∀ i, M.node i ≠ 0 → M.weight i = 0 := by
    intro i hi
    apply le_antisymm
    · exact not_lt.mp fun hpos ↦ hi (h i hpos)
    · exact M.weight_nonneg i
  have hmoment : ∑ i, M.weight i * M.node i = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hi : M.node i = 0
    · simp [hi]
    · rw [hweightZero i hi]
      simp
  rw [M.moment_one] at hmoment
  norm_num at hmoment

/-- The ordinary heat trace splits exactly into its zero mass plus the
strictly positive nonzero-atom excess. -/
theorem DegreeFourMomentModel.zeroMass_add_independentHeatExcess
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    M.zeroMass + M.independentHeatExcess u = M.heatMoment 0 u := by
  unfold DegreeFourMomentModel.zeroMass
    DegreeFourMomentModel.independentHeatExcess
    DegreeFourMomentModel.heatMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : M.node i = 0 <;> simp [hi]

/-- The independent heat excess is strictly positive at every finite real
scale. -/
theorem DegreeFourMomentModel.independentHeatExcess_pos
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    0 < M.independentHeatExcess u := by
  unfold DegreeFourMomentModel.independentHeatExcess
  apply Finset.sum_pos'
  · intro i _hi
    by_cases hi : M.node i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg (M.weight_nonneg i) (Real.exp_pos _).le
  · obtain ⟨i, hweight, hnode⟩ := M.exists_weight_pos_and_node_ne_zero
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [hnode, ↓reduceIte]
    exact mul_pos hweight (Real.exp_pos _)

/-- At every finite scale, the ordinary heat trace is strictly above the
zero-atom mass. -/
theorem DegreeFourMomentModel.zeroMass_lt_heatMoment_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    M.zeroMass < M.heatMoment 0 u := by
  rw [← M.zeroMass_add_independentHeatExcess u]
  linarith [M.independentHeatExcess_pos u]

/-! ## Large heat time and the exact separator criterion -/

/-- The ordinary weighted heat trace converges to the zero-atom mass. -/
theorem DegreeFourMomentModel.tendsto_heatMoment_zero_atTop_zeroMass
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    Tendsto (M.heatMoment 0) atTop (nhds M.zeroMass) := by
  have hsum : Tendsto
      (fun u : ℝ ↦ ∑ i,
        M.weight i * Real.exp (-u * M.node i ^ 2)) atTop
      (nhds (∑ i, M.weight i *
        (if M.node i = 0 then 1 else 0))) := by
    exact tendsto_finsetSum Finset.univ fun i _hi ↦
      (HermitianRankTrace.tendsto_scalarHeat_atTop (M.node i)).const_mul
        (M.weight i)
  have hlimit :
      (∑ i, M.weight i * (if M.node i = 0 then 1 else 0)) =
        M.zeroMass := by
    unfold DegreeFourMomentModel.zeroMass
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : M.node i = 0 <;> simp [hi]
  rw [hlimit] at hsum
  change Tendsto
    (fun u : ℝ ↦ ∑ i, M.weight i * M.node i ^ 0 *
      Real.exp (-u * M.node i ^ 2)) atTop (nhds M.zeroMass)
  simpa using hsum

/-- An ordinary heat-trace upper bound at `5/36` strictly beats the static
`13/18` certificate. -/
theorem DegreeFourMomentModel.thirteen_eighteen_lt_certificate_of_heatMoment_zero_le
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    {u : ℝ} (hheat : M.heatMoment 0 u ≤ (5 : ℝ) / 36) :
    (13 : ℝ) / 18 < M.certificate := by
  unfold DegreeFourMomentModel.certificate
  linarith [M.zeroMass_lt_heatMoment_zero u]

/-- Strict improvement over `13/18` is equivalent to the existence of a
nonnegative scale at which the independent ordinary heat trace crosses below
`5/36`. -/
theorem DegreeFourMomentModel.thirteen_eighteen_lt_certificate_iff_exists_heat
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    (13 : ℝ) / 18 < M.certificate ↔
      ∃ u : ℝ, 0 ≤ u ∧ M.heatMoment 0 u < (5 : ℝ) / 36 := by
  constructor
  · intro hcertificate
    have hzeroMass : M.zeroMass < (5 : ℝ) / 36 := by
      unfold DegreeFourMomentModel.certificate at hcertificate
      linarith
    have heventually : ∀ᶠ u : ℝ in atTop,
        M.heatMoment 0 u < (5 : ℝ) / 36 :=
      M.tendsto_heatMoment_zero_atTop_zeroMass.eventually_lt_const hzeroMass
    obtain ⟨u, huHeat, hu⟩ :=
      (heventually.and (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨u, hu, huHeat⟩
  · rintro ⟨u, _hu, hheat⟩
    exact M.thirteen_eighteen_lt_certificate_of_heatMoment_zero_le hheat.le

/-! ## The sharp adversary stays on the opposite side -/

/-- The sharp model's independent ordinary heat trace is strictly above
`5/36` at every finite real scale. -/
theorem degreeFourSharpModel_five_thirtySix_lt_heatMoment_zero (u : ℝ) :
    (5 : ℝ) / 36 < degreeFourSharpModel.heatMoment 0 u := by
  rw [← degreeFourSharpModel_zeroMass]
  exact degreeFourSharpModel.zeroMass_lt_heatMoment_zero u

/-- Hence no nonnegative finite scale of the sharp model satisfies the
separator condition required to beat `13/18`. -/
theorem degreeFourSharpModel_not_exists_heatMoment_zero_lt_five_thirtySix :
    ¬ ∃ u : ℝ, 0 ≤ u ∧
      degreeFourSharpModel.heatMoment 0 u < (5 : ℝ) / 36 := by
  intro h
  obtain ⟨u, _hu, hheat⟩ := h
  linarith [degreeFourSharpModel_five_thirtySix_lt_heatMoment_zero u]

end

end RiemannGaussian
