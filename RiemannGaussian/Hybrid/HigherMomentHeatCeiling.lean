import RiemannGaussian.Hybrid.HigherMomentCeiling

/-!
# Continuous heat refinement of the sharp degree-four certificate

The degree-four witness can be retained through positive heat time instead of
being collapsed immediately at scale zero.  For a moment model `M`, define

`W_M(u) = sum_i w_i p(x_i)^2 exp(-u x_i^2)`,

where `p(x)=1-(7/4)x+(2/3)x^2` is the sharp quadratic witness.  Lean proves
that `W_M(u)` is exactly a fixed signed linear combination of the five
simultaneous heat moments of orders zero through four.

For every nonnegative heat scale, `1-2 W_M(u)` lies between the static
`13/18` certificate and the exact model certificate.  It is monotone in heat
time and converges to the exact certificate as `u` tends to infinity.  Thus
the continuous carrier really is an information-preserving refinement.

However, the explicit sharp three-atom model has `W_M(u)=5/36` at every
nonnegative scale: its two nonzero atoms are roots of `p`.  Consequently this
entire witness-damped heat family remains stuck at `13/18` on the adversarial
model.  Beating that ceiling requires an observable not annihilated by those
two root channels.  This is an abstract method-ceiling theorem, not an eta or
zeta-zero result.
-/

open Finset Filter Topology
open scoped BigOperators Classical

namespace RiemannGaussian

noncomputable section

/-! ## The witness-weighted heat carrier -/

/-- The quadratic-witness mass retained at heat scale `u`. -/
def DegreeFourMomentModel.witnessHeat
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) : ℝ :=
  ∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
    Real.exp (-u * M.node i ^ 2)

/-- The corresponding scale-dependent lower certificate. -/
def DegreeFourMomentModel.heatCertificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) : ℝ :=
  1 - 2 * M.witnessHeat u

/-- The witness heat is a fixed signed linear combination of the five
simultaneous heat moments.  No moment order or heat scale is discarded. -/
theorem DegreeFourMomentModel.witnessHeat_eq_heatMomentCombination
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    M.witnessHeat u =
      M.heatMoment 0 u - (7 / 2 : ℝ) * M.heatMoment 1 u +
        (211 / 48 : ℝ) * M.heatMoment 2 u -
        (7 / 3 : ℝ) * M.heatMoment 3 u +
        (4 / 9 : ℝ) * M.heatMoment 4 u := by
  unfold DegreeFourMomentModel.witnessHeat
    DegreeFourMomentModel.heatMoment
  calc
    ∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
        Real.exp (-u * M.node i ^ 2) =
      ∑ i, (M.weight i * Real.exp (-u * M.node i ^ 2) -
        (7 / 2 : ℝ) *
          (M.weight i * M.node i * Real.exp (-u * M.node i ^ 2)) +
        (211 / 48 : ℝ) *
          (M.weight i * M.node i ^ 2 * Real.exp (-u * M.node i ^ 2)) -
        (7 / 3 : ℝ) *
          (M.weight i * M.node i ^ 3 * Real.exp (-u * M.node i ^ 2)) +
        (4 / 9 : ℝ) *
          (M.weight i * M.node i ^ 4 * Real.exp (-u * M.node i ^ 2))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold degreeFourMomentWitness
      ring
    _ =
      (∑ i, M.weight i * Real.exp (-u * M.node i ^ 2)) -
        (7 / 2 : ℝ) *
          (∑ i, M.weight i * M.node i * Real.exp (-u * M.node i ^ 2)) +
        (211 / 48 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 2 *
            Real.exp (-u * M.node i ^ 2)) -
        (7 / 3 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 3 *
            Real.exp (-u * M.node i ^ 2)) +
        (4 / 9 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 4 *
            Real.exp (-u * M.node i ^ 2)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ =
      (∑ i, M.weight i * M.node i ^ 0 *
          Real.exp (-u * M.node i ^ 2)) -
        (7 / 2 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 1 *
            Real.exp (-u * M.node i ^ 2)) +
        (211 / 48 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 2 *
            Real.exp (-u * M.node i ^ 2)) -
        (7 / 3 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 3 *
            Real.exp (-u * M.node i ^ 2)) +
        (4 / 9 : ℝ) *
          (∑ i, M.weight i * M.node i ^ 4 *
            Real.exp (-u * M.node i ^ 2)) := by simp

/-- At zero heat scale, the witness carrier is exactly `5/36`. -/
@[simp] theorem DegreeFourMomentModel.witnessHeat_zero
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    M.witnessHeat 0 = (5 : ℝ) / 36 := by
  unfold DegreeFourMomentModel.witnessHeat
  simpa using M.sum_weight_mul_witness_sq_eq

/-- The witness heat is nonnegative at every real scale. -/
theorem DegreeFourMomentModel.witnessHeat_nonneg
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    0 ≤ M.witnessHeat u := by
  unfold DegreeFourMomentModel.witnessHeat
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (M.weight_nonneg i)
      (sq_nonneg (degreeFourMomentWitness (M.node i))))
    (Real.exp_pos _).le

/-- The zero-atom mass is bounded by every witness-heat observation. -/
theorem DegreeFourMomentModel.zeroMass_le_witnessHeat
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    M.zeroMass ≤ M.witnessHeat u := by
  unfold DegreeFourMomentModel.zeroMass
    DegreeFourMomentModel.witnessHeat
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hi : M.node i = 0
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    exact mul_nonneg
      (mul_nonneg (M.weight_nonneg i)
        (sq_nonneg (degreeFourMomentWitness (M.node i))))
      (Real.exp_pos _).le

/-- Increasing heat time can only decrease the witness carrier. -/
theorem DegreeFourMomentModel.witnessHeat_le_of_le
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    {u v : ℝ} (huv : u ≤ v) :
    M.witnessHeat v ≤ M.witnessHeat u := by
  unfold DegreeFourMomentModel.witnessHeat
  apply Finset.sum_le_sum
  intro i _hi
  have hbase : 0 ≤
      M.weight i * degreeFourMomentWitness (M.node i) ^ 2 := by
    exact mul_nonneg (M.weight_nonneg i)
      (sq_nonneg (degreeFourMomentWitness (M.node i)))
  apply mul_le_mul_of_nonneg_left _ hbase
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using
    neg_le_neg (mul_le_mul_of_nonneg_right huv (sq_nonneg (M.node i)))

/-- At every nonnegative scale, the witness heat is at most its static value
`5/36`. -/
theorem DegreeFourMomentModel.witnessHeat_le_five_thirtySix
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    {u : ℝ} (hu : 0 ≤ u) :
    M.witnessHeat u ≤ (5 : ℝ) / 36 := by
  rw [← M.witnessHeat_zero]
  exact M.witnessHeat_le_of_le hu

/-! ## A monotone certificate converging to the exact answer -/

/-- Every nonnegative-scale heat certificate improves on, or equals, the
static `13/18` bound. -/
theorem DegreeFourMomentModel.thirteen_eighteen_le_heatCertificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    {u : ℝ} (hu : 0 ≤ u) :
    (13 : ℝ) / 18 ≤ M.heatCertificate u := by
  unfold DegreeFourMomentModel.heatCertificate
  linarith [M.witnessHeat_le_five_thirtySix hu]

/-- Every heat certificate remains a valid lower bound for the exact model
certificate. -/
theorem DegreeFourMomentModel.heatCertificate_le_certificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) (u : ℝ) :
    M.heatCertificate u ≤ M.certificate := by
  unfold DegreeFourMomentModel.heatCertificate
    DegreeFourMomentModel.certificate
  linarith [M.zeroMass_le_witnessHeat u]

/-- The scale-dependent certificate is monotone increasing with heat time. -/
theorem DegreeFourMomentModel.heatCertificate_le_of_le
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι)
    {u v : ℝ} (huv : u ≤ v) :
    M.heatCertificate u ≤ M.heatCertificate v := by
  unfold DegreeFourMomentModel.heatCertificate
  linarith [M.witnessHeat_le_of_le huv]

/-- The witness heat converges exactly to the zero-atom mass. -/
theorem DegreeFourMomentModel.tendsto_witnessHeat_atTop_zeroMass
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    Tendsto M.witnessHeat atTop (nhds M.zeroMass) := by
  have hsum : Tendsto
      (fun u : ℝ ↦ ∑ i,
        M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
          Real.exp (-u * M.node i ^ 2)) atTop
      (nhds (∑ i,
        M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
          (if M.node i = 0 then 1 else 0))) := by
    exact tendsto_finsetSum Finset.univ fun i _hi ↦
      (HermitianRankTrace.tendsto_scalarHeat_atTop (M.node i)).const_mul
        (M.weight i * degreeFourMomentWitness (M.node i) ^ 2)
  have hlimit :
      (∑ i, M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
        (if M.node i = 0 then 1 else 0)) = M.zeroMass := by
    unfold DegreeFourMomentModel.zeroMass
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : M.node i = 0 <;> simp [hi]
  rw [hlimit] at hsum
  change Tendsto
    (fun u : ℝ ↦ ∑ i,
      M.weight i * degreeFourMomentWitness (M.node i) ^ 2 *
        Real.exp (-u * M.node i ^ 2)) atTop (nhds M.zeroMass)
  exact hsum

/-- The monotone heat certificates converge to the exact certificate. -/
theorem DegreeFourMomentModel.tendsto_heatCertificate_atTop_certificate
    {ι : Type*} [Fintype ι] (M : DegreeFourMomentModel ι) :
    Tendsto M.heatCertificate atTop (nhds M.certificate) := by
  unfold DegreeFourMomentModel.heatCertificate
    DegreeFourMomentModel.certificate
  exact tendsto_const_nhds.sub
    (tendsto_const_nhds.mul M.tendsto_witnessHeat_atTop_zeroMass)

/-! ## The sharp adversary survives this entire heat family -/

/-- The sharp three-atom model saturates the witness-heat bound at every
nonnegative heat scale. -/
theorem degreeFourSharpModel_witnessHeat
    {u : ℝ} (hu : 0 ≤ u) :
    degreeFourSharpModel.witnessHeat u = (5 : ℝ) / 36 := by
  apply le_antisymm
  · exact degreeFourSharpModel.witnessHeat_le_five_thirtySix hu
  · rw [← degreeFourSharpModel_zeroMass]
    exact degreeFourSharpModel.zeroMass_le_witnessHeat u

/-- Consequently the full witness-damped heat certificate remains exactly
`13/18` on the sharp adversarial model at every nonnegative scale. -/
theorem degreeFourSharpModel_heatCertificate
    {u : ℝ} (hu : 0 ≤ u) :
    degreeFourSharpModel.heatCertificate u = (13 : ℝ) / 18 := by
  unfold DegreeFourMomentModel.heatCertificate
  rw [degreeFourSharpModel_witnessHeat hu]
  norm_num

end

end RiemannGaussian
