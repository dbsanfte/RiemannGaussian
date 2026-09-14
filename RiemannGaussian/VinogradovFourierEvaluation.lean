/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProductEnergy

/-!
# Exact frequency fibres and the cost of sampling torus energy

A finite Fourier polynomial keeps the full complex weight sum on each
joint frequency fibre. Orthogonality identifies its energy with the sum
of the squared fibre weights, including their cross terms. Point evaluation
costs at most the number of frequencies attained by nonzero original terms;
no rectangular padding or coordinate projection is required.

This is the finite sampling interface for applying conditioned mean-value
bounds to a distinguished arithmetic phase. It does not supply moment decay.
-/

namespace RiemannGaussian.VinogradovFourierEvaluation
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus VinogradovPartitionEnergy VinogradovShiftedMoment

/-- Use the normalized Haar measure of the original Fourier identities. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The full complex coefficient on one joint frequency fibre. -/
def frequencyWeight {ι d : Type*} [Fintype ι] (v : ι → d → ℤ) (w : ι → ℂ) (c : d → ℤ) : ℂ :=
  ∑ i, if v i = c then w i else 0

/-- Only joint frequencies attained by nonzero original terms are counted. -/
def activeSupport {ι d : Type*} [Fintype ι] (v : ι → d → ℤ) (w : ι → ℂ) : Finset (d → ℤ) :=
  (Finset.univ.filter (fun i => w i ≠ 0)).image v

/-- Group the exact complex polynomial by full frequency fibres, preserving all cross terms. -/
theorem polynomial_eq_frequency_sum {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (S : Finset (d → ℤ))
    (hs : ∀ i, w i ≠ 0 → v i ∈ S) (theta : UnitAddTorus d) :
    polynomial v w theta = ∑ c ∈ S, frequencyWeight v w c * mFourier c theta := by
  unfold polynomial frequencyWeight
  symm
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : w i = 0
  · simp [hw]
  · rw [Finset.sum_eq_single (v i)]
    · simp
    · intro c hc hne
      simp [Ne.symm hne]
    · exact fun h => False.elim (h (hs i hw))

/-- Distinct joint frequencies are orthogonal for normalized Haar measure. -/
theorem integral_energy_of_injective {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (hv : Function.Injective v) (w : ι → ℂ) :
    (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) = ∑ i, ‖w i‖ ^ 2 := by
  have he := congrArg Complex.re (weightedShift_zero v w)
  simp only [Complex.ofReal_re] at he
  unfold polynomial
  rw [← he]
  simp [weightedShift, hv.eq_iff, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    -Complex.ofReal_pow]

/-- The exact energy is the sum of squared full complex fibre weights. -/
theorem integral_energy_eq_frequency_weights {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (S : Finset (d → ℤ))
    (hs : ∀ i, w i ≠ 0 → v i ∈ S) :
    (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) =
      ∑ c ∈ S, ‖frequencyWeight v w c‖ ^ 2 := by
  have hp (theta : UnitAddTorus d) : polynomial v w theta =
      polynomial (fun c : S => c.val) (fun c : S => frequencyWeight v w c.val) theta := by
    rw [polynomial_eq_frequency_sum v w S hs theta]
    exact (Finset.sum_coe_sort S (fun c => frequencyWeight v w c * mFourier c theta)).symm
  simp_rw [hp]
  rw [integral_energy_of_injective _ Subtype.val_injective]
  exact Finset.sum_coe_sort S (fun c => ‖frequencyWeight v w c‖ ^ 2)

/-- Point evaluation is bounded by the actual frequency count times the full torus energy. -/
theorem sample_energy_le {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (S : Finset (d → ℤ))
    (hs : ∀ i, w i ≠ 0 → v i ∈ S) (theta : UnitAddTorus d) :
    ‖polynomial v w theta‖ ^ 2 ≤ (S.card : ℝ) *
      ∫ phi : UnitAddTorus d, ‖polynomial v w phi‖ ^ 2 := by
  rw [polynomial_eq_frequency_sum v w S hs theta, integral_energy_eq_frequency_weights v w S hs]
  simpa only [norm_mul, norm_mFourier_apply, mul_one] using
    VinogradovCongruenceEnergy.sum_energy_le_card_mul S (fun c => frequencyWeight v w c * mFourier c theta)

/-- The sampling bound pays only frequencies attained by nonzero original weights. -/
theorem active_sample_energy_le {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (theta : UnitAddTorus d) :
    ‖polynomial v w theta‖ ^ 2 ≤ ((activeSupport v w).card : ℝ) *
      ∫ phi : UnitAddTorus d, ‖polynomial v w phi‖ ^ 2 := by
  apply sample_energy_le v w (activeSupport v w) _ theta
  intro i hi
  unfold activeSupport
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨i, hi, rfl⟩

end
end RiemannGaussian.VinogradovFourierEvaluation
