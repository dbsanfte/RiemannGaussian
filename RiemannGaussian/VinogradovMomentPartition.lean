/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditionedCompletion
import RiemannGaussian.VinogradovCongruenceEnergy

/-!
# Exact congruence-target partition of the full weighted moment

Complete weighted moment collisions force equality of every translated
block target at its original degree-specific precision. This proves an
exact partition of the full complex Gram form and its actual torus energy.
Literal positive residue windows discharge all tail-divisibility premises.
Arbitrary finite configuration families and complex weights remain intact,
including correlations and restrictions represented by those families.

The identity holds for every nonzero base modulus; primality is needed only
by subsequent counting estimates. The full efficient-congruencing iteration
and the required Vinogradov--Korobov analytic saving are not asserted here.
-/

namespace RiemannGaussian.VinogradovMomentPartition
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus

/-- Use the same normalized circle Haar measure as the original moment theorem. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The chosen circle Haar measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Restriction keeps the original complex weight on one complete target fibre. -/
def targetWeight {ι κ : Type*} (label : ι → κ) (w : ι → ℂ) (c : κ) (i : ι) : ℂ :=
  if label i = c then w i else 0

/-- Exact target partition of the full complex homogeneous Gram form.
Only a proved collision-preserving label condition removes cross-target terms. -/
theorem weightedShift_partition {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (label : ι → κ)
    (hlabel : ∀ i j, v i = v j → label i = label j) :
    VinogradovShiftedMoment.weightedShift v w 0 =
      ∑ c : κ, VinogradovShiftedMoment.weightedShift v
        (targetWeight label w c) 0 := by
  unfold VinogradovShiftedMoment.weightedShift targetWeight
  simp only [add_zero]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hv : v i = v j
  · have hl := hlabel i j hv
    simp [hv, hl]
  · simp [hv]

/-- The full original weighted frequency of each block-and-tail configuration. -/
def mixedFrequency {ι : Type*} {k r : ℕ} (c : Fin k → ℤ) (tau : Fin r → ℤ)
    (x : ι → Fin k → ℤ) (u : ι → Fin r → ℤ) (z : ι) : Fin k → ℤ := fun i =>
  (∑ j, c j * x z j ^ (i.val + 1)) + ∑ j, tau j * u z j ^ (i.val + 1)

/-- Every translated block degree has its own original congruence precision. -/
def blockSignature {ι : Type*} {q b k : ℕ} (eta : ℤ) (c : Fin k → ℤ)
    (x : ι → Fin k → ℤ) (z : ι) : (i : Fin k) → ZMod (q ^ ((i.val + 1) * b)) :=
  fun i => ((∑ j, c j * (x z j - eta) ^ (i.val + 1) : ℤ) : ZMod (q ^ ((i.val + 1) * b)))

/-- Original full-frequency collisions force equality of every degree target;
the tail divisibilities, not an assumed orthogonality property, prove this. -/
theorem mixed_collision_signature {ι : Type*} {q b k r : ℕ} (eta : ℤ)
    (c : Fin k → ℤ) (tau : Fin r → ℤ) (x : ι → Fin k → ℤ) (u : ι → Fin r → ℤ)
    (hu : ∀ z j, (q : ℤ) ^ b ∣ u z j - eta) (z z' : ι)
    (h : mixedFrequency c tau x u z = mixedFrequency c tau x u z') :
    blockSignature (q := q) (b := b) eta c x z = blockSignature (q := q) (b := b) eta c x z' := by
  funext i
  have hd := VinogradovConditionedCompletion.conditioned_weighted_power_difference
    c (x z) (x z') tau (u z) (u z') eta (hu z) (hu z') (n := i.val + 1) (by
      intro d hd hdi
      have he := congrFun h ⟨d - 1, by omega⟩
      simpa only [mixedFrequency, Nat.sub_add_cancel hd] using he)
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (q ^ ((i.val + 1) * b))).mpr
  simpa only [Nat.cast_pow] using hd

/-- Exact decomposition of the whole weighted mixed Gram form into all
attainable degree-congruence targets, for every nonzero base modulus. -/
theorem mixed_gram_partition {ι : Type*} [Fintype ι] {q b k r : ℕ} [NeZero q]
    (eta : ℤ) (c : Fin k → ℤ) (tau : Fin r → ℤ)
    (x : ι → Fin k → ℤ) (u : ι → Fin r → ℤ) (w : ι → ℂ)
    (hu : ∀ z j, (q : ℤ) ^ b ∣ u z j - eta) :
    VinogradovShiftedMoment.weightedShift (mixedFrequency c tau x u) w 0 =
      ∑ target : (i : Fin k) → ZMod (q ^ ((i.val + 1) * b)),
        VinogradovShiftedMoment.weightedShift (mixedFrequency c tau x u)
          (targetWeight (blockSignature (q := q) (b := b) eta c x) w target) 0 :=
  weightedShift_partition (mixedFrequency c tau x u) w
    (blockSignature (q := q) (b := b) eta c x) (mixed_collision_signature (q := q) (b := b) eta c tau x u hu)

/-- Literal finite positive residue windows discharge every divisibility in
the full Gram partition, retaining arbitrary correlated index families and weights. -/
theorem residue_mixed_gram_partition {ι : Type*} [Fintype ι] {q b k r X : ℕ} [NeZero q]
    (eta : ℤ) (c : Fin k → ℤ) (tau : Fin r → ℤ) (x : ι → Fin k → ℤ)
    (u : ι → Fin r → VinogradovConditionedCompletion.PrimeTailWindow q b eta X) (w : ι → ℂ) :
    VinogradovShiftedMoment.weightedShift
      (mixedFrequency c tau x (fun z j => ((u z j).val.val + 1 : ℤ))) w 0 =
      ∑ target : (i : Fin k) → ZMod (q ^ ((i.val + 1) * b)),
        VinogradovShiftedMoment.weightedShift
          (mixedFrequency c tau x (fun z j => ((u z j).val.val + 1 : ℤ)))
          (targetWeight (blockSignature (q := q) (b := b) eta c x) w target) 0 := by
  apply mixed_gram_partition eta c tau x _ w
  intro z j
  have hz := (VinogradovResidueMoment.residue_mod_iff_dvd_sub eta ((u z j).val.val + 1)).mp
    (u z j).property
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hz

/-- The full actual finite-window torus energy is the exact sum of its
congruence-target energies, with arbitrary correlated configurations and weights. -/
theorem residue_mixed_integral_partition {ι : Type*} [Fintype ι] {q b k r X : ℕ} [NeZero q]
    (eta : ℤ) (c : Fin k → ℤ) (tau : Fin r → ℤ) (x : ι → Fin k → ℤ)
    (u : ι → Fin r → VinogradovConditionedCompletion.PrimeTailWindow q b eta X) (w : ι → ℂ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖∑ z, w z * mFourier
        (mixedFrequency c tau x (fun z j => ((u z j).val.val + 1 : ℤ)) z) theta‖ ^ 2) =
      ∑ target : (i : Fin k) → ZMod (q ^ ((i.val + 1) * b)),
        ∫ theta : UnitAddTorus (Fin k),
          ‖∑ z, targetWeight (blockSignature (q := q) (b := b) eta c x) w target z *
            mFourier (mixedFrequency c tau x (fun z j => ((u z j).val.val + 1 : ℤ)) z) theta‖ ^ 2 := by
  have h := residue_mixed_gram_partition (q := q) (b := b) eta c tau x u w
  simp only [VinogradovShiftedMoment.weightedShift_zero] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, Complex.ofReal_re] using hr

end
end RiemannGaussian.VinogradovMomentPartition
