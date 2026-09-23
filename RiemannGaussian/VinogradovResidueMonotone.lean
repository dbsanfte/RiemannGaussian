/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialNonsingular
import RiemannGaussian.VinogradovEndpointDeletion

/-!
# Lossless tail endpoint comparison for the literature iteration

Ford's backward mixed-system iteration uses monotonicity of the actual
congruence-restricted count in its tail endpoint. The oscillating tail
polynomial is not pointwise monotone. We instead expand the residue
moment into actual complete mixed counts on the original block fibres,
and inject the smaller tail into the larger one. No numerical constant
is spent in passing from a quotient endpoint to the prescribed endpoint.
-/

namespace RiemannGaussian.VinogradovResidueMonotone
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovMixedMoments VinogradovMixedDifferencing VinogradovDifferenceEnergy
open VinogradovPolynomialNonsingular VinogradovColourProducts VinogradovMomentPartition
open VinogradovPartitionEnergy

/-- The normalized circle Haar measure used by the original moment. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- All original positive block tuples in one complete residue fibre. -/
abbrev BlockFibre (m P q : ℕ) (hq : 0 < q) (c : Fin m → Fin q) :=
  {x : Fin m → Fin P // tupleLabel m (positiveLabel hq P) x = c}

/-- Restriction to a literal block fibre equals its zero-one colour mask. -/
theorem fibre_polynomial {a : Type*} [Fintype a] (m P q : ℕ) (hq : 0 < q)
    (v : ℕ → a → ℤ) (c : Fin m → Fin q) (theta : UnitAddTorus a) :
    polynomial (fun x : BlockFibre m P q hq c =>
      tupleFrequency m (fun x : Fin P => v (x.val + 1)) x.val) (fun _ => 1) theta =
    polynomial (tupleFrequency m (fun x : Fin P => v (x.val + 1)))
      (targetWeight (tupleLabel m (positiveLabel hq P)) (fun _ => 1) c) theta := by
  have he := polynomial_subtype_eq
    (fun x : Fin m → Fin P => tupleLabel m (positiveLabel hq P) x = c)
    (tupleFrequency m (fun x : Fin P => v (x.val + 1)))
    (targetWeight (tupleLabel m (positiveLabel hq P)) (fun _ => 1) c)
    (by intro x hx; exact if_neg hx) theta
  have hw : (fun x : BlockFibre m P q hq c =>
      targetWeight (tupleLabel m (positiveLabel hq P)) (fun _ => (1 : ℂ)) c x.val) =
        fun _ => 1 := by
    funext x
    exact if_pos x.property
  rw [hw] at he
  exact he

/-- The restricted integral is exactly a sum of actual mixed counts.
Every block residue and every tail equation are retained. -/
theorem residueMixedMoment_eq_sum {κ a : Type*} [Fintype κ] [Fintype a]
    (m s P q : ℕ) (hq : 0 < q) (v : ℕ → a → ℤ) (u : κ → a → ℤ) :
    residueMixedMoment m s P q hq v u =
      ∑ c : Fin m → Fin q, mixedMoment 1 s
        (fun x : BlockFibre m P q hq c =>
          tupleFrequency m (fun x : Fin P => v (x.val + 1)) x.val) u := by
  let E (c : Fin m → Fin q) (theta : UnitAddTorus a) :=
    ‖polynomial (tupleFrequency m (fun x : Fin P => v (x.val + 1)))
      (targetWeight (tupleLabel m (positiveLabel hq P)) (fun _ => 1) c) theta‖ ^ 2
  have hi (c : Fin m → Fin q) : Integrable (fun theta : UnitAddTorus a =>
      E c theta * ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)) :=
    (((continuous_polynomial _ _).norm.pow 2).mul
      ((continuous_polynomial _ _).norm.pow (2 * s))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (theta : UnitAddTorus a) : residueEnergy P q hq v theta ^ m = ∑ c, E c theta := by
    symm
    exact (tuple_colour_energy m (fun x : Fin P => v (x.val + 1))
      (positiveLabel hq P) theta).trans (congrArg (fun x : ℝ => x ^ m)
        (positive_colourEnergy P q hq v theta))
  unfold residueMixedMoment
  simp_rw [he, Finset.sum_mul]
  rw [integral_finsetSum _ (fun c _ => hi c)]
  apply Finset.sum_congr rfl
  intro c hc
  unfold mixedMoment
  simp only [Nat.mul_one, fibre_polynomial, E]

/-- An injective restriction of the tail decreases the original residue
mixed moment. This is an inequality between counts, not between pointwise
absolute values of exponential sums. -/
theorem residueMixedMoment_map_le {κ τ a : Type*}
    [Fintype κ] [Fintype τ] [Fintype a]
    (m s P q : ℕ) (hq : 0 < q) (v : ℕ → a → ℤ) (u : τ → a → ℤ)
    (f : κ → τ) (hf : Function.Injective f) :
    residueMixedMoment m s P q hq v (fun x => u (f x)) ≤
      residueMixedMoment m s P q hq v u := by
  rw [residueMixedMoment_eq_sum, residueMixedMoment_eq_sum]
  apply Finset.sum_le_sum
  intro c hc
  exact VinogradovEndpointDeletion.mixedMoment_map_le 1 s _ u f hf

/-- The tail cutoff can be enlarged with numerical cost exactly one. -/
theorem residueMixedMoment_mono {a : Type*} [Fintype a]
    (m s P q : ℕ) (hq : 0 < q) (v u : ℕ → a → ℤ)
    {Q Q' : ℕ} (hQ : Q ≤ Q') :
    residueMixedMoment m s P q hq v (fun x : Fin Q => u (x.val + 1)) ≤
      residueMixedMoment m s P q hq v (fun x : Fin Q' => u (x.val + 1)) :=
  residueMixedMoment_map_le m s P q hq v (fun x : Fin Q' => u (x.val + 1))
    (Fin.castLE hQ) (Fin.castLE_injective hQ)

end
end RiemannGaussian.VinogradovResidueMonotone
