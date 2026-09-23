/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialNonsingular

/-!
# The actual nonsingular count reaches the next polynomial type

The full dilated monomial tail has exactly the ordinary degree-`k`
Vinogradov moment. The proved nonsingular conditioning inequality then
feeds the quantitative polynomial differencing step. This gives a single
explicit bound on the original integer count with an attained next type,
retaining every original tail equation.
-/

namespace RiemannGaussian.VinogradovNonsingularDescent
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovMixedMoments

/-- The same normalized Haar measure as the original count. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem moment_reindex {ι a b : Type*} [Fintype ι] [Fintype a] [Fintype b]
    (s : ℕ) (v : ι → a → ℤ) (e : b ≃ a) :
    moment s (fun x j => v x (e j)) = moment s v := by
  rw [moment_eq_collisionCount, moment_eq_collisionCount]
  congr 1
  unfold collisionCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Finset.sum_apply]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact h i
  · intro h i
    exact h (e i)

/-- The full positive dilated monomial tail has exactly the original
degree-`d+m` Vinogradov moment. No coordinate is omitted in this transport. -/
theorem monomialTail_moment (s m d p q Q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    moment s (monomialTail m d p q Q) = meanValue s (d + m) Q := by
  let v (x : Fin Q) := VinogradovPowerSumRigidity.integerFrequency (d + m)
    (((p * q : ℕ) : ℤ) * ((x.val + 1 : ℕ) : ℤ))
  have he : monomialTail m d p q Q =
      fun x j => v x (finSumFinEquiv j) := by
    funext x j
    rcases j with j | j
    · simp only [monomialTail, Sum.elim_inl, v, VinogradovPowerSumRigidity.integerFrequency,
        finSumFinEquiv_apply_left, Fin.val_castAdd, Nat.cast_add, Nat.cast_one]
    · simp only [monomialTail, Sum.elim_inr, v, VinogradovPowerSumRigidity.integerFrequency,
        finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.cast_add, Nat.cast_one]
  rw [he, moment_reindex]
  have hscale : ((p * q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hp hq).ne'
  have ha := VinogradovAffineMoment.moment_affine s (d + m)
    (fun x : Fin Q => ((x.val + 1 : ℕ) : ℤ)) hscale 0
  unfold v meanValue monomialFrequency VinogradovPowerSumRigidity.integerFrequency
  unfold VinogradovPowerSumRigidity.integerFrequency at ha
  simpa only [add_zero] using ha

/-- The literal nonsingular polynomial/monomial count reaches an
attained next polynomial type with every numerical conditioning and
differencing cost displayed. The remaining full `K` conditioning must
still handle repeated tuples, prime selection and the residue-tail boundary. -/
theorem exists_nonsingular_descent {p m d r T e : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (hpdeg : d + (m + 1) < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    (hr1 : 1 ≤ r) (hr : r ≤ d + (m + 1))
    {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (P Q q s : ℕ) (hq : 0 < q) (hP : p ^ r ≤ P) :
    ∃ (h T' : ℕ) (G : Fin m → ℤ[X]),
      1 ≤ h ∧ h ≤ P / p ^ r ∧ T' = (h * p ^ r) * T ∧ T ≤ T' ∧ T' ≤ P * T ∧
      G = (fun j => difference ((h * p ^ r : ℕ) : ℤ) (F j.succ)) ∧
      HasType G (d + 1) T' e ∧
      (nonsingularCount p (m + 1) d P s F (monomialTail (m + 1) d p q Q) : ℝ) ≤
        ((p ^ ((r - d) * (r - d - 1) / 2) * (m + 1).factorial : ℕ) : ℝ) *
          max ((2 * ((m + 1 : ℕ) : ℝ) * P) ^ (m + 1) * meanValue s (d + (m + 1)) Q)
            (2 * (2 * (P / p ^ r : ℕ)) ^ (m + 1) *
              (mixedMoment m s (fun x : Fin P => nextFrequency d G (x.val + 1))
                (monomialTail (m + 1) d p q Q) ^ (((m : ℝ) + 1) / (2 * (m : ℝ))) *
              meanValue s (d + (m + 1)) Q ^ (((m : ℝ) - 1) / (2 * (m : ℝ))))) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, T', G, hh, hHP, heT, hlo, hhi, hG, htype, hbound⟩ :=
    exists_typed_difference_bound hm hF s P (p ^ r) (pow_pos hp r) hP
      (monomialTail (m + 1) d p q Q)
  refine ⟨h, T', G, hh, hHP, heT, hlo, hhi, hG, htype, ?_⟩
  have hc := prime_dilated_count_le hpdeg hp2 hpT hr1 hr hF P Q q s
  have hstep := mul_le_mul_of_nonneg_left hbound
    (show (0 : ℝ) ≤ (p ^ ((r - d) * (r - d - 1) / 2) * (m + 1).factorial : ℕ) by positivity)
  simpa only [monomialTail_moment s (m + 1) d p q Q hp hq] using hc.trans hstep

end
end RiemannGaussian.VinogradovNonsingularDescent
