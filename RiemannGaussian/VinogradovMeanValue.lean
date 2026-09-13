/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact high moments and integer frequency collisions

The complete even moment of any finite integer-frequency family equals
the number of pairs of tuples with matching total frequency vectors.
For the monomial frequency vector this is the Vinogradov equal-power-sum
system. The full complex weighted Gram identity remains available upstream.
This identity supplies no quantitative Vinogradov mean-value saving.
-/

namespace RiemannGaussian.VinogradovMeanValue
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate

/-- Use the same normalized Haar measure as the multivariate Fourier library. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The chosen unit-circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι]

/-- Exact multivariate Fourier orthogonality keeps every frequency coordinate. -/
theorem integral_pair (m n : d → ℤ) :
    (∫ θ : UnitAddTorus d, mFourier m θ * conj (mFourier n θ)) =
      if m = n then (1 : ℂ) else 0 := by
  classical
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) n m
  simpa only [ContinuousMap.inner_toLp, eq_comm, mul_comm] using h

/-- A whole weighted Fourier family has exactly its collision Gram form. -/
theorem weighted_gram (v : ι → d → ℤ) (w : ι → ℂ) :
    (∫ θ : UnitAddTorus d,
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ)) =
      ∑ i, ∑ j, if v i = v j then w i * conj (w j) else 0 := by
  classical
  have hi (i j : ι) : Integrable (fun θ : UnitAddTorus d =>
      (w i * conj (w j)) * (mFourier (v i) θ * conj (mFourier (v j) θ))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  have he : (fun θ : UnitAddTorus d =>
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ)) =
      fun θ => ∑ i, ∑ j,
        (w i * conj (w j)) * (mFourier (v i) θ * conj (mFourier (v j) θ)) := by
    funext θ
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [integral_const_mul, integral_pair]
  split_ifs <;> simp

/-- Multiplying phase monomials adds their full frequency vectors exactly. -/
theorem product_mFourier {κ : Type*} (S : Finset κ) (v : κ → d → ℤ) (θ : UnitAddTorus d) :
    (∏ i ∈ S, mFourier (v i) θ) = mFourier (∑ i ∈ S, v i) θ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mFourier_zero]
  | @insert i S hi ih => simp [hi, ih, mFourier_add]

/-- The power expansion retains every ordered tuple before integration. -/
theorem power_expansion (v : ι → d → ℤ) (s : ℕ) (θ : UnitAddTorus d) :
    (∑ i, mFourier (v i) θ) ^ s =
      ∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact product_mFourier _ _ _

/-- The actual even torus moment of an arbitrary integer-frequency family. -/
def moment (s : ℕ) (v : ι → d → ℤ) : ℝ :=
  ∫ θ : UnitAddTorus d, ‖∑ i, mFourier (v i) θ‖ ^ (2 * s)

/-- Ordered tuple pairs with exactly equal total frequency vectors. -/
def collisionCount (s : ℕ) (v : ι → d → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : (Fin s → ι) × (Fin s → ι) =>
    (∑ j, v (p.1 j)) = ∑ j, v (p.2 j))).card

/-- The literal even moment equals the exact equal-frequency tuple count. -/
theorem moment_eq_collisionCount (s : ℕ) (v : ι → d → ℤ) :
    moment s v = collisionCount s v := by
  classical
  apply Complex.ofReal_injective
  rw [moment, ← integral_complex_ofReal]
  have he (θ : UnitAddTorus d) :
      ((‖∑ i, mFourier (v i) θ‖ ^ (2 * s) : ℝ) : ℂ) =
      (∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ) *
        conj (∑ x : Fin s → ι, mFourier (∑ j, v (x j)) θ) := by
    rw [← power_expansion, Complex.mul_conj, ← Complex.sq_norm, norm_pow]
    congr 1
    ring
  simp_rw [he]
  have h := weighted_gram (fun x : Fin s → ι => ∑ j, v (x j)) (fun _ => 1)
  simp only [one_mul, map_one, mul_one] at h
  rw [h, collisionCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> norm_num

/-- A frequency family without collisions has exactly its diagonal second moment. -/
theorem first_moment {v : ι → d → ℤ} (hv : Function.Injective v) :
    moment 1 v = Fintype.card ι := by
  classical
  have h := weighted_gram v (fun _ => 1)
  simp only [one_mul, map_one, mul_one, hv.eq_iff] at h
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at h
  apply Complex.ofReal_injective
  simpa only [moment, mul_one, Complex.mul_conj, ← Complex.sq_norm,
    integral_complex_ofReal, Complex.ofReal_natCast] using h

/-- The integer monomial vector defining the complete Vinogradov system. -/
def monomialFrequency (k : ℕ) (n : ℕ) : Fin k → ℤ := fun j => (n : ℤ) ^ (j.val + 1)

/-- Retaining the first power distinguishes every integer in the system. -/
theorem monomialFrequency_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (monomialFrequency k) := by
  intro m n h
  have h₁ := congrFun h ⟨0, hk⟩
  simpa [monomialFrequency] using h₁

/-- The complete Vinogradov moment on integers `1,...,N`. -/
def meanValue (s k N : ℕ) : ℝ :=
  moment s (fun n : Fin N => monomialFrequency k (n.val + 1))

/-- The genuine Vinogradov mean value is its integer equal-power-sum count. -/
theorem meanValue_eq_count (s k N : ℕ) :
    meanValue s k N = collisionCount s (fun n : Fin N => monomialFrequency k (n.val + 1)) :=
  moment_eq_collisionCount _ _

/-- Real representatives expose the literal multivariate exponential phase. -/
theorem mFourier_real_phase (n : d → ℤ) (α : d → ℝ) :
    mFourier n (fun j => (α j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (n j : ℂ) * (α j : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The torus definition is the usual integral of the polynomial exponential
sum on the unit cube, with every side and exponent explicit. -/
theorem meanValue_eq_cube (s k N : ℕ) : meanValue s k N =
    ∫ α : Fin k → ℝ in {α | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1},
      ‖∑ n : Fin N, Complex.exp (2 * Real.pi * Complex.I *
        ∑ j : Fin k, ((n.val + 1 : ℕ) : ℂ) ^ (j.val + 1) * (α j : ℂ))‖ ^ (2 * s) := by
  unfold meanValue moment
  rw [UnitAddTorus.integral_preimage _ (fun _ : Fin k => 0)]
  simp only [zero_add]
  congr 1
  funext α
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  rw [mFourier_real_phase]
  simp [monomialFrequency]

/-- The first Vinogradov mean value is exactly the interval length. -/
theorem meanValue_one {k : ℕ} (hk : 0 < k) (N : ℕ) : meanValue 1 k N = N := by
  have hv : Function.Injective (fun n : Fin N => monomialFrequency k (n.val + 1)) := by
    intro m n h
    have hn := monomialFrequency_injective hk h
    apply Fin.ext
    omega
  simpa [meanValue] using first_moment hv

end
end RiemannGaussian.VinogradovMeanValue
