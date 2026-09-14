/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialPrimeTransfer

/-!
# Convert prime-separated original solutions into their actual energy

An exact restricted complex correlation precedes Cauchy and absorption.
The original mean value is at most (2R)^2 times the self energy of the
selected prime-separated polynomial, including the zero-moment case.
The energy is built from the original interval and full frequency vectors.
-/

namespace RiemannGaussian.VinogradovInitialEnergy
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovShiftedMoment VinogradovPartitionEnergy
open VinogradovCrossMoment VinogradovInitialPrimeTransfer
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The original cross collisions with a restriction on the first family alone. -/
def restrictedCrossCount {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (u : κ → d → ℤ) (P : ι → Prop) : ℕ :=
  (Finset.univ.filter (fun xy : ι × κ => P xy.1 ∧ v xy.1 = u xy.2)).card

/-- The complete complex correlation of an indicator and the original unrestricted family is exactly its one-sided count. -/
theorem restricted_crossGram {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (u : κ → d → ℤ) (P : ι → Prop) [DecidablePred P] :
    crossGram v u (fun x => if P x then 1 else 0) (fun _ => 1) =
      (restrictedCrossCount v u P : ℂ) := by
  rw [restrictedCrossCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  unfold crossGram
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hp : P x <;> by_cases he : v x = u y <;> simp [hp, he]

/-- The full tuple polynomial retains the original exact power before taking a norm. -/
theorem tuple_polynomial_one {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency r v) (fun _ => 1) theta = polynomial v (fun _ => 1) theta ^ r := by
  simpa only [polynomial, one_mul, tupleFrequency] using (power_expansion v r theta).symm

/-- The full tuple self energy is the actual original moment. -/
theorem tuple_energy_eq_moment {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) :
    (∫ theta : UnitAddTorus d, ‖polynomial (tupleFrequency r v) (fun _ => 1) theta‖ ^ 2) =
      moment r v := by
  unfold moment
  apply integral_congr_ae
  filter_upwards [] with theta
  rw [tuple_polynomial_one, norm_pow, ← pow_mul, Nat.mul_comm r 2]
  simp only [polynomial, one_mul]

/-- A retained share of the original cross count controls the moment by the actual restricted self energy, with its explicit squared cost. -/
theorem moment_le_restricted_energy {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (P : (Fin r → ι) → Prop) [DecidablePred P] {A : ℝ} (hA : 0 ≤ A)
    (hshare : moment r v ≤ A * (restrictedCrossCount (tupleFrequency r v) (tupleFrequency r v) P : ℝ)) :
    moment r v ≤ A ^ 2 * ∫ theta : UnitAddTorus d,
      ‖polynomial (tupleFrequency r v) (fun x => if P x then 1 else 0) theta‖ ^ 2 := by
  let E := ∫ theta : UnitAddTorus d,
    ‖polynomial (tupleFrequency r v) (fun x => if P x then 1 else 0) theta‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hJ : 0 ≤ moment r v := integral_nonneg (fun _ => by positivity)
  have hc := crossGram_norm_le (tupleFrequency r v) (tupleFrequency r v)
    (fun x => if P x then 1 else 0) (fun _ => 1)
  rw [restricted_crossGram, Complex.norm_natCast, tuple_energy_eq_moment] at hc
  change (restrictedCrossCount (tupleFrequency r v) (tupleFrequency r v) P : ℝ) ≤
    E ^ (1 / 2 : ℝ) * moment r v ^ (1 / 2 : ℝ) at hc
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hc
  have hb := hshare.trans (mul_le_mul_of_nonneg_left hc hA)
  have hs := pow_le_pow_left₀ hJ hb 2
  simp only [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hJ] at hs
  by_cases hz : moment r v = 0
  · rw [hz]
    exact mul_nonneg (sq_nonneg _) hE
  · have hp : 0 < moment r v := lt_of_le_of_ne hJ (Ne.symm hz)
    change moment r v ≤ A ^ 2 * E
    nlinarith

/-- The literal separated count is the one-sided restriction of the full original tuple cross count. -/
theorem intervalSeparatedCount_eq_restricted {d : Type*} {X k : ℕ} (s : ℕ)
    (v : Fin X → d → ℤ) (e : Fin k ↪ Fin (s + 2)) (p : ℕ) :
    intervalSeparatedCount s v e p =
      restrictedCrossCount (tupleFrequency (s + 2) v) (tupleFrequency (s + 2) v)
        (fun x => Function.Injective (fun j => ((x (e j)).val + 1) % p)) := by
  unfold intervalSeparatedCount separatedCount restrictedCrossCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every order at least two enters the original restricted energy at some prime in the common explicit packet interval. -/
theorem exists_prime_restricted_energy {d : Type*} [Fintype d]
    (M R k X r : ℕ) (v : Fin X → d → ℤ) (e : Fin k ↪ Fin r)
    (hr : 2 ≤ r) (hM : 0 < M) (hR : 0 < R)
    (hbudget : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M ∧
      moment r v ≤ (2 * (R : ℝ)) ^ 2 * ∫ theta : UnitAddTorus d,
        ‖polynomial (tupleFrequency r v)
          (fun x => if Function.Injective (fun j => ((x (e j)).val + 1) % p) then 1 else 0) theta‖ ^ 2 := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hr
  have hr' : r = s + 2 := by omega
  clear hs
  subst r
  obtain ⟨p, hp, hMp, hpM, hshare⟩ := exists_prime_carrying_moment M R k X s v e hM hR hbudget hsize
  refine ⟨p, hp, hMp, hpM, ?_⟩
  have hshare' : moment (s + 2) v ≤ (2 * (R : ℝ)) *
      (restrictedCrossCount (tupleFrequency (s + 2) v) (tupleFrequency (s + 2) v)
        (fun x => Function.Injective (fun j => ((x (e j)).val + 1) % p)) : ℝ) := by
    simpa only [intervalSeparatedCount_eq_restricted, mul_assoc] using hshare
  exact moment_le_restricted_energy (s + 2) v _ (by positivity) hshare'

end
end RiemannGaussian.VinogradovInitialEnergy
