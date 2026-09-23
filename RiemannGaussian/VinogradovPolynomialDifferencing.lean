/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMixedDifferencing
import RiemannGaussian.VinogradovPolynomialSystems

/-!
# Classical mixed differencing for literal polynomial systems

The original torus includes both the inactive and active polynomial
coordinates. After a difference, the first active coordinate becomes a
constant phase and is removed exactly from the polynomial norm. The
monomial tail continues to use every original coordinate, including that
one. The resulting bound is the quantitative `L`-to-next-`K` step, with
the new type and the entire interval for its multiplier proved.
-/

namespace RiemannGaussian.VinogradovPolynomialDifferencing
noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovMixedMoments VinogradovDifferenceEnergy
open VinogradovMixedDifferencing VinogradovPolynomialSystems

/-- The same normalized Haar measure on the original torus. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Embed the active system in its original full coordinate space. -/
def fullFrequency {m : ℕ} (d : ℕ) (F : Fin m → ℤ[X]) (n : ℕ) :
    (Fin d ⊕ Fin m) → ℤ := Sum.elim (fun _ => 0) (fun j => (F j).eval n)

/-- Embed the next type in the same coordinate space. The first active
coordinate is zero on the polynomial side; the tail still retains it. -/
def nextFrequency {m : ℕ} (d : ℕ) (G : Fin m → ℤ[X]) (n : ℕ) :
    (Fin d ⊕ Fin (m + 1)) → ℤ :=
  Sum.elim (fun _ => 0) (Fin.cases 0 (fun j => (G j).eval n))

/-- The exact constant phase contributed by the first linear difference. -/
def constantFrequency {m : ℕ} (d : ℕ) (F : Fin (m + 1) → ℤ[X]) (h : ℕ) :
    (Fin d ⊕ Fin (m + 1)) → ℤ :=
  Sum.elim (fun _ => 0) (Fin.cases ((F 0).leadingCoeff * h) (fun _ => 0))

/-- A common integer-frequency translation is a unit phase and leaves
the norm of the *entire weighted sum* unchanged. -/
theorem norm_polynomial_add_constant {ι a : Type*} [Fintype ι] [Fintype a]
    (v : ι → a → ℤ) (c : a → ℤ) (w : ι → ℂ) (theta : UnitAddTorus a) :
    ‖polynomial (fun i => c + v i) w theta‖ = ‖polynomial v w theta‖ := by
  have he : polynomial (fun i => c + v i) w theta = mFourier c theta * polynomial v w theta := by
    simp only [polynomial, mFourier_add, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he, norm_mul, norm_mFourier_apply, one_mul]

/-- Every coordinate of the difference is retained: zero inactive
coordinates, the constant linear coordinate, and the next active system. -/
theorem differenceFrequency_eq {m d T e : ℕ} {F : Fin (m + 1) → ℤ[X]}
    (hF : HasType F d T e) (P h : ℕ) (x : Fin P) :
    differenceFrequency P h (fullFrequency d F) x = constantFrequency d F h +
      nextFrequency d (fun j => difference (h : ℤ) (F j.succ)) (x.val + 1) := by
  funext i
  rcases i with i | i
  · simp [differenceFrequency, fullFrequency, constantFrequency, nextFrequency]
  · refine Fin.cases ?_ (fun j => ?_) i
    · have hf : (F 0).natDegree = 1 := (hF 0).1
      have he := congrArg (fun f : ℤ[X] => f.eval ((x.val : ℤ) + 1))
        (difference_linear_constant hf (h : ℤ))
      rw [difference_eval, eval_C] at he
      simpa only [differenceFrequency, fullFrequency, constantFrequency, nextFrequency,
        Sum.elim_inr, Fin.cases_zero, Pi.add_apply, Pi.sub_apply, add_zero, zero_add, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using he
    · simp only [differenceFrequency, fullFrequency, constantFrequency, nextFrequency,
        Sum.elim_inr, Fin.cases_succ, Pi.add_apply, Pi.sub_apply, zero_add, difference_eval,
        Nat.cast_add, Nat.cast_one]
      congr 2
      ring

/-- Constant-phase removal commutes with the original mixed moment.
Every tail coordinate is still present in `u`. -/
theorem mixedMoment_difference_eq {κ : Type*} [Fintype κ]
    {m d T e : ℕ} {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (r s P h : ℕ) (u : κ → (Fin d ⊕ Fin (m + 1)) → ℤ) :
    mixedMoment r s (differenceFrequency P h (fullFrequency d F)) u =
      mixedMoment r s (fun x : Fin P =>
        nextFrequency d (fun j => difference (h : ℤ) (F j.succ)) (x.val + 1)) u := by
  have he := funext (differenceFrequency_eq hF P h)
  unfold mixedMoment
  simp_rw [he, norm_polynomial_add_constant]

/-- The actual polynomial-system differencing inequality. A fixed
positive multiple `h*q` of the congruence modulus gives the next type,
with `T≤T'≤P*T`. No moment estimate or endpoint-completion assumption is
supplied. The original tail stays in its full ambient coordinate space. -/
theorem exists_typed_difference_bound {κ : Type*} [Fintype κ]
    {m d T e : ℕ} (hm : 1 ≤ m) {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (s P q : ℕ) (hq : 0 < q) (hqP : q ≤ P)
    (u : κ → (Fin d ⊕ Fin (m + 1)) → ℤ) :
    ∃ (h T' : ℕ) (G : Fin m → ℤ[X]),
      1 ≤ h ∧ h ≤ P / q ∧ T' = (h * q) * T ∧ T ≤ T' ∧ T' ≤ P * T ∧
      G = (fun j => difference ((h * q : ℕ) : ℤ) (F j.succ)) ∧
      HasType G (d + 1) T' e ∧
      residueMixedMoment (m + 1) s P q hq (fullFrequency d F) u ≤
        max ((2 * ((m + 1 : ℕ) : ℝ) * P) ^ (m + 1) * moment s u)
          (2 * (2 * (P / q : ℕ)) ^ (m + 1) *
            (mixedMoment m s (fun x : Fin P => nextFrequency d G (x.val + 1)) u ^
              (((m : ℝ) + 1) / (2 * (m : ℝ))) *
            moment s u ^ (((m : ℝ) - 1) / (2 * (m : ℝ))))) := by
  obtain ⟨h, hh, hHP, hbound⟩ := exists_difference_bound (by omega : 2 ≤ m + 1)
    s P q hq hqP (fullFrequency d F) u
  have hstep : 1 ≤ h * q := Nat.mul_pos (by omega) hq
  have hstepP : h * q ≤ P := (Nat.mul_le_mul_right q hHP).trans (Nat.div_mul_le_self P q)
  obtain ⟨hlo, hhi⟩ := difference_type_parameter (T := T) hstep hstepP
  refine ⟨h, h * q * T, (fun j => difference ((h * q : ℕ) : ℤ) (F j.succ)),
    hh, hHP, rfl, hlo, hhi, rfl, hasType_difference hF hstep, ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : (1 : ℝ) - ((m : ℝ) + 1) / (2 * (m : ℝ)) =
      ((m : ℝ) - 1) / (2 * (m : ℝ)) := by field_simp; ring
  simpa only [differenceAllowance, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right, mixedMoment_difference_eq hF, he] using hbound

end
end RiemannGaussian.VinogradovPolynomialDifferencing
