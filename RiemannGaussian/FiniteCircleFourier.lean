import RiemannGaussian.FiniteSeparatedSampling
import Mathlib.Analysis.Fourier.ZMod

/-!
# Exact finite circle waves and their energy

The full complex finite Fourier representation precedes every norm estimate.
Character orthogonality evaluates its complete-period energy, and its exact
forward difference retains each frequency's multiplier. These are the finite
ingredients for a sampling bound on the actual divisor phase spectrum.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-- The exact complex wave of a residue frequency at an integer sample. -/
def finiteCircleWave (k : ZMod Q) (n : ℕ) : ℂ := ZMod.stdAddChar ((n : ZMod Q) * k)

/-- The standard finite circle character always has unit norm. -/
theorem norm_stdAddChar_eq_one (k : ZMod Q) : ‖ZMod.stdAddChar k‖ = 1 := by
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Every finite circle wave keeps unit modulus. -/
theorem norm_finiteCircleWave_eq_one (k : ZMod Q) (n : ℕ) : ‖finiteCircleWave k n‖ = 1 :=
  norm_stdAddChar_eq_one _

/-- Conjugation reverses the entire residue frequency. -/
theorem stdAddChar_neg_eq_conj (k : ZMod Q) :
    ZMod.stdAddChar (-k) = starRingEnd ℂ (ZMod.stdAddChar k) := by
  have hk : ZMod.stdAddChar k ≠ 0 := by
    intro h
    have hn := norm_stdAddChar_eq_one k
    rw [h, norm_zero] at hn
    norm_num at hn
  apply (mul_right_inj' hk).mp
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
    Complex.mul_conj', norm_stdAddChar_eq_one]
  norm_num

/-- The wave is periodic at the literal finite-circle period. -/
theorem finiteCircleWave_periodic (k : ZMod Q) : Function.Periodic (finiteCircleWave k) Q := by
  intro n
  simp only [finiteCircleWave, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- Adding integer sample positions preserves both phases in their
exact multiplicative character identity. -/
theorem finiteCircleWave_add (k : ZMod Q) (n m : ℕ) :
    finiteCircleWave k (n + m) = finiteCircleWave k n * finiteCircleWave k m := by
  simp only [finiteCircleWave, Nat.cast_add, add_mul, AddChar.map_add_eq_mul]

/-- The exact next-sample multiplier is the original residue character. -/
theorem finiteCircleWave_succ (k : ZMod Q) (n : ℕ) :
    finiteCircleWave k (n + 1) = finiteCircleWave k n * ZMod.stdAddChar k := by
  rw [finiteCircleWave_add]
  simp only [finiteCircleWave, Nat.cast_one, one_mul]

/-- Integer representatives enumerate the finite circle exactly once. -/
theorem sum_range_natCast_eq_sum_zmod {α : Type*} [AddCommMonoid α] (f : ZMod Q → α) :
    (∑ n ∈ Finset.range Q, f (n : ZMod Q)) = ∑ k : ZMod Q, f k := by
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin Q ≃ ZMod Q :=
    { toFun := fun n ↦ (n.val : ZMod Q)
      invFun := fun k ↦ ⟨k.val, k.val_lt⟩
      left_inv := fun n ↦ Fin.ext (ZMod.val_natCast_of_lt n.isLt)
      right_inv := fun k ↦ ZMod.natCast_zmod_val k }
  exact Equiv.sum_comp e f

/-- The complete-period wave sum is zero at every nonzero frequency,
and is the literal period at the zero frequency. -/
theorem sum_range_finiteCircleWave (k : ZMod Q) :
    (∑ n ∈ Finset.range Q, finiteCircleWave k n) = if k = 0 then (Q : ℂ) else 0 := by
  unfold finiteCircleWave
  rw [sum_range_natCast_eq_sum_zmod (fun x : ZMod Q ↦ ZMod.stdAddChar (x * k))]
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using
    AddChar.sum_mulShift k (ZMod.isPrimitive_stdAddChar Q)

/-- The mixed complex wave product retains its frequency difference. -/
theorem finiteCircleWave_mul_conj (k l : ZMod Q) (n : ℕ) :
    finiteCircleWave k n * starRingEnd ℂ (finiteCircleWave l n) = finiteCircleWave (k - l) n := by
  simp only [finiteCircleWave, ← stdAddChar_neg_eq_conj, ← AddChar.map_add_eq_mul,
    sub_eq_add_neg, mul_add, mul_neg]

/-- Exact orthogonality of every two finite circle frequencies. -/
theorem sum_range_finiteCircleWave_mul_conj (k l : ZMod Q) :
    (∑ n ∈ Finset.range Q, finiteCircleWave k n * starRingEnd ℂ (finiteCircleWave l n)) =
      if k = l then (Q : ℂ) else 0 := by
  simp_rw [finiteCircleWave_mul_conj]
  rw [sum_range_finiteCircleWave]
  simp only [sub_eq_zero]

end

end RiemannGaussian
