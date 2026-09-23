/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovBinomialRows
import RiemannGaussian.VinogradovResidueEndpoint

/-!
# Exact row transport of the complete polynomial and monomial count

The binomial row operation acts on every retained equation together.
The constant row has the same value on both sides, so it is included in
the transport without an unproved phase or boundary premise.
-/

namespace RiemannGaussian.VinogradovRowTransport
noncomputable section
open scoped BigOperators Classical
open Polynomial MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPolynomialSystems VinogradovBinomialRows VinogradovResidueEndpoint
open VinogradovPolynomialDifferencing VinogradovPolynomialConditioning
open VinogradovPolynomialNonsingular

/-- The full equation vector, including its constant tail count. -/
def naturalConfiguration {m s : ℕ} (d : ℕ) (F : Fin m → ℤ[X])
    (x : Fin m → ℕ) (u : Fin s → ℤ) (n : ℕ) : ℤ :=
  (∑ j, (fullSystem d F n).eval (x j : ℤ)) + ∑ j, u j ^ n

/-- The natural degree vector contains exactly the original complete
frequency equations. Its constant equation is automatic from equal
tuple lengths, rather than omitted during row transport. -/
theorem naturalConfiguration_eq_iff {m s : ℕ} (d : ℕ) (F : Fin m → ℤ[X])
    (x y : Fin m → ℕ) (u v : Fin s → ℤ) :
    (∀ n, n ≤ d + m → naturalConfiguration d F x u n = naturalConfiguration d F y v n) ↔
      blockFrequency d F x + tupleFrequency s (integerTail m d) u =
        blockFrequency d F y + tupleFrequency s (integerTail m d) v := by
  constructor
  · intro h
    funext i
    rcases i with i | i
    · have hn : i.val + 1 ≤ d := by omega
      have he := h (i.val + 1) (by omega)
      simpa only [naturalConfiguration, fullSystem_low F hn, eval_zero,
        Finset.sum_const_zero, zero_add, blockFrequency, fullFrequency,
        Pi.add_apply, Finset.sum_apply, tupleFrequency, integerTail, Sum.elim_inl] using he
    · have he := h (d + i.val + 1) (by have := i.isLt; omega)
      simpa only [naturalConfiguration, fullSystem_active, blockFrequency,
        fullFrequency, Pi.add_apply, Finset.sum_apply, tupleFrequency, integerTail,
        Sum.elim_inr] using he
  · intro h n hn
    by_cases hn0 : n = 0
    · subst n
      simp only [naturalConfiguration, fullSystem_low F (Nat.zero_le d), eval_zero,
        Finset.sum_const_zero, zero_add, pow_zero]
    by_cases hnd : n ≤ d
    · let i : Fin d := ⟨n - 1, by omega⟩
      have hi : i.val + 1 = n := by dsimp [i]; omega
      have he := congrFun h (Sum.inl i)
      simpa only [blockFrequency, fullFrequency, Pi.add_apply, Finset.sum_apply,
        Sum.elim_inl, Finset.sum_const_zero, zero_add, tupleFrequency, integerTail,
        hi, naturalConfiguration, fullSystem_low F hnd, eval_zero] using he
    · let i : Fin m := ⟨n - d - 1, by omega⟩
      have hi : n = d + i.val + 1 := by dsimp [i]; omega
      have he := congrFun h (Sum.inr i)
      rw [hi]
      simpa only [blockFrequency, fullFrequency, Pi.add_apply, Finset.sum_apply,
        Sum.elim_inr, tupleFrequency, integerTail, naturalConfiguration,
        fullSystem_active] using he

/-- The entire original configuration is transformed at once. The
polynomial rows and shifted monomials receive the same shift parameter. -/
theorem naturalConfiguration_row {m s : ℕ} (d : ℕ) (c : ℤ) (F : Fin m → ℤ[X])
    (x : Fin m → ℕ) (u : Fin s → ℤ) {n : ℕ} (hn : n ≤ d + m) :
    row c (naturalConfiguration d F x u) n =
      naturalConfiguration d (rowSystem d c F) x (fun j => u j + c) n := by
  have hev (j : Fin m) : row c (fun l => (fullSystem d F l).eval (x j : ℤ)) n =
      (fullSystem d (rowSystem d c F) n).eval (x j : ℤ) := by
    rw [fullSystem_rowSystem d c F hn]
    have he := map_row (Polynomial.evalRingHom (x j : ℤ)) (C c) (fullSystem d F) n
    change (row (C c) (fullSystem d F) n).eval (x j : ℤ) =
      row ((C c).eval (x j : ℤ)) (fun l => (fullSystem d F l).eval (x j : ℤ)) n at he
    simpa only [eval_C] using he.symm
  unfold naturalConfiguration
  rw [row_add, row_sum, row_sum]
  simp only [hev, row_pow]

/-- The row transformation preserves the actual full-frequency
collision condition while shifting every tail entry. -/
theorem frequency_eq_iff_shift {m s : ℕ} (d : ℕ) (c : ℤ) (F : Fin m → ℤ[X])
    (x y : Fin m → ℕ) (u v : Fin s → ℤ) :
    (blockFrequency d F x + tupleFrequency s (integerTail m d) u =
      blockFrequency d F y + tupleFrequency s (integerTail m d) v) ↔
      blockFrequency d (rowSystem d c F) x + tupleFrequency s (integerTail m d) (fun j => u j + c) =
        blockFrequency d (rowSystem d c F) y + tupleFrequency s (integerTail m d) (fun j => v j + c) := by
  rw [← naturalConfiguration_eq_iff, ← naturalConfiguration_eq_iff]
  have he := row_eq_iff c (naturalConfiguration d F x u) (naturalConfiguration d F y v) (d + m)
  have hf : (∀ n, n ≤ d + m → row c (naturalConfiguration d F x u) n =
      row c (naturalConfiguration d F y v) n) ↔
      ∀ n, n ≤ d + m → naturalConfiguration d (rowSystem d c F) x (fun j => u j + c) n =
        naturalConfiguration d (rowSystem d c F) y (fun j => v j + c) n := by
    constructor <;> intro h n hn
    · simpa only [naturalConfiguration_row d c F x u hn, naturalConfiguration_row d c F y v hn]
        using h n hn
    · simpa only [naturalConfiguration_row d c F x u hn, naturalConfiguration_row d c F y v hn]
        using h n hn
  exact he.symm.trans hf

/-- The row shift includes the original monomial dilation `q`. -/
def shiftAmount (p q xi : ℕ) : ℤ := (q : ℤ) * ((p : ℤ) - xi)

/-- The original shifted tail becomes the literal prime-dilated tail.
In particular the scale `q` is present in every row coefficient. -/
theorem shifted_base_add_amount (p q xi x : ℕ) :
    (q : ℤ) * ((p : ℤ) * x + ((xi : ℤ) - p)) + shiftAmount p q xi =
      ((p * q : ℕ) : ℤ) * x := by
  simp only [shiftAmount, Nat.cast_mul]
  ring

/-- Use the original enumeration of nonsingular block tuples. -/
local instance windowFintype (p m P : ℕ) : Fintype (Window p m P) := Fintype.ofFinite _

/-- The shifted count and the prime-dilated count have exactly the same
solutions after changing only the polynomial rows. All original windows,
nonsingularity conditions and low-degree equations are unchanged. -/
theorem shifted_count_eq (p m d P Q q xi s : ℕ) (F : Fin m → ℤ[X]) :
    nonsingularCount p m d P s F (fun x : Fin Q => shiftedTail m d p q xi (x.val + 1)) =
      nonsingularCount p m d P s (rowSystem d (shiftAmount p q xi) F) (monomialTail m d p q Q) := by
  unfold nonsingularCount differenceCount
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_zero]
  have he := frequency_eq_iff_shift d (shiftAmount p q xi) F
    (fun j => (z.1.1.val j).val + 1) (fun j => (z.2.1.val j).val + 1)
    (fun j => (q : ℤ) * ((p : ℤ) * ((z.1.2 j).val + 1 : ℕ) + ((xi : ℤ) - p)))
    (fun j => (q : ℤ) * ((p : ℤ) * ((z.2.2 j).val + 1 : ℕ) + ((xi : ℤ) - p)))
  simpa only [configurationFrequency, windowFrequency, shiftedTail, tupleFrequency,
    shifted_base_add_amount, monomialTail_eq_integerTail] using he

/-- The actual shifted mixed integral becomes the previously defined
prime-dilated integer count, with no integral comparison premise. -/
theorem shifted_mixedMoment_eq_count (p m d P Q q xi s : ℕ) (F : Fin m → ℤ[X]) :
    VinogradovMixedMoments.mixedMoment 1 s (windowFrequency (p := p) (P := P) d F)
      (fun x : Fin Q => shiftedTail m d p q xi (x.val + 1)) =
      (nonsingularCount p m d P s (rowSystem d (shiftAmount p q xi) F)
        (monomialTail m d p q Q) : ℝ) := by
  rw [← shifted_count_eq p m d P Q q xi s F, ← nonsingularMoment_eq_count]
  simp only [VinogradovMixedMoments.mixedMoment, nonsingularMoment, mul_one]

end
end RiemannGaussian.VinogradovRowTransport
