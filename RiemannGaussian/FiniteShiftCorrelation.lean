/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteDiscreteSobolev
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Exact integer-shift correlations before van der Corput estimation

The complete complex correlation of a finitely supported integer sequence
retains both its phase and its actual support. Averaging a consecutive set
of shifts preserves the original mass exactly; its energy is the full
Toeplitz correlation form. For positive `H`, a sequence supported on `N`
consecutive integers has its `H`-shift sum inside the enclosing interval
of length `N+H-1`.
This gives the signed matrix form of the van der Corput inequality without
replacing any correlation by an absolute value.
-/

namespace RiemannGaussian.FiniteShiftCorrelation
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The original complex correlation at integer displacement `h`. -/
def correlation (f : ℤ → ℂ) (h : ℤ) : ℂ :=
  ∑' n : ℤ, f (n + h) * starRingEnd ℂ (f n)

/-- The complete sum of the first `H` integer translates. -/
def shiftedSum (f : ℤ → ℂ) (H : ℕ) (n : ℤ) : ℂ :=
  ∑ h ∈ Finset.range H, f (n + h)

private theorem finite_shift {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h)) :=
  hf.fun_comp_of_injective (Equiv.addRight h).injective

private theorem finite_pair {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h k : ℤ) :
    Function.HasFiniteSupport (fun n ↦ f (n + h) * starRingEnd ℂ (f (n + k))) :=
  (finite_shift hf h).fun_mul_left _

/-- Every original complex correlation is genuinely summable for a
finitely supported sequence. -/
theorem summable_correlation {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    Summable (fun n : ℤ ↦ f (n + h) * starRingEnd ℂ (f n)) :=
  summable_of_hasFiniteSupport ((finite_shift hf h).fun_mul_left _)

/-- Taking the real part of the complete correlation commutes with its
convergent sum; no summand loses its sign. -/
theorem correlation_re {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (h : ℤ) :
    (correlation f h).re = ∑' n : ℤ, (f (n + h) * starRingEnd ℂ (f n)).re :=
  Complex.re_tsum (summable_correlation hf h)

/-- The diagonal is exactly the original square energy. -/
theorem correlation_zero {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) :
    (correlation f 0).re = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  rw [correlation_re hf]
  simp only [add_zero, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

/-- Translating both factors changes only their relative displacement;
the complete complex value is preserved. -/
theorem mixed_shift_eq (f : ℤ → ℂ) (h k : ℤ) :
    (∑' n : ℤ, f (n + h) * starRingEnd ℂ (f (n + k))) = correlation f (h - k) := by
  calc
    _ = ∑' n : ℤ, f ((n + k) + (h - k)) * starRingEnd ℂ (f (n + k)) := by
      apply tsum_congr
      intro n
      congr 2
      ring
    _ = _ := (Equiv.addRight k).tsum_eq
      (fun n : ℤ ↦ f (n + (h - k)) * starRingEnd ℂ (f n))

/-- Reversing a displacement conjugates the complete correlation. -/
theorem correlation_neg (f : ℤ → ℂ) (h : ℤ) :
    correlation f (-h) = starRingEnd ℂ (correlation f h) := by
  simp only [correlation, Complex.conj_tsum]
  calc
    _ = ∑' n : ℤ, f n * starRingEnd ℂ (f (n + h)) := by
      simpa only [zero_sub, add_zero, correlation] using (mixed_shift_eq f 0 h).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [map_mul, starRingEnd_self_apply, mul_comm]

/-- The real correlation is even; the imaginary correlation remains
available through the stronger conjugation identity. -/
theorem correlation_neg_re (f : ℤ → ℂ) (h : ℤ) :
    (correlation f (-h)).re = (correlation f h).re := by
  rw [correlation_neg, Complex.conj_re]

/-- The complete translated family still has finite support. -/
theorem finite_shiftedSum {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    Function.HasFiniteSupport (shiftedSum f H) :=
  Function.HasFiniteSupport.sum (fun h : ℕ ↦ finite_shift hf (h : ℤ)) (Finset.range H)

/-- Every translate has the same total mass, with no boundary terms
omitted from the finite sequence extended by zero. -/
theorem shiftedSum_mass {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, shiftedSum f H n) = (H : ℂ) * ∑' n : ℤ, f n := by
  unfold shiftedSum
  rw [Summable.tsum_finsetSum (s := Finset.range H)
    (fun (h : ℕ) _ ↦ summable_of_hasFiniteSupport (finite_shift hf (h : ℤ)))]
  have hshift (h : ℕ) : (∑' n : ℤ, f (n + h)) = ∑' n : ℤ, f n :=
    (Equiv.addRight (h : ℤ)).tsum_eq f
  simp only [hshift, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Pointwise expansion retains every pair of translated components. -/
theorem norm_sq_shiftedSum_eq (f : ℤ → ℂ) (H : ℕ) (n : ℤ) :
    ‖shiftedSum f H n‖ ^ 2 = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
      (f (n + h) * starRingEnd ℂ (f (n + k))).re := by
  calc
    _ = (shiftedSum f H n * starRingEnd ℂ (shiftedSum f H n)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    _ = _ := by
      simp only [shiftedSum, map_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Complex.re_sum]

/-- The exact energy of the complete shifted family is its full signed
Toeplitz form. Finite support justifies every sum interchange. -/
theorem shiftedSum_energy {f : ℤ → ℂ} (hf : Function.HasFiniteSupport f) (H : ℕ) :
    (∑' n : ℤ, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hp (h k : ℕ) : Function.HasFiniteSupport
      (fun n : ℤ ↦ (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    (finite_pair hf h k).fun_comp (by simp)
  have hi (h : ℕ) : Summable
      (fun n : ℤ ↦ ∑ k ∈ Finset.range H, (f (n + h) * starRingEnd ℂ (f (n + k))).re) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.sum (hp h) (Finset.range H))
  simp_rw [norm_sq_shiftedSum_eq]
  rw [Summable.tsum_finsetSum (fun h _ ↦ hi h)]
  apply Finset.sum_congr rfl
  intro h _
  rw [Summable.tsum_finsetSum (fun k _ ↦ summable_of_hasFiniteSupport (hp h k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.re_tsum (summable_of_hasFiniteSupport (finite_pair hf h k)), mixed_shift_eq]

/-- A sequence supported on `N` consecutive integers has all its first
`H` translates inside the precise interval of length `N+H-1`. -/
theorem shiftedSum_eq_zero_outside {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    ∀ n ∉ Finset.Ico (a - H + 1) (a + N), shiftedSum f H n = 0 := by
  intro n hn
  apply Finset.sum_eq_zero
  intro h hh
  apply hf
  intro hm
  apply hn
  simp only [Finset.mem_Ico] at hm ⊢
  have hh' := Finset.mem_range.mp hh
  omega

/-- The signed matrix form of van der Corput's inequality, with the
exact finite block length and all correlations retained. -/
theorem norm_sum_sq_le_correlation_matrix {f : ℤ → ℂ} {a : ℤ} {N H : ℕ}
    (hH : 0 < H) (hf : ∀ n ∉ Finset.Ico a (a + N), f n = 0) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), f n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) *
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
  have hfinite : Function.HasFiniteSupport f :=
    (Finset.Ico a (a + N)).finite_toSet.subset (by
      intro n hn
      by_contra h
      exact hn (hf n h))
  let S := Finset.Ico (a - H + 1) (a + N)
  have hs := shiftedSum_eq_zero_outside (H := H) hf
  have hmass : (∑ n ∈ S, shiftedSum f H n) =
      (H : ℂ) * ∑ n ∈ Finset.Ico a (a + N), f n := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ) hs,
      shiftedSum_mass hfinite, tsum_eq_sum hf]
  have henergy : (∑ n ∈ S, ‖shiftedSum f H n‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H, (correlation f ((h : ℤ) - k)).re := by
    rw [← tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (fun n hn ↦ by rw [hs n hn, norm_zero, zero_pow (by decide)])]
    exact shiftedSum_energy hfinite H
  have hcard : (S.card : ℝ) = (N : ℝ) + H - 1 := by
    have h := Int.card_Ico_of_le (a := a - H + 1) (b := a + N) (by omega)
    have hc : (S.card : ℤ) = (N : ℤ) + H - 1 := by dsimp [S]; linarith
    exact_mod_cast hc
  have h := norm_sum_sq_le_card_mul_sum_norm_sq S (shiftedSum f H)
  rw [hmass, henergy, hcard, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end
end RiemannGaussian.FiniteShiftCorrelation
