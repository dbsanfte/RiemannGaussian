/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteVanDerCorput
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Van der Corput on exact finite overlaps and weighted phases

Zero extension turns a literal integer interval into a finitely supported
sequence. Its positive-shift correlation is exactly the original overlap
interval, with no periodic wrapping or discarded boundary. The resulting
van der Corput inequalities allow arbitrary complex amplitudes.

For oscillatory terms the complete correlation retains the differenced
phase and both components of the amplitude product. The signed inequality
is available before replacing a correlation by its norm. These are finite
identities and bounds, not an unproved cancellation estimate.
-/

namespace RiemannGaussian.FiniteVanDerCorputPhase
noncomputable section
open Complex FiniteShiftCorrelation
open scoped Classical

/-- The literal integer block extended by zero on its complement. -/
def windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ∈ Finset.Ico a (a + N) then b n else 0

/-- The zero extension has finite support, regardless of the amplitude. -/
theorem finite_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    Function.HasFiniteSupport (windowed a N b) :=
  (Finset.Ico a (a + N)).finite_toSet.subset (by
    intro n hn
    by_contra h
    exact hn (if_neg h))

/-- Every original summand is unchanged inside the block. -/
theorem windowed_on (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {n : ℤ}
    (hn : n ∈ Finset.Ico a (a + N)) : windowed a N b n = b n := by
  simp only [windowed, if_pos hn]

/-- The extension vanishes at every point outside the actual block. -/
theorem windowed_outside (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    ∀ n ∉ Finset.Ico a (a + N), windowed a N b n = 0 := by
  intro n hn
  simp only [windowed, if_neg hn]

/-- The finite sum of the extension is the original finite sum. -/
theorem sum_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), windowed a N b n) =
      ∑ n ∈ Finset.Ico a (a + N), b n :=
  Finset.sum_congr rfl (fun _ hn ↦ windowed_on a N b hn)

/-- The diagonal energy is exactly the original amplitude energy. -/
theorem energy_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), ‖windowed a N b n‖ ^ 2) =
      ∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2 :=
  Finset.sum_congr rfl (fun _ hn ↦ by rw [windowed_on a N b hn])

/-- A positive shift retains precisely the complete overlap. If the
shift exceeds the block length, the interval and correlation are empty. -/
theorem correlation_windowed (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {h : ℤ} (hh : 0 ≤ h) :
    correlation (windowed a N b) h =
      ∑ n ∈ Finset.Ico a (a + N - h), b (n + h) * starRingEnd ℂ (b n) := by
  calc
    _ = ∑ n ∈ Finset.Ico a (a + N - h),
        windowed a N b (n + h) * starRingEnd ℂ (windowed a N b n) := by
      apply tsum_eq_sum
      intro n hn
      by_cases hb : n ∈ Finset.Ico a (a + N)
      · have hs : n + h ∉ Finset.Ico a (a + N) := by
          simp only [Finset.mem_Ico] at hb hn ⊢
          omega
        simp only [windowed, if_neg hs, zero_mul]
      · simp only [windowed, if_neg hb, map_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hb : n ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      have hs : n + h ∈ Finset.Ico a (a + N) := by
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      rw [windowed_on a N b hb, windowed_on a N b hs]

/-- Signed van der Corput for the original finite block, with every
overlap and its complex summands displayed explicitly. -/
theorem signed_window_bound (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), b n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          (∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            b (n + ((h : ℤ) + 1)) * starRingEnd ℂ (b n)).re) := by
  have h := FiniteVanDerCorput.signed_bound hH (windowed_outside a N b)
  rw [sum_windowed, energy_windowed] at h
  have hc (k : ℕ) := correlation_windowed a N b (h := (k : ℤ) + 1) (by omega)
  simpa only [hc] using h

/-- Absolute correlations may be used downstream without altering the
finite overlap intervals or the original complex amplitude sequence. -/
theorem absolute_window_bound (a : ℤ) (N : ℕ) (b : ℤ → ℂ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), b n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖b n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            b (n + ((h : ℤ) + 1)) * starRingEnd ℂ (b n)‖) := by
  have h := FiniteVanDerCorput.absolute_bound hH (windowed_outside a N b)
  rw [sum_windowed, energy_windowed] at h
  have hc (k : ℕ) := correlation_windowed a N b (h := (k : ℤ) + 1) (by omega)
  simpa only [hc] using h

/-- A complete oscillatory term with arbitrary complex amplitude. -/
def phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) : ℂ :=
  w n * Complex.exp ((φ n : ℂ) * Complex.I)

/-- The phase has unit norm, so the diagonal retains exactly the
original amplitude energy. -/
theorem norm_phaseTerm (w : ℤ → ℂ) (φ : ℤ → ℝ) (n : ℤ) :
    ‖phaseTerm w φ n‖ = ‖w n‖ := by
  rw [phaseTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The complete complex product exposes the phase difference without
discarding either component of the amplitude correlation. -/
theorem phaseTerm_pair (w : ℤ → ℂ) (φ : ℤ → ℝ) (n h : ℤ) :
    phaseTerm w φ (n + h) * starRingEnd ℂ (phaseTerm w φ n) =
      (w (n + h) * starRingEnd ℂ (w n)) *
        Complex.exp (((φ (n + h) - φ n : ℝ) : ℂ) * Complex.I) := by
  simp only [phaseTerm, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The signed product contains both a cosine and a sine channel when
the amplitude itself is complex. Neither channel is silently discarded. -/
theorem phaseTerm_pair_re (w : ℤ → ℂ) (φ : ℤ → ℝ) (n h : ℤ) :
    (phaseTerm w φ (n + h) * starRingEnd ℂ (phaseTerm w φ n)).re =
      (w (n + h) * starRingEnd ℂ (w n)).re * Real.cos (φ (n + h) - φ n) -
        (w (n + h) * starRingEnd ℂ (w n)).im * Real.sin (φ (n + h) - φ n) := by
  rw [phaseTerm_pair, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- Real amplitudes retain their signs in the cosine correlation. -/
theorem real_phaseTerm_pair_re (w : ℤ → ℝ) (φ : ℤ → ℝ) (n h : ℤ) :
    (phaseTerm (fun k ↦ (w k : ℂ)) φ (n + h) *
      starRingEnd ℂ (phaseTerm (fun k ↦ (w k : ℂ)) φ n)).re =
        w (n + h) * w n * Real.cos (φ (n + h) - φ n) := by
  rw [phaseTerm_pair_re]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Signed weighted differencing, retaining the actual phase difference
at every point of every finite overlap. -/
theorem signed_phase_bound (a : ℤ) (N : ℕ) (w : ℤ → ℂ) (φ : ℤ → ℝ)
    {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), phaseTerm w φ n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖w n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          (∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            (w (n + ((h : ℤ) + 1)) * starRingEnd ℂ (w n)) *
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)).re) := by
  simpa only [norm_phaseTerm, phaseTerm_pair] using
    signed_window_bound a N (phaseTerm w φ) hH

/-- The weighted absolute differencing inequality follows from the
same exact phase products, with no bound assumed on the amplitudes. -/
theorem absolute_phase_bound (a : ℤ) (N : ℕ) (w : ℤ → ℂ) (φ : ℤ → ℝ)
    {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), phaseTerm w φ n‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) * (∑ n ∈ Finset.Ico a (a + N), ‖w n‖ ^ 2) +
        2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
          ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
            (w (n + ((h : ℤ) + 1)) * starRingEnd ℂ (w n)) *
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  simpa only [norm_phaseTerm, phaseTerm_pair] using
    absolute_window_bound a N (phaseTerm w φ) hH

/-- The classical unweighted differencing inequality, with exactly
`N` diagonal terms and the original finite positive-shift overlaps. -/
theorem unit_phase_bound (a : ℤ) (N : ℕ) (φ : ℤ → ℝ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N),
      Complex.exp ((φ n : ℂ) * Complex.I)‖ ^ 2 ≤
        ((N : ℝ) + H - 1) * ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ((H : ℝ) - h - 1) *
            ‖∑ n ∈ Finset.Ico a (a + N - ((h : ℤ) + 1)),
              Complex.exp (((φ (n + ((h : ℤ) + 1)) - φ n : ℝ) : ℂ) * Complex.I)‖) := by
  have hc : (Finset.Ico a (a + N)).card = N := by
    rw [Int.card_Ico]
    simp
  simpa only [phaseTerm, map_one, one_mul, norm_one, one_pow,
    Finset.sum_const, hc, nsmul_eq_mul, mul_one] using
      absolute_phase_bound a N (fun _ ↦ 1) φ hH

end
end RiemannGaussian.FiniteVanDerCorputPhase
