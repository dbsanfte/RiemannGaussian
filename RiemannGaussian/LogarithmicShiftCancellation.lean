/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FirstDerivativeTest
import RiemannGaussian.ZetaFiniteDifferencing

/-!
# Cancellation of the actual logarithmic overlap phase

The proved logarithmic derivatives discharge the first-derivative test on
every admissible dyadic block. If `t,h,X>0`, `h<=X` and `t*h<=pi*X^2`, a
block contained in `[X,2*X]` has shifted exponential sum bounded by
`12*pi*X^2/(t*h)`, independently of its length.

The same estimate is proved for the complete positive-shift correlation
of the original unweighted imaginary-axis Dirichlet feature, with exact
finite support. Prime and other arbitrary arithmetic weights remain a
separate estimation problem; no signed infinite-prime bound is asserted.
-/

namespace RiemannGaussian.LogarithmicShiftCancellation
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase FiniteShiftCorrelation FiniteVanDerCorputPhase
open scoped Classical

/-- The actual shifted logarithmic phase has cancellation on every
dyadic block in the nonresonant parameter range. All derivative hypotheses
are discharged from its explicit formula. -/
theorem bound {t h X a : ℝ} (ht : 0 < t) (hh : 0 < h) (hX : 0 < X)
    (hhX : h ≤ X) (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X)
    (hscale : t * h ≤ Real.pi * X ^ 2) :
    ‖∑ n ∈ Finset.range N, rotation (shift t h (a + n))‖ ≤
      12 * Real.pi * X ^ 2 / (t * h) := by
  let η : ℝ := t * h / (6 * X ^ 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hupper : t * h / X ^ 2 ≤ Real.pi := (div_le_iff₀ (sq_pos_of_pos hX)).mpr hscale
  have hηpi : η ≤ Real.pi := by
    apply le_trans (b := t * h / X ^ 2) _ hupper
    exact div_le_div_of_nonneg_left (mul_nonneg ht.le hh.le) (sq_pos_of_pos hX)
      (by nlinarith [sq_nonneg X])
  have hxpos {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) : 0 < x :=
    lt_of_lt_of_le hX (ha.trans hx.1)
  have hg := FirstDerivativeTest.bound (shift t h) (slope t h) a N hη
    (fun x hx ↦ hasDerivAt_shift t hh.le (hxpos hx))
    (fun x hx ↦ by
      have hbounds := slope_dyadic_bounds ht.le hh.le hX hhX (ha.trans hx.1) (hx.2.trans hb)
      exact ⟨hbounds.1, by linarith [hbounds.2]⟩)
    (Or.inr ((slope_antitoneOn ht.le hh.le).mono (fun _ hx ↦ hxpos hx)))
  calc
    _ ≤ 2 * Real.pi / η := hg
    _ = _ := by dsimp [η]; field_simp; ring

/-- The cancellation estimate in the exact ratio-phase form, without
replacing the logarithm by a Taylor approximation. -/
theorem log_ratio_bound {t h X a : ℝ} (ht : 0 < t) (hh : 0 < h) (hX : 0 < X)
    (hhX : h ≤ X) (ha : X ≤ a) (N : ℕ) (hb : a + N ≤ 2 * X)
    (hscale : t * h ≤ Real.pi * X ^ 2) :
    ‖∑ n ∈ Finset.range N,
      Complex.exp (((-t * Real.log (1 + h / (a + n)) : ℝ) : ℂ) * Complex.I)‖ ≤
        12 * Real.pi * X ^ 2 / (t * h) := by
  have he (n : ℕ) := shift_eq_log_one_add t hh.le
    (show 0 < a + n by linarith [Nat.cast_nonneg (α := ℝ) n])
  simpa only [he, PhaseIncrementInverse.rotation] using bound ht hh hX hhX ha N hb hscale

/-- The exact integer interval is reindexed by its original natural
offsets, with no dropped endpoints. -/
theorem integer_block_sum (a : ℤ) (N : ℕ) (f : ℤ → ℂ) :
    (∑ n ∈ Finset.Ico a (a + N), f n) = ∑ k ∈ Finset.range N, f (a + k) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  simp

/-- The literal original Dirichlet feature has the bounded logarithmic
correlation on every positive overlap. Its real damping is exactly one on
the imaginary axis, so no arithmetic amplitude is removed in this identity. -/
theorem unit_feature_pair (t : ℝ) {n h : ℤ} (hn : 0 < n) (hh : 0 ≤ h) :
    zetaPrimeFeature ((t : ℂ) * Complex.I) (n + h).toNat *
      starRingEnd ℂ (zetaPrimeFeature ((t : ℂ) * Complex.I) n.toNat) =
        rotation (shift t (h : ℝ) (n : ℝ)) := by
  simpa [ZetaFiniteDifferencing.amplitude, zetaPrimeExpWeight, PhaseIncrementInverse.rotation] using
    ZetaFiniteDifferencing.feature_shift_pair ((t : ℂ) * Complex.I) (fun _ ↦ 1) hn hh

/-- A genuine upper bound for the complete overlap correlation of the
original unweighted Dirichlet block. All cutoffs are exact, including
shifts beyond the end of the block, whose correlations vanish. -/
theorem dirichlet_correlation_bound {t X : ℝ} (ht : 0 < t) (hX : 0 < X)
    {a : ℤ} (ha : X ≤ (a : ℝ)) (N h : ℕ) (hh : 0 < h) (hhX : (h : ℝ) ≤ X)
    (hb : (a : ℝ) + N ≤ 2 * X) (hscale : t * h ≤ Real.pi * X ^ 2) :
    ‖correlation (windowed a N (fun n ↦ zetaPrimeFeature ((t : ℂ) * Complex.I) n.toNat))
      (h : ℤ)‖ ≤ 12 * Real.pi * X ^ 2 / (t * h) := by
  rw [correlation_windowed a N _ (show 0 ≤ (h : ℤ) by positivity)]
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have haZ : 0 < a := by exact_mod_cast lt_of_lt_of_le hX ha
  by_cases hhN : h ≤ N
  · have hend : a + (N : ℤ) - h = a + ((N - h : ℕ) : ℤ) := by omega
    rw [hend]
    have he : (∑ n ∈ Finset.Ico a (a + ((N - h : ℕ) : ℤ)),
        zetaPrimeFeature ((t : ℂ) * Complex.I) (n + h).toNat *
          starRingEnd ℂ (zetaPrimeFeature ((t : ℂ) * Complex.I) n.toNat)) =
        ∑ k ∈ Finset.range (N - h), rotation (shift t (h : ℝ) ((a : ℝ) + k)) := by
      calc
        _ = ∑ n ∈ Finset.Ico a (a + ((N - h : ℕ) : ℤ)),
            rotation (shift t (h : ℝ) (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact unit_feature_pair t (lt_of_lt_of_le haZ (Finset.mem_Ico.mp hn).1) (by positivity)
        _ = _ := by
          rw [integer_block_sum]
          simp only [Int.cast_add, Int.cast_natCast]
    rw [he]
    apply bound ht hhR hX hhX ha (N - h) _ hscale
    have hle : ((N - h : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N h
    linarith
  · rw [Finset.Ico_eq_empty (show ¬a < a + (N : ℤ) - h by omega), Finset.sum_empty, norm_zero]
    positivity

end
end RiemannGaussian.LogarithmicShiftCancellation
