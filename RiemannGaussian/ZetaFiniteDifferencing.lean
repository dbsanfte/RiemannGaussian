/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteVanDerCorputPhase
import RiemannGaussian.LogarithmicShiftPhase
import RiemannGaussian.ZetaPrimeMomentEnvelope
import RiemannGaussian.ZetaMultiplicativePhase

/-!
# Exact weighted differencing of the repository's Dirichlet features

The existing `zetaPrimeFeature` is split into its actual real damping and
logarithmic phase. The weighted van der Corput inequality then applies to
every literal finite positive integer block, keeping arbitrary complex
weights, the complete overlap products, and the signed phase difference.

The overlap phase is exactly `-Im(s)*log(1+h/n)`. Its derivatives are the
ones proved in `LogarithmicShiftPhase`. The weights may encode prime or
von Mangoldt support, but no estimate for their correlations is assumed or
deduced from the smoothness of the phase alone. This finite-block theorem
does not establish the independent signed infinite prime-tail bound.
-/

namespace RiemannGaussian.ZetaFiniteDifferencing
noncomputable section
open Complex FiniteVanDerCorputPhase LogarithmicShiftPhase
open scoped Classical

/-- The original arithmetic weight and the exact real Dirichlet damping.
Integer indexing is used for shifts; terminal blocks contain only positive
integers and hence the conversion to naturals is exact there. -/
def amplitude (s : ℂ) (w : ℕ → ℂ) (n : ℤ) : ℂ :=
  w n.toNat * (zetaPrimeExpWeight s.re n.toNat : ℂ)

/-- The logarithmic phase used by differencing is exactly the unit
phase already retained in the repository's multiplicative matrix transport. -/
theorem phase_eq_multiplicative (t x : ℝ) :
    Complex.exp (((phase t x : ℝ) : ℂ) * Complex.I) = MultiplicativePhase.phase t x := by
  unfold phase MultiplicativePhase.phase
  congr 1
  push_cast
  ring

/-- The existing Dirichlet feature has its exact radial-phase split. -/
theorem feature_polar (s : ℂ) (n : ℕ) :
    zetaPrimeFeature s n = (zetaPrimeExpWeight s.re n : ℂ) *
      Complex.exp (((phase s.im (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [zetaPrimeFeature, zetaPrimeExpWeight, phase, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- The weighted feature is the same complex term used by the general
phase inequality; this is an identity before taking a norm. -/
theorem weighted_feature_eq (s : ℂ) (w : ℕ → ℂ) (n : ℤ) :
    w n.toNat * zetaPrimeFeature s n.toNat =
      phaseTerm (amplitude s w) (fun k ↦ phase s.im (k.toNat : ℝ)) n := by
  rw [feature_polar]
  exact (mul_assoc _ _ _).symm

/-- The norm of the complete weighted feature is its actual damped
amplitude, as used in the diagonal energy of the differencing inequality. -/
theorem norm_weighted_feature (s : ℂ) (w : ℕ → ℂ) (n : ℤ) :
    ‖w n.toNat * zetaPrimeFeature s n.toNat‖ = ‖amplitude s w n‖ := by
  rw [weighted_feature_eq, norm_phaseTerm]

/-- The amplitude norm keeps the original weight and exact radial decay. -/
theorem norm_amplitude (s : ℂ) (w : ℕ → ℂ) (n : ℤ) :
    ‖amplitude s w n‖ = ‖w n.toNat‖ * zetaPrimeExpWeight s.re n.toNat := by
  rw [amplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    zetaPrimeExpWeight, abs_of_pos (Real.exp_pos _)]

private theorem cast_toNat {n : ℤ} (hn : 0 ≤ n) : (n.toNat : ℝ) = (n : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hn

/-- The full complex product of two shifted original features retains
the actual logarithmic phase difference and both weighted amplitudes. -/
theorem feature_shift_pair (s : ℂ) (w : ℕ → ℂ) {n h : ℤ}
    (hn : 0 < n) (hh : 0 ≤ h) :
    (w (n + h).toNat * zetaPrimeFeature s (n + h).toNat) *
      starRingEnd ℂ (w n.toNat * zetaPrimeFeature s n.toNat) =
        (amplitude s w (n + h) * starRingEnd ℂ (amplitude s w n)) *
          Complex.exp (((shift s.im (h : ℝ) (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [weighted_feature_eq, weighted_feature_eq, phaseTerm_pair]
  congr 2
  rw [cast_toNat (show 0 ≤ n + h by omega), cast_toNat hn.le]
  simp only [shift, Int.cast_add]

/-- On the genuine positive overlap, the phase is the logarithm of
`1+h/n`, with no Taylor approximation or singular endpoint. -/
theorem feature_shift_pair_log (s : ℂ) (w : ℕ → ℂ) {n h : ℤ}
    (hn : 0 < n) (hh : 0 ≤ h) :
    (w (n + h).toNat * zetaPrimeFeature s (n + h).toNat) *
      starRingEnd ℂ (w n.toNat * zetaPrimeFeature s n.toNat) =
        (amplitude s w (n + h) * starRingEnd ℂ (amplitude s w n)) *
          Complex.exp (((-s.im * Real.log (1 + (h : ℝ) / (n : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  rw [feature_shift_pair s w hn hh, shift_eq_log_one_add]
  · exact_mod_cast hh
  · exact_mod_cast hn

/-- The complete finite overlap is rewritten into the actual damped
weights and shifted logarithmic phase. Even empty overlaps are exact. -/
theorem overlap_eq (s : ℂ) (w : ℕ → ℂ) {a : ℤ} (ha : 0 < a) (N k : ℕ) :
    (∑ n ∈ Finset.Ico a (a + N - ((k : ℤ) + 1)),
      (w (n + ((k : ℤ) + 1)).toNat * zetaPrimeFeature s (n + ((k : ℤ) + 1)).toNat) *
        starRingEnd ℂ (w n.toNat * zetaPrimeFeature s n.toNat)) =
      ∑ n ∈ Finset.Ico a (a + N - ((k : ℤ) + 1)),
        (amplitude s w (n + ((k : ℤ) + 1)) * starRingEnd ℂ (amplitude s w n)) *
          Complex.exp (((shift s.im ((k : ℝ) + 1) (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : 0 < n := lt_of_lt_of_le ha (Finset.mem_Ico.mp hn).1
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
    feature_shift_pair s w hn' (show 0 ≤ (k : ℤ) + 1 by omega)

/-- Signed van der Corput for literal weighted Dirichlet features on
every finite positive block. The real correlation is retained before the
usual absolute-value estimate. -/
theorem signed_bound (s : ℂ) (w : ℕ → ℂ) {a : ℤ} (ha : 0 < a)
    (N : ℕ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N),
      w n.toNat * zetaPrimeFeature s n.toNat‖ ^ 2 ≤
        ((N : ℝ) + H - 1) * ((H : ℝ) *
          (∑ n ∈ Finset.Ico a (a + N), ‖amplitude s w n‖ ^ 2) +
            2 * ∑ k ∈ Finset.range H, ((H : ℝ) - k - 1) *
              (∑ n ∈ Finset.Ico a (a + N - ((k : ℤ) + 1)),
                (amplitude s w (n + ((k : ℤ) + 1)) * starRingEnd ℂ (amplitude s w n)) *
                  Complex.exp (((shift s.im ((k : ℝ) + 1) (n : ℝ) : ℝ) : ℂ) * Complex.I)).re) := by
  simpa only [norm_weighted_feature, overlap_eq s w ha] using
    signed_window_bound a N (fun n ↦ w n.toNat * zetaPrimeFeature s n.toNat) hH

/-- The absolute-correlation estimate for the same original weighted
Dirichlet block. Its arithmetic correlations still require their own bound. -/
theorem absolute_bound (s : ℂ) (w : ℕ → ℂ) {a : ℤ} (ha : 0 < a)
    (N : ℕ) {H : ℕ} (hH : 0 < H) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N),
      w n.toNat * zetaPrimeFeature s n.toNat‖ ^ 2 ≤
        ((N : ℝ) + H - 1) * ((H : ℝ) *
          (∑ n ∈ Finset.Ico a (a + N), ‖amplitude s w n‖ ^ 2) +
            2 * ∑ k ∈ Finset.range H, ((H : ℝ) - k - 1) *
              ‖∑ n ∈ Finset.Ico a (a + N - ((k : ℤ) + 1)),
                (amplitude s w (n + ((k : ℤ) + 1)) * starRingEnd ℂ (amplitude s w n)) *
                  Complex.exp (((shift s.im ((k : ℝ) + 1) (n : ℝ) : ℝ) : ℂ) * Complex.I)‖) := by
  simpa only [norm_weighted_feature, overlap_eq s w ha] using
    absolute_window_bound a N (fun n ↦ w n.toNat * zetaPrimeFeature s n.toNat) hH

end
end RiemannGaussian.ZetaFiniteDifferencing
