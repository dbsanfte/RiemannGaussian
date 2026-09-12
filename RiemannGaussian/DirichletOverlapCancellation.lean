/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.LogarithmicShiftCancellation
import RiemannGaussian.FiniteAbelVariation

/-!
# Cancellation of complete damped Dirichlet overlap correlations

The real damping in a shifted Dirichlet product is positive and decreasing
when `Re(s)>=0`. Exact finite Abel transport therefore carries the proved
logarithmic cancellation bound to the whole overlap with only its initial
damping as cost. The terminal theorem bounds the original complex
`zetaPrimeFeature` correlation at every admissible positive shift, retaining
all finite cutoffs and the actual real exponent.

These bounds concern ordinary Dirichlet coefficients equal to one. Extra
prime, sieve or polynomial weights require their own variation or arithmetic
estimate. The signed infinite-prime lower bound is not obtained here.
-/

namespace RiemannGaussian.DirichletOverlapCancellation
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase FiniteShiftCorrelation FiniteVanDerCorputPhase
open scoped Classical

/-- The exact real damping in a product of two shifted Dirichlet terms. -/
def damping (σ h x : ℝ) : ℝ := Real.exp (-σ * (Real.log (x + h) + Real.log x))

/-- The damping is strictly positive, so Abel transport retains its
original sign. -/
theorem damping_pos (σ h x : ℝ) : 0 < damping σ h x := Real.exp_pos _

/-- Nonnegative real exponents make the exact overlap damping decrease
throughout the genuine positive domain. -/
theorem damping_antitoneOn {σ h : ℝ} (hσ : 0 ≤ σ) (hh : 0 ≤ h) :
    AntitoneOn (damping σ h) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  unfold damping
  apply Real.exp_le_exp.mpr
  have hl := add_le_add (Real.log_le_log (show 0 < x + h by positivity)
    (show x + h ≤ y + h by linarith)) (Real.log_le_log hx hxy)
  exact mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr hσ)

/-- The original full complex Dirichlet pair factors into exactly its
real damping and its logarithmic phase difference on the positive overlap. -/
theorem feature_pair (s : ℂ) {n h : ℤ} (hn : 0 < n) (hh : 0 ≤ h) :
    zetaPrimeFeature s (n + h).toNat * starRingEnd ℂ (zetaPrimeFeature s n.toNat) =
      (damping s.re (h : ℝ) (n : ℝ) : ℂ) * rotation (shift s.im (h : ℝ) (n : ℝ)) := by
  have hp := ZetaFiniteDifferencing.feature_shift_pair s (fun _ ↦ 1) hn hh
  simp only [ZetaFiniteDifferencing.amplitude, one_mul, Complex.conj_ofReal,
    ← Complex.ofReal_mul, zetaPrimeExpWeight, ← Real.exp_add] at hp
  have hncast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
  have hmcast : ((n + h).toNat : ℝ) = ((n + h : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ n + h by omega)
  rw [hncast, hmcast, Int.cast_add] at hp
  have he : -s.re * Real.log ((n : ℝ) + h) + -s.re * Real.log (n : ℝ) =
      -s.re * (Real.log ((n : ℝ) + h) + Real.log (n : ℝ)) := by ring
  rw [he] at hp
  exact hp

/-- Cancellation survives the entire actual damping on an admissible
block, with the initial damping as the only Abel cost. -/
theorem damped_block_bound {σ t h X a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (hh : 0 < h) (hX : 0 < X) (hhX : h ≤ X) (ha : X ≤ a)
    (N : ℕ) (hb : a + N ≤ 2 * X) (hscale : t * h ≤ Real.pi * X ^ 2) :
    ‖∑ n ∈ Finset.range N,
      (damping σ h (a + n) : ℂ) * rotation (shift t h (a + n))‖ ≤
        (12 * Real.pi * X ^ 2 / (t * h)) * damping σ h a := by
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg (by positivity) (damping_pos σ h a).le
  | succ N =>
    have hw : ∀ n ≤ N, 0 ≤ damping σ h (a + n) := fun n _ ↦ (damping_pos _ _ _).le
    have hm : AntitoneOn (fun n : ℕ ↦ damping σ h (a + n)) (Set.Icc 0 N) := by
      intro i hi j hj hij
      apply damping_antitoneOn hσ hh.le
      · change 0 < a + (i : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) i]
      · change 0 < a + (j : ℝ)
        linarith [Nat.cast_nonneg (α := ℝ) j]
      · have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
    have hp (n : ℕ) (hn : n ≤ N) :
        ‖∑ k ∈ Finset.range (n + 1), rotation (shift t h (a + k))‖ ≤
          12 * Real.pi * X ^ 2 / (t * h) := by
      apply LogarithmicShiftCancellation.bound ht hh hX hhX ha (n + 1) _ hscale
      have hnn : (n : ℝ) ≤ N := by exact_mod_cast hn
      push_cast at hb ⊢
      linarith
    simpa only [Nat.cast_zero, add_zero] using
      FiniteAbelVariation.decreasing_bound (fun n ↦ damping σ h (a + n))
        (fun n ↦ rotation (shift t h (a + n))) N hw hm hp

/-- A genuine bound for the complete original Dirichlet correlation
at every nonnegative real exponent and admissible positive shift. The
original overlap is retained, including empty overlaps beyond the block. -/
theorem correlation_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) {a : ℤ} (ha : X ≤ (a : ℝ)) (N h : ℕ)
    (hh : 0 < h) (hhX : (h : ℝ) ≤ X) (hb : (a : ℝ) + N ≤ 2 * X)
    (hscale : s.im * h ≤ Real.pi * X ^ 2) :
    ‖correlation (windowed a N (fun n ↦ zetaPrimeFeature s n.toNat)) (h : ℤ)‖ ≤
      (12 * Real.pi * X ^ 2 / (s.im * h)) * damping s.re (h : ℝ) (a : ℝ) := by
  rw [correlation_windowed a N _ (show 0 ≤ (h : ℤ) by positivity)]
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have haZ : 0 < a := by exact_mod_cast lt_of_lt_of_le hX ha
  by_cases hhN : h ≤ N
  · have hend : a + (N : ℤ) - h = a + ((N - h : ℕ) : ℤ) := by omega
    rw [hend]
    have he : (∑ n ∈ Finset.Ico a (a + ((N - h : ℕ) : ℤ)),
        zetaPrimeFeature s (n + h).toNat * starRingEnd ℂ (zetaPrimeFeature s n.toNat)) =
        ∑ k ∈ Finset.range (N - h),
          (damping s.re (h : ℝ) ((a : ℝ) + k) : ℂ) *
            rotation (shift s.im (h : ℝ) ((a : ℝ) + k)) := by
      calc
        _ = ∑ n ∈ Finset.Ico a (a + ((N - h : ℕ) : ℤ)),
            (damping s.re (h : ℝ) (n : ℝ) : ℂ) * rotation (shift s.im (h : ℝ) (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact feature_pair s (lt_of_lt_of_le haZ (Finset.mem_Ico.mp hn).1) (by positivity)
        _ = _ := by
          rw [LogarithmicShiftCancellation.integer_block_sum]
          simp only [Int.cast_add, Int.cast_natCast]
    rw [he]
    apply damped_block_bound hσ ht hhR hX hhX ha (N - h) _ hscale
    have hle : ((N - h : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N h
    linarith
  · rw [Finset.Ico_eq_empty (show ¬a < a + (N : ℤ) - h by omega), Finset.sum_empty, norm_zero]
    exact mul_nonneg (by positivity) (damping_pos _ _ _).le

/-- The proved overlap cancellation bounds every correlation in the
original finite van der Corput inequality. This is an independent upper
bound for the complete Dirichlet block in the stated nonresonant regime,
with the exact diagonal, shift weights and initial damping retained. -/
theorem vanDerCorput_bound {s : ℂ} (hσ : 0 ≤ s.re) (ht : 0 < s.im)
    {X : ℝ} (hX : 0 < X) {a : ℤ} (ha : X ≤ (a : ℝ)) (N H : ℕ)
    (hH : 0 < H) (hHX : (H : ℝ) ≤ X) (hb : (a : ℝ) + N ≤ 2 * X)
    (hscale : s.im * H ≤ Real.pi * X ^ 2) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ico a (a + N), zetaPrimeFeature s n.toNat‖ ^ 2 ≤
      ((N : ℝ) + H - 1) * ((H : ℝ) *
        (∑ n ∈ Finset.Ico a (a + N), ‖zetaPrimeFeature s n.toNat‖ ^ 2) +
          2 * ∑ k ∈ Finset.range H, ((H : ℝ) - k - 1) *
            ((12 * Real.pi * X ^ 2 / (s.im * ((k : ℝ) + 1))) *
              damping s.re ((k : ℝ) + 1) (a : ℝ))) := by
  have hv := FiniteVanDerCorput.absolute_bound hH
    (windowed_outside a N (fun n ↦ zetaPrimeFeature s n.toNat))
  rw [sum_windowed, energy_windowed] at hv
  apply hv.trans
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast Nat.succ_le_iff.mpr hH
  apply mul_le_mul_of_nonneg_left _
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : 0 ≤ (N : ℝ) + H - 1)
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro k hk
  have hkr : (k : ℝ) + 1 ≤ H := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
  have hkX : ((k + 1 : ℕ) : ℝ) ≤ X := by push_cast; linarith
  have hkscale : s.im * (k + 1 : ℕ) ≤ Real.pi * X ^ 2 := by
    push_cast
    exact (mul_le_mul_of_nonneg_left hkr ht.le).trans hscale
  have hc := correlation_bound hσ ht hX ha N (k + 1) (by omega) hkX hb hkscale
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ (H : ℝ) - k - 1)
  simpa only [Nat.cast_add, Nat.cast_one] using hc

end
end RiemannGaussian.DirichletOverlapCancellation
