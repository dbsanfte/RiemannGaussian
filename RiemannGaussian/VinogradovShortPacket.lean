/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiProperPrimePowerWork
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A fixed-width prime packet with explicit size conditions

The existing Suzuki proper-prime-power bound and Chebyshev estimates give
at least R primes in (M,8M] whenever M>=4096 and M>=9R^2. This replaces
an iterated-Bertrand packet's exponential width by a constant width,
with an explicit polynomial starting scale. All primes are actual natural
primes, and a finite subset has exactly the requested cardinality.
-/

namespace RiemannGaussian.VinogradovShortPacket
open scoped BigOperators

/-- An elementary logarithm bound keeps the prime-count threshold polynomial. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_self (Real.sqrt_nonneg x)
  rw [Real.log_sqrt hx] at h
  linarith

/-- The actual prime log mass in the eightfold interval is at least twice its base. -/
theorem theta_eight_mul_sub {M : ℝ} (hM : 4096 ≤ M) :
    2 * M ≤ Chebyshev.theta (8 * M) - Chebyshev.theta M := by
  have hM0 : 0 ≤ M := by linarith
  have h8M : 1 ≤ 8 * M := by linarith
  have hpsi := Chebyshev.psi_ge' (x := 8 * M) (by linarith : 0 ≤ 8 * M)
  have hproper := chebyshevPsi_sub_theta_le_eighteen_sqrt h8M
  have htheta := Chebyshev.theta_le_log4_mul_x hM0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at htheta
  have hs : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0
  have hs0 := Real.sqrt_nonneg M
  have hs64 : 64 ≤ Real.sqrt M := (Real.le_sqrt (by norm_num) hM0).mpr (by nlinarith)
  have h8root : Real.sqrt (8 * M) ≤ 3 * Real.sqrt M :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hplusroot : Real.sqrt (8 * M + 2) ≤ 3 * Real.sqrt M :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hlog := Real.log_le_self (Real.sqrt_nonneg (8 * M + 2))
  rw [Real.log_sqrt (by linarith : 0 ≤ 8 * M + 2)] at hlog
  have h2 := Real.log_two_gt_d9
  have h2upper := Real.log_two_lt_d9
  have hproduct := mul_nonneg (show 0 ≤ 6 * M by positivity)
    (show 0 ≤ Real.log 2 - 1 / 2 by linarith)
  nlinarith [mul_nonneg hs0 (show 0 ≤ Real.sqrt M - 64 by linarith)]

/-- Every prescribed packet cardinality fits in the fixed-ratio interval
once the displayed numerical and quadratic thresholds hold. -/
theorem exists_short_packet (M R : ℕ) (hM : 4096 ≤ M) (hR : 9 * R ^ 2 ≤ M) :
    ∃ π : Finset ℕ, π.card = R ∧ ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ 8 * M := by
  classical
  let π := Nat.primesLE (8 * M) \ Nat.primesLE M
  have hmem {p : ℕ} (hp : p ∈ π) : p.Prime ∧ M < p ∧ p ≤ 8 * M := by
    simp only [π, Finset.mem_sdiff, Nat.mem_primesLE] at hp
    have hlo : ¬p ≤ M := fun h => hp.2 ⟨h, hp.1.2⟩
    exact ⟨hp.1.2, by omega, hp.1.1⟩
  have hsum : (∑ p ∈ π, Real.log p) =
      Chebyshev.theta (8 * (M : ℝ)) - Chebyshev.theta M := by
    have ht := Chebyshev.theta_eq_sum_primesLE_log (8 * M)
    push_cast at ht
    rw [ht, Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (by omega : M ≤ 8 * M))
  have hmass : 2 * (M : ℝ) ≤ ∑ p ∈ π, Real.log p := by
    rw [hsum]
    exact theta_eight_mul_sub (by exact_mod_cast hM)
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hs := Real.sq_sqrt hM0
  have hs0 : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < M by omega))
  have h8root : Real.sqrt (8 * (M : ℝ)) ≤ 3 * Real.sqrt M :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hlog : Real.log (8 * (M : ℝ)) ≤ 6 * Real.sqrt M := by
    have h := log_le_two_sqrt (show 0 ≤ 8 * (M : ℝ) by positivity)
    linarith
  have hup : (∑ p ∈ π, Real.log p) ≤ (π.card : ℝ) * (6 * Real.sqrt M) := by
    calc
      _ ≤ ∑ _p ∈ π, 6 * Real.sqrt M := by
        apply Finset.sum_le_sum
        intro p hp
        have h := hmem hp
        exact (Real.log_le_log (by exact_mod_cast h.1.pos)
          (by exact_mod_cast h.2.2)).trans hlog
      _ = _ := by simp
  have hsc : Real.sqrt (M : ℝ) ≤ 3 * (π.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * Real.sqrt (M : ℝ) by positivity)).mp
    nlinarith
  have hRs : 3 * (R : ℝ) ≤ Real.sqrt M :=
    (Real.le_sqrt (by positivity) hM0).mpr (by
      have h : 9 * (R : ℝ) ^ 2 ≤ M := by exact_mod_cast hR
      nlinarith)
  have hcard : R ≤ π.card := by exact_mod_cast (show (R : ℝ) ≤ π.card by linarith)
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨P, hPc, fun p hp => hmem (hP hp)⟩

end RiemannGaussian.VinogradovShortPacket
