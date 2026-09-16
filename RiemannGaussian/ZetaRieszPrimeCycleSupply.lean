/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTentSlope
import RiemannGaussian.ZetaRieszTransportPhase

/-!
# Actual signed arithmetic supply at prime insertions

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszPrimeCycleSupply
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy

/-- The actual quarter-slope error for replacing one prime on a shared
composite squarefree cofactor. -/
def primeProfileError (p q n : ℕ) : ℝ :=
  |Real.log p - Real.log q| / 4 *
    ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|

/-- A local arithmetic error is always nonnegative. -/
theorem primeProfileError_nonneg (p q n : ℕ) : 0 ≤ primeProfileError p q n := by
  unfold primeProfileError
  positivity

/-- The second inserted-prime profile has a proved absolute supply
lower bound from the first, with the whole cofactor error retained. -/
theorem abs_riesz_prime_ge_margin (L : ℝ) {p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    max 0 (|VaughanLogAverage.riesz L (p * n)| - primeProfileError p q n) ≤
      |VaughanLogAverage.riesz L (q * n)| := by
  have he := ZetaRieszTentSlope.abs_riesz_prime_difference_quarter L hp hq hpn hqn hn hcard
  have ht := abs_add_le (VaughanLogAverage.riesz L (p * n) - VaughanLogAverage.riesz L (q * n))
    (VaughanLogAverage.riesz L (q * n))
  rw [sub_add_cancel] at ht
  exact max_le (abs_nonneg _) (by change _ ≤ primeProfileError p q n at he; linarith)

/-- A strict arithmetic margin forces the two actual inserted-prime
profiles to keep the same nonzero sign. -/
theorem riesz_prime_sign_stable (L : ℝ) {p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hm : primeProfileError p q n < |VaughanLogAverage.riesz L (p * n)|) :
    0 < VaughanLogAverage.riesz L (p * n) * VaughanLogAverage.riesz L (q * n) := by
  have he := (ZetaRieszTentSlope.abs_riesz_prime_difference_quarter L hp hq hpn hqn hn hcard).trans_lt hm
  rcases le_or_gt 0 (VaughanLogAverage.riesz L (p * n)) with h | h
  · rw [abs_of_nonneg h, abs_lt] at he
    have hp0 : 0 < VaughanLogAverage.riesz L (p * n) := by
      rw [abs_of_nonneg h] at hm
      exact (primeProfileError_nonneg p q n).trans_lt hm
    have hq0 : 0 < VaughanLogAverage.riesz L (q * n) := by linarith [he.2]
    exact mul_pos hp0 hq0
  · rw [abs_of_neg h, abs_lt] at he
    have hq0 : VaughanLogAverage.riesz L (q * n) < 0 := by linarith [he.1]
    exact mul_pos_of_neg_of_neg h hq0

/-- The positive unfiltered amplitude at its actual integer and order. -/
def positiveBandAmplitude (L : ℝ) (N n : ℕ) : ℝ :=
  Real.log n / L * Real.exp (-(3 / 2 : ℝ) * Real.log n) *
    (Real.log n) ^ N / N.factorial

/-- The literal factorial amplitude is positive on every nonunit
positive integer, for all orders and every positive cutoff. -/
theorem positiveBandAmplitude_pos {L : ℝ} (hL : 0 < L) (N : ℕ) {n : ℕ}
    (hn : 1 < n) : 0 < positiveBandAmplitude L N n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log n := Real.log_pos hnR
  unfold positiveBandAmplitude
  positivity

/-- The real original mass is exactly minus the positive amplitude times
its signed Riesz profile, on the actual squarefree composite band. -/
theorem realBandOne_eq_profile {L : ℝ} {N n : ℕ}
    (hb : n ∈ zetaPrimeLogBand N) (hs : Squarefree n ∧ ¬ n.Prime) :
    realBandOne L N n = -positiveBandAmplitude L N n * VaughanLogAverage.riesz L n := by
  rw [realBandOne, if_pos hb, SquarefreeVaughanLogSource.coefficient, if_pos hs,
    Complex.ofReal_re]
  unfold positiveBandAmplitude
  ring

/-- Every actual unfiltered carrier norm has its complete nonnegative
amplitude times the absolute signed Riesz profile. -/
theorem norm_bandWeight_one_eq_profile {L : ℝ} (hL : 0 < L) {N n : ℕ} (t : ℝ)
    (hn : 1 < n) (hb : n ∈ zetaPrimeLogBand N) (hs : Squarefree n ∧ ¬ n.Prime) :
    ‖bandWeight L 1 N t n‖ = positiveBandAmplitude L N n * |VaughanLogAverage.riesz L n| := by
  rw [bandWeight_one_eq_signed_phase, norm_mul, ZetaArithmeticBandCorrelation.norm_unitPhase,
    mul_one, Complex.norm_real, Real.norm_eq_abs, realBandOne_eq_profile hb hs,
    abs_mul, abs_neg, abs_of_pos (positiveBandAmplitude_pos hL N hn)]

/-- The actual squarefree composite cofactor discharges nonunit and
composite-support obligations after a new prime insertion. -/
theorem prime_inserted_support {q n : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    1 < q * n ∧ Squarefree (q * n) ∧ ¬ (q * n).Prime := by
  have hn1 : n ≠ 1 := by intro he; subst n; simp at hcard
  have hn0 := hn.ne_zero
  have hn2 : 2 ≤ n := by omega
  have hq2 := hq.two_le
  exact ⟨by nlinarith, (Nat.squarefree_mul (hq.coprime_iff_not_dvd.mpr hqn)).mpr ⟨hq.squarefree, hn⟩,
    Nat.not_prime_mul hq.ne_one hn1⟩

/-- The quarter-slope arithmetic margin gives a quantitative lower bound
for the actual original partner mass, including its factorial envelope. -/
theorem norm_prime_partner_ge_margin {L : ℝ} (hL : 0 < L) {N p q n : ℕ} (t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hb : q * n ∈ zetaPrimeLogBand N) :
    positiveBandAmplitude L N (q * n) *
      max 0 (|VaughanLogAverage.riesz L (p * n)| - primeProfileError p q n) ≤
        ‖bandWeight L 1 N t (q * n)‖ := by
  obtain ⟨hq1, hs⟩ := prime_inserted_support hq hqn hn hcard
  rw [norm_bandWeight_one_eq_profile hL t hq1 hb hs]
  exact mul_le_mul_of_nonneg_left (abs_riesz_prime_ge_margin L hp hq hpn hqn hn hcard)
    (positiveBandAmplitude_pos hL N hq1).le


/-- The strict profile margin also preserves the sign of the actual
factorial-weighted carrier amplitudes, at arbitrary moment order. -/
theorem actual_prime_sign_stable {L : ℝ} (hL : 0 < L) {N p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hm : primeProfileError p q n < |VaughanLogAverage.riesz L (p * n)|) :
    0 < realBandOne L N (p * n) * realBandOne L N (q * n) := by
  obtain ⟨hp1, hps⟩ := prime_inserted_support hp hpn hn hcard
  obtain ⟨hq1, hqs⟩ := prime_inserted_support hq hqn hn hcard
  rw [realBandOne_eq_profile hpb hps, realBandOne_eq_profile hqb hqs]
  have he : (-positiveBandAmplitude L N (p * n) * VaughanLogAverage.riesz L (p * n)) *
      (-positiveBandAmplitude L N (q * n) * VaughanLogAverage.riesz L (q * n)) =
      (positiveBandAmplitude L N (p * n) * positiveBandAmplitude L N (q * n)) *
      (VaughanLogAverage.riesz L (p * n) * VaughanLogAverage.riesz L (q * n)) := by ring
  rw [he]
  exact mul_pos (mul_pos (positiveBandAmplitude_pos hL N hp1) (positiveBandAmplitude_pos hL N hq1))
    (riesz_prime_sign_stable L hp hq hpn hqn hn hcard hm)


end
end RiemannGaussian.ZetaRieszPrimeCycleSupply
