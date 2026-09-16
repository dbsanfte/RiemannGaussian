/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCycleSupply

/-!
# Keep the exact signed cofactor profile at the phase target

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTargetProfile
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszPrimeCycleSupply

/-- The exact inserted-prime cofactor profile at any real logarithmic
target, including an ideal opposite phase between two actual primes. -/
def targetProfile (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  VaughanLogAverage.riesz L n - VaughanLogAverage.riesz (L - x) n

/-- The actual prime insertion is exactly its target-profile value. -/
theorem riesz_prime_eq_target (L : ℝ) {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    VaughanLogAverage.riesz L (p * n) = targetProfile L n (Real.log p) :=
  ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpn

/-- Only the target-to-prime logarithmic gap is charged. The profile's
signed change from the starting prime to the target remains exact. -/
def targetProfileError (x : ℝ) (q n : ℕ) : ℝ :=
  |Real.log q - x| / 4 * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|

/-- The shifted profile inherits the independently proved quarter slope. -/
theorem abs_prime_profile_sub_target_le (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    |VaughanLogAverage.riesz L (q * n) - targetProfile L n x| ≤ targetProfileError x q n := by
  rw [riesz_prime_eq_target L hq hqn]
  unfold targetProfile targetProfileError
  rw [sub_sub_sub_cancel_left]
  have he := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter (L - x) (L - Real.log q) hn hcard
  simpa only [sub_sub_sub_cancel_left] using he

/-- The actual profile supplies the exact target value minus only its
small flank error, with no loss across the full half-turn. -/
theorem abs_prime_profile_ge_target (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    max 0 (|targetProfile L n x| - targetProfileError x q n) ≤
      |VaughanLogAverage.riesz L (q * n)| := by
  have he := abs_prime_profile_sub_target_le L x hq hqn hn hcard
  have ht := abs_add_le (VaughanLogAverage.riesz L (q * n) - targetProfile L n x)
    (-VaughanLogAverage.riesz L (q * n))
  have heq : VaughanLogAverage.riesz L (q * n) - targetProfile L n x +
      -VaughanLogAverage.riesz L (q * n) = -targetProfile L n x := by ring
  rw [heq, abs_neg, abs_neg] at ht
  exact max_le (abs_nonneg _) (by linarith)

/-- A positive target margin determines the actual arithmetic sign at
the partner prime; the target value itself is kept signed. -/
theorem prime_target_sign_stable (L x : ℝ) {q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hm : targetProfileError x q n < |targetProfile L n x|) :
    0 < targetProfile L n x * VaughanLogAverage.riesz L (q * n) := by
  have he := (abs_prime_profile_sub_target_le L x hq hqn hn hcard).trans_lt hm
  have herr : 0 ≤ targetProfileError x q n := by unfold targetProfileError; positivity
  rcases le_or_gt 0 (targetProfile L n x) with h | h
  · rw [abs_of_nonneg h, abs_lt] at he
    have hx : 0 < targetProfile L n x := by rw [abs_of_nonneg h] at hm; linarith
    have hq0 : 0 < VaughanLogAverage.riesz L (q * n) := by linarith [he.1]
    exact mul_pos hx hq0
  · rw [abs_of_neg h, abs_lt] at he
    have hq0 : VaughanLogAverage.riesz L (q * n) < 0 := by linarith [he.2]
    exact mul_pos_of_neg_of_neg h hq0

/-- The exact-target supply bound reaches the actual weighted partner
mass at every order and height, on its original support. -/
theorem norm_prime_partner_ge_target {L : ℝ} (hL : 0 < L) (x t : ℝ) {N q n : ℕ}
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hqb : q * n ∈ zetaPrimeLogBand N) :
    positiveBandAmplitude L N (q * n) *
      max 0 (|targetProfile L n x| - targetProfileError x q n) ≤ ‖bandWeight L 1 N t (q * n)‖ := by
  obtain ⟨hq1, hqs⟩ := prime_inserted_support hq hqn hn hcard
  rw [norm_bandWeight_one_eq_profile hL t hq1 hqb hqs]
  exact mul_le_mul_of_nonneg_left (abs_prime_profile_ge_target L x hq hqn hn hcard)
    (positiveBandAmplitude_pos hL N hq1).le


end
end RiemannGaussian.ZetaRieszTargetProfile
