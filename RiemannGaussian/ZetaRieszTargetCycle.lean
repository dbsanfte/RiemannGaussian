/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCycleMargin
import RiemannGaussian.ZetaRieszTargetProfile

/-!
# Exact-target arithmetic supply survives earlier cycle competition

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTargetCycle
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszPrimeCycleSupply
open ZetaRieszRetainedFraction
open ZetaRieszCycleCapacity
open ZetaRieszPrimeCycleMargin
open ZetaRieszTargetProfile

/-- Strictly matching real signs pass through a shared nonzero anchor. -/
theorem same_sign_trans {a b c : ℝ} (hab : 0 < a * b) (hbc : 0 < b * c) : 0 < a * c := by
  rcases mul_pos_iff.mp hab with h | h
  · have hc : 0 < c := (mul_pos_iff_of_pos_left h.2).mp hbc
    exact mul_pos h.1 hc
  · rcases mul_pos_iff.mp hbc with hh | hh
    · linarith [h.2, hh.1]
    · exact mul_pos_of_neg_of_neg h.1 hh.2

/-- Exact signed profile products and literal prime-log phases suffice
for an original higher-prime-count cycle, without a common value estimate. -/
theorem actual_prime_cycle_of_profile_signs {L : ℝ} (hL : 0 < L) {N p q r n : ℕ} (t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hsq : 0 < VaughanLogAverage.riesz L (p * n) * VaughanLogAverage.riesz L (q * n))
    (hsr : 0 < VaughanLogAverage.riesz L (p * n) * VaughanLogAverage.riesz L (r * n))
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    ZetaRieszCycleCore.positiveCycle (bandWeight L 1 N t (p * n))
      (bandWeight L 1 N t (q * n)) (bandWeight L 1 N t (r * n)) := by
  have sign_pair {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (han : ¬ a ∣ n) (hbn : ¬ b ∣ n)
      (hab : a * n ∈ zetaPrimeLogBand N) (hbb : b * n ∈ zetaPrimeLogBand N)
      (hs : 0 < VaughanLogAverage.riesz L (a * n) * VaughanLogAverage.riesz L (b * n)) :
      0 < realBandOne L N (a * n) * realBandOne L N (b * n) := by
    obtain ⟨ha1, has⟩ := prime_inserted_support ha han hn hcard
    obtain ⟨hb1, hbs⟩ := prime_inserted_support hb hbn hn hcard
    calc
      0 < (positiveBandAmplitude L N (a * n) * positiveBandAmplitude L N (b * n)) *
          (VaughanLogAverage.riesz L (a * n) * VaughanLogAverage.riesz L (b * n)) :=
        mul_pos (mul_pos (positiveBandAmplitude_pos hL N ha1) (positiveBandAmplitude_pos hL N hb1)) hs
      _ = realBandOne L N (a * n) * realBandOne L N (b * n) := by
        rw [realBandOne_eq_profile hab has, realBandOne_eq_profile hbb hbs]
        ring
  have haq := sign_pair hp hq hpn hqn hpb hqb hsq
  have har := sign_pair hp hr hpn hrn hpb hrb hsr
  have hqpSign : 0 < realBandOne L N (q * n) * realBandOne L N (p * n) := by
    simpa only [mul_comm] using haq
  have hqrSign := same_sign_trans hqpSign har
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  unfold ZetaRieszCycleCore.positiveCycle
  rw [ZetaRieszCycleCorrelation.area_actual_one,
    ZetaRieszCycleCorrelation.area_actual_one, ZetaRieszCycleCorrelation.area_actual_one,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hq.pos hr.pos hn0,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hr.pos hp.pos hn0,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hp.pos hq.pos hn0]
  exact ⟨mul_pos hqrSign hqr, mul_pos (by simpa only [mul_comm] using har) hrp,
    mul_pos haq hpq⟩

/-- A signed exact target, with only its small flank errors, verifies
the actual prime cycle. The full half-turn profile change stays explicit. -/
theorem actual_prime_cycle_of_target {L : ℝ} (hL : 0 < L) {N p q r n : ℕ} (x t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hs : 0 < VaughanLogAverage.riesz L (p * n) * targetProfile L n x)
    (hmq : targetProfileError x q n < |targetProfile L n x|)
    (hmr : targetProfileError x r n < |targetProfile L n x|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    ZetaRieszCycleCore.positiveCycle (bandWeight L 1 N t (p * n))
      (bandWeight L 1 N t (q * n)) (bandWeight L 1 N t (r * n)) := by
  exact actual_prime_cycle_of_profile_signs hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
    (same_sign_trans hs (prime_target_sign_stable L x hq hqn hn hcard hmq))
    (same_sign_trans hs (prime_target_sign_stable L x hr hrn hn hcard hmr)) hpq hqr hrp

/-- The exact-target arithmetic estimate reaches the saving after all
previous cycles, retaining every separate amplitude, remaining fraction
and oriented phase capacity. No half-turn absolute error is introduced. -/
theorem actual_prime_cycle_after_previous_ge_target_margin {L : ℝ} (hL : 0 < L)
    {N p q r n : ℕ} (x t : ℝ) (es : List (ℕ × ℕ × ℕ))
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hs : 0 < VaughanLogAverage.riesz L (p * n) * targetProfile L n x)
    (hmq : targetProfileError x q n < |targetProfile L n x|)
    (hmr : targetProfileError x r n < |targetProfile L n x|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    let f := bandWeight L 1 N t
    let zp := ZetaRieszMassTransport.ray (f (p * n))
    let zq := ZetaRieszMassTransport.ray (f (q * n))
    let zr := ZetaRieszMassTransport.ray (f (r * n))
    let supply := fun v => positiveBandAmplitude L N (v * n) *
      max 0 (|targetProfile L n x| - targetProfileError x v n)
    rayCapacity zp zq zr
      (retainedFraction f es (p * n) *
        (positiveBandAmplitude L N (p * n) * |VaughanLogAverage.riesz L (p * n)|))
      (retainedFraction f es (q * n) * supply q)
      (retainedFraction f es (r * n) * supply r) *
      (ZetaRieszCycleCore.area zq zr + ZetaRieszCycleCore.area zr zp + ZetaRieszCycleCore.area zp zq) ≤
        ZetaRieszCycleCore.cycleSaving (ZetaRieszCycleIteration.cycleResidual f es (p * n))
          (ZetaRieszCycleIteration.cycleResidual f es (q * n))
          (ZetaRieszCycleIteration.cycleResidual f es (r * n)) := by
  have hcycle := actual_prime_cycle_of_target hL x t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
    hs hmq hmr hpq hqr hrp
  obtain ⟨hp1, hps⟩ := prime_inserted_support hp hpn hn hcard
  have hq1 := (prime_inserted_support hq hqn hn hcard).1
  have hr1 := (prime_inserted_support hr hrn hn hcard).1
  exact cycleSaving_retained_rayCapacity (bandWeight L 1 N t) es (p * n) (q * n) (r * n) hcycle
    (mul_nonneg (positiveBandAmplitude_pos hL N hp1).le (abs_nonneg _))
    (mul_nonneg (positiveBandAmplitude_pos hL N hq1).le (le_max_left _ _))
    (mul_nonneg (positiveBandAmplitude_pos hL N hr1).le (le_max_left _ _))
    (norm_bandWeight_one_eq_profile hL t hp1 hpb hps).symm.le
    (norm_prime_partner_ge_target hL x t hq hqn hn hcard hqb)
    (norm_prime_partner_ge_target hL x t hr hrn hn hcard hrb)


end
end RiemannGaussian.ZetaRieszTargetCycle
