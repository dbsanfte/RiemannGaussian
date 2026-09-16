/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeCycleSupply
import RiemannGaussian.ZetaRieszCycleCapacity

/-!
# Prime-profile margins reach the actual exact-cycle saving

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszPrimeCycleMargin
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy
open ZetaRieszPrimeCycleSupply
open ZetaRieszRetainedFraction
open ZetaRieszCycleCapacity

/-- Actual same-cofactor prime insertions pass the exact positive-cycle
test once their retained arithmetic margins and oriented prime phases do.
There is no separate complex cancellation or amplitude-sign assumption. -/
theorem actual_prime_cycle_of_margins {L : ℝ} (hL : 0 < L) {N p q r n : ℕ} (t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hmq : primeProfileError p q n < |VaughanLogAverage.riesz L (p * n)|)
    (hmr : primeProfileError p r n < |VaughanLogAverage.riesz L (p * n)|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    ZetaRieszCycleCore.positiveCycle (bandWeight L 1 N t (p * n))
      (bandWeight L 1 N t (q * n)) (bandWeight L 1 N t (r * n)) := by
  have haq := actual_prime_sign_stable hL hp hq hpn hqn hn hcard hpb hqb hmq
  have har := actual_prime_sign_stable hL hp hr hpn hrn hn hcard hpb hrb hmr
  have hqrSign : 0 < realBandOne L N (q * n) * realBandOne L N (r * n) := by
    rcases (mul_pos_iff.mp haq) with h | h
    · have hr0 : 0 < realBandOne L N (r * n) := (mul_pos_iff_of_pos_left h.1).mp har
      exact mul_pos h.2 hr0
    · have hr0 : realBandOne L N (r * n) < 0 := by
        rcases mul_pos_iff.mp har with hh | hh
        · linarith [hh.1, h.1]
        · exact hh.2
      exact mul_pos_of_neg_of_neg h.2 hr0
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn.ne_zero
  unfold ZetaRieszCycleCore.positiveCycle
  rw [ZetaRieszCycleCorrelation.area_actual_one,
    ZetaRieszCycleCorrelation.area_actual_one, ZetaRieszCycleCorrelation.area_actual_one,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hq.pos hr.pos hn0,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hr.pos hp.pos hn0,
    ZetaRieszOppositePrimes.prime_insertion_log_difference hp.pos hq.pos hn0]
  exact ⟨mul_pos hqrSign hqr, mul_pos (by simpa only [mul_comm] using har) hrp,
    mul_pos haq hpq⟩

/-- One explicit shared-profile margin supplies a quantitative minimum
for all three original amplitudes. All three factorial envelopes remain. -/
theorem min_actual_prime_mass_ge_margin {L : ℝ} (hL : 0 < L) {N p q r n : ℕ} (t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N) :
    min (positiveBandAmplitude L N (p * n))
      (min (positiveBandAmplitude L N (q * n)) (positiveBandAmplitude L N (r * n))) *
      max 0 (|VaughanLogAverage.riesz L (p * n)| -
        max (primeProfileError p q n) (primeProfileError p r n)) ≤
      min ‖bandWeight L 1 N t (p * n)‖
        (min ‖bandWeight L 1 N t (q * n)‖ ‖bandWeight L 1 N t (r * n)‖) := by
  let g := max 0 (|VaughanLogAverage.riesz L (p * n)| -
    max (primeProfileError p q n) (primeProfileError p r n))
  let k := min (positiveBandAmplitude L N (p * n))
    (min (positiveBandAmplitude L N (q * n)) (positiveBandAmplitude L N (r * n)))
  have hg : 0 ≤ g := le_max_left _ _
  have hgP : g ≤ |VaughanLogAverage.riesz L (p * n)| := by
    refine max_le (abs_nonneg _) ?_
    have he := (primeProfileError_nonneg p q n).trans (le_max_left _ (primeProfileError p r n))
    linarith
  have hgQ : g ≤ max 0 (|VaughanLogAverage.riesz L (p * n)| - primeProfileError p q n) :=
    max_le_max_left 0 (sub_le_sub_left (le_max_left _ _) _)
  have hgR : g ≤ max 0 (|VaughanLogAverage.riesz L (p * n)| - primeProfileError p r n) :=
    max_le_max_left 0 (sub_le_sub_left (le_max_right _ _) _)
  obtain ⟨hp1, hps⟩ := prime_inserted_support hp hpn hn hcard
  obtain ⟨hq1, _⟩ := prime_inserted_support hq hqn hn hcard
  obtain ⟨hr1, _⟩ := prime_inserted_support hr hrn hn hcard
  have hkP : k ≤ positiveBandAmplitude L N (p * n) := min_le_left _ _
  have hkQ : k ≤ positiveBandAmplitude L N (q * n) := (min_le_right _ _).trans (min_le_left _ _)
  have hkR : k ≤ positiveBandAmplitude L N (r * n) := (min_le_right _ _).trans (min_le_right _ _)
  change k * g ≤ _
  refine le_min ?_ (le_min ?_ ?_)
  · rw [norm_bandWeight_one_eq_profile hL t hp1 hpb hps]
    exact (mul_le_mul_of_nonneg_right hkP hg).trans
      (mul_le_mul_of_nonneg_left hgP (positiveBandAmplitude_pos hL N hp1).le)
  · exact ((mul_le_mul_of_nonneg_right hkQ hg).trans
      (mul_le_mul_of_nonneg_left hgQ (positiveBandAmplitude_pos hL N hq1).le)).trans
      (norm_prime_partner_ge_margin hL t hp hq hpn hqn hn hcard hqb)
  · exact ((mul_le_mul_of_nonneg_right hkR hg).trans
      (mul_le_mul_of_nonneg_left hgR (positiveBandAmplitude_pos hL N hr1).le)).trans
      (norm_prime_partner_ge_margin hL t hp hr hpn hrn hn hcard hrb)

/-- A literal higher-prime-count arithmetic triple has a quantitative
exact-cancellation saving, with no complex-sign or capacity premise left
over beyond its explicit profile margin and prime-log sine tests. -/
theorem actual_prime_cycle_saving_ge_margin {L : ℝ} (hL : 0 < L) {N p q r n : ℕ} (t : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hm : max (primeProfileError p q n) (primeProfileError p r n) <
      |VaughanLogAverage.riesz L (p * n)|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    2 * (min (positiveBandAmplitude L N (p * n))
      (min (positiveBandAmplitude L N (q * n)) (positiveBandAmplitude L N (r * n))) *
      max 0 (|VaughanLogAverage.riesz L (p * n)| -
        max (primeProfileError p q n) (primeProfileError p r n))) ≤
      ZetaRieszCycleCore.cycleSaving (bandWeight L 1 N t (p * n))
        (bandWeight L 1 N t (q * n)) (bandWeight L 1 N t (r * n)) := by
  have hcycle := actual_prime_cycle_of_margins hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
    ((le_max_left _ _).trans_lt hm) ((le_max_right _ _).trans_lt hm) hpq hqr hrp
  exact (mul_le_mul_of_nonneg_left
    (min_actual_prime_mass_ge_margin hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb)
    (by norm_num : (0 : ℝ) ≤ 2)).trans
    (ZetaRieszCycleSaving.twice_min_norm_le_cycleSaving hcycle)


/-- The proved arithmetic saving survives every earlier cycle with its
actual remaining-capacity factor. The original cofactor profile margin
is never applied to spent mass or silently treated as fresh supply. -/
theorem actual_prime_cycle_after_previous_ge_margin {L : ℝ} (hL : 0 < L)
    {N p q r n : ℕ} (t : ℝ) (es : List (ℕ × ℕ × ℕ))
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hm : max (primeProfileError p q n) (primeProfileError p r n) <
      |VaughanLogAverage.riesz L (p * n)|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    2 * (min (retainedFraction (bandWeight L 1 N t) es (p * n))
      (min (retainedFraction (bandWeight L 1 N t) es (q * n))
        (retainedFraction (bandWeight L 1 N t) es (r * n))) *
      (min (positiveBandAmplitude L N (p * n))
        (min (positiveBandAmplitude L N (q * n)) (positiveBandAmplitude L N (r * n))) *
        max 0 (|VaughanLogAverage.riesz L (p * n)| -
          max (primeProfileError p q n) (primeProfileError p r n)))) ≤
      ZetaRieszCycleCore.cycleSaving
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L 1 N t) es (p * n))
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L 1 N t) es (q * n))
        (ZetaRieszCycleIteration.cycleResidual (bandWeight L 1 N t) es (r * n)) := by
  have hcycle := actual_prime_cycle_of_margins hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
    ((le_max_left _ _).trans_lt hm) ((le_max_right _ _).trans_lt hm) hpq hqr hrp
  have ha := (retainedFraction_bounds (bandWeight L 1 N t) es (p * n)).1
  have hb := (retainedFraction_bounds (bandWeight L 1 N t) es (q * n)).1
  have hc := (retainedFraction_bounds (bandWeight L 1 N t) es (r * n)).1
  have hd := le_min ha (le_min hb hc)
  have hmargin := min_actual_prime_mass_ge_margin hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
  rw [cycleResidual_eq_retainedFraction, cycleResidual_eq_retainedFraction,
    cycleResidual_eq_retainedFraction]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmargin hd)
    (by norm_num : (0 : ℝ) ≤ 2)).trans (scaled_cycleSaving_ge_min ha hb hc hcycle)


/-- The arithmetic quarter-slope margins now reach the exact saving
with each original factorial amplitude, each spent fraction and each
oriented sine capacity retained separately. Aggregate sufficiency remains
open; none of these local budgets is assumed uniformly positive. -/
theorem actual_prime_cycle_after_previous_ge_oriented_margin {L : ℝ} (hL : 0 < L)
    {N p q r n : ℕ} (t : ℝ) (es : List (ℕ × ℕ × ℕ))
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hrn : ¬ r ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hpb : p * n ∈ zetaPrimeLogBand N) (hqb : q * n ∈ zetaPrimeLogBand N)
    (hrb : r * n ∈ zetaPrimeLogBand N)
    (hm : max (primeProfileError p q n) (primeProfileError p r n) <
      |VaughanLogAverage.riesz L (p * n)|)
    (hpq : 0 < Real.sin (t * (Real.log p - Real.log q)))
    (hqr : 0 < Real.sin (t * (Real.log q - Real.log r)))
    (hrp : 0 < Real.sin (t * (Real.log r - Real.log p))) :
    let f := bandWeight L 1 N t
    let zp := ZetaRieszMassTransport.ray (f (p * n))
    let zq := ZetaRieszMassTransport.ray (f (q * n))
    let zr := ZetaRieszMassTransport.ray (f (r * n))
    let supply := fun v => positiveBandAmplitude L N (v * n) *
      max 0 (|VaughanLogAverage.riesz L (p * n)| - primeProfileError p v n)
    rayCapacity zp zq zr
      (retainedFraction f es (p * n) * supply p)
      (retainedFraction f es (q * n) * supply q)
      (retainedFraction f es (r * n) * supply r) *
      (ZetaRieszCycleCore.area zq zr + ZetaRieszCycleCore.area zr zp + ZetaRieszCycleCore.area zp zq) ≤
        ZetaRieszCycleCore.cycleSaving (ZetaRieszCycleIteration.cycleResidual f es (p * n))
          (ZetaRieszCycleIteration.cycleResidual f es (q * n))
          (ZetaRieszCycleIteration.cycleResidual f es (r * n)) := by
  have hcycle := actual_prime_cycle_of_margins hL t hp hq hr hpn hqn hrn hn hcard hpb hqb hrb
    ((le_max_left _ _).trans_lt hm) ((le_max_right _ _).trans_lt hm) hpq hqr hrp
  have hp1 := (prime_inserted_support hp hpn hn hcard).1
  have hq1 := (prime_inserted_support hq hqn hn hcard).1
  have hr1 := (prime_inserted_support hr hrn hn hcard).1
  exact cycleSaving_retained_rayCapacity (bandWeight L 1 N t) es (p * n) (q * n) (r * n) hcycle
    (mul_nonneg (positiveBandAmplitude_pos hL N hp1).le (le_max_left _ _))
    (mul_nonneg (positiveBandAmplitude_pos hL N hq1).le (le_max_left _ _))
    (mul_nonneg (positiveBandAmplitude_pos hL N hr1).le (le_max_left _ _))
    (norm_prime_partner_ge_margin hL t hp hp hpn hpn hn hcard hpb)
    (norm_prime_partner_ge_margin hL t hp hq hpn hqn hn hcard hqb)
    (norm_prime_partner_ge_margin hL t hp hr hpn hrn hn hcard hrb)


end
end RiemannGaussian.ZetaRieszPrimeCycleMargin
