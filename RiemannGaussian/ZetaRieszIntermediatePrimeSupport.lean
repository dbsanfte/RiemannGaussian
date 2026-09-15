/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLowerDegreeDeletion

/-!
# Every surviving label must contain an intermediate prime

On 0<u<exp(-2/3), every nonzero label in the reduced actual carrier
eventually has a prime factor strictly between N^2 and the physical cutoff.
This follows from the two-large-prime support and the new one-extreme-prime
cap, with the actual floor-dependent head comparison proved eventually.
The intermediate prime's signed correlation with its cofactor remains open.
This support theorem is not a whole-carrier bound or a zero-free improvement.
-/

namespace RiemannGaussian.ZetaRieszIntermediatePrimeSupport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount
open ZetaRieszLowerDegreeBounds
open ZetaRieszLowerDegreeDeletion

/-- On the two-prime deletion interval, every nonzero surviving integer
must carry an actual intermediate prime between N^2 and the physical
cutoff. Thus purely smooth/extreme labels have all been paid there. -/
theorem surviving_intermediate_prime {u L : ℝ} {N n : ℕ}
    (hu : u < Real.exp (-(2 / 3 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : n ∈ degreeResidualBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ N ^ 2 < p ∧
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  have hcontact : u < Real.exp (-(1 / 2 : ℝ)) :=
    hu.trans (Real.exp_lt_exp.mpr (by norm_num))
  have hsemi := ZetaRieszNarrowCarrier.residualBand_subset u N
    (ZetaRieszFourExtremeDeletion.fourResidualBand_subset u N
      (degreeResidualBand_subset u N hn))
  obtain ⟨p, r, hp, hr, hpr, hpn, hrn, hNp, hNr⟩ :=
    ZetaRieszSemiprimeDeletion.surviving_two_large_primes hcontact hNX hsemi hc
  by_cases hpX : p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  · exact ⟨p, hp, hpn, hNp, hpX⟩
  · refine ⟨r, hr, hrn, hNr, ?_⟩
    by_contra hrX
    have hsq : Squarefree n := by
      by_contra hs
      exact hc (by simp [SquarefreeVaughanLogSource.coefficient, hs])
    have hn0 : n ≠ 0 := hsq.ne_zero
    have hpE : p ∈ extremePrimes u N n := Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩, le_of_not_gt hpX⟩
    have hrE : r ∈ extremePrimes u N n := Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hr, hrn, hn0⟩, le_of_not_gt hrX⟩
    have hpair : ({p, r} : Finset ℕ) ⊆ extremePrimes u N n := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hpair
    have hlimit := surviving_extreme_count_le_one hu hn
    have hpaircard : ({p, r} : Finset ℕ).card = 2 := by simp [hpr]
    rw [hpaircard] at hcard
    omega

/-- The physical-head comparison is eventually automatic, so the
intermediate-prime obligation holds eventually for every nonzero survivor. -/
theorem eventually_surviving_intermediate_prime {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ degreeResidualBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0 →
      ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ N ^ 2 < p ∧
        p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu hu1]
    with N hNX
  intro n hn hc
  exact surviving_intermediate_prime huh hNX hn hc

end
end RiemannGaussian.ZetaRieszIntermediatePrimeSupport
