/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleIteration
import RiemannGaussian.ZetaRieszTransportSource

/-!
# The original source survives exact cycle removal

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszCycleSource
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore
open ZetaRieszCycleIteration
open ZetaRieszConditionedEnergy

/-- The full original carrier is exactly its remainder after the
canonical finite list of all positive-cycle tests. -/
theorem actual_band_eq_cycle_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
      ∑ n ∈ zetaPrimeLogBand N,
        cycleResidual (bandWeight L P N t) (actualCycles N).toList n := by
  rw [sum_cycleResidual _ _ _ (fun _ he => actualCycles_valid (Finset.mem_toList.mp he))]
  unfold bandWeight zetaArithmeticBand
  exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])

/-- Pair transport can be applied after the exact cancellations. Every
remaining sent chord and unmatched amplitude is still charged. -/
theorem norm_actual_band_le_cycles_then_transport (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ zetaPrimeLogBand N ∧ e.2 ∈ zetaPrimeLogBand N ∧ e.1 ≠ e.2) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      ZetaRieszMassTransport.transportCost (zetaPrimeLogBand N)
        (cycleResidual (bandWeight L P N t) (actualCycles N).toList) es := by
  rw [actual_band_eq_cycle_sum]
  exact ZetaRieszMassTransport.norm_sum_le_transportCost _ _ _ he

/-- The exact-cycle remainder retains the full negative-multiplicity
source at every hypothetical right-half zero, with its full pole-jet
polynomial and no exposure or simplicity assumption. Its independent
source-scale upper bound remains open. -/
theorem tendsto_actual_cycle_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ zetaPrimeLogBand N,
        cycleResidual (bandWeight (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) (actualCycles N).toList n)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [← actual_band_eq_cycle_sum]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszCycleSource
