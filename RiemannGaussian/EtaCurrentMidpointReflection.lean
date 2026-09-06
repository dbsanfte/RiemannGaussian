import RiemannGaussian.EtaCurrentAdjacentMidpoint
import RiemannGaussian.EtaCurrentHeadMidpoint

/-!
# The completed reflection term in the actual midpoint coefficient

At its exact multiplicity, the full eta moment is nonzero. The functional
equation evaluates its reflected channel rather than making it vanish.
Substitution in the finite midpoint pair isolates a finite reflection
defect times this nonzero leading moment, and retains both signed tails.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The actual nonzero completed eta moment at the zero's exact multiplicity. -/
def pairedEtaCompletedLeadingMoment (rho : NontrivialZetaZero) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    pairedEtaLogLaplaceMoment (analyticZetaZeroMultiplicity rho) rho.1

/-- The completed centered tail of the actual eta logarithmic measure. -/
def pairedEtaCompletedMomentTail (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N

/-- The exact leading completed moment cannot vanish. -/
theorem pairedEtaCompletedLeadingMoment_ne_zero (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingMoment rho ≠ 0 :=
  mul_ne_zero (mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))
    (NontrivialZetaZero.coe_ne_zero rho)) (pairedEtaLogLaplaceMoment_multiplicity_ne_zero rho)

/-- The functional equation reflects the nonzero leading moment with its exact parity. -/
theorem pairedEtaCompletedLeadingMoment_conjugatePartner (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingMoment (NontrivialZetaZero.conjugatePartner rho) =
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho * starRingEnd ℂ (pairedEtaCompletedLeadingMoment rho) := by
  simpa only [pairedEtaCompletedLeadingMoment, analyticZetaZeroMultiplicity_conjugatePartner] using
    pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho

/-- The order at the exact multiplicity is the full nonzero moment minus
the actual centered tail, with completion retained. -/
theorem pairedEtaFiniteCompletedMoment_top_eq_sub_tail (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaFiniteCompletedMoment rho N (analyticZetaZeroMultiplicity rho) =
      pairedEtaCompletedLeadingMoment rho - pairedEtaCompletedMomentTail rho N (analyticZetaZeroMultiplicity rho) := by
  unfold pairedEtaFiniteCompletedMoment pairedEtaCompletedLeadingMoment pairedEtaCompletedMomentTail
  rw [pairedEtaLeadingLogLaplaceMoment_eq_cutoffCenteredPartial_add_tail rho N]
  ring

/-- The finite reflection defect of the literal centered eta moments. -/
def pairedEtaFiniteCompletedMomentReflectionDefect (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k -
    (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho * starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho N k)

/-- The full signed pair between a finite centered eta moment and an actual tail. -/
def pairedEtaFiniteTailCompletedMomentPair (rho : NontrivialZetaZero) (N k l : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k)
    (pairedEtaCompletedMomentTail (NontrivialZetaZero.conjugatePartner rho) N l)
    (pairedEtaFiniteCompletedMoment rho N k) (pairedEtaCompletedMomentTail rho N l)

private theorem etaSignedCompletedPair_sub_reflected (m : ℕ) (Ap A D Tp T : ℂ) :
    etaSignedCompletedPair Ap ((-1 : ℂ) ^ m * starRingEnd ℂ D - Tp) A (D - T) =
      (-1 : ℂ) ^ m * (Ap - (-1 : ℂ) ^ m * starRingEnd ℂ A) * D -
        etaSignedCompletedPair Ap Tp A T := by
  have he : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [etaSignedCompletedPair, map_sub, map_mul, map_pow, map_neg, map_one,
    starRingEnd_apply, star_star]
  linear_combination (star A * D) * he

/-- Completed reflection isolates the finite defect multiplying the
nonzero leading eta moment; the two tail channels remain signed. -/
theorem pairedEtaFiniteCompletedMomentPair_top_eq_reflection_sub_tail
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaFiniteCompletedMomentPair rho N k (analyticZetaZeroMultiplicity rho) =
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          pairedEtaFiniteCompletedMomentReflectionDefect rho N k * pairedEtaCompletedLeadingMoment rho -
        pairedEtaFiniteTailCompletedMomentPair rho N k (analyticZetaZeroMultiplicity rho) := by
  have hp := pairedEtaFiniteCompletedMoment_top_eq_sub_tail (NontrivialZetaZero.conjugatePartner rho) N
  simp only [analyticZetaZeroMultiplicity_conjugatePartner] at hp
  unfold pairedEtaFiniteCompletedMomentPair
  rw [hp, pairedEtaFiniteCompletedMoment_top_eq_sub_tail, pairedEtaCompletedLeadingMoment_conjugatePartner]
  exact etaSignedCompletedPair_sub_reflected _ _ _ _ _ _

/-- The actual shifted-head reflection defect retains its negative head sign. -/
def pairedEtaHeadCompletedMomentReflectionDefect (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k -
    (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho * starRingEnd ℂ (pairedEtaHeadCompletedMoment rho N k)

/-- The complete signed pair of the actual negative head and successor centered tail. -/
def pairedEtaHeadTailCompletedMomentPair (rho : NontrivialZetaZero) (N k l : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k)
    (pairedEtaCompletedMomentTail (NontrivialZetaZero.conjugatePartner rho) (N + 2) l)
    (pairedEtaHeadCompletedMoment rho N k) (pairedEtaCompletedMomentTail rho (N + 2) l)

/-- The order at the exact multiplicity in the head/prefix pair isolates
the actual head reflection defect and both successor-tail channels. -/
theorem pairedEtaHeadCompletedMomentPair_top_eq_reflection_sub_tail
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaHeadCompletedMomentPair rho N k (analyticZetaZeroMultiplicity rho) =
      (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          pairedEtaHeadCompletedMomentReflectionDefect rho N k * pairedEtaCompletedLeadingMoment rho -
        pairedEtaHeadTailCompletedMomentPair rho N k (analyticZetaZeroMultiplicity rho) := by
  have hp := pairedEtaFiniteCompletedMoment_top_eq_sub_tail (NontrivialZetaZero.conjugatePartner rho) (N + 2)
  simp only [analyticZetaZeroMultiplicity_conjugatePartner] at hp
  unfold pairedEtaHeadCompletedMomentPair
  rw [hp, pairedEtaFiniteCompletedMoment_top_eq_sub_tail, pairedEtaCompletedLeadingMoment_conjugatePartner]
  exact etaSignedCompletedPair_sub_reflected _ _ _ _ _ _

/-- In the repeated-zero branch the actual midpoint coefficient contains
the finite reflection defect times the nonzero leading moment, with its
diagonal pair and signed tail correction fully retained. -/
theorem pairedEtaLeadingCurrentMidpointMoment_eq_adjacent_reflection (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaLeadingCurrentMidpointMoment rho N =
      pairedEtaLogTailCutoff (N + 2) * pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N +
        (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          ((pairedEtaFiniteCompletedMomentPair rho (N + 2)
              (analyticZetaZeroMultiplicity rho - 1) (analyticZetaZeroMultiplicity rho - 1)).re +
            ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
                pairedEtaFiniteCompletedMomentReflectionDefect rho (N + 2) (analyticZetaZeroMultiplicity rho - 2) *
                  pairedEtaCompletedLeadingMoment rho -
              pairedEtaFiniteTailCompletedMomentPair rho (N + 2)
                (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho)).re) := by
  rw [pairedEtaLeadingCurrentMidpointMoment_eq_adjacent_arithmetic rho hm,
    pairedEtaFiniteCompletedMomentPair_top_eq_reflection_sub_tail]

/-- In the simple-zero branch the exact midpoint coefficient retains its
two cutoff origins, raised head term, and head reflection defect paired
with the nonzero leading moment and explicit successor tail. -/
theorem pairedEtaLeadingCurrentMidpointMoment_eq_head_reflection (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaLeadingCurrentMidpointMoment rho N =
      ((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2) *
          pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N +
        (pairedEtaHeadCompletedMomentPair rho N 1 0).re +
          (-pairedEtaHeadCompletedMomentReflectionDefect rho N 0 * pairedEtaCompletedLeadingMoment rho -
            pairedEtaHeadTailCompletedMomentPair rho N 0 1).re := by
  have hp := pairedEtaHeadCompletedMomentPair_top_eq_reflection_sub_tail rho N 0
  simp only [hm, pow_one, neg_one_mul] at hp
  rw [pairedEtaLeadingCurrentMidpointMoment_eq_head_arithmetic rho hm, hp]

end

end RiemannGaussian
