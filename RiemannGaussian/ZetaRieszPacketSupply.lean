/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPacketCycle

/-!
# Arithmetic projection floors for signed prime packets

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPacketSupply
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore ZetaRieszCycleIteration ZetaRieszCycleCorrelation
open ZetaRieszMassTransport ZetaRieszRetainedFraction ZetaRieszConditionedEnergy
open ZetaRieszPacketCycle

/-- An actual atom exposes its complete oriented mass along any reference ray. -/
theorem area_eq_norm_mul_ray (z w : ℂ) : area z w = ‖w‖ * area z (ray w) := by
  have h := ZetaRieszCycleCapacity.area_smul 1 ‖w‖ z (ray w)
  simpa only [one_smul, norm_smul_ray, one_mul] using h

/-- Separate remaining fractions and arithmetic mass floors aggregate
before taking the packet norm. The exact angular weights stay inside the sum. -/
theorem retained_projection_floor (Q : Finset ℕ) (f : ℕ → ℂ) (eta lower : ℕ → ℝ)
    {z : ℂ} (hz : ‖z‖ ≤ 1)
    (heta : ∀ n ∈ Q, 0 ≤ eta n) (hlower : ∀ n ∈ Q, lower n ≤ ‖f n‖)
    (hangle : ∀ n ∈ Q, 0 ≤ area z (ray (f n))) :
    (∑ n ∈ Q, eta n * lower n * area z (ray (f n))) ≤
      ‖∑ n ∈ Q, eta n • f n‖ := by
  apply le_trans _ (projection_sum_le_norm Q (fun n => eta n • f n) hz)
  apply Finset.sum_le_sum
  intro n hn
  have he := ZetaRieszCycleCapacity.area_smul 1 (eta n) z (f n)
  rw [one_smul, one_mul, area_eq_norm_mul_ray z (f n)] at he
  rw [he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hlower n hn) (heta n hn)) (hangle n hn)

/-- The genuine prime packet has a proved full-polynomial arithmetic
capacity, including all cofactor signs, angular weights and spent fractions. -/
theorem full_prime_packet_projection_floor (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (processed : List (ℕ × ℕ × ℕ)) {n : ℕ} {z : ℂ}
    (hn : Squarefree n) (hn1 : n ≠ 1) (hz : ‖z‖ ≤ 1)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n)
    (hangle : ∀ q ∈ Q, 0 ≤ area z (ray (bandWeight L P N t (q * n)))) :
    (∑ q ∈ Q, retainedFraction (bandWeight L P N t) processed (q * n) *
      (‖ZetaArithmeticBandCorrelation.bandAmplitude L P N t (q * n)‖ *
        max 0 (|ZetaRieszTargetProfile.targetProfile L n x| -
          ZetaRieszFullCycleSupply.cofactorTargetError x q n)) *
        area z (ray (bandWeight L P N t (q * n)))) ≤
      ‖∑ q ∈ Q, cycleResidual (bandWeight L P N t) processed (q * n)‖ := by
  simp_rw [cycleResidual_eq_retainedFraction]
  apply retained_projection_floor Q (fun q => bandWeight L P N t (q * n)) _ _ hz
    (fun q _ => (retainedFraction_bounds _ _ _).1) _ hangle
  intro q hq
  exact ZetaRieszFullCycleSupply.norm_full_prime_partner_ge_cofactor_target
    L x P N t (hQ q hq).1 (hQ q hq).2 hn hn1

end
end RiemannGaussian.ZetaRieszPacketSupply
