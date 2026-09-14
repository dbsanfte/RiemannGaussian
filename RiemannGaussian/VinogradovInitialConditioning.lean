/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialEnergy
import RiemannGaussian.VinogradovInitialFactor

/-!
# The full mean value enters the existing conditioned iteration

For k>=2, s>0, X>=4*k^4 and X^(k*(k-1))<M^R, there are an actual prime
M<p<=2^R*M and canonical residue eta with
J_(k+s,k)(X)<=(2R)^2*p^(2s)*I_(0,1)(X;0,eta).

The repeated-coordinate exception, finite common prime packet, original
restricted energy, exact factorization and digit refinement are all proved.
No upper mean-value budget is assumed. This closes the initial global
conditioning interface; the critical high-moment exponent, VK zeta growth
and a new zero-free width still require further arguments.
-/

namespace RiemannGaussian.VinogradovInitialConditioning
noncomputable section
open scoped Classical BigOperators
open UnitAddTorus MeasureTheory
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
open VinogradovMeanValue VinogradovShiftedMoment VinogradovPartitionEnergy
open VinogradovInitialEnergy VinogradovInitialFactor
open VinogradovSingularConditioning

/-- The literal global Vinogradov mean value enters the existing initial conditioned mixed moment, with one actual prime and residue and every cost explicit; no upper moment budget is assumed. -/
theorem exists_initial_conditioning (M R k s X : ℕ) (hk : 2 ≤ k) (hs : 0 < s)
    (hM : 0 < M) (hR : 0 < R) (hbudget : X ^ (k * (k - 1)) < M ^ R)
    (hsize : 4 * k ^ 4 ≤ X) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M ∧
      ∃ eta : Fin p, meanValue (k + s) k X ≤
        (2 * (R : ℝ)) ^ 2 * (p : ℝ) ^ (2 * s) *
          mixedMoment p k 0 1 0 eta.val X s (fun _ => true) := by
  let e : Fin k ↪ Fin (k + s) := ⟨Fin.castAdd s, by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (k + s) => z.val) hij)⟩
  obtain ⟨p, hp, hMp, hpM, henergy⟩ := exists_prime_restricted_energy
    M R k X (k + s) (fun n : Fin X => monomialFrequency k (n.val + 1)) e
    (by omega) hM hR hbudget hsize
  let : NeZero p := ⟨hp.ne_zero⟩
  change moment (k + s) (fun n : Fin X => monomialFrequency k (n.val + 1)) ≤
    (2 * (R : ℝ)) ^ 2 * ∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (tupleFrequency (k + s) (fun n : Fin X => monomialFrequency k (n.val + 1)))
        (fun x => if Function.Injective (fun j : Fin k => ((x (Fin.castAdd s j)).val + 1) % p) then 1 else 0) theta‖ ^ 2 at henergy
  rw [separated_energy_eq_mixedMoment] at henergy
  have hnext := initial_mixed_le_next p k s X hs
  have hbound := henergy.trans (mul_le_mul_of_nonneg_left hnext (sq_nonneg _))
  obtain ⟨eta, _, hmax⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin (p ^ (0 + 1))))) Finset.univ_nonempty
    (fun c : Fin (p ^ (0 + 1)) => mixedMoment p k 0 1 0 c.val X s (fun _ => true))
  have heq : nextMixedMaximum p k 0 0 0 X s (fun _ => true) =
      mixedMoment p k 0 1 0 eta.val X s (fun _ => true) := hmax
  rw [heq] at hbound
  refine ⟨p, hp, hMp, hpM, ⟨eta.val, by simpa only [Nat.zero_add, pow_one] using eta.isLt⟩, ?_⟩
  simpa only [meanValue, mul_assoc] using hbound

end
end RiemannGaussian.VinogradovInitialConditioning
