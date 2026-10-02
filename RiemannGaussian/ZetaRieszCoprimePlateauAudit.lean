/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallGcdPayment
import RiemannGaussian.ZetaRieszPrefixCoherenceAudit

/-!
# The signed late-prefix channel survives coprimality

After all proper divisors and before the label itself, the literal sharp
prefix is -mu(n). Thus the coherent signed channel is the WHOLE weighted
Möbius moment, not the unsigned number of occupied bins or counts. This
holds on actual coprime labels too, and at active post-hinge cutoffs.

The finite one-sided inequality keeps that moment signed. Its magnitude
for the original whole core is not bounded here. The numerical -79/1000
floor, its remaining signed energy budget and zero exclusion remain open.
-/

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCoprimePlateauAudit
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor

/-- The actual large divisor prefix is a single parity channel once
its reflected cutoff lies below the least prime. The strict endpoint
is retained; no arithmetic density or phase approximation enters. -/
theorem sharp_late_plateau {n k : ℕ} (hn : Squarefree n) (hn1 : n ≠ 1)
    (hk : 0 < k) (hkn : k < n) (hrough : (n-1)/k < n.minFac) :
    sharp k n = -(μ n : ℝ) := by
  have hq : 0 < (n-1)/k := by
    have hle : 1 ≤ (n-1)/k := by
      rw [Nat.le_div_iff_mul_le hk]
      omega
    omega
  have he := ZetaRieszSquarefreeDualMean.sharp_reflection hn hn1 hk
  change sharp k n = -(μ n : ℝ)*sharp ((n-1)/k) n at he
  rw [ZetaRieszPrefixCoherenceAudit.sharp_eq_one_of_lt_minFac hq hrough,mul_one] at he
  exact he

/-- Sum all counts and their ACTUAL complex-phase real weights first.
Their signed Möbius moment survives, irrespective of coprimality. -/
theorem correlation_late_plateau (S : Finset ℕ) (w : ℕ → ℝ) {k : ℕ}
    (hk : 0 < k) (hSF : ∀ n ∈ S,Squarefree n ∧ n ≠ 1)
    (hplateau : ∀ n ∈ S,k < n ∧ (n-1)/k < n.minFac) :
    correlation S w k = -(∑ n ∈ S,w n*(μ n : ℝ)) := by
  rw [correlation,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sharp_late_plateau (hSF n hn).1 (hSF n hn).2 hk
    (hplateau n hn).1 (hplateau n hn).2]
  ring

/-- An exact contribution to the EXISTING joined energy on arbitrary
selected cutoffs. The adverse set, if used, is not selected again. -/
theorem plateau_energy_eq (B S : Finset ℕ) (w : ℕ → ℝ)
    (hB : ∀ k ∈ B,0 < k) (hSF : ∀ n ∈ S,Squarefree n ∧ n ≠ 1)
    (hplateau : ∀ k ∈ B,∀ n ∈ S,k < n ∧ (n-1)/k < n.minFac) :
    (∑ k ∈ B,correlation S w k^2/(k : ℝ)) =
      (∑ n ∈ S,w n*(μ n : ℝ))^2*(∑ k ∈ B,1/(k : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [correlation_late_plateau S w (hB k hk) hSF (hplateau k hk),neg_sq]
  ring

/-- The common late channel is retained in the actual full energy.
This does NOT assert the native signed moment is large or small. -/
theorem phaseEnergy_plateau_lower (X : ℕ) (B S : Finset ℕ) (w f : ℕ → ℝ)
    (hB : B ⊆ activeCutoffs X f) (hSF : ∀ n ∈ S,Squarefree n ∧ n ≠ 1)
    (hplateau : ∀ k ∈ B,∀ n ∈ S,k < n ∧ (n-1)/k < n.minFac) :
    (∑ n ∈ S,w n*(μ n : ℝ))^2*(∑ k ∈ B,1/(k : ℝ)) ≤
      phaseEnergy X S w f := by
  rw [← plateau_energy_eq B S w (fun k hk =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (hB hk)).1).1) hSF hplateau]
  exact Finset.sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- Full periods inside the plateau keep the SAME signed moment.
Grouping cutoffs cannot manufacture oscillation in this contribution. -/
theorem plateau_pairing_eq (B S : Finset ℕ) (w f : ℕ → ℝ)
    (hB : ∀ k ∈ B,0 < k) (hSF : ∀ n ∈ S,Squarefree n ∧ n ≠ 1)
    (hplateau : ∀ k ∈ B,∀ n ∈ S,k < n ∧ (n-1)/k < n.minFac) :
    (∑ k ∈ B,correlation S w k*(f k-f (k+1))) =
      (∑ n ∈ S,w n*(μ n : ℝ))*(∑ k ∈ B,(f (k+1)-f k)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [correlation_late_plateau S w (hB k hk) hSF (hplateau k hk)]
  ring

/-- A direct finite one-sided bound, with no absolute-value price on
the favorable sign. The UNPAID signed moment remains explicit. This
is a conditional geometry bound, not the numerical whole-core floor. -/
theorem signed_plateau_floor (X : ℕ) (B S : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (hB : B ⊆ Finset.Icc 1 X) (hSF : ∀ n ∈ S,Squarefree n ∧ n ≠ 1)
    (hplateau : ∀ k ∈ B,∀ n ∈ S,k < n ∧ (n-1)/k < n.minFac) :
    let f := correctedProfile X L 1 0;
    -max (-(∑ n ∈ S,w n*(μ n : ℝ))) 0*(∑ k ∈ B,(f (k+1)-f k)) ≤
      ∑ k ∈ B,correlation S w k*(f k-f (k+1)) := by
  let f := correctedProfile X L 1 0
  dsimp only at ⊢
  have hstep : 0 ≤ ∑ k ∈ B,(f (k+1)-f k) := by
    apply Finset.sum_nonneg
    intro k hk
    have he := ZetaRieszPostHingeEnergy.corrected_step_nonpos (hB hk) L
    dsimp [f]
    linarith only [he]
  rw [plateau_pairing_eq B S w f (fun k hk => (Finset.mem_Icc.mp (hB hk)).1)
    hSF hplateau]
  exact mul_le_mul_of_nonneg_right (by
    linarith only [le_max_left (-(∑ n ∈ S,w n*(μ n : ℝ))) 0]) hstep

/-- Two genuinely coprime, squarefree, three-prime labels have equal
late sharp columns at an active post-hinge cutoff. This regression is
not a native core population or an example of the carrier's weights. -/
theorem coprime_three_prime_regression :
    Nat.Coprime 1001 7429 ∧ Squarefree (1001 : ℕ) ∧ Squarefree (7429 : ℕ) ∧
    sharp 500 1001 = 1 ∧ sharp 500 7429 = 1 ∧
    500 ∈ activeCutoffs 7429 (correctedProfile 7429 (log 499) 1 0) := by
  have hs₁ : Squarefree (1001 : ℕ) := by
    rw [show (1001 : ℕ)=7*(11*13) by norm_num,Nat.squarefree_mul_iff]
    exact ⟨by decide,(by norm_num : Nat.Prime 7).squarefree,
      Nat.squarefree_mul_iff.mpr ⟨by decide,(by norm_num : Nat.Prime 11).squarefree,
        (by norm_num : Nat.Prime 13).squarefree⟩⟩
  have hs₂ : Squarefree (7429 : ℕ) := by
    rw [show (7429 : ℕ)=17*(19*23) by norm_num,Nat.squarefree_mul_iff]
    exact ⟨by decide,(by norm_num : Nat.Prime 17).squarefree,
      Nat.squarefree_mul_iff.mpr ⟨by decide,(by norm_num : Nat.Prime 19).squarefree,
        (by norm_num : Nat.Prime 23).squarefree⟩⟩
  have hm₁ : μ 1001 = -1 := by
    rw [show (1001 : ℕ)=7*(11*13) by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
    norm_num
  have hm₂ : μ 7429 = -1 := by
    rw [show (7429 : ℕ)=17*(19*23) by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19),
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
    norm_num
  refine ⟨by decide,hs₁,hs₂,?_,?_,?_⟩
  · rw [sharp_late_plateau hs₁ (by decide) (by decide) (by decide) (by norm_num)]
    norm_num [hm₁]
  · rw [sharp_late_plateau hs₂ (by decide) (by decide) (by decide) (by norm_num)]
    norm_num [hm₂]
  · exact ZetaRieszManyBinCorrelationAudit.post_hinge_active (by decide) (by decide)
      (log_le_log (by norm_num : (0 : ℝ)<499) (by norm_num : (499 : ℝ)≤500))

/-- Removing the diagonal leaves a POSITIVE coprime cross contribution
at the same actual active cutoff. No orthogonality follows from gcd=1.
The test weights are one, not the original carrier's phase weights. -/
theorem coprime_cutoff_cross_positive :
    (∑ n ∈ ({1001,7429} : Finset ℕ),∑ m ∈ ({1001,7429} : Finset ℕ).erase n,
      sharp 500 n*sharp 500 m/(500 : ℝ)) = 1/250 := by
  obtain ⟨_,_,_,h₁,h₂,_⟩ := coprime_three_prime_regression
  norm_num [h₁,h₂]

end RiemannGaussian.ZetaRieszCoprimePlateauAudit
