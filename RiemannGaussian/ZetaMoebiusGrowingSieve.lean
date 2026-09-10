/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFiniteSieve
import Mathlib.Data.Nat.Log

/-!
# A cofinal arithmetic sieve with a discharged overlap budget

At divisor cutoff `D`, select every positive mixed-prime factor below
`log₂ D`. The exact grouped inclusion-exclusion cost is at most `D`.
The entire union is therefore independently negligible at the original
source scale. The full negative multiplicity source remains on products
whose every mixed-prime divisor lies beyond the growing sieve threshold.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Every eligible factor below the actual sieve threshold. -/
def zetaMoebiusSieveHead (H : ℕ) : Finset ℕ :=
  (Finset.range H).filter (fun P ↦ 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P)

/-- Every selected factor meets the independent analytic sector hypotheses. -/
theorem zetaMoebiusSieveHead_eligible (H : ℕ) :
    ∀ P ∈ zetaMoebiusSieveHead H, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P := by
  intro P hP
  exact (Finset.mem_filter.mp hP).2

/-- The number of selected factors is bounded independently of their
arithmetic distribution; this provides a fully discharged initial schedule. -/
theorem card_zetaMoebiusSieveHead_le (H : ℕ) : (zetaMoebiusSieveHead H).card ≤ H :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range H)

/-- The actual grouped overlap cost fits the original divisor budget,
including every nonempty least-common-multiple intersection. -/
theorem divisibilitySieveCost_zetaMoebiusSieveHead_log_le {D : ℕ} (hD : 0 < D) :
    divisibilitySieveCost (zetaMoebiusSieveHead (Nat.log 2 D)) ≤ D := by
  apply (divisibilitySieveCost_le_pow _).trans
  exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2)
    (card_zetaMoebiusSieveHead_le (Nat.log 2 D))).trans (Nat.pow_log_le_self 2 hD.ne')

/-- Taking the natural binary logarithm preserves cofinality. -/
theorem tendsto_natLog_two_of_tendsto {D : ℕ → ℕ} (hD : Tendsto D atTop atTop) :
    Tendsto (fun N ↦ Nat.log 2 (D N)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  exact (hD.eventually_ge_atTop (2 ^ B)).mono
    (fun _ hN ↦ Nat.le_log_of_pow_le (by norm_num) hN)

/-- The actual selected-zero cutoff is positive at every order. -/
theorem zetaRightHalfPoleJetCutoff_pos (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    0 < zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N := by
  have hq := one_lt_zetaMoebiusHeadGrowth
    (by linarith [NontrivialZetaZero.re_lt_one rho] : 0 < 3 / 2 - rho.1.re) (by linarith)
  exact (Nat.one_le_floor_iff _).mpr (one_le_pow₀ hq.le)

/-- The fixed explicit sieve at the actual original divisor cutoff. -/
def zetaRightHalfMoebiusSieve (rho : NontrivialZetaZero) (N : ℕ) : Finset ℕ :=
  zetaMoebiusSieveHead (Nat.log 2
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N))

/-- Both arithmetic eligibility and the full overlap cost hold at every
order for the explicit sieve; no estimate is left as a hypothesis. -/
theorem zetaRightHalfMoebiusSieve_budget (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (∀ P ∈ zetaRightHalfMoebiusSieve rho N, 0 < P ∧ P ≠ 1 ∧ ¬IsPrimePow P) ∧
      divisibilitySieveCost (zetaRightHalfMoebiusSieve rho N) ≤
        zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N :=
  ⟨zetaMoebiusSieveHead_eligible _,
    divisibilitySieveCost_zetaMoebiusSieveHead_log_le (zetaRightHalfPoleJetCutoff_pos rho hrho N)⟩

/-- Every fixed mixed-prime factor eventually belongs to the simultaneous
sieve. This is one cofinal family, rather than a separate limit for each factor. -/
theorem eventually_mem_zetaRightHalfMoebiusSieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {P : ℕ} (hP : 0 < P) (hP1 : P ≠ 1)
    (hmix : ¬IsPrimePow P) :
    ∀ᶠ N in atTop, P ∈ zetaRightHalfMoebiusSieve rho N := by
  have h := tendsto_natLog_two_of_tendsto (tendsto_zetaRightHalfPoleJetCutoff rho hrho)
  filter_upwards [h.eventually_ge_atTop (P + 1)] with N hN
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP, hP1, hmix⟩

/-- Independent decay of the entire union removed by the explicit
cofinal sieve, with all convergence and overlap-budget hypotheses discharged. -/
theorem tendsto_zetaRightHalfMoebiusGrowingSieve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSieveFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfMoebiusSieve rho N) N (3 / 2 + I * rho.1.im)) atTop (𝓝 0) :=
  tendsto_zetaRightHalfMoebiusSieve rho hrho (zetaRightHalfMoebiusSieve rho)
    (Filter.Eventually.of_forall (zetaRightHalfMoebiusSieve_budget rho hrho))

/-- The full negative multiplicity source survives this single
simultaneous cofinal sieve, with its literal arithmetic complement retained. -/
theorem tendsto_zetaRightHalfMoebiusGrowingSieve_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusSievedRemainderFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfMoebiusSieve rho N) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) :=
  tendsto_zetaRightHalfMoebiusSievedRemainder rho hrho (zetaRightHalfMoebiusSieve rho)
    (Filter.Eventually.of_forall (zetaRightHalfMoebiusSieve_budget rho hrho))

/-- The surviving support excludes every mixed-prime divisor below
the threshold, an exact structural condition on the original product. -/
theorem zetaMoebiusSieveHead_survivor_iff (H n : ℕ) :
    (¬∃ P ∈ zetaMoebiusSieveHead H, P ∣ n) ↔
      ∀ P : ℕ, 0 < P → P ≠ 1 → ¬IsPrimePow P → P ∣ n → H ≤ P := by
  constructor
  · intro h P hP hP1 hmix hPn
    by_contra hlt
    exact h ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP, hP1, hmix⟩, hPn⟩
  · intro h ⟨P, hP, hPn⟩
    obtain ⟨hPH, hP0, hP1, hmix⟩ := Finset.mem_filter.mp hP
    have hlt := Finset.mem_range.mp hPH
    have hge := h P hP0 hP1 hmix hPn
    omega

/-- The source is carried by the original arithmetic products after
excluding all small mixed-prime divisors on a proved cofinal threshold. -/
theorem tendsto_zetaRightHalfMoebiusGrowingSieve_divisor_remainder (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      if ∀ P : ℕ, 0 < P → P ≠ 1 → ¬IsPrimePow P → P ∣ n → Nat.log 2 (D N) ≤ P then
        zetaMoebiusLogTailCoefficient (D N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n
      else 0) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  dsimp only
  convert tendsto_zetaRightHalfMoebiusGrowingSieve_remainder rho hrho using 1
  funext N
  unfold zetaMoebiusSievedRemainderFilter zetaRightHalfMoebiusSieve
  simp only [zetaMoebiusSieveHead_survivor_iff]

end
end RiemannGaussian
