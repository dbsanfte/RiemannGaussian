/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerCells

/-!
# Larger explicit composite-owner decay ranges

These independent component estimates retain the original full filter,
all heights and the actual floor-defined cutoff. They preserve the full
pole-jet source but do not bound the remaining semiprime and large-owner
signed response or prove a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszOwnerBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells ZetaRieszArithmeticCells
open ZetaRieszConditionedEnergy ZetaArithmeticLogWindow
open ZetaRieszOwnerWindow
open ZetaRieszOwnerMass
open ZetaRieszOwnerCells

/-- A common geometric base for all composite owners up to exp(N/5)
in the original quantitative source-radius range. -/
def fifthOwnerRate : ℝ := (3 / 2) * Real.exp (-(9403 / 23040 : ℝ))

theorem fifthOwnerRate_lt_one : fifthOwnerRate < 1 := by
  have hlog : Real.log (3 / 2 : ℝ) - 9403 / 23040 < 0 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have he : fifthOwnerRate = Real.exp (Real.log (3 / 2 : ℝ) - 9403 / 23040) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), fifthOwnerRate, Real.exp_neg]
    ring
  rw [he, Real.exp_lt_one_iff]
  exact hlog

theorem windowRate_fifth_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    windowRate u (-2 * Real.log u + 1 / 5) (2 / 3) (513 / 512) ≤ fifthOwnerRate := by
  have h := windowRate_source_le hu (1 / 5) (2 / 3) (513 / 512) (2 / 3)
    (by norm_num) (by norm_num) huh
  norm_num [fifthOwnerRate] at h ⊢
  exact h

/-- The full absolute deletion range improves from exp(N/10) to
exp(N/5), with a uniform geometric rate and no unproved prime estimate. -/
theorem eventually_fifth_owner_mass_le (P : Polynomial ℂ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      u ^ (N + 1) * ∑ m ∈ ownerBand (1 / 5) N,
        ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
          fifthOwnerRate ^ N * (u * tiltConstant P (2 / 3) (513 / 512)) := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u < -(2 / 3 : ℝ) := by simpa only [Real.log_exp] using Real.log_lt_log hu huh
  have hb := eventually_owner_mass_le P hu hu1 (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (by linarith) (by norm_num : (1 / 2 : ℝ) < 2 / 3) (by norm_num : (1 : ℝ) < 513 / 512)
  filter_upwards [hb] with N hN
  intro t
  apply (hN t).trans
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀
    (windowRate_pos hu (by norm_num) _ _).le (windowRate_fifth_le hu huh) N)
  unfold tiltConstant
  exact mul_nonneg hu.le (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))
    (zetaMoebiusLogMajorantMass_nonneg _))

theorem tendsto_fifth_owner_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand (1 / 5) N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0) := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u < -(2 / 3 : ℝ) := by simpa only [Real.log_exp] using Real.log_lt_log hu huh
  exact tendsto_owner_mass P t hu hu1 (by norm_num) (by linarith)
    (by norm_num) (by norm_num) ((windowRate_fifth_le hu huh).trans_lt fifthOwnerRate_lt_one)

/-- The original full pole-jet source survives the strictly larger
exp(N/5) deletion; the semiprime and larger-owner sum remains open. -/
theorem tendsto_fifth_remaining_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ remainingCells (1 / 5) (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply tendsto_remaining_source
  exact tendsto_fifth_owner_mass _ _ (by linarith [NontrivialZetaZero.re_lt_one rho]) huh

/-- A second explicit common base keeps the exp(N/10) deletion while
expanding its source-radius range from exp(-2/3) to exp(-16/25). -/
def tenthOwnerRate : ℝ := (3 / 2) * Real.exp (-(10427 / 25600 : ℝ))

theorem tenthOwnerRate_lt_one : tenthOwnerRate < 1 := by
  have hlog : Real.log (3 / 2 : ℝ) - 10427 / 25600 < 0 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_three_lt_d9, Real.log_two_gt_d9]
  have he : tenthOwnerRate = Real.exp (Real.log (3 / 2 : ℝ) - 10427 / 25600) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num), tenthOwnerRate, Real.exp_neg]
    ring
  rw [he, Real.exp_lt_one_iff]
  exact hlog

theorem windowRate_tenth_le {u : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(16 / 25 : ℝ))) :
    windowRate u (-2 * Real.log u + 1 / 10) (2 / 3) (513 / 512) ≤ tenthOwnerRate := by
  have h := windowRate_source_le hu (1 / 10) (2 / 3) (513 / 512) (16 / 25)
    (by norm_num) (by norm_num) huh
  norm_num [tenthOwnerRate] at h ⊢
  exact h

/-- An independent geometric bound extends the fixed exp(N/10)
owner schedule to the larger explicit source-radius range. -/
theorem eventually_tenth_owner_mass_le (P : Polynomial ℂ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(16 / 25 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      u ^ (N + 1) * ∑ m ∈ ownerBand (1 / 10) N,
        ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
          tenthOwnerRate ^ N * (u * tiltConstant P (2 / 3) (513 / 512)) := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u < -(16 / 25 : ℝ) := by simpa only [Real.log_exp] using Real.log_lt_log hu huh
  have hb := eventually_owner_mass_le P hu hu1 (by norm_num : (0 : ℝ) ≤ 1 / 10)
    (by linarith) (by norm_num : (1 / 2 : ℝ) < 2 / 3) (by norm_num : (1 : ℝ) < 513 / 512)
  filter_upwards [hb] with N hN
  intro t
  apply (hN t).trans
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀
    (windowRate_pos hu (by norm_num) _ _).le (windowRate_tenth_le hu huh) N)
  unfold tiltConstant
  exact mul_nonneg hu.le (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity))
    (zetaMoebiusLogMajorantMass_nonneg _))

theorem tendsto_tenth_owner_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u : ℝ}
    (hu : 0 < u) (huh : u < Real.exp (-(16 / 25 : ℝ))) :
    Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand (1 / 10) N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0) := by
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u < -(16 / 25 : ℝ) := by simpa only [Real.log_exp] using Real.log_lt_log hu huh
  exact tendsto_owner_mass P t hu hu1 (by norm_num) (by linarith)
    (by norm_num) (by norm_num) ((windowRate_tenth_le hu huh).trans_lt tenthOwnerRate_lt_one)

/-- The full multiplicity source is preserved on the expanded
quantitative radius range after deleting every composite owner up to exp(N/10). -/
theorem tendsto_tenth_remaining_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(16 / 25 : ℝ))) :
    Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ remainingCells (1 / 10) (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply tendsto_remaining_source
  exact tendsto_tenth_owner_mass _ _ (by linarith [NontrivialZetaZero.re_lt_one rho]) huh
end
end RiemannGaussian.ZetaRieszOwnerBounds
