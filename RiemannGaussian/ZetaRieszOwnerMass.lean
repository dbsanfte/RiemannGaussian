/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerWindow

/-!
# Absolute mass of growing composite-owner ranges

These independent component estimates retain the original full filter,
all heights and the actual floor-defined cutoff. They preserve the full
pole-jet source but do not bound the remaining semiprime and large-owner
signed response or prove a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszOwnerMass
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeEndpoint ZetaRieszOwnedCells ZetaRieszArithmeticCells
open ZetaRieszConditionedEnergy ZetaArithmeticLogWindow
open ZetaRieszOwnerWindow

/-- Entire canonical composite-owner fibres up to an arbitrary
exponential growth exponent. The support is independent of height and filter. -/
def ownerBand (δ : ℝ) (N : ℕ) : Finset ℕ :=
  (arithmeticBand N).filter (fun m =>
    ¬ (ownerCofactor m).Prime ∧ Real.log (ownerCofactor m) ≤ δ * N)

theorem ownerBand_mono {δ ε : ℝ} (hδε : δ ≤ ε) (N : ℕ) : ownerBand δ N ⊆ ownerBand ε N := by
  intro m hm
  obtain ⟨hm, hp, hlog⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hm, hp, hlog.trans (mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg N))⟩

/-- The previous fixed deletion is exactly this family's tenth window. -/
theorem ownerBand_tenth (N : ℕ) :
    ownerBand (1 / 10) N = ZetaRieszSmallCompositeCells.smallOwnerBand N := by
  simp only [ownerBand, ZetaRieszSmallCompositeCells.smallOwnerBand, div_eq_mul_inv, one_mul, mul_comm]

/-- The new fifth window includes every atom of the previous tenth
window and permits additional complete composite-owner fibres. -/
theorem smallOwnerBand_subset_fifth (N : ℕ) :
    ZetaRieszSmallCompositeCells.smallOwnerBand N ⊆ ownerBand (1 / 5) N := by
  rw [← ownerBand_tenth]
  exact ownerBand_mono (by norm_num) N

/-- Saturation couples the surviving owner's prime to the physical
length, and therefore locates the full integer product in the paid window. -/
theorem owner_log_le {u δ : ℝ} {N m : ℕ} (hm : m ∈ ownerBand δ N)
    (hsat : δ * N ≤ SquarefreeVaughanLogSource.length u N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ -2 * Real.log u * N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m ≠ 0) :
    Real.log m ≤ (-2 * Real.log u + δ) * N := by
  obtain ⟨hband, hnp, hn⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hprod, hsf, hn0, hne, hnot⟩ := arithmetic_owner_factorization hband
  have hpL : Real.log (largestPrime m) < SquarefreeVaughanLogSource.length u N := by
    by_contra h
    have hz := ZetaRieszFixedCofactor.coefficient_prime_mul_eq_zero_of_large
      hsf hne hnp hp hnot (hn.trans hsat) (le_of_not_gt h)
    rw [hprod] at hz
    exact hc hz
  have hlog : Real.log m = Real.log (largestPrime m) + Real.log (ownerCofactor m) := by
    calc
      _ = Real.log (largestPrime m * ownerCofactor m : ℕ) :=
        congrArg (fun a : ℕ => Real.log a) hprod.symm
      _ = _ := by rw [Nat.cast_mul, Real.log_mul
        (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hn0)]
  rw [hlog]
  nlinarith

/-- No growing cofactor-count factor is charged: the full divisor
majorant pays for all selected original atoms in one sum. -/
theorem norm_owner_sum_le_of_length (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) {u δ q σ : ℝ} (hu : 0 < u) (hq : 1 / 2 < q) (hσ : 1 < σ)
    (hsat : δ * N ≤ SquarefreeVaughanLogSource.length u N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ -2 * Real.log u * N)
    (heta : ∀ m ∈ ownerBand δ N, ‖eta m‖ ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      eta m * bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
        windowRate u (-2 * Real.log u + δ) q σ ^ N * (u * tiltConstant P q σ) := by
  let S := (ownerBand δ N).filter (fun m =>
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m ≠ 0)
  have he : (∑ m ∈ ownerBand δ N,
      eta m * bandWeight (SquarefreeVaughanLogSource.length u N) P N t m) =
      ∑ m ∈ S, (eta m * SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) m) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) m := by
    rw [show S = _ from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    rw [bandWeight, if_pos hb]
    by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) m = 0
    · simp [hc]
    · simp only [if_pos hc, mul_assoc]
  rw [he]
  refine norm_window_sum_le S _ ?_ P N t hu hq hσ ?_
  · intro m hm
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hm
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (heta m hm) (norm_nonneg _)).trans
      (by simpa only [one_mul] using (SquarefreeVaughanLogSource.norm_coefficient_le
        (SquarefreeVaughanLogSource.length_pos u N) m))
  · intro m hm
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    exact owner_log_le hm hsat hL hc

/-- The same bound controls the complete absolute mass, hence every
bounded mask and every subdivision of these whole cofactor fibres. -/
theorem owner_mass_le_of_length (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {u δ q σ : ℝ} (hu : 0 < u) (hq : 1 / 2 < q) (hσ : 1 < σ)
    (hsat : δ * N ≤ SquarefreeVaughanLogSource.length u N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ -2 * Real.log u * N) :
    u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
        windowRate u (-2 * Real.log u + δ) q σ ^ N * (u * tiltConstant P q σ) := by
  let w := bandWeight (SquarefreeVaughanLogSource.length u N) P N t
  let eta : ℕ → ℂ := fun m => (‖w m‖ : ℂ) / w m
  have heta (m : ℕ) : ‖eta m‖ ≤ 1 := by
    dsimp [eta]
    by_cases hw : w m = 0
    · simp [hw]
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hw)]
  have he (m : ℕ) : eta m * w m = (‖w m‖ : ℂ) := by
    by_cases hw : w m = 0
    · simp [hw]
    · exact div_mul_cancel₀ _ hw
  have h := norm_owner_sum_le_of_length P N t eta hu hq hσ hsat hL (fun m _ => heta m)
  change ‖(u : ℂ) ^ (N + 1) * ∑ m ∈ ownerBand δ N, eta m * w m‖ ≤ _ at h
  simp_rw [he] at h
  rw [← Complex.ofReal_sum, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu.le, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h

/-- A positive exponent strictly below the physical slope is saturated
eventually. The order threshold is proved to exist, not numerically evaluated. -/
theorem eventually_owner_saturated {u δ : ℝ} (hu : 0 < u) (hδ : 0 ≤ δ)
    (hδu : δ < -2 * Real.log u) :
    ∀ᶠ N : ℕ in atTop, δ * N ≤ SquarefreeVaughanLogSource.length u N := by
  have huh : u < Real.exp (-(δ / 2)) := by
    calc
      u = Real.exp (Real.log u) := (Real.exp_log hu).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  have h := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (show 0 ≤ δ / 2 by positivity) huh
  filter_upwards [h] with N hN
  nlinarith

/-- An independent geometric allowance for the complete growing
composite-owner class, uniform in ordinate and with the original full filter. -/
theorem eventually_owner_mass_le (P : Polynomial ℂ) {u δ q σ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hδ : 0 ≤ δ) (hδu : δ < -2 * Real.log u)
    (hq : 1 / 2 < q) (hσ : 1 < σ) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
      u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
        ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N t m‖ ≤
          windowRate u (-2 * Real.log u + δ) q σ ^ N * (u * tiltConstant P q σ) := by
  filter_upwards [eventually_owner_saturated hu hδ hδu,
    eventually_length_le_source_log hu hu1] with N hsat hL
  exact fun t => owner_mass_le_of_length P N t hu hq hσ hsat hL

/-- Once the explicit scalar rate is subunit, the whole absolute mass
vanishes even for an arbitrary moving height. -/
theorem tendsto_owner_mass (P : Polynomial ℂ) (t : ℕ → ℝ) {u δ q σ : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hδ : 0 ≤ δ) (hδu : δ < -2 * Real.log u)
    (hq : 1 / 2 < q) (hσ : 1 < σ)
    (hr : windowRate u (-2 * Real.log u + δ) q σ < 1) :
    Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
      ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => mul_nonneg
    (pow_nonneg hu.le _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))))
    ((eventually_owner_mass_le P hu hu1 hδ hδu hq hσ).mono (fun N hN => hN (t N)))
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (windowRate_pos hu (by linarith : 0 < q) _ _).le hr).mul_const (u * tiltConstant P q σ)

/-- Throughout the right-half source-radius interval away from one
scalar contact, some genuinely exponential composite-owner deletion has
independently vanishing absolute mass. No hypothetical zero is assumed. -/
theorem exists_growing_owner_mass_decay {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hne : u ≠ Real.exp (-(1 / 2 : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < -2 * Real.log u ∧
      ∀ (P : Polynomial ℂ) (t : ℕ → ℝ),
        Tendsto (fun N => u ^ (N + 1) * ∑ m ∈ ownerBand δ N,
          ‖bandWeight (SquarefreeVaughanLogSource.length u N) P N (t N) m‖) atTop (nhds 0) := by
  obtain ⟨δ, hδ, hδu, hr⟩ := exists_owner_window_parameters hu hu1 hne
  refine ⟨δ, hδ, hδu, fun P t => tendsto_owner_mass P t (by linarith) hu1
    hδ.le hδu (ZetaRieszCofactorTiltRate.optimalTilt_gt_half hu hu1) (by linarith) hr⟩

end
end RiemannGaussian.ZetaRieszOwnerMass
