/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRepeatedSolutions

/-!
# Absorb the initial repeated-coordinate exception

Split the complete original solution count exactly according to whether a
selected block is injective. The exceptional count is at most
k^2*J_r^(1-1/(2r)). The actual diagonal lower bound absorbs this exception
when the original alphabet has at least 4*k^4 elements, proving J_r<=2D
for the retained distinct-block count. No moment upper bound is assumed.
-/

namespace RiemannGaussian.VinogradovInitialExceptional
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovShiftedMoment VinogradovRepeatedSolutions
open VinogradovRepeatedSolutions.Pairs VinogradovCrossMoment
/-- The original full collisions with a repetition among the selected left coordinates. -/
def exceptionalCount {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ)
    {k : ℕ} (e : Fin k ↪ Fin (s + 2)) : ℕ :=
  (Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
    ¬ Function.Injective (xy.1 ∘ e) ∧
    tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)).card
/-- A finite covering by actual repeated-pair classes retains the complete frequency equations. -/
theorem exceptionalCount_le_pairCount {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ)
    {k : ℕ} (e : Fin k ↪ Fin (s + 2)) :
    exceptionalCount s v e ≤ k ^ 2 * repeatedPairCount s v := by
  let B (ij : Fin k × Fin k) := if ij.1 ≠ ij.2 then
    Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
      xy.1 (e ij.1) = xy.1 (e ij.2) ∧
      tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2) else ∅
  have hc (ij : Fin k × Fin k) (_ : ij ∈ Finset.univ) : (B ij).card ≤ repeatedPairCount s v := by
    by_cases hij : ij.1 ≠ ij.2
    · simpa only [B, if_pos hij, pairCollisionCount] using
        pairCollisionCount_le_first s v (e ij.1) (e ij.2) (e.injective.ne hij)
    · simp only [B, if_neg hij, Finset.card_empty, Nat.zero_le]
  have hs : Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
      ¬ Function.Injective (xy.1 ∘ e) ∧
      tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2) ⊆
      Finset.univ.biUnion B := by
    intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    have hex : ∃ i j : Fin k, i ≠ j ∧ xy.1 (e i) = xy.1 (e j) := by
      by_contra hn
      apply hx.1
      intro i j hij
      by_contra hne
      exact hn ⟨i, j, hne, hij⟩
    obtain ⟨i, j, hij, heq⟩ := hex
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    simp only [B, if_pos hij, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨heq, hx.2⟩
  apply (Finset.card_le_card hs).trans
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two] using
    Finset.card_biUnion_le_card_mul Finset.univ B (repeatedPairCount s v) hc
/-- Every repeated selected-coordinate contribution is strictly below the source moment exponent. -/
theorem exceptionalCount_le_moment {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) {k : ℕ} (e : Fin k ↪ Fin (s + 2)) :
    (exceptionalCount s v e : ℝ) ≤
      (k : ℝ) ^ 2 * moment (s + 2) v ^ (1 - 1 / ((2 * (s + 2) : ℕ) : ℝ)) := by
  have hc : (exceptionalCount s v e : ℝ) ≤ (k : ℝ) ^ 2 * (repeatedPairCount s v : ℝ) := by
    exact_mod_cast exceptionalCount_le_pairCount s v e
  exact hc.trans (mul_le_mul_of_nonneg_left (repeatedPairCount_le_moment s v) (sq_nonneg _))
/-- The complementary original collisions whose selected left coordinates are distinct. -/
def distinctCount {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ)
    {k : ℕ} (e : Fin k ↪ Fin (s + 2)) : ℕ :=
  (Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
    Function.Injective (xy.1 ∘ e) ∧
    tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)).card
/-- Distinct and repeated selected coordinates partition all original moment solutions exactly. -/
theorem distinctCount_add_exceptionalCount {ι d : Type*} [Fintype ι]
    (s : ℕ) (v : ι → d → ℤ) {k : ℕ} (e : Fin k ↪ Fin (s + 2)) :
    distinctCount s v e + exceptionalCount s v e =
      crossCount (tupleFrequency (s + 2) v) (tupleFrequency (s + 2) v) := by
  classical
  unfold distinctCount exceptionalCount crossCount
  rw [← Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    intro xy hg hb
    have hb' := (@Finset.mem_filter _ _ _ _ _).mp hb
    have hg' := (@Finset.mem_filter _ _ _ _ _).mp hg
    exact hb'.2.1 hg'.2.1)]
  congr 1
  ext xy
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto
/-- The same complete two-sided collision count is exactly the original homogeneous moment. -/
theorem moment_eq_crossCount {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) :
    moment r v = (crossCount (tupleFrequency r v) (tupleFrequency r v) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_natCast, ← crossGram_one]
  have hw : tupleWeight r (fun _ : ι => (1 : ℂ)) = fun _ => 1 := by
    funext x
    simp [tupleWeight]
  have he := even_moment_eq_crossGram r v (fun _ => 1)
  rw [hw] at he
  simpa only [VinogradovPartitionEnergy.polynomial, one_mul, moment] using he
/-- The initial nonsingular candidates retain the full moment except for a proved lower-exponent allowance. -/
theorem moment_sub_exceptional_allowance_le_distinctCount {ι d : Type*}
    [Fintype ι] [Fintype d] (s : ℕ) (v : ι → d → ℤ)
    {k : ℕ} (e : Fin k ↪ Fin (s + 2)) :
    moment (s + 2) v - (k : ℝ) ^ 2 *
      moment (s + 2) v ^ (1 - 1 / ((2 * (s + 2) : ℕ) : ℝ)) ≤ distinctCount s v e := by
  have hsplit : (distinctCount s v e : ℝ) + (exceptionalCount s v e : ℝ) = moment (s + 2) v := by
    rw [moment_eq_crossCount]
    exact_mod_cast distinctCount_add_exceptionalCount s v e
  have hbad := exceptionalCount_le_moment s v e
  linarith
/-- Every original tuple supplies its own diagonal full-frequency collision. -/
theorem card_le_self_crossCount {ι d : Type*} [Fintype ι] (v : ι → d → ℤ) :
    Fintype.card ι ≤ crossCount v v := by
  unfold crossCount
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset ι))
    (t := Finset.univ.filter (fun xy : ι × ι => v xy.1 = v xy.2)) (fun x => (x, x))
    (fun x _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
    (fun x _ y _ he => congrArg Prod.fst he)
  simpa only [Finset.card_univ] using h
/-- The complete homogeneous moment contains the entire diagonal tuple count. -/
theorem diagonal_le_moment {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) : (Fintype.card ι : ℝ) ^ r ≤ moment r v := by
  rw [moment_eq_crossCount]
  have h := card_le_self_crossCount (tupleFrequency r v)
  simp only [Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h
/-- Beyond an explicit sample-size threshold, distinct selected coordinates carry at least half of the full actual moment, with no upper moment estimate assumed. -/
theorem moment_le_twice_distinctCount {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) {k : ℕ} (e : Fin k ↪ Fin (s + 2))
    (hsize : 4 * k ^ 4 ≤ Fintype.card ι) :
    moment (s + 2) v ≤ 2 * (distinctCount s v e : ℝ) := by
  let J := moment (s + 2) v
  let C := 2 * (k : ℝ) ^ 2
  let q : ℝ := ((2 * (s + 2) : ℕ) : ℝ)
  have hJ : 0 ≤ J := by dsimp [J]; rw [moment_eq_crossCount]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (by omega : 1 < 2 * (s + 2))
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ 1 / q := by positivity
  have hb : 0 ≤ 1 - 1 / q := sub_nonneg.mpr ((div_le_one hq0).mpr hq.le)
  have hCsize : C ^ 2 ≤ (Fintype.card ι : ℝ) := by
    have h : (4 : ℝ) * (k : ℝ) ^ 4 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hsize
    dsimp [C]
    nlinarith
  have hpow : C ^ (2 * (s + 2)) ≤ J := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (sq_nonneg C) hCsize (s + 2)).trans (diagonal_le_moment (s + 2) v)
  have hlo : C ≤ J ^ (1 / q) := by
    have hroot := Real.rpow_le_rpow (pow_nonneg hC _) hpow ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC] at hroot
    change C ^ (q * (1 / q)) ≤ J ^ (1 / q) at hroot
    simpa only [mul_one_div_cancel hq0.ne', Real.rpow_one] using hroot
  have hprod : C * J ^ (1 - 1 / q) ≤ J := by
    calc
      _ ≤ J ^ (1 / q) * J ^ (1 - 1 / q) :=
        mul_le_mul_of_nonneg_right hlo (Real.rpow_nonneg hJ _)
      _ = J ^ (1 / q + (1 - 1 / q)) := (Real.rpow_add_of_nonneg hJ ha hb).symm
      _ = J := by rw [show 1 / q + (1 - 1 / q) = 1 by ring, Real.rpow_one]
  have hprod' : 2 * ((k : ℝ) ^ 2 * J ^ (1 - 1 / q)) ≤ J := by
    simpa only [C, mul_assoc] using hprod
  have hfloor := moment_sub_exceptional_allowance_le_distinctCount s v e
  change J - (k : ℝ) ^ 2 * J ^ (1 - 1 / q) ≤ (distinctCount s v e : ℝ) at hfloor
  linarith
end
end RiemannGaussian.VinogradovInitialExceptional
