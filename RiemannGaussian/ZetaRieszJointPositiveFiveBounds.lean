/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveBudget
import RiemannGaussian.ZetaRieszCentralReserve

/-!
# Paying a fixed positive-five sector in the whole joint estimates

One half of the already proved central period surplus pays every selected
positive-five label, across all phases of that period. Only labels in the
previous signed rest are charged. The remaining half and every favorable
observation survive in the same whole-sum lower or upper comparison.
The cached central-capacity application discharges the original payment.
-/

namespace RiemannGaussian.ZetaRieszJointPositiveFiveBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPositiveFiveBudget ZetaRieszCapacityPhaseBudget
open ZetaRieszJointAllocation

/-- All selected positive-five labels in a complete original phase period. -/
def periodPopulation (S : Finset ℕ) (L v y : ℝ) (m : ℕ) : Finset ℕ :=
  (Finset.range (8*m)).biUnion (fun i => population S L
    (v+periodAngle m i/|y|) (Real.pi/(4*m*|y|)))

/-- The complete period subset retains all its original labels. -/
theorem periodPopulation_subset (S : Finset ℕ) (L v y : ℝ) (m : ℕ) :
    periodPopulation S L v y m ⊆ S := by
  intro n hn
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hn
  exact (Finset.mem_filter.mp hi).1

/-- No phase-boundary labels disappear between adjacent half-open cells. -/
theorem mem_periodPopulation {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < |y|)
    (S : Finset ℕ) (L v : ℝ) (n : ℕ) :
    n ∈ periodPopulation S L v y m ↔
      n ∈ S ∧ Squarefree n ∧ n.primeFactors.card = 5 ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      0 < (SquarefreeVaughanLogSource.coefficient L n).re ∧
      ∀ p ∈ n.primeFactors.erase (ZetaRieszPrimeEndpoint.largestPrime n),
        (1/10 : ℝ)*Real.log n ≤ Real.log p ∧ Real.log p ≤ (9/80 : ℝ)*Real.log n := by
  constructor
  · intro hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hn,hs,hc,hlo,hhi,hpos,hshare⟩ := Finset.mem_filter.mp hn
    have ht := period_cell_bounds hm (Finset.mem_range.mp hi) v hy
    exact ⟨hn,hs,hc,ht.1.trans_lt hlo,hhi.trans ht.2,hpos,hshare⟩
  · rintro ⟨hn,hs,hc,hlo,hhi,hpos,hshare⟩
    obtain ⟨i,hi,hil,hih⟩ := period_cells_cover hm hy hlo hhi
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hn,hs,hc,hil,hih,hpos,hshare⟩⟩

/-- The entire positive-five period costs at most half of the old
`m V₀ h / 500` surplus, with the exact radial kernel and original phase. -/
theorem eventually_period_norm_mass {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 54 ≤ |y|)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L v V₀ : ℝ),
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      (∀ i ∈ Finset.range (8*m), (69/100 : ℝ)*(v+periodAngle m i/|y|) ≤ L ∧
        L ≤ (7/10 : ℝ)*(v+periodAngle m i/|y|)) →
      0 ≤ V₀ → Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V₀ →
      (∑ n ∈ periodPopulation S L v y m,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (m : ℝ)/1000*V₀*(Real.pi/(4*m*|y|)) := by
  have hy0 : 0 < |y| := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_norm_mass hh hhu,eventually_ge_atTop (1 : ℕ)]
    with N hmass hN S A L v V₀ hlo hhi hL hV₀ hVr
  let h := Real.pi/(4*m*|y|)
  let T := fun i => v+periodAngle m i/|y|
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨V₁,hV₁,hV⟩ := ZetaRieszPhaseBudget.radial_period_comparable
    (by omega : 0 < N) hy hlo hhi
  have hVbase : V₁ ≤ Real.exp (-v/2)*v^N/N.factorial := by
    simpa only [zero_div,add_zero] using (hV 0 (by
      constructor <;> linarith [Real.pi_pos])).1
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      (∑ n ∈ population S L (T i) h,
        ‖residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖) ≤
          (101/1000000 : ℝ)*V₀*h := by
    have hg := period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have hNt : (N : ℝ) ≤ T i := by dsimp [T]; nlinarith [hg.1]
    have ht0 : 0 < T i := by nlinarith
    have hu := (upper_radial ht0 hNt hh.le hhu).trans
      (mul_le_mul_of_nonneg_left
        (hV (periodAngle m i) (periodAngle_bounds hm (Finset.mem_range.mp hi).le)).2
        (by norm_num : (0 : ℝ) ≤ 1001/1000))
    have hrad : Real.exp (-T i/2)*(T i+h)^N/N.factorial ≤ (101/100 : ℝ)*V₀ := by
      dsimp only [T,h] at hu ⊢
      nlinarith only [hu,hVbase,hVr,hV₀]
    have hb := hmass S A (T i) L y hNt (hL i hi).1 (hL i hi).2
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℝ) ≤ 1/10000)) hh.le
    exact hb.trans (by nlinarith only [hc])
  have hdisj : (↑(Finset.range (8*m)) : Set ℕ).PairwiseDisjoint
      (fun i => population S L (T i) h) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro n hni hnj
    obtain ⟨_,_,_,hli,hui,_,_⟩ := Finset.mem_filter.mp hni
    obtain ⟨_,_,_,hlj,huj,_,_⟩ := Finset.mem_filter.mp hnj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have he := period_cells_separated hm hij v hy0
      change T i+h ≤ T j at he
      linarith
    · have he := period_cells_separated hm hji v hy0
      change T j+h ≤ T i at he
      linarith
  have hs := Finset.sum_le_sum hrow
  rw [periodPopulation,Finset.sum_biUnion hdisj]
  apply hs.trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [mul_nonneg (Nat.cast_nonneg m) (mul_nonneg hV₀ hh.le)]

/-- Spend the new debit only inside the old signed rest. A positive
observation of that population is retained, not thrown away. -/
theorem joint_floor_of_payment {S P B : Finset ℕ} (f : ℕ → ℂ)
    {whole d : ℝ} (hB : B ⊆ S\P)
    (hcost : (∑ n ∈ B, ‖f n‖) ≤ d)
    (hpay : (∑ n ∈ S\P, f n).re+2*d ≤ whole) :
    (∑ n ∈ S\(P ∪ B), f n).re+max (∑ n ∈ B, f n).re 0+d ≤ whole := by
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hB)
  simp only [Complex.add_re,sdiff_sdiff_left] at he
  change (∑ n ∈ S\(P ∪ B), f n).re+(∑ n ∈ B, f n).re = (∑ n ∈ S\P, f n).re at he
  have hb := (Complex.abs_re_le_norm (∑ n ∈ B, f n)).trans ((norm_sum_le _ _).trans hcost)
  have hs : max (∑ n ∈ B, f n).re 0-d ≤ (∑ n ∈ B, f n).re := by
    rcases le_total 0 (∑ n ∈ B, f n).re with h | h
    · rw [max_eq_left h]
      linarith [abs_nonneg (∑ n ∈ B, f n).re]
    · rw [max_eq_right h]
      linarith [(abs_le.mp hb).1]
  linarith only [he,hs,hpay]

/-- The alternative ceiling uses the same debit once and preserves
every favorable negative observation of the newly paid population. -/
theorem joint_ceiling_of_payment {S P B : Finset ℕ} (f : ℕ → ℂ)
    {whole d : ℝ} (hB : B ⊆ S\P)
    (hcost : (∑ n ∈ B, ‖f n‖) ≤ d)
    (hpay : whole ≤ (∑ n ∈ S\P, f n).re-2*d) :
    whole ≤ (∑ n ∈ S\(P ∪ B), f n).re+min (∑ n ∈ B, f n).re 0-d := by
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hB)
  simp only [Complex.add_re,sdiff_sdiff_left] at he
  change (∑ n ∈ S\(P ∪ B), f n).re+(∑ n ∈ B, f n).re = (∑ n ∈ S\P, f n).re at he
  have hb := (Complex.abs_re_le_norm (∑ n ∈ B, f n)).trans ((norm_sum_le _ _).trans hcost)
  have hs : (∑ n ∈ B, f n).re ≤ min (∑ n ∈ B, f n).re 0+d := by
    rcases le_total (∑ n ∈ B, f n).re 0 with h | h
    · rw [min_eq_left h]
      linarith [abs_nonneg (∑ n ∈ B, f n).re]
    · rw [min_eq_right h]
      linarith [(abs_le.mp hb).2]
  linarith only [he,hs,hpay]

end
end RiemannGaussian.ZetaRieszJointPositiveFiveBounds
