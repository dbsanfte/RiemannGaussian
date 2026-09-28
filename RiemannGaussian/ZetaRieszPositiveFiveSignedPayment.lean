/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveCertifiedPayment

/-!
# One-sided phase costs for the full positive-five interior

The angular certificate is charged only against the adverse half of the
actual product phase. All original allocation weights remain present.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveSignedPayment
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPositiveFiveCover ZetaRieszPositiveFiveCells
open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation ZetaRieszDominantAllocation

private theorem amplitude_le_window {n : ℕ} (hn : n ≠ 0) {t h : ℝ}
    (ht : t ≤ Real.log n) (hth : Real.log n ≤ t+h) (N : ℕ) :
    amplitude N n ≤ (Real.exp (-t/2)*(t+h)^N/N.factorial)*(n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Real.exp (-(3/2 : ℝ)*Real.log n) =
      Real.exp (-Real.log n/2)*(n : ℝ)⁻¹ := by
    rw [show (n : ℝ)⁻¹ = Real.exp (-Real.log n) by rw [Real.exp_neg,Real.exp_log hnR],
      ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (-Real.log n/2)*(Real.log n)^N/N.factorial ≤
      Real.exp (-t/2)*(t+h)^N/N.factorial := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
      (pow_le_pow_left₀ (Real.log_natCast_nonneg n) hth N) (by positivity) (Real.exp_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr hnR.le)
  unfold amplitude
  rw [he]
  convert hm using 1 <;> first | rfl | ring

/-- Either directed phase cost is controlled without replacing the
original cosine by its absolute value. The numerical mass premise is the
literal checked-cover theorem, not a prime-density assumption. -/
theorem directed_phase_mass_le {B : Cover.Box} (S A : Finset ℕ)
    (N : ℕ) (L t h δ y e M : ℝ) (hh : 0 ≤ h) (ht : 0 ≤ t+h) (he : |e| ≤ 1)
    (hmass : (∑ n ∈ population B S L t h δ,
      max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤ M) :
    (∑ n ∈ population B S L t h δ,
      max 0 (e*(residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)) ≤
      (Real.exp (-t/2)*(t+h)^N/N.factorial)*
        (max 0 (e*Real.cos (y*t))+|y| * h)*M := by
  let V := Real.exp (-t/2)*(t+h)^N/N.factorial
  let D := max 0 (e*Real.cos (y*t))+|y| * h
  have hD : 0 ≤ D := add_nonneg (le_max_left _ _) (mul_nonneg (abs_nonneg _) hh)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hp (n : ℕ) (hn : n ∈ population B S L t h δ) :
      max 0 (e*(residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) ≤
        V*D*(max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) := by
    obtain ⟨_,hs,_,htn,hnth,hpos,_⟩ := Finset.mem_filter.mp hn
    have hphase : |y*Real.log n-y*t| ≤ |y| * h := by
      rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr htn.le)]
      exact mul_le_mul_of_nonneg_left (by linarith only [hnth]) (abs_nonneg y)
    have hcos := (Real.abs_cos_sub_cos_le (y*Real.log n) (y*t)).trans hphase
    have hed : e*Real.cos (y*Real.log n) ≤ D := by
      have hvar : e*(Real.cos (y*Real.log n)-Real.cos (y*t)) ≤ |y| * h := by
        calc
          _ ≤ |e*(Real.cos (y*Real.log n)-Real.cos (y*t))| := le_abs_self _
          _ = |e| * |Real.cos (y*Real.log n)-Real.cos (y*t)| := abs_mul _ _
          _ ≤ 1*(|y| * h) := mul_le_mul he hcos (abs_nonneg _) (by norm_num)
          _ = _ := one_mul _
      dsimp [D]
      nlinarith only [hvar,le_max_right 0 (e*Real.cos (y*t))]
    have hw : weight A N n ≤ V*(n : ℝ)⁻¹ := by
      have h := mul_le_mul_of_nonneg_right
        (show 1-boundedShare A N n ≤ 1 by linarith only [(boundedShare_bounds A N n).1])
        (ZetaRieszCosineCarrier.factorial_envelope_nonneg N n)
      simp only [one_mul] at h
      exact h.trans (amplitude_le_window hs.ne_zero htn.le hnth N)
    have hcoeff : 0 ≤ weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re :=
      mul_nonneg (weight_nonneg _ _ _) hpos.le
    have hpoint : max 0 (e*(residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) ≤
        (weight A N n*(SquarefreeVaughanLogSource.coefficient L n).re)*D := by
      apply max_le (mul_nonneg hcoeff hD)
      rw [re_residual_atom]
      convert mul_le_mul_of_nonneg_left hed hcoeff using 1
      ring
    apply hpoint.trans
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw hpos.le) hD
    convert hb using 1
    rw [max_eq_right hpos.le]
    dsimp [V]
    ring
  have hs := Finset.sum_le_sum hp
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hV hD))

/-- A checked total below `0.003961` pays the literal directed phase cost
by `1/250`, including all counting and moving-endpoint errors. -/
theorem eventually_directed_mass_of_checked_tree {lo hi owner : ℚ}
    (tree : Cover.Tree) {B : Cover.Box}
    (hcheck : Cover.check (ZetaRieszPositiveFiveCover.check lo hi owner) tree B = true)
    (htotal : (Cover.totals tree B).2 ≤ 3961/1000000)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    {h δ : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L t y e : ℝ),
      (N : ℝ) ≤ t → (lo : ℝ)*(t+h) ≤ L → L ≤ (hi : ℝ)*t → |e| ≤ 1 →
      (∑ n ∈ population B S L t h δ,
        max 0 (e*(residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)) ≤
        (1/250 : ℝ)*((Real.exp (-t/2)*(t+h)^N/N.factorial)*
          (max 0 (e*Real.cos (y*t))+|y| * h)*h) := by
  have htR : ((Cover.totals tree B).2 : ℝ) ≤ ((3961/1000000 : ℚ) : ℝ) := Rat.cast_le.mpr htotal
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at htR
  have hbudget : (1003/1000 : ℝ)*((Cover.totals tree B).2 : ℝ)+1/100000 ≤ 1/250 := by
    linarith only [htR]
  filter_upwards [ZetaRieszPositiveFiveCertifiedPayment.eventually_checked_tree_mass_upper
    tree hcheck hlo hhi hh hhu hδ (by norm_num : (0 : ℝ) < 1/100000),
    eventually_ge_atTop (1 : ℕ)] with N hmass hN S A L t y e hNt hLlo hLhi he
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hcost := (hmass S L t hNt hLlo hLhi).trans
    (mul_le_mul_of_nonneg_right hbudget hh.le)
  have hb := directed_phase_mass_le S A N L t h δ y e ((1/250 : ℝ)*h)
    hh.le (by linarith only [hNr,hNt,hh]) he hcost
  convert hb using 1
  ring

/-- Complete original phase period for the full positive-five interior. -/
def periodPopulation (S : Finset ℕ) (L v y : ℝ) (m : ℕ) (δ : ℝ) : Finset ℕ :=
  (Finset.range (8*m)).biUnion (fun i => population root S L
    (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|) (Real.pi/(4*m*|y|)) δ)

/-- Every selected label retains the original support masks. -/
theorem periodPopulation_subset (S : Finset ℕ) (L v y : ℝ) (m : ℕ) (δ : ℝ) :
    periodPopulation S L v y m δ ⊆ S := by
  intro n hn
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hn
  exact (Finset.mem_filter.mp hi).1

/-- Original half-open phase cells are disjoint, independently of the
angular subdivision or factorial weights. -/
theorem period_populations_disjoint {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 < |y|)
    (S : Finset ℕ) (L v δ : ℝ) :
    ∀ i ∈ Finset.range (8*m), ∀ j ∈ Finset.range (8*m), i ≠ j →
      Disjoint (population root S L (v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|)
        (Real.pi/(4*m*|y|)) δ)
        (population root S L (v+ZetaRieszCapacityPhaseBudget.periodAngle m j/|y|)
        (Real.pi/(4*m*|y|)) δ) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro n hn hm'
  have hni := (Finset.mem_filter.mp hn).2.2.2
  have hnj := (Finset.mem_filter.mp hm').2.2.2
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hsep := ZetaRieszCapacityPhaseBudget.period_cells_separated hm hij v hy
    linarith only [hni.2.1,hnj.1,hsep]
  · have hsep := ZetaRieszCapacityPhaseBudget.period_cells_separated hm hji v hy
    linarith only [hnj.2.1,hni.1,hsep]

/-- The whole original phase period inherits the checked one-sided
cost, with every cosine kept inside the sum over phase cells. -/
theorem eventually_directed_period_of_checked_tree {lo hi owner : ℚ}
    (tree : Cover.Tree)
    (hcheck : Cover.check (ZetaRieszPositiveFiveCover.check lo hi owner) tree root = true)
    (htotal : (Cover.totals tree root).2 ≤ 3961/1000000)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    {m : ℕ} (hm : 0 < m) {y δ : ℝ} (hy : 0 < |y|)
    (hhu : Real.pi/(4*m*|y|) ≤ 1/100000) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S A : Finset ℕ) (L v e : ℝ),
      let h := Real.pi/(4*m*|y|)
      let T := fun i => v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      (∀ i ∈ Finset.range (8*m), (N : ℝ) ≤ T i ∧
        (lo : ℝ)*(T i+h) ≤ L ∧ L ≤ (hi : ℝ)*T i) → |e| ≤ 1 →
      (∑ n ∈ periodPopulation S L v y m δ,
        max 0 (e*(residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n).re)) ≤
        ∑ i ∈ Finset.range (8*m), (1/250 : ℝ)*
          ((Real.exp (-T i/2)*(T i+h)^N/N.factorial)*
            (max 0 (e*Real.cos (y*T i))+|y| * h)*h) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 < Real.pi/(4*m*|y|) := by positivity
  filter_upwards [eventually_directed_mass_of_checked_tree tree hcheck htotal hlo hhi hh hhu hδ]
    with N hmass S A L v e
  dsimp only
  intro hgeom he
  rw [periodPopulation,Finset.sum_biUnion (period_populations_disjoint hm hy S L v δ)]
  exact Finset.sum_le_sum (fun i hi => hmass S A L _ y e (hgeom i hi).1
    (hgeom i hi).2.1 (hgeom i hi).2.2 he)

end
end RiemannGaussian.ZetaRieszPositiveFiveSignedPayment
