/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveLeafPayment

/-!
# An exhaustive certificate pays the literal positive-five population

All accepted leaves, including zero branches and shared faces, are
aggregated against the original finite sum. Heavy numerical covers remain
optional applications of this small generic checking theorem.
-/

namespace RiemannGaussian.ZetaRieszPositiveFiveCertifiedPayment
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPositiveFiveCover ZetaRieszPositiveFiveCells
open ZetaRieszPositiveFiveCellPayment ZetaRieszPositiveFiveLeafPayment

/-- Every accepted leaf pays its complete original population, including
empty ordering and cap branches. No numerical leaf can be omitted. -/
theorem eventually_checked_leaf_mass_upper {lo hi owner : ℚ} {B : Cover.Box} {w : ℚ × ℚ}
    (hcheck : ZetaRieszPositiveFiveCover.check lo hi owner B w = true)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    {h δ ε : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (L t : ℝ),
      (N : ℝ) ≤ t → (lo : ℝ)*(t+h) ≤ L → L ≤ (hi : ℝ)*t →
      (∑ n ∈ population B S L t h δ,
        max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤
        ((1003/1000 : ℝ)*(Cover.area B*w.2 : ℚ)+ε)*h := by
  have hc := hcheck
  simp only [ZetaRieszPositiveFiveCover.check,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hv := hc.1.1
  have harea : (0 : ℝ) ≤ (Cover.area B*w.2 : ℚ) := by
    exact_mod_cast mul_nonneg
      (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hv.2.2.2.1 i).2)) hc.1.2
  have hcost : 0 ≤ ((1003/1000 : ℝ)*(Cover.area B*w.2 : ℚ)+ε)*h := by positivity
  by_cases hwidth : ∀ i, (B i).1 < (B i).2
  · by_cases hactive : ¬ ((B 2).2 ≤ (B 1).1 ∨ (cap lo hi B w.1 w.2).height ≤ offset lo B ∨
        (cap lo hi B w.1 w.2).b ≤ offset lo B)
    · exact eventually_active_leaf_mass_upper hcheck hwidth hactive hlo hhi hh hhu hδ hε
    · have hz := not_not.mp hactive
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN S L t hNt hLlo hLhi
      have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
      rw [population_empty_of_zero_branch hv w hlo hhi hz S (hNr.trans_le hNt) hLlo hLhi,
        Finset.sum_empty]
      exact hcost
  · push Not at hwidth
    obtain ⟨i,hi⟩ := hwidth
    have he (S : Finset ℕ) (L t : ℝ) : population B S L t h δ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨_,_,_,_,_,_,q,a,b,r,_,_,_,_,_,hshare⟩ := Finset.mem_filter.mp hn
      have hx := Set.mem_pi.mp hshare i (Set.mem_univ i)
      have hi' : ((B i).2 : ℝ) ≤ (B i).1 := by exact_mod_cast hi
      exact (hx.1.trans_le (hx.2.trans hi')).false
    exact Filter.Eventually.of_forall (fun _ S L t _ _ _ => by rw [he,Finset.sum_empty]; exact hcost)

/-- An exhaustive checked tree bounds the original finite arithmetic
population by its actual rational leaf total. The extra slack is arbitrarily
small and is divided across the finite tree, not charged once per label. -/
theorem eventually_checked_tree_mass_upper {lo hi owner : ℚ} (tree : Cover.Tree) {B : Cover.Box}
    (hcheck : Cover.check (ZetaRieszPositiveFiveCover.check lo hi owner) tree B = true)
    (hlo : (2 : ℝ) ≤ 3*(lo : ℝ)) (hhi : 4*(hi : ℝ) ≤ 3)
    {h δ ε : ℝ} (hh : 0 < h) (hhu : h ≤ 1/100000) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (L t : ℝ),
      (N : ℝ) ≤ t → (lo : ℝ)*(t+h) ≤ L → L ≤ (hi : ℝ)*t →
      (∑ n ∈ population B S L t h δ,
        max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)) ≤
        ((1003/1000 : ℝ)*((Cover.totals tree B).2 : ℝ)+ε)*h := by
  induction tree generalizing B ε with
  | leaf w =>
    exact eventually_checked_leaf_mass_upper hcheck hlo hhi hh hhu hδ hε
  | split i q l r ihl ihr =>
    simp only [Cover.check,Bool.and_eq_true,decide_eq_true_eq] at hcheck
    filter_upwards [ihl hcheck.1.2 (half_pos hε),ihr hcheck.2 (half_pos hε)]
      with N hl hr S L t hNt hLlo hLhi
    have hleft := hl S L t hNt hLlo hLhi
    have hright := hr S L t hNt hLlo hLhi
    let f := fun n : ℕ => max 0 (SquarefreeVaughanLogSource.coefficient L n).re/(n : ℝ)
    let P := population (CertifiedBoxCover.leftBox B i q) S L t h δ
    let Q := population (CertifiedBoxCover.rightBox B i q) S L t h δ
    have hsub : population B S L t h δ ⊆ P ∪ Q := population_subset_split B i q S L t h δ
    have hsum : (∑ n ∈ population B S L t h δ, f n) ≤ (∑ n ∈ P, f n)+(∑ n ∈ Q, f n) := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by dsimp [f]; positivity)).trans
      have he := Finset.sum_union_inter (s₁ := P) (s₂ := Q) (f := f)
      have hp : 0 ≤ ∑ n ∈ P ∩ Q, f n := Finset.sum_nonneg (fun n _ => by dsimp [f]; positivity)
      linarith only [he,hp]
    change _ ≤ ((1003/1000 : ℝ)*
      (((Cover.totals l (CertifiedBoxCover.leftBox B i q)).2+
        (Cover.totals r (CertifiedBoxCover.rightBox B i q)).2 : ℚ) : ℝ)+ε)*h
    push_cast
    dsimp [P,Q,f] at hsum
    nlinarith only [hsum,hleft,hright]

end
end RiemannGaussian.ZetaRieszPositiveFiveCertifiedPayment
