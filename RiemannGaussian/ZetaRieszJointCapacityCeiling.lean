/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOppositePhase
import RiemannGaussian.ZetaRieszJointCapacityFloor
import RiemannGaussian.ZetaRieszCapacityPhaseBudget

/-!
# Joint upper capacity bounds with one unchanged signed complement

The complete checked five-prime angular population is calibrated as a
whole, retaining its original arithmetic weights. This provides the
negative credit that opposes the positive-coefficient four-prime debit
on positive-cosine windows. No whole-carrier ceiling is assumed or proved.
-/

namespace RiemannGaussian.ZetaRieszJointCapacityCeiling
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszOppositePhase ZetaRieszJointCapacityFloor
open ZetaRieszFourBoundaryCover ZetaRieszFourOrderingBudget

/-- Every label in the complete interior supply has a nonpositive
arithmetic coefficient independently of its observed phase. -/
theorem interior_supply_coefficient_nonpos {M : ℕ} {L lo hi t h b y : ℝ}
    (ht : 0 < t) (hL : 0 < L) (hlo : lo ≤ L/t) (hhi : L/t ≤ hi)
    {v : Fin 4 → Fin M}
    (hv : v ∈ ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b)
    {n : ℕ} (hn : n ∈ ZetaRieszJointPrimeCells.supplyCell t h y
      (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b)) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 := by
  have hg := (Finset.mem_filter.mp hv).2
  dsimp only at hg
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · have ho : ∀ i k, i < k →
        t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i+t*b ≤
          t*ZetaRieszFiveInteriorBudget.gridLo 0 b v k := by
      intro i k hik
      nlinarith [hg.2.1 i k hik]
    have hqp : t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 3+t*b ≤
        t-∑ i, (t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i+t*b) := by
      simp_rw [← mul_add,← Finset.mul_sum]
      nlinarith [hg.2.2.2.1]
    have hsat : t-t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 3-
        t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 2+h ≤ L := by
      have hh := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.1 ht.le
      have hl := (le_div_iff₀ ht).mp hlo
      rw [mul_add,mul_div_cancel₀ _ ht.ne'] at hh
      nlinarith only [hh,hl]
    have hthree : L ≤ t-(t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 1+t*b)-
        (t*ZetaRieszFiveInteriorBudget.gridLo 0 b v 0+t*b) := by
      have hh := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.2 ht.le
      have hl := (div_le_iff₀ ht).mp hhi
      nlinarith only [hh,hl]
    exact ZetaRieszFivePrimeCells.cell_products_coefficient_nonpos ht.le hL ho hqp hsat hthree
      (by simpa only [ZetaRieszJointPrimeCells.supplyCell,if_pos hp] using hn)
  · simp only [ZetaRieszJointPrimeCells.supplyCell,if_neg hp,Finset.notMem_empty] at hn

/-- Independent component ceilings combine without duplicating either
population. The entire remaining signed sum appears exactly once. -/
theorem joint_ceiling_of_disjoint {S Q D : Finset ℕ} (f : ℕ → ℂ) {debit credit : ℝ}
    (hQ : Q ⊆ S) (hdis : Disjoint Q D)
    (hfour : (∑ n ∈ S, f n).re ≤ (∑ n ∈ S\Q, f n).re+debit)
    (hfive : (∑ n ∈ S, f n).re ≤ (∑ n ∈ S\D, f n).re-credit) :
    (∑ n ∈ S, f n).re ≤ (∑ n ∈ S\(Q ∪ D), f n).re+debit-credit := by
  have hQ' : Q ⊆ S\D := Finset.subset_sdiff.mpr ⟨hQ,hdis⟩
  have h₁ := congrArg Complex.re (Finset.sum_sdiff (f := f) hQ)
  have h₂ := congrArg Complex.re (Finset.sum_sdiff (f := f) hQ')
  have he : (S\D)\Q = S\(Q ∪ D) := by ext n; simp; tauto
  rw [he] at h₂
  simp only [Complex.add_re] at h₁ h₂
  linarith

/-- Disjoint upper payments aggregate with one exact signed complement.
This also allows each interval to use its own calibration height. -/
theorem family_ceiling_of_pairwise_disjoint {ι : Type*}
    (I : Finset ι) (S : Finset ℕ) (P : ι → Finset ℕ) (f : ℕ → ℂ) (g : ι → ℝ)
    (hdis : Set.PairwiseDisjoint (↑I) P)
    (hceil : ∀ i ∈ I, (∑ n ∈ S, f n).re ≤ (∑ n ∈ S\P i, f n).re+g i) :
    (∑ n ∈ S, f n).re ≤ (∑ n ∈ S\I.biUnion P, f n).re+(∑ i ∈ I, g i) := by
  have hneg := family_floor_of_pairwise_disjoint I S P (fun n => -f n) (fun i => -g i)
    hdis (by
      intro i hi
      simp only [Finset.sum_neg_distrib,Complex.neg_re]
      linarith only [hceil i hi])
  simp only [Finset.sum_neg_distrib,Complex.neg_re] at hneg
  linarith only [hneg]

/-- The full-period calibrated debit contains EXACTLY all eligible
positive-coefficient four-prime labels in that period. In particular,
calibration does not drop any original positive or negative phase. -/
theorem mem_full_period_calibrated_iff (S : Finset ℕ) (L a : ℝ)
    {m : ℕ} (hm : 0 < m) {v y : ℝ} (hy : 0 < |y|)
    (hv : 1 ≤ v-Real.pi/|y|) (hhu : Real.pi/(4*m*|y|) ≤ 1/100000) (n : ℕ) :
    (n ∈ (Finset.range (8*m)).biUnion (fun i =>
      let t := v+ZetaRieszCapacityPhaseBudget.periodAngle m i/|y|
      adversePopulation S L t (Real.pi/(4*m*|y|)) (Real.pi/t) a)) ↔
      n ∈ S ∧ Squarefree n ∧ n.primeFactors.card = 4 ∧
      (∀ p ∈ n.primeFactors, a < Real.log p) ∧
      v-Real.pi/|y| < Real.log n ∧ Real.log n ≤ v+Real.pi/|y| ∧
      0 < (SquarefreeVaughanLogSource.coefficient L n).re := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 ≤ Real.pi/(4*m*|y|) := by positivity
  constructor
  · intro hn
    obtain ⟨i,hi,hn⟩ := Finset.mem_biUnion.mp hn
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy
    have hp := (mem_calibrated_population_iff S L a (hv.trans ht.1) hh hhu n).mp hn
    exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,ht.1.trans_lt hp.2.2.2.2.1,
      hp.2.2.2.2.2.1.trans ht.2,hp.2.2.2.2.2.2⟩
  · rintro ⟨hn,hs,hcount,hp,hlo,hhi,hpos⟩
    obtain ⟨i,hi,hil,hih⟩ := ZetaRieszCapacityPhaseBudget.period_cells_cover hm hy hlo hhi
    have ht := ZetaRieszCapacityPhaseBudget.period_cell_bounds hm (Finset.mem_range.mp hi) v hy
    exact Finset.mem_biUnion.mpr ⟨i,hi,
      (mem_calibrated_population_iff S L a (hv.trans ht.1) hh hhu n).mpr
        ⟨hn,hs,hcount,hp,hil,hih,hpos⟩⟩

/-- Calibrating the ENTIRE literal five-prime angular population transfers
its checked lower integral into an original-height upper credit. All
angular boundary costs are inherited once, with no new counting theorem. -/
theorem eventually_five_core_ceiling (B : ZetaRieszCapacityCover.Box) {u h b lo hi : ℝ} {M : ℕ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000)
    (hb : 0 < b) (hsmall : b ≤ 1/100000000000000000000) (hcover : (1 : ℝ) ≤ M*b)
    (hlo : (17/25 : ℝ) ≤ lo)
    (hB : ∀ x ∈ ZetaRieszCapacityCover.region B, x 0 ≤ (1 : ℝ) ∧ x 1 ≤ (1/2 : ℝ)) :
    ∀ᶠ j : ℕ in atTop, ∀ t y : ℝ,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let I := ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b
      let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
        (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N → lo ≤ L/t → L/t ≤ hi →
      0 ≤ Real.cos (y*t)-|y| * h →
      (ZetaRieszParityPacket.coreResponse u y N K).re ≤
      (∑ n ∈ S\D, residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
        (((996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region B,
          ZetaRieszFiveCapacityCover.density lo hi (1/100) x)-1/50000)*
          ((1-|Real.pi/t| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
            (Real.cos (y*t)-|y| * h)*h)) := by
  filter_upwards [ZetaRieszFiveAngularDomain.eventually_core_capacity_floor B
    hu hU hh hhu hb hsmall hcover hlo hB,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_ge_atTop (1 : ℕ))] with j hJ hN t y
  dsimp only
  intro htlo hthi hlt htl hphase
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let I := ZetaRieszFiveAngularBoundary.interiorFamily M lo hi (h/t) b
  let D := I.biUnion (fun v => ZetaRieszJointPrimeCells.supplyCell t h (Real.pi/t)
    (fun i => t*ZetaRieszFiveInteriorBudget.gridLo 0 b v i) (fun _ => t*b))
  let f := fun (y : ℝ) (n : ℕ) =>
    residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let C := ((996/1000 : ℝ)*(∫ x in ZetaRieszCapacityCover.region B,
    ZetaRieszFiveCapacityCover.density lo hi (1/100) x)-1/50000)*
      ((Real.exp (-(t+h)/2)*t^N/N.factorial)*(1-|Real.pi/t| * h)*h)
  have ht : 1 ≤ t := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [htlo,hn]
  have ht0 : 0 < t := by linarith
  have hcal := calibration_phase ht hh.le hhu
  have hf := hJ t (Real.pi/t) htlo hthi hlt htl
  rw [hcal.1] at hf
  have heps : 0 ≤ 1-|Real.pi/t| * h := by linarith [hcal.2]
  simp only [neg_neg,max_eq_right heps] at hf
  have hez := congrArg Complex.re
    (Finset.sum_sdiff (f := f (Real.pi/t : ℝ)) (Finset.inter_subset_left (s₂ := D) : S ∩ D ⊆ S))
  have hey := congrArg Complex.re
    (Finset.sum_sdiff (f := f y) (Finset.inter_subset_left (s₂ := D) : S ∩ D ⊆ S))
  simp only [Finset.sdiff_inter_self_left,Complex.add_re] at hez hey
  have hfloor : C ≤ (∑ n ∈ S ∩ D, f (Real.pi/t : ℝ) n).re := by
    change (∑ n ∈ S\D, f (Real.pi/t : ℝ) n).re+C ≤
      (∑ n ∈ S, f (Real.pi/t : ℝ) n).re at hf
    linarith only [hez,hf]
  have hupper := ceiling_of_calibrated_floor (S ∩ D) A N L t h y (Real.pi/t) C
    (by
      intro n hn
      obtain ⟨v,hv,hn⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hn).2
      exact interior_supply_coefficient_nonpos ht0 (SquarefreeVaughanLogSource.length_pos u N)
        hlt htl hv hn)
    (by
      intro n hn
      obtain ⟨v,_,hn⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hn).2
      have ht' := supplyCell_log_bounds hn
      exact ⟨ht'.1.le,ht'.2⟩) hphase hfloor
  change (∑ n ∈ S, f y n).re ≤ _
  have hsum := hey.symm.le.trans (add_le_add (le_refl (∑ n ∈ S\D, f y n).re) hupper)
  convert hsum using 1 <;> first | rfl | (dsimp only [C]; ring)

end
end RiemannGaussian.ZetaRieszJointCapacityCeiling
