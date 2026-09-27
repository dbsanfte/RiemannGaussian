/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeCells

/-!
# Joint literal four/five-prime cell floors

Finite collections of adverse four-prime cells and favorable five-prime
cells are compared inside the unchanged core. Debit cells and their prime
intervals may overlap;
credit cells are disjoint by their ordered outer-prime geometry. Common
total-log windows retain the exact product phase, including its zero
crossings. The final inequality leaves the entire complement signed.
Its explicit geometric credits and debits still have to be compared over
a covering population before asserting a whole-sector payment.
-/

namespace RiemannGaussian.ZetaRieszJointPrimeCells
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCoupledWindow ZetaRieszMacroPrimeWindows
open ZetaRieszFourPrimeCells

/-- The five-prime cell is spent only when its entire total-log phase
window has favorable sign. Otherwise all its labels remain in the rest. -/
def supplyCell (t h y : ℝ) (lo H : Fin 4 → ℝ) : Finset ℕ :=
  if Real.cos (y*t)+|y| * h ≤ 0 then
    ((Fintype.piFinset (fun i => logPrimes (lo i) (H i))).image
      (fun p => (∏ i, p i : ℕ))).biUnion (fun m =>
        (logPrimes (t-Real.log m) h).image (fun p => m*p))
  else ∅

/-- Explicit cell credit, zero when the fixed total-log window has no
certified favorable phase margin. Counting and allocation cost 3/1000. -/
def cellCredit (N : ℕ) (L t h y : ℝ) (lo H : Fin 4 → ℝ) : ℝ :=
  (997/1000 : ℝ)*(t/L)*ZetaRieszFivePrimeCells.boxCap L t h lo (fun i => lo i+H i)*
    max 0 (-Real.cos (y*t)-|y| * h)*(Real.exp (-(t+h)/2)*t^N/N.factorial)*
    (h/(t-∑ i, lo i))*(∏ i, H i/(lo i+H i))

/-- Every certified favorable cell has a literal lower bound for all
phases. Cosine-zero neighborhoods receive zero credit, not deleted debit. -/
theorem eventually_supply_cell_lower {h α β : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ (lo H : Fin 4 → ℝ) (A : Finset ℕ) (L t y : ℝ),
      (∀ i, α*N ≤ lo i) → (∀ i, β*N ≤ H i) →
      (∀ i j, i < j → lo i+H i ≤ lo j) → 0 < L →
      α*N ≤ t-(∑ i, (lo i+H i)) →
      lo 3+H 3 ≤ t-(∑ i, (lo i+H i)) → t-(∑ i, lo i)+h ≤ (9/16 : ℝ)*t →
      t-lo 3-lo 2+h ≤ L → L ≤ t-(lo 1+H 1)-(lo 0+H 0) →
      cellCredit N L t h y lo H ≤
        (∑ n ∈ supplyCell t h y lo H,
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [ZetaRieszFivePrimeCells.eventually_five_cell_lower hh hhu hα hβ]
    with N hN lo H A L t y hlo hH horder hL hmin hqp hmax hsat htriple
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · simpa only [cellCredit,supplyCell,if_pos hp,max_eq_right (show
      0 ≤ -Real.cos (y*t)-|y| * h by linarith)] using
      hN lo H A L t y hlo hH horder hL hmin hqp hmax hsat htriple hp
  · simp only [cellCredit,supplyCell,if_neg hp,max_eq_left (show
      -Real.cos (y*t)-|y| * h ≤ 0 by linarith),mul_zero,zero_mul,Finset.sum_empty,Complex.zero_re]
    rfl

/-- Unioning adverse populations does not spend any credit twice, even
when upper-cover cells overlap. Repeated adverse atoms only enlarge debit. -/
theorem sum_cells_le_union_of_nonpos {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (D : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ I, ∀ n ∈ D i, f n ≤ 0) :
    (∑ i ∈ I, ∑ n ∈ D i, f n) ≤ ∑ n ∈ I.biUnion D, f n := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hI := ih (fun j hj n hn => hf j (Finset.mem_insert_of_mem hj) n hn)
    have hcap : (∑ n ∈ D i ∩ I.biUnion D, f n) ≤ 0 :=
      Finset.sum_nonpos (fun n hn => hf i (Finset.mem_insert_self _ _)
        n (Finset.mem_inter.mp hn).1)
    have he := Finset.sum_union_inter (s₁ := D i) (s₂ := I.biUnion D) (f := f)
    rw [Finset.sum_insert hi,Finset.biUnion_insert]
    linarith

/-- The two count classes are disjoint, irrespective of their prime-log
cells or phase boundaries. -/
theorem adverse_supply_disjoint (S : Finset ℕ) (L t h y : ℝ)
    {lo4 H4 : Fin 3 → ℝ} {lo5 H5 : Fin 4 → ℝ}
    (ho4 : ∀ i j, i < j → lo4 i+H4 i ≤ lo4 j)
    (hp4 : lo4 2+H4 2 ≤ t-(∑ i, (lo4 i+H4 i)))
    (ho5 : ∀ i j, i < j → lo5 i+H5 i ≤ lo5 j)
    (hp5 : lo5 3+H5 3 ≤ t-(∑ i, (lo5 i+H5 i)))
    (hm5 : t-(∑ i, lo5 i)+h ≤ (9/16 : ℝ)*t) :
    Disjoint (adverseCell S L t h y lo4 H4) (supplyCell t h y lo5 H5) := by
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hc4 := adverseCell_count S L t h y ho4 hp4 hn
    have hc5 := ZetaRieszFivePrimeCells.cell_products_count ho5 hp5 hm5
      (by simpa only [supplyCell,if_pos hp] using hn')
    omega
  · simp only [supplyCell,if_neg hp,Finset.disjoint_empty_right]

/-- A whole finite family of literal four-prime debits is paired with
geometrically disjoint five-prime credits. Only explicit cell geometry is
assumed; all arithmetic coefficient, counting, allocation and mask costs
are proved. The complete complement stays signed in the same core. -/
theorem eventually_joint_cell_family_floor {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β)
    {ι κ : Type*} [DecidableEq ι] :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ι) (J : Finset κ)
      (lo4 H4 : ι → Fin 3 → ℝ) (lo5 H5 : κ → Fin 4 → ℝ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D4 := I.biUnion (fun i => adverseCell S L t h y (lo4 i) (H4 i))
      let D5 := J.biUnion (fun i => supplyCell t h y (lo5 i) (H5 i))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∀ i ∈ I, (∀ a, α*N ≤ lo4 i a) ∧ (∀ a, β*N ≤ H4 i a) ∧
        (∀ a b, a < b → lo4 i a+H4 i a ≤ lo4 i b) ∧
        α*N ≤ t-(∑ a, (lo4 i a+H4 i a)) ∧
        lo4 i 2+H4 i 2 ≤ t-(∑ a, (lo4 i a+H4 i a))) →
      (∀ i ∈ J, (∀ a, α*N ≤ lo5 i a) ∧ (∀ a, β*N ≤ H5 i a) ∧
        (∀ a b, a < b → lo5 i a+H5 i a ≤ lo5 i b) ∧
        α*N ≤ t-(∑ a, (lo5 i a+H5 i a)) ∧
        lo5 i 3+H5 i 3 ≤ t-(∑ a, (lo5 i a+H5 i a)) ∧
        t-(∑ a, lo5 i a)+h ≤ (9/16 : ℝ)*t ∧
        t-lo5 i 3-lo5 i 2+h ≤ L ∧ L ≤ t-(lo5 i 1+H5 i 1)-(lo5 i 0+H5 i 0)) →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        ∃ a, lo5 i a+H5 i a ≤ lo5 j a ∨ lo5 j a+H5 j a ≤ lo5 i a) →
      (∑ n ∈ S\(D4 ∪ D5),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ J, cellCredit N L t h y (lo5 i) (H5 i))-
        (∑ i ∈ I, cellDebit N L t h y (lo4 i) (H4 i)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hroom : u < Real.exp (-(5/8 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 5/8) hroom
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_adverse_cell_floor hh hhu hα hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_supply_cell_lower hh hhu hα hβ)]
    with j hj hL hch hfour hfive I J lo4 H4 lo5 H5 t y
  dsimp only
  intro htlo hthi h4 h5 hsep
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let F4 := fun i => adverseCell S L t h y (lo4 i) (H4 i)
  let F5 := fun i => supplyCell t h y (lo5 i) (H5 i)
  let D4 := I.biUnion F4
  let D5 := J.biUnion F5
  have hL0 := SquarefreeVaughanLogSource.length_pos u N
  have hch' := hch t htlo hthi
  have h4bound (i : ι) (hi : i ∈ I) :
      -cellDebit N L t h y (lo4 i) (H4 i) ≤ (∑ n ∈ F4 i, f n).re := by
    obtain ⟨hlo,hH,ho,hmin,hqp⟩ := h4 i hi
    exact hfour (lo4 i) (H4 i) A S L t y hlo hH ho hL0 hch'.1 hch'.2 hmin hqp
  have h5bound (i : κ) (hi : i ∈ J) :
      cellCredit N L t h y (lo5 i) (H5 i) ≤ (∑ n ∈ F5 i, f n).re := by
    obtain ⟨hlo,hH,ho,hmin,hqp,hmax,hsat,htriple⟩ := h5 i hi
    exact hfive (lo5 i) (H5 i) A L t y hlo hH ho hL0 hmin hqp hmax hsat htriple
  have h4S : D4 ⊆ S := Finset.biUnion_subset.mpr
    (fun i _ => adverseCell_subset S L t h y (lo4 i) (H4 i))
  have h5S : D5 ⊆ S := by
    apply Finset.biUnion_subset.mpr
    intro i hi
    by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
    · obtain ⟨_hlo,_hH,ho,_hmin,hqp,hmax,_hsat,_htriple⟩ := h5 i hi
      simpa only [F5,supplyCell,if_pos hp] using
        (ZetaRieszFivePrimeCells.cell_products_subset_core j hj hu hU (by linarith)
          ho hqp hmax htlo hthi)
    · simp only [F5,supplyCell,if_neg hp,Finset.empty_subset]
  have hdis5 : Set.PairwiseDisjoint (↑J) F5 := by
    intro i hi v hv hiv
    by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
    · obtain ⟨_,_,hiorder,_,hiqp,himax,_,_⟩ := h5 i hi
      obtain ⟨_,_,hvorder,_,hvqp,hvmax,_,_⟩ := h5 v hv
      simpa only [F5,supplyCell,if_pos hp] using
        (ZetaRieszFivePrimeCells.cell_products_disjoint hiorder hvorder hiqp hvqp
          himax hvmax (hsep i hi v hv hiv))
    · simp only [F5,supplyCell,if_neg hp,Finset.disjoint_empty_left]
  have hdis45 : Disjoint D4 D5 := by
    apply (Finset.disjoint_biUnion_left I F4 D5).mpr
    intro i hi
    apply (Finset.disjoint_biUnion_right (F4 i) J F5).mpr
    intro v hv
    obtain ⟨_,_,hiorder,_,hiqp⟩ := h4 i hi
    obtain ⟨_,_,hvorder,_,hvqp,hvmax,_,_⟩ := h5 v hv
    exact adverse_supply_disjoint S L t h y hiorder hiqp hvorder hvqp hvmax
  have hfourSum : -(∑ i ∈ I, cellDebit N L t h y (lo4 i) (H4 i)) ≤
      (∑ n ∈ D4, f n).re := by
    have h₁ := Finset.sum_le_sum h4bound
    have h₂ := sum_cells_le_union_of_nonpos I F4 (fun n => (f n).re)
      (fun i _ n hn => adverseCell_atom_nonpos S A N L t h y (lo4 i) (H4 i) hn)
    simp only [← Complex.re_sum] at h₂
    simp only [← Complex.re_sum,Finset.sum_neg_distrib] at h₁
    exact h₁.trans h₂
  have hfiveSum : (∑ i ∈ J, cellCredit N L t h y (lo5 i) (H5 i)) ≤
      (∑ n ∈ D5, f n).re := by
    rw [Finset.sum_biUnion hdis5,Complex.re_sum]
    exact Finset.sum_le_sum h5bound
  have hDS : D4 ∪ D5 ⊆ S := Finset.union_subset h4S h5S
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Finset.sum_union hdis45,Complex.add_re,Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith


/-- Actual count four and count five stay disjoint even when an adverse
cell crosses a prime-order boundary. -/
theorem boundary_supply_disjoint (S : Finset ℕ) (L t h y : ℝ)
    {lo4 H4 : Fin 3 → ℝ} {lo5 H5 : Fin 4 → ℝ}
    (ho5 : ∀ i j, i < j → lo5 i+H5 i ≤ lo5 j)
    (hp5 : lo5 3+H5 3 ≤ t-(∑ i, (lo5 i+H5 i)))
    (hm5 : t-(∑ i, lo5 i)+h ≤ (9/16 : ℝ)*t) :
    Disjoint (boundaryCell S L t h y lo4 H4) (supplyCell t h y lo5 H5) := by
  by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
  · apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hc4 := boundaryCell_count S L t h y hn
    have hc5 := ZetaRieszFivePrimeCells.cell_products_count ho5 hp5 hm5
      (by simpa only [supplyCell,if_pos hp] using hn')
    omega
  · simp only [supplyCell,if_neg hp,Finset.disjoint_empty_right]

/-- The joint signed floor now accepts adverse cells with overlapping
cofactor windows. Only their positive prime-log and final-window bounds
remain; literal ordering and sign masks handle all ordering boundaries.
Five-prime credits remain geometrically disjoint and every other term
stays signed in the original core. -/
theorem eventually_joint_boundary_family_floor {u h α β : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) (hβ : 0 < β)
    {ι κ : Type*} [DecidableEq ι] :
    ∀ᶠ j : ℕ in atTop, ∀ (I : Finset ι) (J : Finset κ)
      (lo4 H4 : ι → Fin 3 → ℝ) (lo5 H5 : κ → Fin 4 → ℝ) (t y : ℝ),
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
      let L := SquarefreeVaughanLogSource.length u N
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
      let S := ZetaRieszParityPacket.coreBand u N K
      let D4 := I.biUnion (fun i => boundaryCell S L t h y (lo4 i) (H4 i))
      let D5 := J.biUnion (fun i => supplyCell t h y (lo5 i) (H5 i))
      (39/20 : ℝ)*N ≤ t → t+h ≤ (203/100 : ℝ)*N →
      (∀ i ∈ I, (∀ a, α*N ≤ lo4 i a) ∧ (∀ a, β*N ≤ H4 i a) ∧
        α*N ≤ t-(∑ a, (lo4 i a+H4 i a))) →
      (∀ i ∈ J, (∀ a, α*N ≤ lo5 i a) ∧ (∀ a, β*N ≤ H5 i a) ∧
        (∀ a b, a < b → lo5 i a+H5 i a ≤ lo5 i b) ∧
        α*N ≤ t-(∑ a, (lo5 i a+H5 i a)) ∧
        lo5 i 3+H5 i 3 ≤ t-(∑ a, (lo5 i a+H5 i a)) ∧
        t-(∑ a, lo5 i a)+h ≤ (9/16 : ℝ)*t ∧
        t-lo5 i 3-lo5 i 2+h ≤ L ∧ L ≤ t-(lo5 i 1+H5 i 1)-(lo5 i 0+H5 i 0)) →
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        ∃ a, lo5 i a+H5 i a ≤ lo5 j a ∨ lo5 j a+H5 j a ≤ lo5 i a) →
      (∑ n ∈ S\(D4 ∪ D5),
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
        (∑ i ∈ J, cellCredit N L t h y (lo5 i) (H5 i))-
        (∑ i ∈ I, cellDebit N L t h y (lo4 i) (H4 i)) ≤
        (ZetaRieszParityPacket.coreResponse u y N K).re := by
  have hroom : u < Real.exp (-(5/8 : ℝ)) :=
    hU.trans_lt (ZetaRieszWideOwnerAudit.radius_lt_source.trans
      (Real.exp_lt_exp.mpr (by norm_num)))
  have hlength := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 5/8) hroom
  filter_upwards [eventually_ge_atTop 32,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually hlength,
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_core_length_chamber hu hU (h := h)),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_boundary_cell_floor hh hhu hα hβ),
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder.eventually
      (eventually_supply_cell_lower hh hhu hα hβ)]
    with j hj hL hch hfour hfive I J lo4 H4 lo5 H5 t y
  dsimp only
  intro htlo hthi h4 h5 hsep
  let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
  let K := ZetaRieszPrimeCountFrequency.dyadicPrimeCount j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := ZetaRieszParityPacket.coreBand u N K
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let F4 := fun i => boundaryCell S L t h y (lo4 i) (H4 i)
  let F5 := fun i => supplyCell t h y (lo5 i) (H5 i)
  let D4 := I.biUnion F4
  let D5 := J.biUnion F5
  have hL0 := SquarefreeVaughanLogSource.length_pos u N
  have hch' := hch t htlo hthi
  have h4bound (i : ι) (hi : i ∈ I) :
      -cellDebit N L t h y (lo4 i) (H4 i) ≤ (∑ n ∈ F4 i, f n).re := by
    obtain ⟨hlo,hH,hmin⟩ := h4 i hi
    exact hfour (lo4 i) (H4 i) A S L t y hlo hH hL0 hch'.1 hch'.2 hmin
  have h5bound (i : κ) (hi : i ∈ J) :
      cellCredit N L t h y (lo5 i) (H5 i) ≤ (∑ n ∈ F5 i, f n).re := by
    obtain ⟨hlo,hH,ho,hmin,hqp,hmax,hsat,htriple⟩ := h5 i hi
    exact hfive (lo5 i) (H5 i) A L t y hlo hH ho hL0 hmin hqp hmax hsat htriple
  have h4S : D4 ⊆ S := Finset.biUnion_subset.mpr
    (fun i _ => boundaryCell_subset S L t h y (lo4 i) (H4 i))
  have h5S : D5 ⊆ S := by
    apply Finset.biUnion_subset.mpr
    intro i hi
    by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
    · obtain ⟨_hlo,_hH,ho,_hmin,hqp,hmax,_hsat,_htriple⟩ := h5 i hi
      simpa only [F5,supplyCell,if_pos hp] using
        (ZetaRieszFivePrimeCells.cell_products_subset_core j hj hu hU (by linarith)
          ho hqp hmax htlo hthi)
    · simp only [F5,supplyCell,if_neg hp,Finset.empty_subset]
  have hdis5 : Set.PairwiseDisjoint (↑J) F5 := by
    intro i hi v hv hiv
    by_cases hp : Real.cos (y*t)+|y| * h ≤ 0
    · obtain ⟨_,_,hiorder,_,hiqp,himax,_,_⟩ := h5 i hi
      obtain ⟨_,_,hvorder,_,hvqp,hvmax,_,_⟩ := h5 v hv
      simpa only [F5,supplyCell,if_pos hp] using
        (ZetaRieszFivePrimeCells.cell_products_disjoint hiorder hvorder hiqp hvqp
          himax hvmax (hsep i hi v hv hiv))
    · simp only [F5,supplyCell,if_neg hp,Finset.disjoint_empty_left]
  have hdis45 : Disjoint D4 D5 := by
    apply (Finset.disjoint_biUnion_left I F4 D5).mpr
    intro i _hi
    apply (Finset.disjoint_biUnion_right (F4 i) J F5).mpr
    intro v hv
    obtain ⟨_,_,hvorder,_,hvqp,hvmax,_,_⟩ := h5 v hv
    exact boundary_supply_disjoint S L t h y hvorder hvqp hvmax
  have hfourSum : -(∑ i ∈ I, cellDebit N L t h y (lo4 i) (H4 i)) ≤
      (∑ n ∈ D4, f n).re := by
    have h₁ := Finset.sum_le_sum h4bound
    have h₂ := sum_cells_le_union_of_nonpos I F4 (fun n => (f n).re)
      (fun i _ n hn => boundaryCell_atom_nonpos S A N L t h y (lo4 i) (H4 i) hn)
    simp only [← Complex.re_sum] at h₂
    simp only [← Complex.re_sum,Finset.sum_neg_distrib] at h₁
    exact h₁.trans h₂
  have hfiveSum : (∑ i ∈ J, cellCredit N L t h y (lo5 i) (H5 i)) ≤
      (∑ n ∈ D5, f n).re := by
    rw [Finset.sum_biUnion hdis5,Complex.re_sum]
    exact Finset.sum_le_sum h5bound
  have hDS : D4 ∪ D5 ⊆ S := Finset.union_subset h4S h5S
  have he := congrArg Complex.re (Finset.sum_sdiff (f := f) hDS)
  rw [Finset.sum_union hdis45,Complex.add_re,Complex.add_re] at he
  change _ ≤ (∑ n ∈ S, f n).re
  linarith

end
end RiemannGaussian.ZetaRieszJointPrimeCells
