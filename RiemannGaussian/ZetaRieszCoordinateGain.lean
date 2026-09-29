/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszConditionedPrimeEnergy

/-!
# A coordinate saving raises the original floor and lowers its ceiling

The signed arithmetic center is invariant under every admissible common
prime-coordinate map. An exact reduction of the existing cost therefore
improves both endpoints by the same nonnegative amount. Rational plane
rotations provide admissible choices without deleting a prime direction.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszCoordinateGain
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszQuadraticPrimeEnergy ZetaRieszConditionedPrimeEnergy

private theorem cross_rotate (X : ℕ) (P : Finset ℕ) (O F : ℕ → ℕ → ℝ) (a : ℕ) :
    logCross X (fun d => rotate P O a (fun p => F p d)) =
      rotate P O a (fun p => logCross X (F p)) := by
  simp only [logCross,rotate,← Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

private theorem delta_rotate (X : ℕ) (P : Finset ℕ) (O F : ℕ → ℕ → ℝ) (a k : ℕ) :
    centeredDelta X (fun d => rotate P O a (fun p => F p d)) k =
      rotate P O a (fun p => centeredDelta X (F p) k) := by
  simp only [centeredDelta]
  rw [cross_rotate]
  simp only [rotate,Finset.sum_div,Finset.sum_mul,mul_sub,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem slope_rotate (X : ℕ) (P : Finset ℕ) (O F : ℕ → ℕ → ℝ) (a : ℕ) :
    quadraticSlope X (fun d => rotate P O a (fun p => F p d)) =
      rotate P O a (fun p => quadraticSlope X (F p)) := by
  simp only [quadraticSlope,quadraticCross]
  simp_rw [delta_rotate]
  simp only [rotate,Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-- The signed center is the SAME literal arithmetic sum in every admissible
coordinate system. Optimizing the width introduces no new center to pay. -/
theorem center_eq_unrotated (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ)
    (hO : Coordinates I P O) :
    quadraticCenter X S I P O W F =
      ∑ n ∈ S, ∑ p ∈ P, W n p*quadraticSlope X (F p)*secondMoment n := by
  simp only [quadraticCenter,slope_rotate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_mul]
  have he : (∑ a ∈ I, rotate P O a (fun p => quadraticSlope X (F p))*
      (rotate P O a (W n)*secondMoment n)) =
      (∑ a ∈ I, rotate P O a (W n)*rotate P O a (fun p => quadraticSlope X (F p)))*secondMoment n := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he,coordinate_pairing I P O hO]

/-- Exact signed cross terms in the two-coordinate quadratic energy. -/
theorem pair_energy (S : Finset ℕ) (w v : ℕ → ℝ) (c s : ℝ) :
    (∑ n ∈ S, (c*w n+s*v n)^2) =
      c^2*(∑ n ∈ S, w n^2)+s^2*(∑ n ∈ S, v n^2)+
        2*c*s*(∑ n ∈ S, w n*v n) := by
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem sum_changed_two (I : Finset ℕ) (f g : ℕ → ℝ) {a b : ℕ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (hsame : ∀ i ∈ I, i ≠ a → i ≠ b → g i=f i) :
    (∑ i ∈ I, g i) = (∑ i ∈ I, f i)-f a-f b+g a+g b := by
  have hb' : b ∈ I.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,hb⟩
  have hf1 := Finset.sum_erase_add I f ha
  have hf2 := Finset.sum_erase_add (I.erase a) f hb'
  have hg1 := Finset.sum_erase_add I g ha
  have hg2 := Finset.sum_erase_add (I.erase a) g hb'
  have hs : (∑ i ∈ (I.erase a).erase b, g i)=(∑ i ∈ (I.erase a).erase b, f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h1 := Finset.mem_erase.mp hi
    have h2 := Finset.mem_erase.mp h1.2
    exact hsame i h2.2 h2.1 h1.1
  linarith

/-- Rotate exactly two coordinates; every other prime direction remains. -/
def pairRotate (O : ℕ → ℕ → ℝ) (a b : ℕ) (c s : ℝ) (i p : ℕ) : ℝ :=
  if i=a then c*O a p+s*O b p else
  if i=b then -s*O a p+c*O b p else O i p

/-- A plane rotation preserves the exact finite arithmetic pairing. No
prime mode, row, factorial order or actual integer is discarded. -/
theorem coordinates_pairRotate (I P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (hO : Coordinates I P O) {a b : ℕ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (c s : ℝ) (hcs : c^2+s^2=1) : Coordinates I P (pairRotate O a b c s) := by
  intro p hp q hq
  rw [sum_changed_two I (fun i => O i p*O i q) _ ha hb hab
    (fun i _ hia hib => by simp [pairRotate,hia,hib])]
  simp only [pairRotate,ite_true,if_neg (Ne.symm hab)]
  rw [hO p hp q hq]
  have he : (c*O a p+s*O b p)*(c*O a q+s*O b q)+
      (-s*O a p+c*O b p)*(-s*O a q+c*O b q) = O a p*O a q+O b p*O b q := by
    calc
      _ = (c^2+s^2)*(O a p*O a q+O b p*O b q) := by ring
      _ = _ := by rw [hcs,one_mul]
  linarith only [he]

/-- A rational parameter gives exact rotation coefficients, with no
floating orthogonality or normalization assumption. -/
def rationalPair (O : ℕ → ℕ → ℝ) (a b : ℕ) (t : ℝ) : ℕ → ℕ → ℝ :=
  pairRotate O a b ((1-t^2)/(1+t^2)) (2*t/(1+t^2))

/-- Every rational-plane candidate is an admissible input to the ORIGINAL
joint bound. This theorem also permits any real parameter. -/
theorem coordinates_rationalPair (I P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (hO : Coordinates I P O) {a b : ℕ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b)
    (t : ℝ) : Coordinates I P (rationalPair O a b t) := by
  apply coordinates_pairRotate I P O hO ha hb hab
  have hd : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Apply a finite exact rational rotation recipe, keeping every coordinate. -/
def rationalSequence (O : ℕ → ℕ → ℝ) (steps : List (ℕ × ℕ × ℚ)) : ℕ → ℕ → ℝ :=
  steps.foldl (fun Q step => rationalPair Q step.1 step.2.1 step.2.2) O

/-- An exact rational recipe is admissible from any admissible starting
map, in particular from identity coordinates. Numerical cost certification
is a separate obligation; this proves the recipe's exact algebra. -/
theorem coordinates_rationalSequence (I P : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (hO : Coordinates I P O) (steps : List (ℕ × ℕ × ℚ))
    (hsteps : ∀ step ∈ steps, step.1 ∈ I ∧ step.2.1 ∈ I ∧ step.1 ≠ step.2.1) :
    Coordinates I P (rationalSequence O steps) := by
  induction steps generalizing O with
  | nil => exact hO
  | cons step rest ih =>
    have hs := hsteps step (List.mem_cons_self ..)
    exact ih _ (coordinates_rationalPair I P O hO hs.1 hs.2.1 hs.2.2 step.2.2)
      (fun s hs => hsteps s (List.mem_cons_of_mem _ hs))

/-- A nonnegative, exact reduction in the existing cost. This is a budget
comparison, not a new carrier or a numerical certification predicate. -/
def gain (oldCost newCost : ℝ) : ℝ := max 0 (oldCost-newCost)

/-- A strict reduction in the existing cost gives a strictly positive gain. -/
theorem gain_pos {oldCost newCost : ℝ} (h : newCost < oldCost) :
    0 < gain oldCost newCost := lt_max_of_lt_right (sub_pos.mpr h)

private theorem improve_enclosure {J H B C D : ℝ}
    (hbase : -B ≤ J ∧ J ≤ B) (hC : H-C ≤ J ∧ J ≤ H+C)
    (hD : H-D ≤ J ∧ J ≤ H+D) :
    max (-B) (H-C+gain C D) ≤ J ∧ J ≤ min B (H+C-gain C D) := by
  by_cases h : D ≤ C
  · rw [gain,max_eq_right (sub_nonneg.mpr h)]
    exact ⟨max_le hbase.1 (by linarith only [hD.1]),le_min hbase.2 (by linarith only [hD.2])⟩
  · rw [gain,max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),add_zero,sub_zero]
    exact ⟨max_le hbase.1 hC.1,le_min hbase.2 hC.2⟩

/-- Every admissible coordinate change keeps the WHOLE literal center
exactly unchanged, before either signed inequality is used. -/
theorem wholeCenter_eq (A B I₀ I₁ : Finset ℕ) (O₀ O₁ : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ)
    (h₀ : Coordinates I₀ (ownerPrimes B) O₀) (h₁ : Coordinates I₁ (ownerPrimes B) O₁) :
    wholeCenter A B I₀ O₀ N L y scale=wholeCenter A B I₁ O₁ N L y scale :=
  (center_eq_unrotated _ _ _ _ _ _ _ h₀).trans
    (center_eq_unrotated _ _ _ _ _ _ _ h₁).symm

open ZetaRieszParityPacket

/-- The directly probed quadratic cost has the SAME exact two-sided gain
rule. E remains the original, unevaluated arithmetic constant. -/
theorem exists_core_quadratic_gain_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I₀ I₁ : Finset ℕ)
      (O₀ O₁ : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I₀ (ownerPrimes B) O₀ → Coordinates I₁ (ownerPrimes B) O₁ →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H := wholeCenter A B I₀ O₀ N L y (u^(N+1));
      let C := wholeQuadraticCost E A B I₀ O₀ N L y (u^(N+1));
      let D := wholeQuadraticCost E A B I₁ O₁ N L y (u^(N+1));
      let B₀ := wholeCost E A B I₀ O₀ N L y (u^(N+1));
      let J := u^(N+1)*(coreResponse u y N K).re;
      max (-B₀) (H-C+gain C D) ≤ J ∧ J ≤ min B₀ (H+C-gain C D) := by
  obtain ⟨E,hE,hbound⟩ := exists_core_quadratic_bounds
  refine ⟨E,hE,fun u y N K I₀ I₁ O₀ O₁ h₀ h₁ => ?_⟩
  have h0 := hbound u y N K I₀ O₀ h₀
  have h1 := hbound u y N K I₁ O₁ h₁
  dsimp only at h0 h1 ⊢
  rw [← wholeCenter_eq _ _ _ _ _ _ _ _ _ _ h₀ h₁] at h1
  exact improve_enclosure ⟨(max_le_iff.mp h0.1).1,(le_min_iff.mp h0.2.1).1⟩
    ⟨(max_le_iff.mp h0.1).2,(le_min_iff.mp h0.2.1).2⟩
    ⟨(max_le_iff.mp h1.1).2,(le_min_iff.mp h1.2.1).2⟩

/-- Disjoint cofactor/owner populations ADD their actual cost savings.
Each population may select its own coordinates, retaining all its labels,
all counts and its exact signed center. There is no family-count loss. -/
theorem exists_partition_quadratic_gain_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A I : Finset ℕ) (B V₀ V₁ : ℕ → Finset ℕ)
      (O₀ O₁ : ℕ → ℕ → ℕ → ℝ) (N : ℕ) (L y scale : ℝ),
      (I : Set ℕ).PairwiseDisjoint B →
      (∀ i ∈ I, ∀ m ∈ B i, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      (∀ i ∈ I, Coordinates (V₀ i) (ownerPrimes (B i)) (O₀ i)) →
      (∀ i ∈ I, Coordinates (V₁ i) (ownerPrimes (B i)) (O₁ i)) →
      let J := scale*(∑ m ∈ I.biUnion B,
        ZetaRieszJointAllocation.residualCoefficient A L N m*
          zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let H := ∑ i ∈ I, wholeCenter A (B i) (V₀ i) (O₀ i) N L y scale;
      let C := ∑ i ∈ I, wholeQuadraticCost E A (B i) (V₀ i) (O₀ i) N L y scale;
      let G := ∑ i ∈ I, gain
        (wholeQuadraticCost E A (B i) (V₀ i) (O₀ i) N L y scale)
        (wholeQuadraticCost E A (B i) (V₁ i) (O₁ i) N L y scale);
      H-C+G ≤ J ∧ J ≤ H+C-G := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_quadratic_bounds
  refine ⟨E,hE,fun A I B V₀ V₁ O₀ O₁ N L y scale hdis hB hO₀ hO₁ => ?_⟩
  have hb i (hi : i ∈ I) := hbound A (B i) (V₀ i) (O₀ i) N L y scale
    (hB i hi) (hO₀ i hi)
  have hd i (hi : i ∈ I) := hbound A (B i) (V₁ i) (O₁ i) N L y scale
    (hB i hi) (hO₁ i hi)
  have hcell i (hi : i ∈ I) := by
    have h0 := hb i hi
    have h1 := hd i hi
    dsimp only at h0 h1
    rw [← wholeCenter_eq _ _ _ _ _ _ _ _ _ _ (hO₀ i hi) (hO₁ i hi)] at h1
    have h := improve_enclosure
      ⟨(max_le_iff.mp h0.1).1,(le_min_iff.mp h0.2.1).1⟩
      ⟨(max_le_iff.mp h0.1).2,(le_min_iff.mp h0.2.1).2⟩
      ⟨(max_le_iff.mp h1.1).2,(le_min_iff.mp h1.2.1).2⟩
    exact And.intro (max_le_iff.mp h.1).2 (le_min_iff.mp h.2).2
  dsimp only
  rw [Finset.sum_biUnion hdis,Complex.re_sum,Finset.mul_sum]
  constructor
  · simpa only [Finset.sum_add_distrib,Finset.sum_sub_distrib] using
      Finset.sum_le_sum (fun i hi => (hcell i hi).1)
  · simpa only [Finset.sum_add_distrib,Finset.sum_sub_distrib] using
      Finset.sum_le_sum (fun i hi => (hcell i hi).2)

/-- A coordinate saving raises the whole-core floor and lowers its ceiling
by the SAME exact gain, with unchanged arithmetic center and constant.
All original labels and masks remain. A small eventual cost is still open. -/
theorem exists_core_gain_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I₀ I₁ : Finset ℕ)
      (O₀ O₁ : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I₀ (ownerPrimes B) O₀ → Coordinates I₁ (ownerPrimes B) O₁ →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H := wholeCenter A B I₀ O₀ N L y (u^(N+1));
      let C := wholeConditionedCost E A B I₀ O₀ N L y (u^(N+1));
      let D := wholeConditionedCost E A B I₁ O₁ N L y (u^(N+1));
      let B₀ := wholeCost E A B I₀ O₀ N L y (u^(N+1));
      let J := u^(N+1)*(coreResponse u y N K).re;
      max (-B₀) (H-C+gain C D) ≤ J ∧ J ≤ min B₀ (H+C-gain C D) := by
  obtain ⟨E,hE,hbound⟩ := exists_core_conditioned_bounds
  refine ⟨E,hE,fun u y N K I₀ I₁ O₀ O₁ h₀ h₁ => ?_⟩
  have h0 := hbound u y N K I₀ O₀ h₀
  have h1 := hbound u y N K I₁ O₁ h₁
  dsimp only at h0 h1 ⊢
  rw [← wholeCenter_eq _ _ _ _ _ _ _ _ _ _ h₀ h₁] at h1
  exact improve_enclosure ⟨(max_le_iff.mp h0.1).1,(le_min_iff.mp h0.2.1).1⟩
    ⟨(max_le_iff.mp h0.1).2,(le_min_iff.mp h0.2.1).2⟩
    ⟨(max_le_iff.mp h1.1).2,(le_min_iff.mp h1.2.1).2⟩

end RiemannGaussian.ZetaRieszCoordinateGain
