/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointPrimeEnergy
import RiemannGaussian.ZetaRieszCentralRadialCost

/-!
# Retaining cofactor phase cancellation before the cutoff energy

The earlier joint cost squares each cofactor weight separately. Here its
literal signed correlation with the sharp Möbius prefix is summed first.
Finite summation by parts and weighted Cauchy--Schwarz give both signed
bounds without an unevaluated arithmetic constant. This is an inequality
for the original finite carrier, not a prime-density completion.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszCofactorPhaseEnergy
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy

/-- The actual sharp divisor prefix, with all subset signs. -/
def sharp (k n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 k, if d ∣ n then (μ d : ℝ) else 0

/-- The original cofactor weights, including their phase and all masks,
are summed against the arithmetic prefix before any square or norm. -/
def correlation (S : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ S, w n*sharp k n

/-- Only cutoffs at which the exact profile changes can contribute. -/
def activeCutoffs (R : ℕ) (f : ℕ → ℝ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun k => f k ≠ f (k+1))

/-- The cofactor phase remains inside this signed arithmetic correlation. -/
def phaseEnergy (R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ activeCutoffs R f, correlation S w k^2/(k : ℝ)

/-- The existing finite cutoff profile energy, on its exact support. -/
def profileEnergy (R : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ activeCutoffs R f, (k : ℝ)*(f k-f (k+1))^2

/-- No derivative cutoff is omitted: inactive terms have exactly zero energy. -/
theorem profileEnergy_eq (R : ℕ) (f : ℕ → ℝ) :
    profileEnergy R f = ∑ k ∈ Finset.Icc 1 R, (k : ℝ)*(f k-f (k+1))^2 := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hn
  have he : f k = f (k+1) := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hk,h⟩)
  simp [he]

/-- The full signed sum is bounded after cofactor cancellation. There is
no arithmetic-mean constant and no absolute value on individual cofactors. -/
theorem signed_prefix_bound (R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hend : f (R+1)=0) :
    |∑ n ∈ S, w n*(∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0))| ≤
      sqrt (phaseEnergy R S w f*profileEnergy R f) := by
  have he : (∑ n ∈ S, w n*(∑ d ∈ Finset.Icc 1 R,
      f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ k ∈ activeCutoffs R f, correlation S w k*(f k-f (k+1)) := by
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile R f _ hend, Finset.mul_sum]
    rw [Finset.sum_comm]
    symm
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).trans
    · apply Finset.sum_congr rfl
      intro k _
      simp only [correlation,sharp,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    · intro k hk hn
      have he : f k=f (k+1) := by
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨hk,h⟩)
      simp [he]
  rw [he]
  apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
  have hp : 0 ≤ phaseEnergy R S w f :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hq : 0 ≤ profileEnergy R f :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  rw [sq_abs,sq_sqrt (mul_nonneg hp hq)]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (activeCutoffs R f)
    (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  intro k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    exact_mod_cast (by omega : k ≠ 0)
  apply le_of_eq
  field_simp

/-- Duality recovers the former mean budget with ONE universal constant.
The signed prefix energy can be strictly smaller; its cross-cofactor terms
have not been removed by this upper comparison. -/
theorem exists_phaseEnergy_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ (X R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      phaseEnergy R S w f ≤ E*X*(∑ n ∈ S, w n^2) := by
  obtain ⟨E,hE,hmean⟩ := ZetaRieszSignedCutoffEnergy.exists_signed_profile_mean
  refine ⟨E,hE,fun X R S w f hS hSF => ?_⟩
  let b := fun k => if k ∈ activeCutoffs R f then correlation S w k/(k : ℝ) else 0
  let q := phaseEnergy R S w f
  have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have henergy : (∑ k ∈ Finset.Icc 1 R, (k : ℝ)*b k^2)=q := by
    simp only [b,ite_pow,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_ite,mul_zero,
      ← Finset.sum_filter]
    have hfilter : (Finset.Icc 1 R).filter (fun k => k ∈ activeCutoffs R f) =
        activeCutoffs R f := Finset.filter_mem_eq_inter.trans
      (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
      exact_mod_cast (by omega : k ≠ 0)
    field_simp
  have hpair : (∑ n ∈ S, w n*(∑ k ∈ Finset.Icc 1 R, b k*sharp k n))=q := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner k : (∑ n ∈ S, w n*(b k*sharp k n))=b k*correlation S w k := by
      simp only [correlation,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    simp_rw [hinner]
    simp only [b,ite_mul,zero_mul,← Finset.sum_filter]
    have hfilter : (Finset.Icc 1 R).filter (fun k => k ∈ activeCutoffs R f) =
        activeCutoffs R f := Finset.filter_mem_eq_inter.trans
      (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
    rw [hfilter]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hm := hmean X R S b hS hSF
  rw [henergy] at hm
  have hc := (Finset.sum_mul_sq_le_sq_mul_sq S w
    (fun n => ∑ k ∈ Finset.Icc 1 R, b k*sharp k n)).trans
      (mul_le_mul_of_nonneg_left hm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [hpair] at hc
  by_cases hzero : q=0
  · rw [show phaseEnergy R S w f=q from rfl,hzero]
    positivity
  · have hpos := lt_of_le_of_ne hq (Ne.symm hzero)
    change q ≤ _
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [hc]

/-- Joint prime coordinates are unchanged; each coordinate now keeps its
cofactor phases coupled through every sharp divisor cutoff. The affine-log
null profile may still be chosen freely, with no discarded correction. -/
def cost (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ)
    (slope : ℕ → ℝ) : ℝ :=
  ∑ a ∈ I,
    let f := centeredProfile X (fun d => rotate P O a (fun p => F p d)) (slope a)
    sqrt (phaseEnergy X S (fun n => rotate P O a (W n)) f*profileEnergy X f)

/-- Both signed inequalities for the complete original matrix. Only exact
finite algebraic coordinate conditions occur; identity coordinates suffice. -/
theorem joint_bounds (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ)
    (slope : ℕ → ℝ) (hO : Coordinates I P O)
    (hS : S ⊆ Finset.Ioc 1 X) (hSF : ∀ n ∈ S, Squarefree n ∧ ¬n.Prime) :
    let J := ∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n;
    let C := cost X S I P O W F slope;
    -C ≤ J ∧ J ≤ C := by
  let f := fun a => centeredProfile X
    (fun d => rotate P O a (fun p => F p d)) (slope a)
  let w := fun a n => rotate P O a (W n)
  have he n (hn : n ∈ S) a :
      (∑ d ∈ Finset.Icc 1 X, f a d*(if d ∣ n then (μ d : ℝ) else 0)) =
        rotate P O a (fun p => divisorResponse (F p) n) := by
    have hx := Finset.mem_Ioc.mp (hS hn)
    rw [prefix_eq_divisors (by omega : 0 < n) hx.2]
    rw [divisor_centering (hSF n hn).1 (hSF n hn).2 (by omega) hx.2]
    simp only [rotate,divisorResponse,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hs : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      ∑ a ∈ I, ∑ n ∈ S, w a n*(∑ d ∈ Finset.Icc 1 X,
        f a d*(if d ∣ n then (μ d : ℝ) else 0)) := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp_rw [he n hn]
    exact (coordinate_pairing I P O hO (W n)
      (fun p => divisorResponse (F p) n)).symm
  apply abs_le.mp
  rw [hs]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ =>
    signed_prefix_bound X S (w a) (f a) (by simp [f,centeredProfile])))

private theorem profileEnergy_centered (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    profileEnergy X (centeredProfile X f a) = shiftedEnergy X f a := by
  rw [profileEnergy_eq]
  have he : ∀ k ∈ Finset.Ico 1 X,
      centeredProfile X f a k-centeredProfile X f a (k+1) = f k-f (k+1)-a*logStep k := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    simp only [centeredProfile,if_pos (by omega : k ≤ X),if_pos (by omega : k+1 ≤ X),logStep]
    ring
  have hx : centeredProfile X f a X=0 := by simp [centeredProfile]
  have hx' : centeredProfile X f a (X+1)=0 := by simp [centeredProfile]
  unfold shiftedEnergy
  rw [← Finset.sum_congr rfl (fun (k : ℕ) hk => congrArg (fun z : ℝ => (k : ℝ)*z^2) (he k hk))]
  symm
  apply Finset.sum_subset (by
    intro k hk
    have := Finset.mem_Ico.mp hk
    exact Finset.mem_Icc.mpr ⟨this.1,this.2.le⟩)
  intro k hk hk'
  have hkX : k=X := by simp only [Finset.mem_Icc,Finset.mem_Ico] at hk hk'; omega
  rw [hkX,hx,hx']
  simp

/-- With the same universal mean budget, the cofactor-phase cost never
exceeds the earlier centered joint cost. All signed cross-cofactor terms
are retained on the smaller side, independently of phase or prime count. -/
theorem exists_cost_le_joint :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ),
      S ⊆ Finset.Ioc 1 X → (∀ n ∈ S, Squarefree n) →
      cost X S I P O W F (fun a =>
        logCross X (fun d => rotate P O a (fun p => F p d))/logEnergy X) ≤
      jointCost E X S I P O W F := by
  obtain ⟨E,hE,hbound⟩ := exists_phaseEnergy_bound
  refine ⟨E,hE,fun X S I P O W F hS hSF => ?_⟩
  apply Finset.sum_le_sum
  intro a _
  dsimp only
  rw [profileEnergy_centered]
  apply sqrt_le_sqrt
  have hb := hbound X X S (fun n => rotate P O a (W n))
    (centeredProfile X (fun d => rotate P O a (fun p => F p d))
      (logCross X (fun d => rotate P O a (fun p => F p d))/logEnergy X)) hS hSF
  have h := mul_le_mul_of_nonneg_right hb
    (centeredEnergy_nonneg X (fun d => rotate P O a (fun p => F p d)))
  simpa only [centeredEnergy,mul_assoc,mul_left_comm,mul_comm] using h

open ZetaRieszJointAllocation

/-- The new cost applied to the unchanged factorial prime weights. -/
def primePhaseCost (X N : ℕ) (A S I P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ) (L y scale : ℝ) : ℝ :=
  cost X S I P O (maskedWeight A Q L y scale N) (hinge L) slope

/-- BOTH signed literal arithmetic bounds, without an unknown multiplicative
constant. Original prime-row holes, full factorial allocation, cofactor
signs and product phase are inside the new explicit cost. -/
theorem literal_bounds (X N : ℕ) (A S I P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ) (L y scale : ℝ)
    (hO : Coordinates I P O) (hS : S ⊆ Finset.Ioc 1 X)
    (hSF : ∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card)
    (hQ : ∀ n ∈ S, Q n ⊆ P)
    (hp : ∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) :
    let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
      residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
    let C := primePhaseCost X N A S I P Q O slope L y scale;
    -C ≤ J ∧ J ≤ C := by
  have hnp n (hn : n ∈ S) : ¬n.Prime := by
    intro h
    have hc := (hSF n hn).2
    simp [h.primeFactors] at hc
  have hb := joint_bounds X S I P O (maskedWeight A Q L y scale N) (hinge L)
    slope hO hS (fun n hn => ⟨(hSF n hn).1,hnp n hn⟩)
  have he : (∑ n ∈ S, ∑ p ∈ P,
      maskedWeight A Q L y scale N n p*divisorResponse (hinge L p) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        residualCoefficient A L N (p*n)*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re := by
    simp only [Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hfilter : P.filter (fun p => p ∈ Q n)=Q n := by
      rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (hQ n hn)]
    simp only [maskedWeight,ite_mul,zero_mul,← Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro p hpn
    rw [atom_eq A L y N (hSF n hn).1 (hSF n hn).2 (hp n hn p hpn).1 (hp n hn p hpn).2]
    ring
  simpa only [he,primePhaseCost] using hb

/-- The exact phase cost of a whole finite support with canonical ownership. -/
def wholePhaseCost (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  primePhaseCost ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O slope L y scale

/-- All squarefree labels/counts in the specified support are covered once.
There is no completion, omitted exterior, or prime-distribution premise. -/
theorem whole_bounds (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (hO : Coordinates I (ownerPrimes B) O) :
    let J := scale*(∑ m ∈ B,
      residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
    let C := wholePhaseCost A B I O slope N L y scale;
    -C ≤ J ∧ J ≤ C := by
  have hS : cofactors B ⊆ Finset.Ioc 1 ((cofactors B).sup id) := by
    intro n hn
    have hd := cofactors_data B hB hn
    have hn1 : n ≠ 1 := by intro h; simp [h] at hd
    exact Finset.mem_Ioc.mpr ⟨by have := hd.1.ne_zero; omega,Finset.le_sup (f := id) hn⟩
  have hb := literal_bounds ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O slope L y scale hO hS (fun _ hn => cofactors_data B hB hn)
    (by
      intro n _ p hp
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨m,(Finset.mem_filter.mp hm).1,rfl⟩)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.1⟩)
  have he := ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B)
    (fun m => residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m)
    (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩)
  rw [owner_labels_eq B hB] at he
  simpa only [he,wholePhaseCost,Nat.mul_comm] using hb

/-- Disjoint populations may be combined with their actual computed phase
costs. Every prime count stays in its original population; no count factor
or unknown arithmetic constant is introduced. -/
theorem partition_bounds (A I : Finset ℕ) (B V : ℕ → Finset ℕ)
    (O : ℕ → ℕ → ℕ → ℝ) (slope : ℕ → ℕ → ℝ) (N : ℕ) (L y scale : ℝ)
    (hdis : (I : Set ℕ).PairwiseDisjoint B)
    (hB : ∀ i ∈ I, ∀ m ∈ B i, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (hO : ∀ i ∈ I, Coordinates (V i) (ownerPrimes (B i)) (O i)) :
    let J := scale*(∑ m ∈ I.biUnion B,
      residualCoefficient A L N m*zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
    let C := ∑ i ∈ I, wholePhaseCost A (B i) (V i) (O i) (slope i) N L y scale;
    -C ≤ J ∧ J ≤ C := by
  have hb i (hi : i ∈ I) :=
    whole_bounds A (B i) (V i) (O i) (slope i) N L y scale (hB i hi) (hO i hi)
  dsimp only
  rw [Finset.sum_biUnion hdis,Complex.re_sum,Finset.mul_sum]
  have hlo := Finset.sum_le_sum (fun i hi => (hb i hi).1)
  rw [Finset.sum_neg_distrib] at hlo
  exact ⟨hlo,Finset.sum_le_sum (fun i hi => (hb i hi).2)⟩

open ZetaRieszParityPacket

/-- An unconditional constant-free enclosure of the ORIGINAL whole core.
Every moving mask and all factorial orders remain. A sufficient eventual
size bound for this explicit signed-correlation cost is still required. -/
theorem core_bounds (u y : ℝ) (N K : ℕ) (I : Finset ℕ)
    (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ)
    (hO : Coordinates I (ownerPrimes ((coreBand u N K).filter Squarefree)) O) :
    let C := wholePhaseCost (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      ((coreBand u N K).filter Squarefree) I O slope N
      (SquarefreeVaughanLogSource.length u N) y (u^(N+1));
    -C ≤ u^(N+1)*(coreResponse u y N K).re ∧
      u^(N+1)*(coreResponse u y N K).re ≤ C := by
  have hB : ∀ m ∈ (coreBand u N K).filter Squarefree,
      Squarefree m ∧ 3 ≤ m.primeFactors.card := by
    intro m hm
    have h := Finset.mem_filter.mp hm
    exact ⟨h.2,core_count h.1⟩
  have h := whole_bounds (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) I O slope N
    (SquarefreeVaughanLogSource.length u N) y (u^(N+1)) hB hO
  simpa only [core_eq_squarefree] using h

open Filter Topology

/-- Both whole-core bounds retain the better of the new signed-correlation
cost and the already proved large-order radial bound. The old outer error
is charged only on the radial branch; the new cost covers the full core. -/
theorem exists_eventual_core_intersection :
    ∃ E C : ℝ, 0 < E ∧ 0 ≤ C ∧ ∀ (u : ℝ),
      0 < u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
      ∀ᶠ N : ℕ in atTop, ∀ (y : ℝ) (K : ℕ) (I : Finset ℕ)
        (O : ℕ → ℕ → ℝ) (slope : ℕ → ℝ),
        Coordinates I (ownerPrimes ((coreBand u N K).filter Squarefree)) O →
        let D := wholePhaseCost (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          ((coreBand u N K).filter Squarefree) I O slope N
          (SquarefreeVaughanLogSource.length u N) y (u^(N+1));
        let G := min (ZetaRieszCentralCostGrowth.growthBound E u N)
          (ZetaRieszCentralRadialCost.radialGrowthBound E u N)+ZetaRieszLargeOrderCore.rate^N*C;
        -min D G ≤ u^(N+1)*(coreResponse u y N K).re ∧
          u^(N+1)*(coreResponse u y N K).re ≤ min D G := by
  obtain ⟨E,C,hE,hC,hbound⟩ := ZetaRieszCentralRadialCost.exists_eventual_core_radial_bound
  refine ⟨E,C,hE,hC,fun u hu hU => ?_⟩
  filter_upwards [hbound u hu hU] with N hb y K I O slope hO
  have hphase := core_bounds u y N K I O slope hO
  have hrad := hb y K
  dsimp only at hphase hrad ⊢
  have hi {J D G : ℝ} (hd : -D ≤ J ∧ J ≤ D) (hg : -G ≤ J ∧ J ≤ G) :
      -min D G ≤ J ∧ J ≤ min D G := by
    have hl : -J ≤ min D G := le_min (by linarith only [hd.1]) (by linarith only [hg.1])
    exact ⟨by linarith only [hl],le_min hd.2 hg.2⟩
  exact hi hphase hrad.2

end RiemannGaussian.ZetaRieszCofactorPhaseEnergy
