/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszQuadraticPrimeEnergy

/-!
# Deduct the known arithmetic moment from the remaining signed allowance

The exact second divisor moment constrains the same weighted arithmetic
functional used in both carrier bounds. Orthogonality of the quadratic
residual lets its known squared correlation be removed before the square
root. Every prime count, original phase and factorial order remains.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszConditionedPrimeEnergy
open Real ZetaRieszJointPrimeEnergy ZetaRieszCenteredPrimeEnergy
  ZetaRieszQuadraticPrimeEnergy

private theorem energy_delta (X : ℕ) (f : ℕ → ℝ) :
    centeredEnergy X f = ∑ k ∈ Finset.Ico 1 X, (k : ℝ)*centeredDelta X f k^2 := rfl

private theorem delta_linear (X : ℕ) (f g : ℕ → ℝ) (a b : ℝ) (k : ℕ) :
    centeredDelta X (fun d => a*f d+b*g d) k =
      a*centeredDelta X f k+b*centeredDelta X g k := by
  have he : logCross X (fun d => a*f d+b*g d)=a*logCross X f+b*logCross X g := by
    simp only [logCross,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [centeredDelta,he]
  ring

private theorem quadratic_orthogonal (X : ℕ) (f : ℕ → ℝ)
    (hV : centeredEnergy X logSquare ≠ 0) :
    quadraticCross X (quadraticProfile X f)=0 := by
  have he : quadraticProfile X f = fun d => 1*f d+(-quadraticSlope X f)*logSquare d := by
    funext d
    simp [quadraticProfile,sub_eq_add_neg]
  rw [he]
  simp only [quadraticCross,delta_linear]
  have hs : (∑ k ∈ Finset.Ico 1 X,
      (k : ℝ)*(1*centeredDelta X f k+(-quadraticSlope X f)*centeredDelta X logSquare k)*
        centeredDelta X logSquare k) =
      quadraticCross X f-quadraticSlope X f*centeredEnergy X logSquare := by
    simp only [quadraticCross,energy_delta,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hs,quadraticSlope]
  field_simp
  ring

private theorem energy_linear (X : ℕ) (f g : ℕ → ℝ) (a b : ℝ) :
    centeredEnergy X (fun d => a*f d+b*g d) =
      a^2*centeredEnergy X f+b^2*centeredEnergy X g+
        2*a*b*(∑ k ∈ Finset.Ico 1 X,
          (k : ℝ)*centeredDelta X f k*centeredDelta X g k) := by
  simp only [energy_delta,delta_linear,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A known orthogonal moment consumes part of a quadratic functional's
allowance. The saved term is explicit and nonnegative, for both signs. -/
theorem orthogonal_moment_bound {A Q V R M : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (h : ∀ a b : ℝ, (a*R+b*M)^2 ≤ A*(a^2*Q+b^2*V)) :
    0 ≤ A-M^2/V ∧ R^2 ≤ (A-M^2/V)*Q := by
  have hR : R^2 ≤ A*Q := by simpa using h 1 0
  have hM : M^2 ≤ A*V := by simpa using h 0 1
  by_cases hv : V=0
  · simpa [hv] using And.intro hA hR
  have hvp : 0 < V := lt_of_le_of_ne hV (Ne.symm hv)
  have hn : 0 ≤ A-M^2/V := sub_nonneg.mpr ((div_le_iff₀ hvp).mpr hM)
  refine ⟨hn,?_⟩
  let t := V*R^2+Q*M^2
  have hb : t^2 ≤ A*Q*V*t := by
    dsimp [t]
    convert h (V*R) (Q*M) using 1 <;> ring
  have hsmall : t ≤ A*Q*V := by
    by_contra hnot
    have hd : 0 < t-A*Q*V := sub_pos.mpr (lt_of_not_ge hnot)
    have hp : 0 < t := lt_of_le_of_lt (mul_nonneg (mul_nonneg hA hQ) hV) (lt_of_not_ge hnot)
    have := mul_pos hp hd
    nlinarith only [hb,this]
  apply (mul_le_mul_iff_left₀ hvp).mp
  have he : ((A-M^2/V)*Q)*V = A*Q*V-Q*M^2 := by
    field_simp
  rw [he]
  dsimp [t] at hsmall
  nlinarith only [hsmall]

/-- The exact signed arithmetic correlation, supported on two-prime cofactors. -/
def momentPair (S : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ n ∈ S, w n*secondMoment n

/-- The known moment is deducted from the SAME arithmetic weight allowance. -/
def remainingWeight (E : ℝ) (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ n ∈ S, (w n)^2)*E*X-(momentPair S w)^2/centeredEnergy X logSquare

private theorem weighted_mean_bound (E : ℝ) (X : ℕ) (S : Finset ℕ)
    (w g : ℕ → ℝ)
    (hmean : ∀ f : ℕ → ℝ, (∑ n ∈ S, divisorResponse f n^2) ≤ E*X*centeredEnergy X f) :
    (∑ n ∈ S, w n*divisorResponse g n)^2 ≤
      (∑ n ∈ S, w n^2)*E*X*centeredEnergy X g := by
  have hs := (Finset.sum_mul_sq_le_sq_mul_sq S w (divisorResponse g)).trans
    (mul_le_mul_of_nonneg_left (hmean g) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  simpa only [mul_assoc] using hs

/-- The actual residual pairing has a strictly reduced squared allowance
whenever the known moment is nonzero and the residual energy is positive.
The zero-energy cases are covered exactly. -/
theorem residual_pair_bound (E : ℝ) (hE : 0 ≤ E) (X : ℕ) (S : Finset ℕ)
    (w f : ℕ → ℝ)
    (hmean : ∀ g : ℕ → ℝ, (∑ n ∈ S, divisorResponse g n^2) ≤ E*X*centeredEnergy X g) :
    0 ≤ remainingWeight E X S w ∧
      (∑ n ∈ S, w n*divisorResponse (quadraticProfile X f) n)^2 ≤
        remainingWeight E X S w*quadraticEnergy X f := by
  let A := (∑ n ∈ S, w n^2)*E*X
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hE) (Nat.cast_nonneg X)
  by_cases hv : centeredEnergy X logSquare=0
  · simp only [remainingWeight,hv,div_zero,sub_zero]
    exact ⟨hA,weighted_mean_bound E X S w (quadraticProfile X f) hmean⟩
  apply orthogonal_moment_bound hA (quadraticEnergy_nonneg X f) (centeredEnergy_nonneg X logSquare)
  intro a b
  have he : (∑ n ∈ S, w n*divisorResponse
      (fun d => a*quadraticProfile X f d+b*logSquare d) n) =
      a*(∑ n ∈ S, w n*divisorResponse (quadraticProfile X f) n)+b*momentPair S w := by
    simp only [divisorResponse,momentPair,secondMoment,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hb := weighted_mean_bound E X S w
    (fun d => a*quadraticProfile X f d+b*logSquare d) hmean
  rw [he,energy_linear] at hb
  change _ ≤ A*(a^2*quadraticEnergy X f+b^2*centeredEnergy X logSquare+
    2*a*b*quadraticCross X (quadraticProfile X f)) at hb
  rw [quadratic_orthogonal X f hv,mul_zero,add_zero] at hb
  exact hb

/-- The remaining allowance never exceeds the previous one. The saving
is the explicitly retained moment squared, divided by its profile energy. -/
theorem remainingWeight_le (E : ℝ) (X : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) :
    remainingWeight E X S w ≤ (∑ n ∈ S, w n^2)*E*X :=
  sub_le_self _ (div_nonneg (sq_nonneg _) (centeredEnergy_nonneg _ _))

/-- The exact nonnegative saving in each squared residual allowance. -/
theorem squaredAllowance_saving (E : ℝ) (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    ((∑ n ∈ S, w n^2)*E*X)*quadraticEnergy X f-
      remainingWeight E X S w*quadraticEnergy X f =
      (momentPair S w)^2/centeredEnergy X logSquare*quadraticEnergy X f := by
  unfold remainingWeight
  ring

/-- The squared allowance decreases strictly whenever its known arithmetic
correlation and residual profile energy are both nonzero. -/
theorem squaredAllowance_strict (E : ℝ) (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hm : momentPair S w ≠ 0) (hv : 0 < centeredEnergy X logSquare)
    (hq : 0 < quadraticEnergy X f) :
    remainingWeight E X S w*quadraticEnergy X f <
      ((∑ n ∈ S, w n^2)*E*X)*quadraticEnergy X f := by
  apply sub_pos.mp
  rw [squaredAllowance_saving]
  exact mul_pos (div_pos (sq_pos_of_ne_zero hm) hv) hq

/-- The coupled cost with the known arithmetic moment paid before the square root. -/
def conditionedCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ I, sqrt (remainingWeight E X S (fun n => rotate P O a (W n))*
    quadraticEnergy X (fun d => rotate P O a (fun p => F p d)))

/-- Both signs benefit from this PROVED cost reduction at every finite
population, with the SAME arithmetic constant, profiles and full weights. -/
theorem conditionedCost_le_quadraticCost (E : ℝ) (X : ℕ) (S I P : Finset ℕ)
    (O W F : ℕ → ℕ → ℝ) :
    conditionedCost E X S I P O W F ≤ quadraticCost E X S I P O W F := by
  apply Finset.sum_le_sum
  intro a _
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right (remainingWeight_le E X S _)
    (quadraticEnergy_nonneg X _)

private theorem divisor_rotate (P : Finset ℕ) (O F : ℕ → ℕ → ℝ) (a n : ℕ) :
    divisorResponse (fun d => rotate P O a (fun p => F p d)) n =
      rotate P O a (fun p => divisorResponse (F p) n) := by
  simp only [divisorResponse,rotate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The known arithmetic moment reduces the residual allowance for BOTH
signs of the entire coupled sum, without removing any selected label. -/
theorem exists_joint_conditioned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X : ℕ) (S I P : Finset ℕ) (O W F : ℕ → ℕ → ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ ¬n.Prime) →
      let J := ∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n;
      let H := quadraticCenter X S I P O W F;
      let K := conditionedCost E X S I P O W F;
      H-K ≤ J ∧ J ≤ H+K ∧ |J| ≤ jointCost E X S I P O W F := by
  obtain ⟨E,hE,hmean⟩ := exists_centered_divisor_mean
  refine ⟨E,hE,fun X S I P O W F hO hS hSF => ?_⟩
  let f := fun a d => rotate P O a (fun p => F p d)
  let w := fun a n => rotate P O a (W n)
  have hpair : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (f a) n := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp_rw [f,divisor_rotate]
    exact (coordinate_pairing I P O hO (W n) (fun p => divisorResponse (F p) n)).symm
  have hb0 a : |∑ n ∈ S, w a n*divisorResponse (f a) n| ≤
      sqrt ((∑ n ∈ S, (w a n)^2)*E*X*centeredEnergy X (f a)) := by
    have hs := (Finset.sum_mul_sq_le_sq_mul_sq S (w a) (divisorResponse (f a))).trans
      (mul_le_mul_of_nonneg_left (hmean X S (f a) hS hSF)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg (by positivity) (centeredEnergy_nonneg _ _))]
    simpa only [mul_assoc] using hs
  have hbound0 : |∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n| ≤
      jointCost E X S I P O W F := by
    rw [hpair]
    exact (Finset.abs_sum_le_sum_abs _ I).trans (Finset.sum_le_sum (fun a _ => hb0 a))
  have hb a : |∑ n ∈ S, w a n*divisorResponse (quadraticProfile X (f a)) n| ≤
      sqrt (remainingWeight E X S (w a)*quadraticEnergy X (f a)) := by
    have hs := residual_pair_bound E hE.le X S (w a) (f a)
      (fun g => hmean X S g hS hSF)
    apply (sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    rw [sq_abs,sq_sqrt (mul_nonneg hs.1 (quadraticEnergy_nonneg _ _))]
    exact hs.2
  have he : (∑ n ∈ S, ∑ p ∈ P, W n p*divisorResponse (F p) n) =
      quadraticCenter X S I P O W F+
        ∑ a ∈ I, ∑ n ∈ S, w a n*divisorResponse (quadraticProfile X (f a)) n := by
    rw [hpair]
    simp only [quadraticCenter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp_rw [divisor_quadratic X _ (f a)]
    simp only [Finset.mul_sum,mul_add,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [f,w]; ring)
  have hbound := (Finset.abs_sum_le_sum_abs _ I).trans
    (Finset.sum_le_sum (fun a (_ : a ∈ I) => hb a))
  obtain ⟨hl,hu⟩ := abs_le.mp hbound
  dsimp only [conditionedCost]
  refine ⟨?_,?_,hbound0⟩ <;> rw [he] <;> linarith only [hl,hu]

/-- The original masked carrier's cost after retaining its known correlation. -/
def primeConditionedCost (E : ℝ) (X N : ℕ) (A S I P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ) : ℝ :=
  conditionedCost E X S I P O (maskedWeight A Q L y scale N) (hinge L)

private theorem literal_sum_eq (N : ℕ) (A S P : Finset ℕ)
    (Q : ℕ → Finset ℕ) (L y scale : ℝ)
    (hSF : ∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card)
    (hQ : ∀ n ∈ S, Q n ⊆ P)
    (hp : ∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) :
    (∑ n ∈ S, ∑ p ∈ P, maskedWeight A Q L y scale N n p*divisorResponse (hinge L p) n) =
      scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re := by
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

/-- Both inequalities for the ORIGINAL carrier, with every mask, phase and
factorial order retained. The width is PROVED no larger than the previous
joint cost with the SAME constant and coordinates. The center remains signed. -/
theorem exists_literal_conditioned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (X N : ℕ) (A S I P : Finset ℕ)
      (Q : ℕ → Finset ℕ) (O : ℕ → ℕ → ℝ) (L y scale : ℝ),
      Coordinates I P O → S ⊆ Finset.Ioc 1 X →
      (∀ n ∈ S, Squarefree n ∧ 2 ≤ n.primeFactors.card) →
      (∀ n ∈ S, Q n ⊆ P) → (∀ n ∈ S, ∀ p ∈ Q n, p.Prime ∧ ¬p ∣ n) →
      let J := scale*(∑ n ∈ S, ∑ p ∈ Q n,
        ZetaRieszJointAllocation.residualCoefficient A L N (p*n)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*n)).re;
      let H := primeCenter X N A S I P Q O L y scale;
      let K := primeConditionedCost E X N A S I P Q O L y scale;
      let C := primeCost E X N A S I P Q O L y scale;
      max (-C) (H-K) ≤ J ∧ J ≤ min C (H+K) ∧ K ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_joint_conditioned_bounds
  refine ⟨E,hE,fun X N A S I P Q O L y scale hO hS hSF hQ hp => ?_⟩
  have hnp n (hn : n ∈ S) : ¬n.Prime := by
    intro h
    have hc := (hSF n hn).2
    simp [h.primeFactors] at hc
  have hb := hbound X S I P O (maskedWeight A Q L y scale N) (hinge L) hO hS
    (fun n hn => ⟨(hSF n hn).1,hnp n hn⟩)
  rw [literal_sum_eq N A S P Q L y scale hSF hQ hp] at hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb.2.2
  exact ⟨max_le hl hb.1,le_min hu hb.2.1,(conditionedCost_le_quadraticCost E X S I P O _ _).trans
    (quadraticCost_le_jointCost hE.le X S I P O _ _)⟩

/-- The entire support's narrowed width, without any interval-cover premise. -/
def wholeConditionedCost (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) : ℝ :=
  primeConditionedCost E ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale

/-- All squarefree labels of count at least three receive the same coupled
enclosure. Its exact center has only triple-prime incidences, and the width
improvement requires no new arithmetic hypothesis. -/
theorem exists_whole_conditioned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
      (N : ℕ) (L y scale : ℝ),
      (∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card) →
      Coordinates I (ownerPrimes B) O →
      let J := scale*(∑ m ∈ B,
        ZetaRieszJointAllocation.residualCoefficient A L N m*
          zetaPrimeLogKernel N (3/2+Complex.I*y) m).re;
      let H := wholeCenter A B I O N L y scale;
      let K := wholeConditionedCost E A B I O N L y scale;
      let C := wholeCost E A B I O N L y scale;
      max (-C) (H-K) ≤ J ∧ J ≤ min C (H+K) ∧ K ≤ C := by
  obtain ⟨E,hE,hbound⟩ := exists_literal_conditioned_bounds
  refine ⟨E,hE,fun A B I O N L y scale hB hO => ?_⟩
  have hS : cofactors B ⊆ Finset.Ioc 1 ((cofactors B).sup id) := by
    intro n hn
    have hd := cofactors_data B hB hn
    have hn1 : n ≠ 1 := by intro h; simp [h] at hd
    exact Finset.mem_Ioc.mpr ⟨by have := hd.1.ne_zero; omega,Finset.le_sup (f := id) hn⟩
  have hb := hbound ((cofactors B).sup id) N A (cofactors B) I (ownerPrimes B)
    (ownerRows B) O L y scale hO hS (fun _ hn => cofactors_data B hB hn)
    (fun _ _ => Finset.image_subset_image (Finset.filter_subset _ _))
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.1⟩)
  have he := ZetaRieszCoupledWindow.sum_owned_products (cofactors B) (ownerRows B)
    (fun m => ZetaRieszJointAllocation.residualCoefficient A L N m*
      zetaPrimeLogKernel N (3/2+Complex.I*y) m)
    (fun _ hn => (cofactors_data B hB hn).1.ne_zero)
    (fun _ _ _ hp => ⟨(ownerRows_data B hB hp).1,(ownerRows_data B hB hp).2.2⟩)
  rw [owner_labels_eq B hB] at he
  simpa only [he,wholeCenter,wholeConditionedCost,wholeCost,Nat.mul_comm] using hb

open ZetaRieszParityPacket

/-- A narrower signed enclosure for the ENTIRE source-scaled original core.
The center and width are explicit; their sufficient eventual combined size
is still open, and no simple- or multiple-zero exclusion is claimed. -/
theorem exists_core_conditioned_bounds :
    ∃ E : ℝ, 0 < E ∧ ∀ (u y : ℝ) (N K : ℕ) (I : Finset ℕ) (O : ℕ → ℕ → ℝ),
      let B := (coreBand u N K).filter Squarefree;
      Coordinates I (ownerPrimes B) O →
      let A := ZetaRieszAnnulusJoint.intermediatePrimes u N;
      let L := SquarefreeVaughanLogSource.length u N;
      let H := wholeCenter A B I O N L y (u^(N+1));
      let C := wholeConditionedCost E A B I O N L y (u^(N+1));
      let B₀ := wholeCost E A B I O N L y (u^(N+1));
      max (-B₀) (H-C) ≤ u^(N+1)*(coreResponse u y N K).re ∧
        u^(N+1)*(coreResponse u y N K).re ≤ min B₀ (H+C) ∧ C ≤ B₀ := by
  obtain ⟨E,hE,hbound⟩ := exists_whole_conditioned_bounds
  refine ⟨E,hE,fun u y N K I O hO => ?_⟩
  have hb := hbound (ZetaRieszAnnulusJoint.intermediatePrimes u N)
    ((coreBand u N K).filter Squarefree) I O N (SquarefreeVaughanLogSource.length u N) y
    (u^(N+1)) (fun m hm => ⟨(Finset.mem_filter.mp hm).2,core_count (Finset.mem_filter.mp hm).1⟩) hO
  simpa only [← core_eq_squarefree] using hb

/-- The whole-core improvement uses the SAME population and coordinates;
its width cannot exceed the previous quadratic width. -/
theorem wholeConditionedCost_le (E : ℝ) (A B I : Finset ℕ) (O : ℕ → ℕ → ℝ)
    (N : ℕ) (L y scale : ℝ) :
    wholeConditionedCost E A B I O N L y scale ≤
      wholeQuadraticCost E A B I O N L y scale :=
  conditionedCost_le_quadraticCost E _ _ _ _ _ _ _

end RiemannGaussian.ZetaRieszConditionedPrimeEnergy
