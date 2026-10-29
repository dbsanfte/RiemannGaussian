/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1UniversalModeData
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Weighted coefficient cancellation over every modular jet algebra

Each original mode has its proved dyadic weight. Affine row products preserve
the sum of those weights coefficientwise, including in rings with zero divisors.
Consequently every omitted mode monomial vanishes modulo the actual precision.
The original packet/group construction and acquired-tuple sum are later joins.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1WeightedPolynomial
open scoped BigOperators
variable {V R : Type*} [CommRing R]

/-- Exact positive-mode weight of one finite exponent vector. -/
def degree (w : V→ℕ) (e : V→₀ℕ) : ℕ := e.sum fun v n => w v*n

/-- Weights add under the actual exponent-vector addition in polynomial multiplication. -/
theorem degree_add (w : V→ℕ) (e f : V→₀ℕ) : degree w (e+f)=degree w e+degree w f := by
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => Nat.mul_add _ _ _)

/-- The zero monomial has no dyadic cost. -/
theorem degree_zero (w : V→ℕ) : degree w 0=0 := by simp [degree]

/-- An isolated mode power has its literal multiplicity times its original weight. -/
theorem degree_single (w : V→ℕ) (v : V) (n : ℕ) : degree w (Finsupp.single v n)=w v*n := by
  classical
  simp [degree]

/-- Coefficientwise dyadic ideal membership; no multiplicative valuation law is used. -/
def Weighted (w : V→ℕ) (P : MvPolynomial V R) : Prop :=
  ∀ e,(2:R)^degree w e∣P.coeff e

/-- A literal acquired coefficient licenses its one monomial. -/
theorem weighted_monomial (w : V→ℕ) (e : V→₀ℕ) (c : R)
    (hc : (2:R)^degree w e∣c) : Weighted w (MvPolynomial.monomial e c) := by
  classical
  intro f
  rw [MvPolynomial.coeff_monomial]
  split_ifs with he
  · subst f;exact hc
  · exact dvd_zero _

/-- Every local scalar is free of mode weight. -/
theorem weighted_C (w : V→ℕ) (c : R) : Weighted w (MvPolynomial.C c) := by
  apply weighted_monomial w 0 c
  simp [degree_zero]

/-- Sums retain exact coefficientwise powers of two. -/
theorem weighted_add (w : V→ℕ) (P Q : MvPolynomial V R)
    (hp : Weighted w P) (hq : Weighted w Q) : Weighted w (P+Q) := by
  intro e
  change (2:R)^degree w e∣P.coeff e+Q.coeff e
  exact dvd_add (hp e) (hq e)

/-- Negating a row coefficient loses no precision. -/
theorem weighted_neg (w : V→ℕ) (P : MvPolynomial V R) (hp : Weighted w P) : Weighted w (-P) := by
  intro e
  simpa only [MvPolynomial.coeff_neg] using dvd_neg.mpr (hp e)

/-- Actual coefficient convolution adds the independent mode weights exactly. -/
theorem weighted_mul (w : V→ℕ) (P Q : MvPolynomial V R)
    (hp : Weighted w P) (hq : Weighted w Q) : Weighted w (P*Q) := by
  classical
  intro e
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro pair hpair
  have he : pair.1+pair.2=e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  have hw : degree w pair.1+degree w pair.2=degree w e := by rw [←degree_add,he]
  rw [←hw,pow_add]
  exact mul_dvd_mul (hp pair.1) (hq pair.2)

/-- Finite actual affine mode sums preserve the acquired coefficient content. -/
theorem weighted_sum {A : Type*} (w : V→ℕ) (s : Finset A) (P : A→MvPolynomial V R)
    (hp : ∀ a∈s,Weighted w (P a)) : Weighted w (∑ a∈s,P a) := by
  classical
  intro e
  rw [MvPolynomial.coeff_sum]
  exact Finset.dvd_sum (fun a ha => hp a ha e)

/-- Products of all original affine Boolean row factors retain total mode weight. -/
theorem weighted_prod {A : Type*} (w : V→ℕ) (s : Finset A) (P : A→MvPolynomial V R)
    (hp : ∀ a∈s,Weighted w (P a)) : Weighted w (∏ a∈s,P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,map_one] using weighted_C w (1:R)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact weighted_mul w _ _ (hp a (by simp)) (ih (fun b hb => hp b (by simp [hb])))

/-- Explicit original-weight affine rows, with signed Boolean complement allowed. -/
theorem weighted_affine (w : V→ℕ) (modes : Finset V) (base : R) (c : V→R)
    (hc : ∀ v∈modes,(2:R)^w v∣c v) (bit : Bool) :
    Weighted w (if bit then MvPolynomial.C base+
      ∑ v∈modes,MvPolynomial.C (c v)*MvPolynomial.X v else
      1-(MvPolynomial.C base+∑ v∈modes,MvPolynomial.C (c v)*MvPolynomial.X v)) := by
  have hs : Weighted w (∑ v∈modes,MvPolynomial.C (c v)*MvPolynomial.X v) := by
    apply weighted_sum
    intro v hv
    rw [MvPolynomial.C_mul_X_eq_monomial]
    apply weighted_monomial
    simpa only [degree_single,Nat.mul_one] using hc v hv
  have hrow := weighted_add w _ _ (weighted_C w base) hs
  cases bit
  · simpa only [Bool.false_eq_true,ite_false,sub_eq_add_neg] using
      weighted_add w 1 _ (by simpa only [map_one] using weighted_C w (1:R)) (weighted_neg w _ hrow)
  · exact hrow

/-- Every mode monomial outside the actual strict precision budget is zero. -/
theorem coefficient_zero (w : V→ℕ) (P : MvPolynomial V R) (hp : Weighted w P)
    (p : ℕ) (hmod : (2:R)^p=0) (e : V→₀ℕ) (he : p≤degree w e) : P.coeff e=0 := by
  have hz : (2:R)^degree w e=0 := by
    rw [show degree w e=p+(degree w e-p) by omega,pow_add,hmod,zero_mul]
  have hd := hp e
  rw [hz,zero_dvd_iff] at hd
  exact hd

/-- Every actual modular-algebra map supplies exactly the required nilpotence. -/
theorem modular_nilpotence (p : ℕ) (f : ZMod (2^p)→+*R) : (2:R)^p=0 := by
  have h : (2:ZMod (2^p))^p=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^p)
  simpa only [map_pow,map_ofNat,map_zero] using congrArg f h

/-- Erased strict weighted-budget restriction; it is not a proposed full polynomial algorithm. -/
noncomputable def lowPart (w : V→ℕ) (p : ℕ) (P : MvPolynomial V R) : MvPolynomial V R := by
  classical
  exact ∑ e∈P.support.filter (fun e => degree w e<p),MvPolynomial.monomial e (P.coeff e)

/-- Removing every out-of-budget monomial preserves the entire polynomial. -/
theorem lowPart_eq (w : V→ℕ) (P : MvPolynomial V R) (hp : Weighted w P)
    (p : ℕ) (hmod : (2:R)^p=0) : lowPart w p P=P := by
  classical
  rw [lowPart,Finset.sum_filter]
  calc
    _ = ∑ e∈P.support,MvPolynomial.monomial e (P.coeff e) := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : degree w e<p
      · simp only [he,ite_true]
      · simp only [he,ite_false,coefficient_zero w P hp p hmod e (by omega),map_zero]
    _ = P := MvPolynomial.support_sum_monomial_coeff P

/-- The single useful value is already the strict weighted-budget sum in every
actual modular jet algebra, even when its coefficients have zero divisors. -/
theorem eval_lowPart (w : V→ℕ) (P : MvPolynomial V R) (hp : Weighted w P)
    (p : ℕ) (f : ZMod (2^p)→+*R) (values : V→R) :
    MvPolynomial.eval values P=
      ∑ e∈P.support.filter (fun e => degree w e<p),P.coeff e*(e.prod fun v n => values v^n) := by
  classical
  have h := congrArg (MvPolynomial.eval values) (lowPart_eq w P hp p (modular_nilpotence p f))
  rw [lowPart,map_sum] at h
  simpa only [MvPolynomial.eval_monomial] using h.symm

end RiemannGaussian.SemiprimeD1WeightedPolynomial
