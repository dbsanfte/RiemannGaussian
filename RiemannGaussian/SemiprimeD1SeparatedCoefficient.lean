/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WeightedPolynomial

/-! # Exact coefficient separation for modes with one target

Disjoint target families permit a coefficient to factor before any polynomial
table is constructed. All results apply to commutative rings with zero divisors.
The physical packet/group ownership and actual entry producer are later joins.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1SeparatedCoefficient
open scoped BigOperators
variable {V G R : Type*} [CommRing R]
attribute [local instance] Classical.propDecidable

/-- Erased exponent restriction to one designated family of target modes. -/
noncomputable def restrict (S : Set V) (e : V→₀ℕ) : V→₀ℕ := by
  classical
  exact e.filter fun v => v∈S

/-- Restriction retains exactly the original exponents in the chosen family. -/
theorem restrict_apply (S : Set V) (e : V→₀ℕ) (v : V) :
    restrict S e v=if v∈S then e v else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

/-- A row family uses only modes whose unique target lies in its designated set. -/
def On (S : Set V) (P : MvPolynomial V R) : Prop :=
  ∀ e,P.coeff e≠0→∀ v,v∉S→e v=0

/-- Enlarging the allowed family preserves actual mode ownership. -/
theorem on_mono (S T : Set V) (hst : S⊆T) (P : MvPolynomial V R) (hp : On S P) : On T P := by
  intro e he v hv
  exact hp e he v (fun h => hv (hst h))

/-- Constant empty row products use no mode variables. -/
theorem on_one (S : Set V) : On S (1 : MvPolynomial V R) := by
  classical
  intro e he v _
  rw [MvPolynomial.coeff_one] at he
  have hz : e=0 := by
    by_contra h
    simp only [Ne.symm h,ite_false,ne_eq,not_true_eq_false] at he
  simp only [hz,Finsupp.zero_apply]

/-- Coefficient convolution cannot introduce a mode outside the row family's targets. -/
theorem on_mul (S : Set V) (P Q : MvPolynomial V R) (hp : On S P) (hq : On S Q) : On S (P*Q) := by
  classical
  intro e he v hv
  by_contra hbad
  apply he
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hP : P.coeff pair.1=0
  · rw [hP,zero_mul]
  by_cases hQ : Q.coeff pair.2=0
  · rw [hQ,mul_zero]
  have hs : pair.1+pair.2=e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  have hval := congrArg (fun e => e v) hs
  simp only [Finsupp.add_apply,hp pair.1 hP v hv,hq pair.2 hQ v hv,zero_add] at hval
  exact False.elim (hbad hval.symm)

/-- Complete finite row products retain their actual designated target family. -/
theorem on_prod {A : Type*} (S : Set V) (indices : Finset A) (P : A→MvPolynomial V R)
    (hp : ∀ a∈indices,On S (P a)) : On S (∏ a∈indices,P a) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using on_one (R:=R) S
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact on_mul S _ _ (hp a (by simp)) (ih (fun b hb => hp b (by simp [hb])))

/-- Splitting exponents between complementary target families leaves only ONE
nonzero term in the coefficient convolution; the other antidiagonal terms cancel. -/
theorem coefficient_split (S : Set V) (P Q : MvPolynomial V R)
    (hp : On S P) (hq : On Sᶜ Q) (e : V→₀ℕ) :
    (P*Q).coeff e=P.coeff (restrict S e)*Q.coeff (restrict Sᶜ e) := by
  classical
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_single (restrict S e,restrict Sᶜ e)
  · intro pair hpair hne
    by_cases hP : P.coeff pair.1=0
    · rw [hP,zero_mul]
    by_cases hQ : Q.coeff pair.2=0
    · rw [hQ,mul_zero]
    have hs : pair.1+pair.2=e := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
    have heq : pair=(restrict S e,restrict Sᶜ e) := by
      apply Prod.ext
      · ext v
        have hh := congrArg (fun e => e v) hs
        simp only [Finsupp.add_apply] at hh
        rw [restrict_apply]
        by_cases hv : v∈S
        · rw [ite_eq_left hv]
          have hz := hq pair.2 hQ v (by simpa using hv)
          omega
        · rw [ite_eq_right hv]
          exact hp pair.1 hP v hv
      · ext v
        have hh := congrArg (fun e => e v) hs
        simp only [Finsupp.add_apply] at hh
        rw [restrict_apply]
        by_cases hv : v∈S
        · rw [ite_eq_right (by simpa using hv)]
          exact hq pair.2 hQ v (by simpa using hv)
        · rw [ite_eq_left (by simpa using hv)]
          have hz := hp pair.1 hP v hv
          omega
    exact False.elim (hne heq)
  · intro hnot
    apply False.elim
    apply hnot
    apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
    ext v
    simp only [Finsupp.add_apply,restrict_apply,Set.mem_compl_iff]
    by_cases hv : v∈S <;> simp only [hv,ite_true,ite_false,not_true_eq_false,not_false_eq_true,add_zero,zero_add]

/-- The single coefficient factors over every finite set of unique target owners. -/
theorem coefficient_owners [DecidableEq G] (owner : V→G) (groups : Finset G)
    (P : G→MvPolynomial V R) (hp : ∀ g∈groups,On {v|owner v=g} (P g)) (e : V→₀ℕ) :
    (∏ g∈groups,P g).coeff (restrict {v|owner v∈groups} e)=
      ∏ g∈groups,(P g).coeff (restrict {v|owner v=g} e) := by
  classical
  induction groups using Finset.induction_on with
  | empty =>
    have hz : restrict {v|owner v∈(∅ : Finset G)} e=0 := by
      ext v
      simp only [restrict_apply,Set.mem_ofPred_eq,Finset.notMem_empty,ite_false,Finsupp.zero_apply]
    rw [Finset.prod_empty,hz,Finset.prod_empty,MvPolynomial.coeff_one]
    simp only [ite_true]
  | @insert g groups hg ih =>
    rw [Finset.prod_insert hg,Finset.prod_insert hg]
    have hrest : On {v|owner v=g}ᶜ (∏ h∈groups,P h) := by
      apply on_prod
      intro h hh
      apply on_mono {v|owner v=h} _ _ (P h) (hp h (by simp [hh]))
      intro v hv
      change owner v≠g
      change owner v=h at hv
      intro he
      apply hg
      exact (hv.symm.trans he) ▸ hh
    rw [coefficient_split {v|owner v=g} _ _ (hp g (by simp)) hrest]
    have hleft : restrict {v|owner v=g} (restrict {v|owner v∈insert g groups} e)=
        restrict {v|owner v=g} e := by
      ext v
      simp only [restrict_apply,Set.mem_ofPred_eq,Finset.mem_insert]
      split_ifs <;> simp_all
    have hright : restrict {v|owner v=g}ᶜ (restrict {v|owner v∈insert g groups} e)=
        restrict {v|owner v∈groups} e := by
      ext v
      simp only [restrict_apply,Set.mem_compl_iff,Set.mem_ofPred_eq,Finset.mem_insert]
      by_cases he : owner v=g
      · simp [he,hg]
      · simp [he]
    rw [hleft,hright,ih (fun h hh => hp h (by simp [hh]))]

/-- With all owners present, restriction disappears and the exact D.16 coefficient
separation has no convolution or unknown projection left. -/
theorem coefficient_all_owners [Fintype G] (owner : V→G) (P : G→MvPolynomial V R)
    (hp : ∀ g,On {v|owner v=g} (P g)) (e : V→₀ℕ) :
    (∏ g,P g).coeff e=∏ g,(P g).coeff (restrict {v|owner v=g} e) := by
  classical
  have h := coefficient_owners owner Finset.univ P (fun g _ => hp g) e
  have he : restrict {v|owner v∈(Finset.univ : Finset G)} e=e := by
    ext v
    simp only [restrict_apply,Set.mem_ofPred_eq,Finset.mem_univ,ite_true]
  rw [he] at h
  exact h

end RiemannGaussian.SemiprimeD1SeparatedCoefficient
