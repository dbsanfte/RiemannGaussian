/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedDetectorResidueObstruction

/-!
# Uneven row-specific block budgets do not remove the detector obstruction

For a fixed original row, the large-fiber exceptions occur at at most two
residues of the hidden prime modulo m. Summing across a prime candidate
set with bounded residue fibers therefore pays every row's full weight,
even when the block budget is distributed unevenly between rows.

The investigation journal applies this finite arithmetic estimate to
predetermined row-specific layouts with a near-linear TOTAL block budget.
Its analytic density, selector counting and infinitude remain classical;
none is an additional Lean axiom or a proved acquisition upper bound.

The final algebraic lemmas check the quadratic congruence and regular
discriminant branch used by a separate manuscript-dependent obstruction
for layouts selected from the low residue N modulo m squared.
-/

namespace RiemannGaussian.SemiprimeRowSpecificDetectorObstruction

open scoped BigOperators
open Polynomial SemiprimeSeedDetectorResidueObstruction

/-- The two residue-map degeneracies for one actual row and prime candidate. -/
abbrev DetectorException (p m j : ℕ) : Prop :=
  (cofactorCoefficient p m j : ZMod m)=0 ∨ (detectorQuadratic p j : ZMod m)=0

/-- Each fixed original row is exceptional for at most two hidden-prime residues. -/
theorem exceptional_prime_residues_card {m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (P : Finset ℕ) :
    ((P.filter fun p : ℕ => DetectorException p m j).image fun p : ℕ => (p : ZMod m)).card≤2 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  have hjz : (j : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime j m).mpr hj).ne_zero
  let Q : (ZMod m)[X] := (X-C (j : ZMod m))*
    (C ((j : ZMod m)^2)+C (1-2*(j : ZMod m))*X)
  have hQ : Q≠0 := by
    intro hz
    have hc := congrArg (fun F : (ZMod m)[X] => F.coeff 0) hz
    simp only [Q,mul_coeff_zero,coeff_sub,coeff_X_zero,coeff_C_zero,
      coeff_zero,coeff_add,zero_sub,mul_zero,add_zero] at hc
    exact (mul_ne_zero (neg_ne_zero.mpr hjz) (pow_ne_zero 2 hjz)) hc
  have hdegree : Q.natDegree≤2 := by
    dsimp only [Q]
    compute_degree!
  have hsub : (P.filter fun p : ℕ => DetectorException p m j).image (fun p : ℕ => (p : ZMod m))⊆
      Q.roots.toFinset := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hQ).mpr
    change Q.eval (p : ZMod m)=0
    simp only [Q,eval_mul,eval_sub,eval_add,eval_X,eval_C]
    rcases (Finset.mem_filter.mp hp).2 with hC|hD
    · rw [←(cofactorCoefficient_zero_iff hj).mp hC,sub_self,zero_mul]
    · have hd : (j : ZMod m)^2+(1-2*(j : ZMod m))*(p : ZMod m)=0 := by
        have he : (detectorQuadratic p j : ZMod m)=
            (j : ZMod m)^2+(1-2*(j : ZMod m))*(p : ZMod m) := by
          simp only [detectorQuadratic,Int.cast_add,Int.cast_sub,Int.cast_mul,
            Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
          ring
        rwa [←he]
      rw [hd,mul_zero]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le Q.roots).trans ((Polynomial.card_roots' Q).trans hdegree))

/-- Bounded prime-candidate residue fibers pay the exceptional candidates at each row. -/
theorem exceptional_prime_count {m j H : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (P : Finset ℕ)
    (hres : ∀ a : ZMod m, (P.filter fun p : ℕ => (p : ZMod m)=a).card≤H) :
    (P.filter fun p : ℕ => DetectorException p m j).card≤2*H := by
  classical
  let E := P.filter fun p : ℕ => DetectorException p m j
  have hc : (E.image fun p : ℕ => (p : ZMod m)).card≤2 := exceptional_prime_residues_card hm hj P
  have hf (a : ZMod m) : (E.filter fun p : ℕ => (p : ZMod m)=a).card≤H := by
    apply (Finset.card_le_card ?_).trans (hres a)
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh.1).1,hh.2⟩
  calc
    E.card=∑ a∈E.image (fun p : ℕ => (p : ZMod m)), (E.filter fun p : ℕ => (p : ZMod m)=a).card :=
      Finset.card_eq_sum_card_image _ E
    _≤∑ _a∈E.image (fun p : ℕ => (p : ZMod m)), H := Finset.sum_le_sum fun a _ => hf a
    _=(E.image fun p : ℕ => (p : ZMod m)).card*H := by simp only [Finset.sum_const,smul_eq_mul]
    _≤2*H := Nat.mul_le_mul_right H hc

/-- A single row's detector fibers are paid after averaging actual prime candidates. -/
theorem detector_row_prime_fiber_bound {m j H : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (P : Finset ℕ)
    (hp : ∀ p∈P, (p : ZMod m)≠0 ∧ (p : ZMod m)≠1)
    (hres : ∀ a : ZMod m, (P.filter fun p : ℕ => (p : ZMod m)=a).card≤H)
    (t : ℕ→ℤ) :
    (∑ p∈P, (detectorResidueFiber p m j (t p)).card)≤P.card+2*m*H := by
  classical
  let E := P.filter fun p : ℕ => DetectorException p m j
  have hc : E.card≤2*H := exceptional_prime_count hm hj P hres
  have hle : (∑ p∈P, (detectorResidueFiber p m j (t p)).card)≤
      ∑ p∈P, (1+if DetectorException p m j then m else 0) := by
    apply Finset.sum_le_sum
    intro p hP
    by_cases he : DetectorException p m j
    · simpa only [ite_eq_left he] using
        (detectorResidueFiber_card_le_m hm hj (hp p hP).1 (hp p hP).2 (t p)).trans
          (Nat.le_add_left m 1)
    · have hgood := not_or.mp he
      simpa only [ite_eq_right he,add_zero] using
        detectorResidueFiber_card_le_one hm hj hgood.1 hgood.2 (t p)
  have hsum : (∑ p∈P, (1+if DetectorException p m j then m else 0))=P.card+E.card*m := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one]
    rw [←Finset.sum_filter]
    simp only [E,Finset.sum_const,smul_eq_mul]
  rw [hsum] at hle
  calc
    (∑ p∈P, (detectorResidueFiber p m j (t p)).card)≤P.card+E.card*m := hle
    _≤P.card+(2*H)*m := Nat.add_le_add_left (Nat.mul_le_mul_right m hc) P.card
    _=P.card+2*m*H := by ring

/-- Arbitrary nonuniform row weights cost only their total budget, not the largest row. -/
theorem detector_weighted_whole_family_bound {m H : ℕ} (hm : m.Prime)
    (P : Finset ℕ) (hp : ∀ p∈P, (p : ZMod m)≠0 ∧ (p : ZMod m)≠1)
    (hres : ∀ a : ZMod m, (P.filter fun p : ℕ => (p : ZMod m)=a).card≤H)
    (W : ℕ→ℕ) (t : ℕ→ℕ→ℤ) :
    (∑ p∈P, ∑ r∈Finset.range (m-1),
      W r*(detectorResidueFiber p m (r+1) (t p r)).card)≤
        (P.card+2*m*H)*(∑ r∈Finset.range (m-1), W r) := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ r∈Finset.range (m-1), ∑ p∈P,
      W r*(detectorResidueFiber p m (r+1) (t p r)).card)≤
        ∑ r∈Finset.range (m-1), W r*(P.card+2*m*H) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrm : r+1<m := by have hh := Finset.mem_range.mp hr; omega
      have hj : (r+1).Coprime m :=
        (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrm)).symm
      rw [←Finset.mul_sum]
      exact Nat.mul_le_mul_left (W r) (detector_row_prime_fiber_bound hm hj P hp hres (fun p : ℕ => t p r))
    _=(P.card+2*m*H)*(∑ r∈Finset.range (m-1), W r) := by
      rw [←Finset.sum_mul]
      exact Nat.mul_comm _ _

/-- A literal local hit and the known low residue give a quadratic in the hidden prime. -/
theorem detector_hit_quadratic_congruence {p q m n v R δ r a : ℤ}
    (hcofactor : p-1=v*R) (hhit : q+δ-m^2*r=a*R)
    (hn : m^2∣p*q-n) :
    m^2∣a*p^2-(a+v*δ)*p-v*n := by
  obtain ⟨c,hc⟩ := hn
  refine ⟨v*(c-r*p),?_⟩
  linear_combination -v*p*hhit+a*p*hcofactor+v*hc

/-- Completing the square connects the hidden-prime derivative with the discriminant. -/
theorem detector_discriminant_identity {F : Type*} [CommRing F] (a v δ n x : F) :
    (a+v*δ)^2+4*a*v*n =
      (2*a*x-(a+v*δ))^2-4*a*(a*x^2-(a+v*δ)*x-v*n) := by
  ring

/-- At a repeated root, the discriminant derivative in the multiplier has an exact value. -/
theorem detector_repeated_root_derivative_identity {F : Type*} [CommRing F]
    {a v δ n x : F} (hf : a*x^2-(a+v*δ)*x-v*n=0)
    (hd : 2*a*x-(a+v*δ)=0) :
    x*(2*(a+v*δ)+4*v*n)=4*v*n*(x-1) := by
  linear_combination 2*x*hd-4*hf

/-- The permitted repeated-root branch is regular in the multiplier; it has no singular lift. -/
theorem detector_repeated_root_discriminant_derivative_ne_zero {F : Type*} [Field F]
    {a v δ n x : F} (hf : a*x^2-(a+v*δ)*x-v*n=0)
    (hd : 2*a*x-(a+v*δ)=0) (h2 : (2 : F)≠0)
    (hv : v≠0) (hn : n≠0) (hx : x≠1) :
    2*(a+v*δ)+4*v*n≠0 := by
  have h4 : (4 : F)≠0 := by
    convert pow_ne_zero 2 h2 using 1
    ring
  have he := detector_repeated_root_derivative_identity hf hd
  intro hz
  rw [hz,mul_zero] at he
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hv) hn) (sub_ne_zero.mpr hx)) he.symm

end RiemannGaussian.SemiprimeRowSpecificDetectorObstruction
