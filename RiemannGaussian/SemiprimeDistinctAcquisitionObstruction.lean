import RiemannGaussian.SemiprimePartnerAcquisitionObstruction
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

/-!
# Finite kernels for distinct-tag acquisition obstructions

An integer multiplication matrix whose reduction has a kernel of
dimension at least f has determinant divisible by p^f. Invertible
residue-field transformations and their integer lifts are constructed
internally. Cyclotomic component degrees equal the hidden prime's
public residue order; a finite union bounds the small-order classes.

The original quotient-row giant exponent, weighted hit polynomial,
true-tag specialization and literal centered lift retain their exact
integer source. These identities support the journal's all-local-hit
small-weight obstruction and honest three-term Gauss obstruction.

The actual-input density counts, cyclotomic Gauss norm construction,
CRT kernel-dimension implication and norm-size estimates remain
classical. No analytic or coverage premise is introduced as an axiom.
The complete guaranteed one-sixth factorization and bit clock remain open.
-/

namespace RiemannGaussian.SemiprimeDistinctAcquisitionObstruction

open scoped BigOperators
open Matrix

/-- Every prime-divisible integer row supplies one factor of that prime
in the integer determinant, retaining its full multiplicity. -/
theorem prime_rows_det_power_dvd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℤ) (F : Finset (Fin n))
    (hrows : ∀ i ∈ F, ∀ j, p ∣ A i j) : p^F.card ∣ A.det := by
  classical
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => if i ∈ F then A i j/p else A i j
  have hfactor : A=diagonal (fun i => if i ∈ F then p else 1)*B := by
    ext i j
    rw [diagonal_mul]
    dsimp only [B]
    by_cases hi : i ∈ F
    · simp only [ite_eq_left hi]
      exact (Int.mul_ediv_cancel' (hrows i hi j)).symm
    · simp only [ite_eq_right hi,one_mul]
  have hprod : (∏ i : Fin n, if i ∈ F then p else 1)=p^F.card := by
    rw [Finset.prod_ite_mem_eq]
    simp only [Finset.prod_const]
  rw [hfactor,det_mul,det_diagonal,hprod]
  exact dvd_mul_right _ _

/-- Integer lifts of invertible row/column transformations preserve the
prime-power divisibility extracted from their transformed zero rows. -/
theorem transformed_prime_rows_det_power_dvd {n : ℕ}
    (A V U : Matrix (Fin n) (Fin n) ℤ) (p : ℤ) (F : Finset (Fin n))
    (hV : IsCoprime p V.det) (hU : IsCoprime p U.det)
    (hrows : ∀ i ∈ F, ∀ j, p ∣ (V*A*U) i j) : p^F.card ∣ A.det := by
  have hd := prime_rows_det_power_dvd (V*A*U) p F hrows
  rw [det_mul,det_mul] at hd
  have h := (hU.pow_left (m:=F.card)).dvd_of_dvd_mul_right hd
  exact (hV.pow_left (m:=F.card)).dvd_of_dvd_mul_left h

/-- The canonical pointwise lift from a prime residue field to integers. -/
def integerLift {p n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => (A i j).val

theorem integerLift_map {p n : ℕ} [NeZero p]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    (integerLift A).map (Int.castRingHom (ZMod p))=A := by
  ext i j
  change (((A i j).val : ℤ) : ZMod p)=A i j
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem integerLift_det_coprime {p n : ℕ} (hp : p.Prime)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : IsUnit A) :
    IsCoprime (p : ℤ) (integerLift A).det := by
  let : Fact p.Prime := ⟨hp⟩
  have hz : ((integerLift A).det : ZMod p)≠0 := by
    have hdet := (isUnit_iff_isUnit_det A).mp hA
    rw [Int.cast_det]
    have hmap : (integerLift A).map (fun z : ℤ => (z : ZMod p))=A := integerLift_map A
    rw [hmap]
    exact hdet.ne_zero
  apply Int.isCoprime_iff_nat_coprime.mpr
  rw [Int.natAbs_natCast]
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (Int.natCast_dvd.mpr hd))

/-- A rank deficiency f in reduction modulo p supplies at least f prime
factors in the ORIGINAL integer determinant. The residue field
transformations are lifted internally; none is an extra premise. -/
theorem rank_deficiency_det_prime_power_dvd {p n : ℕ} (hp : p.Prime)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    (p : ℤ)^(n-(A.map (Int.castRingHom (ZMod p))).rank) ∣ A.det := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let M := A.map (Int.castRingHom (ZMod p))
  obtain ⟨V,U,e,hV,hU,hNormal⟩ := exists_rank_normal_form M
  let F : Finset (Fin n) := Finset.univ.image
    fun i : Fin (Fintype.card (Fin n)-M.rank) => e.symm (Sum.inr i)
  have hcard : F.card=n-M.rank := by
    rw [Finset.card_image_of_injective]
    · simp only [Finset.card_univ,Fintype.card_fin]
    · exact e.symm.injective.comp Sum.inr_injective
  have hrows : ∀ i ∈ F, ∀ j, (p : ℤ) ∣ (integerLift V*A*integerLift U) i j := by
    intro i hi j
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hmap : (integerLift V*A*integerLift U).map (Int.castRingHom (ZMod p))=
        V*M*U := by
      rw [Matrix.map_mul,Matrix.map_mul,integerLift_map,integerLift_map]
    change ((integerLift V*A*integerLift U).map (Int.castRingHom (ZMod p)))
      (e.symm (Sum.inr k)) j=0
    rw [hmap,hNormal]
    simp only [Matrix.submatrix,Matrix.of_apply,e.apply_symm_apply]
    cases e j <;> rfl
  have hd := transformed_prime_rows_det_power_dvd A (integerLift V) (integerLift U)
    (p : ℤ) F (integerLift_det_coprime hp V hV) (integerLift_det_coprime hp U hU) hrows
  simpa only [hcard] using hd

theorem rank_deficiency_at_least_det_prime_power_dvd {p n f : ℕ} (hp : p.Prime)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hf : f≤n-(A.map (Int.castRingHom (ZMod p))).rank) : (p : ℤ)^f ∣ A.det :=
  (pow_dvd_pow (p : ℤ) hf).trans (rank_deficiency_det_prime_power_dvd hp A)

/-- A residue-field kernel of dimension at least f supplies p^f in the
integer determinant. This is the finite matrix contract used by the
cyclotomic residue-degree argument. -/
theorem kernel_dimension_det_prime_power_dvd {p n f : ℕ} [Fact p.Prime]
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hf : f≤Module.finrank (ZMod p)
      (LinearMap.ker (A.map (Int.castRingHom (ZMod p))).mulVecLin)) :
    (p : ℤ)^f ∣ A.det := by
  apply rank_deficiency_at_least_det_prime_power_dvd Fact.out A
  have h := LinearMap.finrank_range_add_finrank_ker
    (A.map (Int.castRingHom (ZMod p))).mulVecLin
  rw [Module.finrank_fin_fun] at h
  change f≤n-Module.finrank (ZMod p)
    (LinearMap.range (A.map (Int.castRingHom (ZMod p))).mulVecLin)
  omega

open scoped BigOperators
open Polynomial

/-- Public residues that satisfy some positive exponent at most the
threshold. This overcounts all residues of small multiplicative order. -/
noncomputable def lowOrderResidues {m : ℕ} [Fact m.Prime] (T : ℕ) : Finset (ZMod m) :=
  (Finset.range T).biUnion fun r =>
    ((X : (ZMod m)[X])^(r+1)-C 1).roots.toFinset

/-- Polynomial root counts bound the complete low-order residue union,
without using prime distribution or a primitive-root computation. -/
theorem lowOrderResidues_card_le {m : ℕ} [Fact m.Prime] (T : ℕ) :
    (lowOrderResidues (m:=m) T).card ≤ T^2 := by
  classical
  unfold lowOrderResidues
  apply (Finset.card_biUnion_le).trans
  calc
    ∑ r ∈ Finset.range T,
        (((X : (ZMod m)[X])^(r+1)-C 1).roots.toFinset).card
      ≤ ∑ _r ∈ Finset.range T, T := by
        apply Finset.sum_le_sum
        intro r hr
        have hdeg := Polynomial.card_roots_X_pow_sub_C
          (R:=ZMod m) (n:=r+1) (Nat.succ_pos r) (1 : ZMod m)
        exact (Multiset.toFinset_card_le _).trans
          (hdeg.trans (by have h := Finset.mem_range.mp hr; omega))
    _ = T^2 := by simp [pow_two]

/-- Every actual prime residue of small cyclotomic residue degree lies
in the displayed public union, via its supplied unit modulo m. -/
theorem unit_mem_lowOrderResidues {m : ℕ} [Fact m.Prime]
    (u : (ZMod m)ˣ) (T : ℕ) (hdegree : orderOf u ≤ T) :
    (u : ZMod m) ∈ lowOrderResidues (m:=m) T := by
  classical
  have hpos : 0 < orderOf u := orderOf_pos u
  have hpow : (u : ZMod m) ^ orderOf u = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun w : (ZMod m)ˣ => (w : ZMod m)) (pow_orderOf_eq_one u)
  unfold lowOrderResidues
  apply Finset.mem_biUnion.mpr
  refine ⟨orderOf u-1, Finset.mem_range.mpr (by omega), ?_⟩
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots
    (X_pow_sub_C_ne_zero (by omega : 0<orderOf u-1+1) (1 : ZMod m))).mpr
  change ((X : (ZMod m)[X])^(orderOf u-1+1)-C 1).eval (u : ZMod m)=0
  simp only [eval_sub, eval_pow, eval_X, eval_C,
    Nat.sub_add_cancel hpos, hpow, sub_self]

/-- The actual degree of every irreducible cyclotomic component is the
public multiplicative order of the hidden prime residue modulo m. -/
theorem cyclotomic_component_degree {P m : ℕ} [Fact P.Prime]
    (hcop : P.Coprime m) {F : (ZMod P)[X]}
    (hfactor : F ∣ cyclotomic m (ZMod P)) (hirr : Irreducible F) :
    F.natDegree = orderOf (ZMod.unitOfCoprime P hcop) := by
  simpa only [pow_one] using
    Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
      (p:=P) (f:=1) (by simp : Fintype.card (ZMod P)=P^1) hcop hfactor hirr

open SemiprimeQuotientRows SemiprimeMaskAcquisitionObstruction

/-- The retained offset of the original signed quotient row. -/
def weightedOffset (m j a b : ℤ) : ℤ := a+m*b-2*a*j

/-- The exact original-hit polynomial after fixing both public digits. -/
def weightedHitPolynomial (p v K t δ n : ℤ) : ℤ :=
  K*p^2-(K+v*δ)*p-v*t*n

/-- This exponent is the actual quadratic-row exponent, including its
integer centered coefficient, rather than only its lower projection. -/
theorem weighted_giantExponent_eq {N m j a b c t : ℤ}
    (h : quotientRelation N m j a b c t) :
    giantExponent m j a b c=t*N+weightedOffset m j a b := by
  rw [giantExponent_eq h]
  unfold weightedOffset
  ring

/-- Clearing an actual weighted hit eliminates its signed index while
retaining the exact multiple of m squared. -/
theorem weighted_hit_multiplier_identity
    (p q m v R j a b t i K : ℤ) (hcofactor : p-1=v*R)
    (hhit : t*q+weightedOffset m j a b-m^2*i=K*R) :
    weightedHitPolynomial p v K t (weightedOffset m j a b) (p*q)
      =-v*p*m^2*i := by
  have h := hit_multiplier_polynomial_identity p (t*q) m v R
    (weightedOffset m j a b) i K hcofactor hhit
  convert h using 1
  dsimp only [weightedHitPolynomial]
  ring

/-- The weighted polynomial is fixed by the complete two-digit public
state, even when the hit came from a false residue row. -/
theorem weighted_hit_multiplier_modEq {m : ℕ}
    (p q v R j a b t i K n : ℤ) (hcofactor : p-1=v*R)
    (hhit : t*q+weightedOffset m j a b-(m : ℤ)^2*i=K*R)
    (hstate : p*q ≡ n [ZMOD (m : ℤ)^2]) :
    weightedHitPolynomial p v K t (weightedOffset m j a b) n
      ≡0 [ZMOD (m : ℤ)^2] := by
  have hs : p*(t*q) ≡ t*n [ZMOD (m : ℤ)^2] := by
    convert hstate.mul_left t using 1
    ring
  have h := hit_multiplier_polynomial_modEq p (t*q) v R
    (weightedOffset m j a b) i K (t*n) hcofactor hhit hs
  convert h using 1
  dsimp only [weightedHitPolynomial]
  ring

/-- At its own tag the original quotient relation reduces the hit
polynomial exactly, before any reduction modulo m squared. -/
theorem weighted_true_tag_polynomial_identity {N m j a b c t v K : ℤ}
    (h : quotientRelation N m j a b c t) :
    weightedHitPolynomial j v K t (weightedOffset m j a b) N
      =(K+v*a)*j*(j-1)-v*m^2*c := by
  unfold quotientRelation at h
  unfold weightedHitPolynomial weightedOffset
  linear_combination v*h

/-- Shifting the upper public carry changes the ACTUAL centered lift's
linear coefficient by the corresponding inverse-tag carry modulo m. -/
theorem liftRow_upper_carry_shift {N inverse a t u : ℤ} {m j : ℕ}
    (hm : 0<m) (hinv : (j : ℤ)*inverse ≡1 [ZMOD m])
    (hpair : a ≡N*inverse^2*t [ZMOD m]) :
    t*u ≡-(j : ℤ)*((liftRow (N+(m : ℤ)*u) m j inverse a t).b-
      (liftRow N m j inverse a t).b) [ZMOD m] := by
  have hN : N ≡N+(m : ℤ)*u [ZMOD m] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨u,by ring⟩
  have hpairNew : a ≡(N+(m : ℤ)*u)*inverse^2*t [ZMOD m] :=
    hpair.trans ((hN.mul_right (inverse^2)).mul_right t)
  have h := liftRow_correct hinv hpair
  have hNew := liftRow_correct hinv hpairNew
  change quotientRelation N m j a (liftRow N m j inverse a t).b
    (liftRow N m j inverse a t).c t at h
  change quotientRelation (N+(m : ℤ)*u) m j a
    (liftRow (N+(m : ℤ)*u) m j inverse a t).b
    (liftRow (N+(m : ℤ)*u) m j inverse a t).c t at hNew
  unfold quotientRelation at h hNew
  apply Int.modEq_iff_dvd.mpr
  refine ⟨(liftRow N m j inverse a t).c-
    (liftRow (N+(m : ℤ)*u) m j inverse a t).c,?_⟩
  apply mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ)≠0)
  linear_combination hNew-h

end RiemannGaussian.SemiprimeDistinctAcquisitionObstruction
