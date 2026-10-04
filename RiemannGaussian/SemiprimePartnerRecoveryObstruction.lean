/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowPartnerOffsets

/-!
# Reciprocal degeneracy of the actual residue-partner recovery equations

Swapped public coefficient rows have an exact integral index transport.
After that transport, the N-normalized reciprocal of the partner's
quadratic is a scalar multiple of the original quadratic, for every index
in any commutative ring. Their genuine Sylvester resultant is identically
zero, even with a symbolic index. The true-factor witnesses satisfy this
same relation: there is no second independent polynomial equation from
this pairing. Integrality, other rows, and useful cross-residue incidence
remain separate arithmetic requirements.
-/

namespace RiemannGaussian.SemiprimePartnerRecoveryObstruction

open SemiprimeQuotientRows SemiprimeQuotientCentering SemiprimeEuclidRowFamily
open SemiprimeCompanionRows SemiprimeCompanionCenterSpectrum SemiprimeAffineRowRoots
open SemiprimeRowAreaSpectrum SemiprimeRowPartnerOffsets SemiprimeCenteredOffsetExtractor
open Polynomial

/-- The exact public correction between the two hidden collision indices. -/
def partnerStep (m : ℕ) (u v : FamilyPacket) (s : ℤ) : ℤ :=
  partnerDelta m u v s/(m : ℤ)^2

/-- The quotient is exact on the original public source. -/
theorem publicPacket_partner_step_exact {N m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) :
    packetOffset m v=s*packetOffset m u+(m : ℤ)^2*partnerStep m u v s := by
  have he := Int.mul_ediv_cancel' (publicPacket_partner_delta_dvd hm hu hv s ha ht hprod)
  change (m : ℤ)^2*partnerStep m u v s=partnerDelta m u v s at he
  unfold partnerDelta at he
  linear_combination -he

/-- Opposite public centers give only a zero or one-step change of index. -/
theorem publicPacket_partner_step_cases {N m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (hs : s=-1 ∨ s=1) (ha : v.original.a=s*u.original.t)
    (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (side : Bool)
    (huc : CenterChoice N m u side) (hvc : CenterChoice N m v (!side)) :
    partnerStep m u v s=0 ∨ partnerStep m u v s=1 ∨ partnerStep m u v s=-1 := by
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm
  have hpow := sq_pos_of_pos hmz
  have hd := publicPacket_partner_delta_dvd hm hu hv s ha ht hprod
  have hb := partner_delta_abs_le hm u v s hs ha ht side huc hvc
  have he := Int.mul_ediv_cancel' hd
  change (m : ℤ)^2*partnerStep m u v s=partnerDelta m u v s at he
  rcases bounded_multiple hpow hd hb with h0|hplus|hminus
  · left
    apply mul_left_cancel₀ hpow.ne'
    simpa only [h0,mul_zero] using he
  · right; left
    apply mul_left_cancel₀ hpow.ne'
    simpa only [hplus,mul_one] using he
  · right; right
    apply mul_left_cancel₀ hpow.ne'
    simpa only [hminus,mul_neg_one] using he

/-- Keep the actual signed factor sum before eliminating an unknown index. -/
def factorSum (m : ℕ) (w : FamilyPacket) (p q : ℤ) : ℤ :=
  w.original.a*p+packetOffset m w+w.original.t*q

/-- Swapping the factor orientation supplies the same linear equation. -/
theorem partner_factor_sum (m : ℕ) (u v : FamilyPacket) (s p q : ℤ)
    (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a) :
    factorSum m v q p=s*factorSum m u p q+partnerDelta m u v s := by
  simp only [factorSum,partnerDelta,ha,ht]
  ring

/-- Every actual packet at the true residue has an integral collision index.
No short-window assumption, primality, or balanced-ratio assumption is used. -/
theorem publicPacket_factor_index {p q m : ℕ} (hm : 0<m) (hp : 0<p)
    {w : FamilyPacket} (hw : w∈publicPackets (p*q) m) (hj : w.residue=p%m) :
    ∃ i : ℤ, (m : ℤ)^2*i=factorSum m w p q ∧
      quadratic (centeredPacketRow m w).a (centeredPacketRow m w).b
        (centeredPacketRow m w).c (p/m : ℕ)=(p : ℤ)*i := by
  have hcoord : (p : ℤ)=(m : ℤ)*(p/m : ℕ)+w.residue := by
    rw [hj]
    have hd := Nat.mod_add_div p m
    exact_mod_cast (by omega : p=m*(p/m)+p%m)
  have hcop : IsCoprime (p : ℤ) (m : ℤ) := by
    obtain ⟨x,y,hxy⟩ := (publicPacket_residue_coprime hw).isCoprime
    refine ⟨x,y-x*(p/m : ℕ),?_⟩
    linear_combination hxy+x*hcoord
  have hrel : quotientRelation ((p : ℤ)*q) m w.residue
      (centeredPacketRow m w).a (centeredPacketRow m w).b
      (centeredPacketRow m w).c (centeredPacketRow m w).t := by
    simpa only [Nat.cast_mul] using publicPacket_relation hm hw
  obtain ⟨i,hi⟩ := quotient_row_integer_index hcoord hrel hcop
  refine ⟨i,?_,hi⟩
  have he := scaled_quadratic_factor_sum hcoord hrel
  rw [hi] at he
  have hpz : (p : ℤ)≠0 := by exact_mod_cast hp.ne'
  apply mul_left_cancel₀ hpz
  simp only [factorSum,packetOffset,centeredPacketRow,shiftRow] at he ⊢
  linear_combination he

/-- The integral indices of the two true-factor rows are affinely dependent. -/
theorem publicPacket_factor_indices_related {p q m : ℕ} (hm : 0<m)
    (hp : 0<p) (hq : 0<q) {u v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hj : u.residue=p%m) (hk : v.residue=q%m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a) :
    ∃ i k : ℤ, (m : ℤ)^2*i=factorSum m u p q ∧
      (m : ℤ)^2*k=factorSum m v q p ∧ k=s*i+partnerStep m u v s := by
  obtain ⟨i,hi,_⟩ := publicPacket_factor_index hm hp hu hj
  obtain ⟨k,hkIndex,_⟩ := publicPacket_factor_index (p:=q) (q:=p) hm hq
    (by simpa only [Nat.mul_comm q p] using hv) hk
  have hprod : (m : ℤ)∣(p*q : ℕ)-(u.residue : ℤ)*v.residue := by
    simpa only [hj,hk,Nat.cast_mul] using factor_residue_product_dvd p q m
  have hstep := publicPacket_partner_step_exact hm hu hv s ha ht hprod
  have hsum := partner_factor_sum m u v s p q ha ht
  have hmz : (0 : ℤ)<m := by exact_mod_cast hm
  refine ⟨i,k,hi,hkIndex,?_⟩
  apply mul_left_cancel₀ (sq_pos_of_pos hmz).ne'
  rw [hkIndex]
  unfold partnerDelta at hsum
  linear_combination hsum-s*hi+hstep

/-- The quadratic in the original factor coordinate, retaining its unknown index. -/
noncomputable def recoveryPolynomial {R : Type*} [CommRing R]
    (N m : ℕ) (w : FamilyPacket) (i : R) : R[X] :=
  quadraticPolynomial (w.original.a : R)
    ((packetOffset m w : R)-(m : R)^2*i) ((N : R)*(w.original.t : R))

/-- N-normalized reciprocal coefficient form for the partner factor N/x. -/
noncomputable def reciprocalRecoveryPolynomial {R : Type*} [CommRing R]
    (N m : ℕ) (w : FamilyPacket) (i : R) : R[X] :=
  quadraticPolynomial (w.original.t : R)
    ((packetOffset m w : R)-(m : R)^2*i) ((N : R)*(w.original.a : R))

/-- The reciprocal coefficient form is the original polynomial at the
partner coordinate, with only the exact known factors x² and N cleared. -/
theorem recovery_reciprocal_evaluation {R : Type*} [CommRing R]
    (N m : ℕ) (w : FamilyPacket) (i x y : R) (hxy : x*y=(N : R)) :
    x^2*(recoveryPolynomial N m w i).eval y=
      (N : R)*(reciprocalRecoveryPolynomial N m w i).eval x := by
  simp only [recoveryPolynomial,reciprocalRecoveryPolynomial,quadraticPolynomial,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  linear_combination (w.original.a : R)*(x*y+(N : R))*hxy+
    ((packetOffset m w : R)-(m : R)^2*i)*x*hxy

/-- The retained factor sum gives the literal recovery equation at p. -/
theorem recovery_eval_of_factor_sum (p q m : ℕ) (w : FamilyPacket) (i : ℤ)
    (hi : (m : ℤ)^2*i=factorSum m w p q) :
    (recoveryPolynomial (p*q) m w i).eval (p : ℤ)=0 := by
  simp only [recoveryPolynomial,quadraticPolynomial,eval_add,eval_mul,eval_C,
    eval_pow,eval_X,Int.cast_id,Nat.cast_mul]
  unfold factorSum at hi
  linear_combination -(p : ℤ)*hi

/-- Both original recovery equations have the true factor roots at their
transported integral indices. Their later reciprocal degeneracy does not
erase these roots or prove that a correct index has been found publicly. -/
theorem publicPacket_factor_partner_recovery {p q m : ℕ} (hm : 0<m)
    (hp : 0<p) (hq : 0<q) {u v : FamilyPacket}
    (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hj : u.residue=p%m) (hk : v.residue=q%m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a) :
    ∃ i : ℤ, (recoveryPolynomial (p*q) m u i).eval (p : ℤ)=0 ∧
      (recoveryPolynomial (p*q) m v (s*i+partnerStep m u v s)).eval (q : ℤ)=0 := by
  obtain ⟨i,k,hi,hkIndex,htransport⟩ :=
    publicPacket_factor_indices_related hm hp hq hu hv hj hk s ha ht
  refine ⟨i,recovery_eval_of_factor_sum p q m u i hi,?_⟩
  have he := recovery_eval_of_factor_sum q p m v k hkIndex
  simpa only [Nat.mul_comm q p,htransport] using he

/-- The reciprocal partner equation is redundant for every possible index.
The ring may itself be a polynomial ring in a symbolic index. -/
theorem publicPacket_reciprocal_recovery_eq {R : Type*} [CommRing R]
    {N m : ℕ} (hm : 0<m) {u v : FamilyPacket}
    (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (i : R) :
    reciprocalRecoveryPolynomial N m v ((s : R)*i+(partnerStep m u v s : R))=
      C (s : R)*recoveryPolynomial N m u i := by
  have he := congrArg (fun z : ℤ => (z : R))
    (publicPacket_partner_step_exact hm hu hv s ha ht hprod)
  simp only [Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast] at he
  simp only [reciprocalRecoveryPolynomial,recoveryPolynomial,quadraticPolynomial,
    ha,ht,Int.cast_mul,he,map_add,map_sub,map_mul,map_pow]
  ring

/-- Genuine Sylvester elimination gives zero identically, not a factor test. -/
theorem publicPacket_partner_recovery_resultant_zero {R : Type*} [CommRing R]
    {N m : ℕ} (hm : 0<m) {u v : FamilyPacket}
    (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (i : R) :
    Polynomial.resultant (recoveryPolynomial N m u i)
      (reciprocalRecoveryPolynomial N m v ((s : R)*i+(partnerStep m u v s : R)))
      2 2=0 := by
  have he := congrArg (fun z : ℤ => (z : R))
    (publicPacket_partner_step_exact hm hu hv s ha ht hprod)
  simp only [Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast] at he
  unfold recoveryPolynomial reciprocalRecoveryPolynomial
  rw [quadratic_resultant]
  simp only [ha,ht,Int.cast_mul,he]
  ring

/-- Eliminating the factor coordinate still gives the zero polynomial when
the index itself is left symbolic. This is not merely a true-index zero. -/
theorem publicPacket_symbolic_partner_resultant_zero {N m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) :
    Polynomial.resultant (recoveryPolynomial N m u (X : ℤ[X]))
      (reciprocalRecoveryPolynomial N m v
        ((s : ℤ[X])*X+(partnerStep m u v s : ℤ[X]))) 2 2=0 :=
  publicPacket_partner_recovery_resultant_zero hm hu hv s ha ht hprod X

/-- Every integer index gives full saturation, so this test selects no index.
Solving a recovery quadratic after its correct index is known is a separate step. -/
theorem publicPacket_partner_resultant_saturated {N m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets N m) (hv : v∈publicPackets N m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a)
    (hprod : (m : ℤ)∣(N : ℤ)-(u.residue : ℤ)*v.residue) (i : ℤ) :
    N.gcd (Polynomial.resultant (recoveryPolynomial N m u i)
      (reciprocalRecoveryPolynomial N m v (s*i+partnerStep m u v s)) 2 2).natAbs=N := by
  have he : Polynomial.resultant (recoveryPolynomial N m u i)
      (reciprocalRecoveryPolynomial N m v (s*i+partnerStep m u v s)) 2 2=0 := by
    simpa only [Int.cast_id] using
      publicPacket_partner_recovery_resultant_zero hm hu hv s ha ht hprod i
  rw [he]
  simp only [Int.natAbs_zero,Nat.gcd_zero_right]

/-- The actual two factor residues satisfy the symbolic obstruction directly. -/
theorem publicPacket_factor_partner_symbolic_resultant_zero {p q m : ℕ} (hm : 0<m)
    {u v : FamilyPacket} (hu : u∈publicPackets (p*q) m) (hv : v∈publicPackets (p*q) m)
    (hj : u.residue=p%m) (hk : v.residue=q%m)
    (s : ℤ) (ha : v.original.a=s*u.original.t) (ht : v.original.t=s*u.original.a) :
    Polynomial.resultant (recoveryPolynomial (p*q) m u (X : ℤ[X]))
      (reciprocalRecoveryPolynomial (p*q) m v
        ((s : ℤ[X])*X+(partnerStep m u v s : ℤ[X]))) 2 2=0 := by
  have hprod : (m : ℤ)∣(p*q : ℕ)-(u.residue : ℤ)*v.residue := by
    simpa only [hj,hk,Nat.cast_mul] using factor_residue_product_dvd p q m
  exact publicPacket_symbolic_partner_resultant_zero hm hu hv s ha ht hprod

end RiemannGaussian.SemiprimePartnerRecoveryObstruction
