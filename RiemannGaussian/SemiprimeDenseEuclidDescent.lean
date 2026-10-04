/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseCarryBoundary
import Mathlib.Algebra.Polynomial.Monic

/-!
# Exact Euclidean descent of the retained carry boundaries

Jump levels give public indices without scanning a row matrix. At a
coprime slope, the interior after-jump roots form the Euclidean child
curve, with transformed public powers and an explicit unit phase. The
endpoint is retained before cancellation at the polynomial source.
An interior geometric branch proves that the smaller products and
endpoints alone do not detect all parent collisions. The retained
target-shift relation is not a paid collision-acquisition algorithm.
-/

namespace RiemannGaussian.SemiprimeDenseEuclidDescent

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeDenseCarryBoundary Polynomial
open scoped BigOperators

/-- Public index immediately preceding the kth crossed floor level. -/
def jumpIndex (m u k : ℕ) : ℕ := (m*k-1)/u

/-- All crossed levels, including the final endpoint level. -/
def levels (u : ℕ) : Finset ℕ := insert u (residues u)

/-- Level membership keeps both positive and endpoint bounds. -/
theorem mem_levels {u k : ℕ} (hu : 0<u) : k∈levels u ↔ 0<k ∧ k≤u := by
  simp only [levels,Finset.mem_insert,mem_residues]
  omega

/-- The crossed level's index retains the exact floors on both sides. -/
theorem jumpIndex_floors {m u k : ℕ} (hu : 0<u) (hum : u<m)
    (hk : 0<k) :
    u*jumpIndex m u k/m=k-1 ∧ u*(jumpIndex m u k+1)/m=k := by
  have hm : 0<m := by omega
  have hmk : 0<m*k := Nat.mul_pos hm hk
  have hp : m*k-1+1=m*k := by omega
  have hd := Nat.mod_add_div (m*k-1) u
  have hr := Nat.mod_lt (m*k-1) hu
  change (m*k-1)%u+u*jumpIndex m u k=m*k-1 at hd
  have hkm : k-1+1=k := by omega
  constructor
  · apply Nat.div_eq_of_lt_le
    · nlinarith only [hd,hr,hp,hkm,hum]
    · nlinarith only [hd,hp,hkm,Nat.zero_le ((m*k-1)%u)]
  · apply Nat.div_eq_of_lt_le
    · nlinarith only [hd,hr,hp]
    · nlinarith only [hd,hp,hum,Nat.zero_le ((m*k-1)%u)]

/-- Every crossed level produces an original positive-denominator jump. -/
theorem jumpIndex_mem {m u k : ℕ} (hu : 0<u) (hum : u<m)
    (hk : 0<k) (hku : k≤u) : jumpIndex m u k∈jumpSet m u := by
  have hf := jumpIndex_floors hu hum hk
  have hm : 0<m := by omega
  have hmk : 0<m*k := Nat.mul_pos hm hk
  have hp : m*k-1+1=m*k := by omega
  have ht : jumpIndex m u k<m := by
    unfold jumpIndex
    apply (Nat.div_lt_iff_lt_mul hu).mpr
    nlinarith only [hp,Nat.mul_le_mul_left m hku]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ht,?_⟩
  unfold carryJump
  rw [hf.1,hf.2]
  omega

/-- A retained jump's after-floor is a valid crossed level. -/
theorem jump_level_mem {m u t : ℕ} (hu : 0<u)
    (ht : t∈jumpSet m u) : u*(t+1)/m∈levels u := by
  have hmem := Finset.mem_filter.mp ht
  have htm := Finset.mem_range.mp hmem.1
  have hm : 0<m := by omega
  have htop : u*(t+1)/m≤u := by
    have h := Nat.div_le_div_right (c:=m) (Nat.mul_le_mul_left u (by omega : t+1≤m))
    simpa only [Nat.mul_div_cancel _ hm] using h
  apply (mem_levels hu).mpr
  have hinc := carryJump_add m u t
  rw [hmem.2] at hinc
  refine ⟨?_,htop⟩
  rw [←hinc]
  exact Nat.succ_pos _

/-- Indexing by crossed levels recovers every original jump, with no search. -/
theorem jumpIndex_inverse {m u t : ℕ} (hu : 0<u) (hum : u<m)
    (ht : t∈jumpSet m u) : jumpIndex m u (u*(t+1)/m)=t := by
  have hmem := Finset.mem_filter.mp ht
  have hm : 0<m := hu.trans hum
  have hk := (mem_levels hu).mp (jump_level_mem hu ht)
  have hp : m*(u*(t+1)/m)-1+1=m*(u*(t+1)/m) := by
    have h := Nat.mul_pos hm hk.1
    omega
  have hlo := Nat.mul_div_le (u*(t+1)) m
  have hhi := Nat.lt_mul_div_succ (u*t) hm
  have hinc := carryJump_add m u t
  rw [hmem.2] at hinc
  rw [hinc] at hhi
  unfold jumpIndex
  apply Nat.div_eq_of_lt_le
  · nlinarith only [hhi,hp]
  · nlinarith only [hlo,hp]

/-- The jump index map is injective on its complete crossed-level range. -/
theorem jumpIndex_injective {m u : ℕ} (hu : 0<u) (hum : u<m)
    {k l : ℕ} (hk : k∈levels u) (hl : l∈levels u)
    (he : jumpIndex m u k=jumpIndex m u l) : k=l := by
  have hk₀ := (mem_levels hu).mp hk
  have hl₀ := (mem_levels hu).mp hl
  have hfk := (jumpIndex_floors hu hum hk₀.1).2
  have hfl := (jumpIndex_floors hu hum hl₀.1).2
  rw [he] at hfk
  exact hfk.symm.trans hfl

/-- The complete carry boundary is exactly the image of the public level map. -/
theorem jumpSet_eq_levels_image {m u : ℕ} (hu : 0<u) (hum : u<m) :
    jumpSet m u=(levels u).image (jumpIndex m u) := by
  ext t
  rw [Finset.mem_image]
  constructor
  · intro ht
    exact ⟨u*(t+1)/m,jump_level_mem hu ht,jumpIndex_inverse hu hum ht⟩
  · rintro ⟨k,hk,rfl⟩
    have h := (mem_levels hu).mp hk
    exact jumpIndex_mem hu hum h.1 h.2

/-- The final crossed level is the original last denominator, not a new row. -/
theorem jumpIndex_last {m u : ℕ} (hu : 0<u) (hum : u<m) :
    jumpIndex m u u=m-1 := by
  have hp : m*u-1+1=m*u := by have h := Nat.mul_pos (by omega : 0<m) hu; omega
  have hm : m-1+1=m := by omega
  unfold jumpIndex
  apply Nat.div_eq_of_lt_le
  · nlinarith only [hp,hm,hu]
  · nlinarith only [hp,hm]

/-- Euclidean quotient and remainder retain the exact numerator division. -/
theorem divided_product (m u k : ℕ) (hu : 0<u) :
    m*k/u=(m/u)*k+(m%u)*k/u := by
  have he : m*k=(m%u)*k+u*((m/u)*k) := by
    calc
      _=((m%u)+u*(m/u))*k := by rw [Nat.mod_add_div]
      _=_ := by ring
  rw [he,Nat.add_mul_div_left _ _ hu]
  omega

/-- Coprime interior levels have the exact ceiling offset required by
the smaller curve; no unproved rounding or endpoint convention is used. -/
theorem jumpIndex_interior {m u k : ℕ} (hu : 0<u) (hum : u<m)
    (hcop : m.Coprime u) (hk : 0<k) (hku : k<u) :
    jumpIndex m u k+1=(m/u)*k+(m%u)*k/u+1 := by
  have hnot : ¬u∣m*k := by
    intro hd
    exact Nat.not_dvd_of_pos_of_lt hk hku (hcop.symm.dvd_of_dvd_mul_left hd)
  have hr₀ : 0<(m*k)%u := by
    by_contra hn
    have hz : (m*k)%u=0 := by omega
    exact hnot (Nat.dvd_of_mod_eq_zero hz)
  have hr₁ := Nat.mod_lt (m*k) hu
  have hd := Nat.mod_add_div (m*k) u
  have hp : m*k-1+1=m*k := by
    have h := Nat.mul_pos (by omega : 0<m) hk
    omega
  have he : jumpIndex m u k=m*k/u := by
    unfold jumpIndex
    apply Nat.div_eq_of_lt_le
    · nlinarith only [hd,hr₀,hp]
    · nlinarith only [hd,hr₁,hp]
  rw [he,divided_product m u k hu]

/-- The Euclidean child's public step power. -/
def childStep {G : Type*} [CommGroup G] (A B : G) (m u : ℕ) : G :=
  A^(m/u)*B⁻¹

/-- The Euclidean child's public carry power. -/
def childCarry {G : Type*} [CommGroup G] (A : G) : G := A⁻¹

/-- The retained phase of the parent orientation. -/
def orientationPhase {G : Type*} [CommGroup G] (A B : G) (negative : Bool) : G :=
  A*B^(-((if negative then 1 else 0 : ℕ) : ℤ))

/-- The child's transformed powers combine to the exact parent monomial. -/
theorem child_monomial {G : Type*} [CommGroup G] (A B : G) (q k d : ℕ) :
    (A^q*B⁻¹)^k*(A⁻¹)^(-(d : ℤ))=A^(q*k+d)*B^(-(k : ℤ)) := by
  calc
    _=(A^(q*k)*(B⁻¹)^k)*A^d := by
      simp only [mul_pow,←pow_mul,zpow_neg,zpow_natCast,inv_pow,inv_inv]
    _=_ := by
      rw [pow_add,zpow_neg,zpow_natCast,inv_pow]
      ac_rfl

/-- Every interior after-jump value is exactly a phased child value.
The child uses the canonical orientation; the parent sign stays in the phase. -/
theorem after_jump_child {G : Type*} [CommGroup G] (A B : G)
    {m u k : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (hk : 0<k) (hku : k<u) (negative : Bool) :
    curveValue A B m u negative (jumpIndex m u k+1)=
      orientationPhase A B negative*
        curveValue (childStep A B m u) (childCarry A) u (m%u) false k := by
  have hf := (jumpIndex_floors hu hum hk).2
  have ht := jumpIndex_interior hu hum hcop hk hku
  have hs : curveValue (childStep A B m u) (childCarry A) u (m%u) false k=
      A^((m/u)*k+(m%u)*k/u)*B^(-(k : ℤ)) :=
    child_monomial A B (m/u) k ((m%u)*k/u)
  rw [hs,curveValue,hf,ht]
  have hb : -((k+(if negative then 1 else 0) : ℕ) : ℤ)=
      -(k : ℤ)+(-((if negative then 1 else 0 : ℕ) : ℤ)) := by
    simp only [Nat.cast_add,neg_add]
  rw [hb,zpow_add,pow_succ]
  unfold orientationPhase
  ac_rfl

/-- The first original root is precisely the retained orientation phase. -/
theorem orientationPhase_eq_first {G : Type*} [CommGroup G] (A B : G)
    {m u : ℕ} (hum : u<m) (negative : Bool) :
    orientationPhase A B negative=curveValue A B m u negative 1 := by
  simp [orientationPhase,curveValue,Nat.div_eq_of_lt hum]

/-- On a retained jump, its before value is B times its after value. -/
theorem before_jump_relation {G : Type*} [CommGroup G] (A B : G)
    {m u t : ℕ} (ht : t∈jumpSet m u) (negative : Bool) :
    A*curveValue A B m u negative t=B*curveValue A B m u negative (t+1) := by
  have hδ := (Finset.mem_filter.mp ht).2
  rw [curveValue_step A B, hδ]
  simp only [Nat.cast_one,zpow_neg_one]
  simp [mul_assoc,mul_left_comm]

/-- The interior before roots retain the same child with the exact B phase. -/
theorem before_jump_child {G : Type*} [CommGroup G] (A B : G)
    {m u k : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (hk : 0<k) (hku : k<u) (negative : Bool) :
    A*curveValue A B m u negative (jumpIndex m u k)=
      (orientationPhase A B negative*B)*
        curveValue (childStep A B m u) (childCarry A) u (m%u) false k := by
  rw [before_jump_relation A B (jumpIndex_mem hu hum hk (Nat.le_of_lt hku)),
    after_jump_child A B hu hum hcop hk hku]
  ac_rfl

/-- Complete jump products reindex by crossed levels, without enumerating m slots. -/
theorem jump_product_levels {M : Type*} [CommMonoid M] (f : ℕ→M)
    {m u : ℕ} (hu : 0<u) (hum : u<m) :
    (∏ t∈jumpSet m u, f t)=∏ k∈levels u, f (jumpIndex m u k) := by
  rw [jumpSet_eq_levels_image hu hum,Finset.prod_image]
  exact fun _ hk _ hl he => jumpIndex_injective hu hum hk hl he

/-- Scaling each root by a unit has an exact polynomial substitution and phase. -/
theorem root_product_scale {R : Type*} [CommRing R] (S : Rˣ) (f : ℕ→Rˣ)
    {u : ℕ} (hu : 0<u) :
    (∏ k∈residues u, (X-C ((S*f k : Rˣ) : R)))=
      C ((S : R)^(u-1))*
        (∏ k∈residues u, (X-C (f k : R))).comp (C ((S⁻¹ : Rˣ) : R)*X) := by
  have hi : C (S : R)*C ((S⁻¹ : Rˣ) : R)=(1 : R[X]) := by
    rw [←C_mul]
    simp
  have hf (k : ℕ) : X-C ((S*f k : Rˣ) : R)=
      C (S : R)*(C ((S⁻¹ : Rˣ) : R)*X-C (f k : R)) := by
    simp only [Units.val_mul,C_mul]
    linear_combination -(X : R[X])*hi
  simp only [hf,Finset.prod_mul_distrib,Finset.prod_const,residues_card hu,
    Polynomial.prod_comp,Polynomial.sub_comp,Polynomial.X_comp,
    Polynomial.C_comp,map_pow]

/-- The complete smaller source after its explicit public unit phase.
This definition is a mathematical product, not a fast evaluation routine. -/
noncomputable def phasedChildPolynomial {R : Type*} [CommRing R]
    (A B S : Rˣ) (m u : ℕ) : R[X] :=
  C ((S : R)^(u-1))*
    (sourcePolynomial (childStep A B m u) (childCarry A) u (m%u) false).comp
      (C ((S⁻¹ : Rˣ) : R)*X)

/-- The complete after boundary is the phased Euclidean child plus its endpoint. -/
theorem afterPolynomial_descent {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (negative : Bool) :
    afterPolynomial A B m u negative=
      (X-C (curveValue (G:=Rˣ) A B m u negative m : R))*
        phasedChildPolynomial A B (orientationPhase A B negative) m u := by
  have hlast : jumpIndex m u u+1=m := by
    rw [jumpIndex_last hu hum]
    omega
  have hnot : u∉residues u := by simp only [mem_residues]; omega
  unfold afterPolynomial
  rw [jump_product_levels _ hu hum,levels,Finset.prod_insert hnot,hlast]
  congr 1
  have he : (∏ k∈residues u,
      (X-C (curveValue (G:=Rˣ) A B m u negative (jumpIndex m u k+1) : R)))=
      ∏ k∈residues u, (X-C ((orientationPhase A B negative*
        curveValue (childStep A B m u) (childCarry A) u (m%u) false k : Rˣ) : R)) := by
    apply Finset.prod_congr rfl
    intro k hk
    have h := mem_residues.mp hk
    rw [after_jump_child A B hu hum hcop h.1 h.2]
  rw [he,root_product_scale _ _ hu]
  rfl

/-- The complete before boundary retains the B-shifted endpoint and child. -/
theorem beforePolynomial_descent {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (negative : Bool) :
    beforePolynomial A B m u negative=
      (X-C ((B*curveValue A B m u negative m : Rˣ) : R))*
        phasedChildPolynomial A B (orientationPhase A B negative*B) m u := by
  have hlast : jumpIndex m u u+1=m := by
    rw [jumpIndex_last hu hum]
    omega
  have hend : A*curveValue A B m u negative (jumpIndex m u u)=
      B*curveValue A B m u negative m := by
    rw [before_jump_relation A B (jumpIndex_mem hu hum hu (Nat.le_refl u)),hlast]
  have hnot : u∉residues u := by simp only [mem_residues]; omega
  unfold beforePolynomial
  rw [jump_product_levels _ hu hum,levels,Finset.prod_insert hnot,hend]
  congr 1
  have he : (∏ k∈residues u,
      (X-C ((A*curveValue A B m u negative (jumpIndex m u k) : Rˣ) : R)))=
      ∏ k∈residues u, (X-C (((orientationPhase A B negative*B)*
        curveValue (childStep A B m u) (childCarry A) u (m%u) false k : Rˣ) : R)) := by
    apply Finset.prod_congr rfl
    intro k hk
    have h := mem_residues.mp hk
    rw [before_jump_child A B hu hum hcop h.1 h.2]
  rw [he,root_product_scale _ _ hu]
  rfl

/-- Cancelling the common monic endpoint at the polynomial source gives
an exact Euclidean functional relation. No evaluated nonzero or unit
premise is imposed; all remaining child and endpoint zeros are retained. -/
theorem euclidean_polynomial_relation {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (negative : Bool) :
    shiftedPolynomial A B m u negative*
        phasedChildPolynomial A B (orientationPhase A B negative) m u*
        (X-C (orientationPhase (G:=Rˣ) A B negative : R))=
      sourcePolynomial A B m u negative*
        (X-C ((B*curveValue A B m u negative m : Rˣ) : R))*
        phasedChildPolynomial A B (orientationPhase A B negative*B) m u := by
  have he := adjacent_polynomial_telescoping A B (hu.trans hum) hum negative
  rw [afterPolynomial_descent A B hu hum hcop negative,
    beforePolynomial_descent A B hu hum hcop negative,
    ←orientationPhase_eq_first A B hum negative] at he
  apply (monic_X_sub_C (curveValue (G:=Rˣ) A B m u negative m : R)).isRegular.2
  calc
    _=shiftedPolynomial A B m u negative*
      ((X-C (curveValue (G:=Rˣ) A B m u negative m : R))*
        phasedChildPolynomial A B (orientationPhase A B negative) m u)*
      (X-C (orientationPhase (G:=Rˣ) A B negative : R)) := by ring
    _=_ := he
    _=_ := by ring

/-- The same exact relation exposes the parent's public target shift.
It does not compute the original product value from one child value. -/
theorem euclidean_target_relation {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (negative : Bool) :
    C ((A : R)^(m-1))*
        (sourcePolynomial A B m u negative).comp (C ((A⁻¹ : Rˣ) : R)*X)*
        phasedChildPolynomial A B (orientationPhase A B negative) m u*
        (X-C (orientationPhase (G:=Rˣ) A B negative : R))=
      sourcePolynomial A B m u negative*
        (X-C ((B*curveValue A B m u negative m : Rˣ) : R))*
        phasedChildPolynomial A B (orientationPhase A B negative*B) m u := by
  rw [←shiftedPolynomial_rephase A B (hu.trans hum) negative]
  exact euclidean_polynomial_relation A B hu hum hcop negative

/-- Coprimality is preserved by the public Euclidean remainder descent. -/
theorem child_coprime {m u : ℕ} (hcop : m.Coprime u) :
    u.Coprime (m%u) := by
  change Nat.gcd u (m%u)=1
  rw [Nat.gcd_comm,←Nat.gcd_rec]
  exact hcop.symm

/-- An interior public numerator is coprime to m after canonical reduction. -/
theorem public_slope_coprime {N m j : ℕ} (hm : 0<m)
    (hN : m.Coprime N) (hj : j.Coprime m) :
    m.Coprime (representative N m j 1) := by
  change Nat.gcd m ((quotientSlope N m j*1)%m)=1
  rw [Nat.mul_one,Nat.gcd_comm,←Nat.gcd_rec]
  exact quotientSlope_coprime hm hN hj

/-- The actual N-only descriptor discharges every arithmetic descent premise.
Neither a prime factor nor a local multiplicative order is an input. -/
theorem public_slope_bounds {N m j : ℕ} (hm : 1<m)
    (hN : m.Coprime N) (hj : j.Coprime m) :
    0<representative N m j 1 ∧ representative N m j 1<m ∧
      m.Coprime (representative N m j 1) := by
  have hc := public_slope_coprime (by omega : 0<m) hN hj
  have hp : 0<representative N m j 1 := by
    by_contra hn
    have hz : representative N m j 1=0 := by omega
    rw [hz] at hc
    have h : m=1 := by simpa using hc
    omega
  exact ⟨hp,Nat.mod_lt _ (by omega),hc⟩

/-- Every actual cached residue obeys the complete division-free child relation.
The public prefix checks discharge the generic coprimality premises. -/
theorem public_euclidean_relation {R : Type*} [CommRing R] (g : Rˣ)
    {N m j : ℕ} (hm : 1<m) (hN : m.Coprime N) (hj : j.Coprime m)
    (negative : Bool) :
    let s := progressionSeed g N m j
    shiftedPolynomial s.step s.carryStep m s.slope negative*
        phasedChildPolynomial s.step s.carryStep
          (orientationPhase s.step s.carryStep negative) m s.slope*
        (X-C (orientationPhase (G:=Rˣ) s.step s.carryStep negative : R))=
      sourcePolynomial s.step s.carryStep m s.slope negative*
        (X-C ((s.carryStep*curveValue s.step s.carryStep m s.slope negative m : Rˣ) : R))*
        phasedChildPolynomial s.step s.carryStep
          (orientationPhase s.step s.carryStep negative*s.carryStep) m s.slope := by
  have h := public_slope_bounds hm hN hj
  exact euclidean_polynomial_relation _ _ h.1 h.2.1 h.2.2 negative

/-- A parent collision transports to its shifted parent, a complete child,
or the original first endpoint. This is a field projection statement;
no division by a child or endpoint evaluation is performed. -/
theorem source_shift_child_zero {K : Type*} [Field K] (A B : Kˣ)
    {m u : ℕ} (hu : 0<u) (hum : u<m) (hcop : m.Coprime u)
    (negative : Bool) (x : K)
    (hx : (sourcePolynomial A B m u negative).eval x=0) :
    (sourcePolynomial A B m u negative).eval (((A⁻¹ : Kˣ) : K)*x)=0 ∨
      (phasedChildPolynomial A B (orientationPhase A B negative) m u).eval x=0 ∨
      x=(orientationPhase (G:=Kˣ) A B negative : K) := by
  have he := congrArg (fun P : K[X] => P.eval x)
    (euclidean_target_relation A B hu hum hcop negative)
  simp only [eval_mul,eval_comp,eval_sub,eval_X,eval_C] at he
  rw [hx,zero_mul,zero_mul] at he
  have hscalar : (A : K)^(m-1)≠0 := pow_ne_zero _ A.ne_zero
  rcases mul_eq_zero.mp he with hc | hf
  · rcases mul_eq_zero.mp hc with hp | hchild
    · exact Or.inl ((mul_eq_zero.mp hp).resolve_left hscalar)
    · exact Or.inr (Or.inl hchild)
  · exact Or.inr (Or.inr (sub_eq_zero.mp hf))

/-- At slope one the Euclidean child has no roots, for every phase. -/
theorem unitSlope_child_one {R : Type*} [CommRing R] (A B S : Rˣ) (m : ℕ) :
    phasedChildPolynomial A B S m 1=1 := by
  simp [phasedChildPolynomial,sourcePolynomial,residues]

/-- Interior values at slope one are an ordinary geometric progression. -/
theorem unitSlope_value {G : Type*} [CommGroup G] (A B : G)
    {m t : ℕ} (ht : t<m) : curveValue A B m 1 false t=A^t := by
  simp [curveValue,Nat.div_eq_of_lt ht]

/-- An original retained root always vanishes in the complete source product. -/
theorem source_eval_at_root {R : Type*} [CommRing R] (A B : Rˣ)
    {m u t : ℕ} (ht : t∈residues m) (negative : Bool) :
    (sourcePolynomial A B m u negative).eval
      (curveValue (G:=Rˣ) A B m u negative t : R)=0 := by
  simp only [sourcePolynomial,eval_prod]
  apply Finset.prod_eq_zero ht
  simp only [eval_sub,eval_X,eval_C,sub_self]

/-- Arbitrarily long geometric parent rows can have interior collisions
invisible to both complete Euclidean children and both retained endpoints.
Thus child/endpoints alone are not a collision detector for the source. -/
theorem geometric_interior_unseen {K : Type*} [Field K] (A B : Kˣ)
    {m t : ℕ} (ht₁ : 1<t) (htm : t<m) (horder : m<orderOf A) :
    let x : K := (A^t : Kˣ)
    (sourcePolynomial A B m 1 false).eval x=0 ∧
      (phasedChildPolynomial A B (orientationPhase A B false) m 1).eval x=1 ∧
      (phasedChildPolynomial A B (orientationPhase A B false*B) m 1).eval x=1 ∧
      x≠(orientationPhase (G:=Kˣ) A B false : K) ∧
      x≠((B*curveValue A B m 1 false m : Kˣ) : K) := by
  have hm : 0<m := by omega
  have hx := source_eval_at_root A B ((mem_residues).mpr ⟨by omega,htm⟩)
    (u:=1) false
  rw [unitSlope_value A B htm] at hx
  have hf : (A^t : K)≠(A : K) := by
    intro he
    have hu : A^t=A^1 := Units.ext (by simpa using he)
    have hh := pow_injOn_Iio_orderOf (x:=A)
      (htm.trans horder) (by omega : 1<orderOf A) hu
    omega
  have hend : B*curveValue A B m 1 false m=A^m := by
    rw [curveValue,Nat.one_mul,Nat.div_self hm]
    simp
  have hl : (A^t : K)≠(A^m : K) := by
    intro he
    have hu : A^t=A^m := Units.ext (by simpa using he)
    have hh := pow_injOn_Iio_orderOf (x:=A) (htm.trans horder) horder hu
    omega
  refine ⟨hx,?_,?_,?_,?_⟩
  · rw [unitSlope_child_one,eval_one]
  · rw [unitSlope_child_one,eval_one]
  · simpa [orientationPhase] using hf
  · simpa [hend] using hl

end RiemannGaussian.SemiprimeDenseEuclidDescent
