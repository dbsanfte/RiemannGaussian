/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeOffsetCarryObstruction

/-!
# Shifted-target norms retain a restrictive period envelope

The actual original target-vs-shifted-target norm is a product of all
literal cross differences. Every local hit forces a positive multiple of
its retained local order into a short interval. Excluding that arithmetic
envelope in both hidden fields makes every acquired scalar and component
unit. Global separation also handles aggregate saturation on a nonunit
branch by retaining a proper individual pair.

The investigation journal uses this finite source bridge to obstruct
polylogarithmic shift catalogs indexed by the full two-digit residue
N modulo m squared on infinitely many actual long-base-2 inputs. It also
supplies actual unit gates for the first executed remainder overrun.
Analytic density, infinite families and bit-complexity claims are not
additional Lean axioms in this module.
-/

namespace RiemannGaussian.SemiprimeShiftedNormAcquisitionObstruction

open scoped BigOperators
open Polynomial
open SemiprimeCauchyAcquisitionObstruction SemiprimeGlobalPhaseCancellation
open SemiprimeSeedSumAcquisition SemiprimeSeedPointRigidity
open SemiprimeDenseRowCarries SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeSeedHermiteQuotient SemiprimeSharedIntervalJet
open SemiprimeNormCancellationObstruction SemiprimeSeedGeometricRecurrence
open SemiprimeGeometricRows SemiprimeOffsetCarryObstruction SemiprimeDenseRowCoverage

/-- Literal original normalized target against another original target. -/
noncomputable def shiftedCross {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ)
    (i j : Fin (m-1)) : ZMod N :=
  seedPoint g m 1 (i.val+1) t-seedPoint g m 1 (j.val+1) 0

/-- One scalar cross test; its gcd can be saturated. -/
noncomputable def crossNorm {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ) : ZMod N :=
  ∏ i : Fin (m-1), ∏ j : Fin (m-1), shiftedCross g m t i j

/-- Actual source-preserving scalar acquired by monic multipoint evaluation. -/
noncomputable def shiftedTargetNorm {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ) : ZMod N :=
  ∏ i : Fin (m-1),
    (targetPolynomial (seedTargets g m)).eval (seedPoint g m 1 (i.val+1) t)

/-- A literal list of row labels has the same product as its finite range. -/
theorem list_prod_map_range_eq_finset_prod
    {R : Type*} [CommMonoid R] (f : ℕ→R) (n : ℕ) :
    ((List.range n).map f).prod=∏ r∈Finset.range n,f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ,Finset.prod_range_succ,ih]

/-- Product-of-evaluations and product-of-cross-differences are identical;
no Cauchy denominator or hidden prime inverse is involved. -/
theorem shiftedTargetNorm_eq_crossNorm {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ) :
    shiftedTargetNorm g m t=crossNorm g m t := by
  unfold shiftedTargetNorm crossNorm
  apply Finset.prod_congr rfl
  intro i _
  simp only [targetPolynomial,seedTargets,progressionSeeds,eval_list_prod,
    List.map_map,Function.comp_def,eval_sub,eval_X,eval_C]
  rw [list_prod_map_range_eq_finset_prod]
  unfold shiftedCross
  simp only [seedPoint,normalizedPoint,zero_mul,pow_zero,inv_one,
    Units.val_one,one_mul]
  exact (Fin.prod_univ_eq_prod_range _ (m-1)).symm

/-- The scalar is a unit exactly when every literal cross difference is. -/
theorem crossNorm_isUnit_iff {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ) :
    IsUnit (crossNorm g m t) ↔ ∀ i j : Fin (m-1),IsUnit (shiftedCross g m t i j) := by
  simp only [crossNorm,IsUnit.prod_iff,Finset.mem_univ,true_implies]

/-- Monic multipoint scalar output is a unit exactly when all source crosses are units. -/
theorem shiftedTargetNorm_isUnit_iff {N : ℕ} (g : (ZMod N)ˣ) (m t : ℕ) :
    IsUnit (shiftedTargetNorm g m t) ↔
      ∀ i j : Fin (m-1),IsUnit (shiftedCross g m t i j) := by
  rw [shiftedTargetNorm_eq_crossNorm,crossNorm_isUnit_iff]

/-- Offset-independent necessary period multiple for any local shifted hit. -/
def periodEnvelope (m t R : ℕ) : Prop :=
  ∃ k : ℕ, 0<k ∧ |(m : ℤ)^2*t-(k : ℤ)*R|≤4*(m : ℤ)^2

/-- An actual hit yields a POSITIVE multiple, not an unrestricted signed
or zero multiple. The common N phase cancels before this bound. -/
theorem positive_periodEnvelope_of_zpow_eq
    {G : Type*} [Group G] (u : G) (N m t : ℕ) (a b : ℤ)
    (hm : 4≤m) (ht : 8≤t)
    (ha : -3*(m : ℤ)^2≤a ∧ a≤(m : ℤ)^2)
    (hb : -3*(m : ℤ)^2≤b ∧ b≤(m : ℤ)^2)
    (he : u^((N : ℤ)+a-(m : ℤ)^2*t)=u^((N : ℤ)+b)) :
    periodEnvelope m t (orderOf u) := by
  have hmpos : 0<(m : ℤ)^2 := pow_pos (by omega : 0<(m : ℤ)) 2
  have htZ : (8 : ℤ)≤t := by exact_mod_cast ht
  have hlower : 8*(m : ℤ)^2≤(m : ℤ)^2*t := by
    nlinarith only [mul_le_mul_of_nonneg_left htZ hmpos.le]
  have hpositive : 0<(m : ℤ)^2*t+b-a := by
    nlinarith only [ha.2,hb.1,hlower,hmpos]
  have hd := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr he
  have hdiv : (orderOf u : ℤ)∣(m : ℤ)^2*t+b-a := by
    convert (dvd_neg.mpr hd) using 1
    ring
  obtain ⟨l,hl⟩ := hdiv
  have hlpos : 0<l := by
    by_contra hnot
    have hlle : l≤0 := le_of_not_gt hnot
    have hproduct := mul_nonpos_of_nonneg_of_nonpos
      (Int.natCast_nonneg (orderOf u)) hlle
    linarith only [hl,hpositive,hproduct]
  have hcast : (l.toNat : ℤ)=l := Int.toNat_of_nonneg hlpos.le
  refine ⟨l.toNat,?_,?_⟩
  · have hp : (0 : ℤ)<(l.toNat : ℤ) := by rw [hcast]; exact hlpos
    exact_mod_cast hp
  · have hres : (m : ℤ)^2*t-(l.toNat : ℤ)*orderOf u=a-b := by
      rw [hcast]
      nlinarith only [hl]
    rw [hres,abs_le]
    constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2]

/-- Any coefficient-ring specialization producing a local cross hit
has its retained unit order in the positive period envelope. -/
theorem specialized_shiftedCross_hit_periodEnvelope
    {N m t : ℕ} {R : Type*} [CommRing R]
    (f : ZMod N→+*R) (g : (ZMod N)ˣ)
    (hm : 4≤m) (hmprime : m.Prime) (ht : 8≤t)
    (i j : Fin (m-1)) (hhit : f (shiftedCross g m t i j)=0) :
    periodEnvelope m t (orderOf (Units.map f.toMonoidHom g)) := by
  have hicop : (i.val+1).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have hjcop : (j.val+1).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have hiBound := seedOffset_bounds (N := N) (m := m) (j := i.val+1)
    (by omega) (by omega) (by omega)
  have hjBound := seedOffset_bounds (N := N) (m := m) (j := j.val+1)
    (by omega) (by omega) (by omega)
  unfold shiftedCross at hhit
  rw [seedPoint_eq_zpow _ hmprime.pos hicop,
    seedPoint_eq_zpow _ hmprime.pos hjcop] at hhit
  have he : (Units.map f.toMonoidHom g)^pointExponent N m 1 (i.val+1) t=
      (Units.map f.toMonoidHom g)^pointExponent N m 1 (j.val+1) 0 := by
    apply Units.ext
    apply sub_eq_zero.mp
    simpa only [map_sub,Units.coe_map,←map_zpow,
      RingHom.toMonoidHom_eq_coe,MonoidHom.coe_coe] using hhit
  apply positive_periodEnvelope_of_zpow_eq (Units.map f.toMonoidHom g) N m t
    (seedOffset N m (i.val+1)) (seedOffset N m (j.val+1)) hm ht hiBound hjBound
  simpa only [pointExponent,Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,sub_zero] using he

/-- Excluding the envelope in BOTH local periods makes every original
cross difference a unit. This bridges the arithmetic count to the
literal acquired scalar without inferring anything about internal pivots. -/
theorem cross_units_of_no_local_periodEnvelope {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (ht : 8≤t)
    (hleft : ¬periodEnvelope m t (orderOf (leftUnit (projectedUnit g m))))
    (hright : ¬periodEnvelope m t (orderOf (rightUnit (projectedUnit g m)))) :
    ∀ i j : Fin (m-1),IsUnit (shiftedCross (projectedUnit g m) m t i j) := by
  intro i j
  apply SemiprimeIntervalJet.isUnit_of_prime_reductions hp hq
  · intro hz
    exact hleft (specialized_shiftedCross_hit_periodEnvelope
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)) (projectedUnit g m)
        hm hmprime ht i j hz)
  · intro hz
    exact hright (specialized_shiftedCross_hit_periodEnvelope
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)) (projectedUnit g m)
        hm hmprime ht i j hz)

/-- The order-envelope exclusions directly certify the actual acquired norm as a unit. -/
theorem shiftedTargetNorm_unit_of_no_local_periodEnvelope {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (ht : 8≤t)
    (hleft : ¬periodEnvelope m t (orderOf (leftUnit (projectedUnit g m))))
    (hright : ¬periodEnvelope m t (orderOf (rightUnit (projectedUnit g m)))) :
    IsUnit (shiftedTargetNorm (projectedUnit g m) m t) :=
  (shiftedTargetNorm_isUnit_iff _ _ _).mpr
    (cross_units_of_no_local_periodEnvelope hp hq hm hmprime g ht hleft hright)

/-- On the all-unit arithmetic branch, the acquired scalar and every
acquired original row component have gcd one. Internal Euclidean
pivots or subresultant coefficients are not part of this statement. -/
theorem unit_shiftedTargetNorm_component_gcd_one {N : ℕ} [NeZero N]
    (g : (ZMod N)ˣ) (m t : ℕ) (hunit : IsUnit (shiftedTargetNorm g m t)) :
    N.gcd (shiftedTargetNorm g m t).val=1 ∧
      ∀ i : Fin (m-1), N.gcd
        ((targetPolynomial (seedTargets g m)).eval
          (seedPoint g m 1 (i.val+1) t)).val=1 := by
  constructor
  · exact (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr hunit
  · have hcomponents : ∀ i : Fin (m-1), IsUnit
        ((targetPolynomial (seedTargets g m)).eval
          (seedPoint g m 1 (i.val+1) t)) := by
      simpa only [shiftedTargetNorm,IsUnit.prod_iff,Finset.mem_univ,true_implies] using hunit
    intro i
    exact (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr (hcomponents i)

/-- The shift stays shorter than the actual GLOBAL order, while its
integer gap is positive. No distinct-tag or distinct-offset premise is
needed: every scaled cross difference is globally nonzero. -/
theorem long_shiftedCross_ne_zero {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 8≤t) (htupper : t≤4*m^2) (i j : Fin (m-1)) :
    shiftedCross (projectedUnit g m) m t i j≠0 := by
  have hicop : (i.val+1).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have hjcop : (j.val+1).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have hiBound := seedOffset_bounds (N := p*q) (m := m) (j := i.val+1)
    (by omega) (by omega) (by omega)
  have hjBound := seedOffset_bounds (N := p*q) (m := m) (j := j.val+1)
    (by omega) (by omega) (by omega)
  let a := pointExponent (p*q) m 1 (i.val+1) t
  let b := pointExponent (p*q) m 1 (j.val+1) 0
  have hmpos : 0<(m : ℤ)^2 := pow_pos (by omega : 0<(m : ℤ)) 2
  have htZ : (8 : ℤ)≤t := by exact_mod_cast ht
  have htuZ : (t : ℤ)≤4*(m : ℤ)^2 := by exact_mod_cast htupper
  have hmul : (m : ℤ)^2*t≤4*(m : ℤ)^4 := by
    nlinarith only [htuZ,sq_nonneg (m : ℤ)]
  have hlower : 8*(m : ℤ)^2≤(m : ℤ)^2*t := by
    nlinarith only [mul_le_mul_of_nonneg_left htZ hmpos.le]
  have hab : a≠b := by
    dsimp only [a,b,pointExponent]
    simp only [Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,sub_zero]
    nlinarith only [hiBound.2,hjBound.1,hlower,hmpos]
  have hgap : (a-b).natAbs≤4*m^4+4*m^2 := by
    have h : |a-b|≤4*(m : ℤ)^4+4*(m : ℤ)^2 := by
      dsimp only [a,b,pointExponent]
      simp only [Nat.cast_one,Nat.cast_zero,mul_one,mul_zero,sub_zero]
      rw [abs_le]
      constructor <;> nlinarith only [hiBound.1,hiBound.2,hjBound.1,hjBound.2,
        hmul,hlower,hmpos]
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hm2 : 1≤m^2 := by nlinarith only [hm]
  have hm24 : m^2≤m^4 := by
    calc
      m^2=m^2*1 := by ring
      _≤m^2*m^2 := Nat.mul_le_mul_left _ hm2
      _=m^4 := by ring
  have hshort : (a-b).natAbs<orderOf (projectedUnit g m) := by
    have hord := long_global_order_bound hp hq hpq g hlong
    have hsum : 4*m^4+4*m^2<16*m^4 := by nlinarith only [hm2,hm24]
    exact hgap.trans_lt (hsum.trans hord)
  unfold shiftedCross
  rw [seedPoint_eq_zpow _ hmprime.pos hicop,seedPoint_eq_zpow _ hmprime.pos hjcop]
  exact zpow_short_gap_ne_zero (projectedUnit g m) a b hab hshort

/-- Original interval bound supplies the upper shift hypothesis. -/
theorem long_interval_shiftedCross_ne_zero {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 8≤t) (htupper : t≤seedLength m) (i j : Fin (m-1)) :
    shiftedCross (projectedUnit g m) m t i j≠0 :=
  long_shiftedCross_ne_zero hp hq hpq hm hmprime g hlong ht
    (htupper.trans (seedLength_bounds hm).2) i j

/-- A NONUNIT aggregate implies a proper individual difference factor,
even when different p/q hits make the aggregate itself globally zero. -/
theorem nonunit_crossNorm_proper_pair {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 8≤t) (htupper : t≤seedLength m)
    (hnorm : ¬IsUnit (crossNorm (projectedUnit g m) m t)) :
    ∃ i j : Fin (m-1), SemiprimeGroupSelection.ProperDivisor (p*q)
      ((p*q).gcd (shiftedCross (projectedUnit g m) m t i j).val) := by
  have hnon : ¬∀ i j : Fin (m-1),IsUnit
      (shiftedCross (projectedUnit g m) m t i j) := by
    intro h
    exact hnorm ((crossNorm_isUnit_iff _ _ _).mpr h)
  push Not at hnon
  obtain ⟨i,j,hij⟩ := hnon
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  exact ⟨i,j,SemiprimeTraceRows.proper_gcd_of_nonzero_nonunit
    (long_interval_shiftedCross_ne_zero hp hq hpq hm hmprime g hlong ht htupper i j) hij⟩

/-- Recovery contract for the actual acquired scalar, including its
saturated branch. This asserts an individual pair gcd, not that the
aggregate scalar gcd is proper. -/
theorem nonunit_shiftedTargetNorm_proper_pair {p q m t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (ht : 8≤t) (htupper : t≤seedLength m)
    (hnorm : ¬IsUnit (shiftedTargetNorm (projectedUnit g m) m t)) :
    ∃ i j : Fin (m-1), SemiprimeGroupSelection.ProperDivisor (p*q)
      ((p*q).gcd (shiftedCross (projectedUnit g m) m t i j).val) := by
  rw [shiftedTargetNorm_eq_crossNorm] at hnorm
  exact nonunit_crossNorm_proper_pair hp hq hpq hm hmprime g hlong ht htupper hnorm

/-- Unit values give literal linear-factor Bezout certificates. -/
theorem target_coprime_of_unit_evals
    {R : Type*} [CommRing R] (xs : List R) (F : R[X])
    (hvalues : ∀ x∈xs,IsUnit (F.eval x)) :
    IsCoprime (targetPolynomial xs) F := by
  induction xs with
  | nil => exact isCoprime_one_left
  | cons x xs ih =>
    change IsCoprime ((X-C x)*targetPolynomial xs) F
    apply IsCoprime.mul_left _ (ih (fun y hy => hvalues y (List.mem_cons_of_mem x hy)))
    have hc : IsUnit (C (F.eval x) : R[X]) := (hvalues x List.mem_cons_self).map C
    have hbase : IsCoprime (X-C x) (C (F.eval x)) := by
      simpa only [mul_one] using
        (isCoprime_mul_unit_left_right hc (X-C x) 1).mpr isCoprime_one_right
    have h := hbase.add_mul_left_right (F /ₘ (X-C x))
    rw [←modByMonic_X_sub_C_eq_C_eval,modByMonic_add_div] at h
    exact h

/-- Every scaled cross unit is retained, including repeated target labels. -/
theorem target_power_coprime_scaled
    {R : Type*} [CommRing R] (xs : List R) (k : ℕ) (c : R)
    (hcross : ∀ x∈xs,∀ y∈xs,IsUnit (c*x-y)) :
    IsCoprime ((targetPolynomial xs)^k)
      (((targetPolynomial xs)^k).comp (C c*X)) := by
  have heval : ∀ (ys : List R) (z : R), (∀ y∈ys,IsUnit (z-y)) →
      IsUnit ((targetPolynomial ys).eval z) := by
    intro ys
    induction ys with
    | nil =>
      intro z _
      simpa only [targetPolynomial,List.map_nil,List.prod_nil,eval_one] using
        (isUnit_one : IsUnit (1 : R))
    | cons y ys ih =>
      intro z hz
      change IsUnit (((X-C y)*targetPolynomial ys).eval z)
      rw [eval_mul,eval_sub,eval_X,eval_C]
      exact (hz y List.mem_cons_self).mul
        (ih z (fun w hw => hz w (List.mem_cons_of_mem y hw)))
  have h : IsCoprime (targetPolynomial xs)
      ((targetPolynomial xs).comp (C c*X)) := by
    apply target_coprime_of_unit_evals
    intro x hx
    rw [eval_comp,eval_mul,eval_C,eval_X]
    exact heval xs (c*x) (hcross x hx)
  simpa only [pow_comp] using h.pow_left.pow_right

/-- At the first degree overrun, the ACTUAL quotient is still too short to
vanish after scaling. The shift-coprime premise is the factor-free branch
of the shifted-target cross-difference test. This concerns the naive
truncation update, not an update acquiring its missing quotient. -/
theorem first_overrun_reduce_then_shift_fails
    {R : Type*} [CommRing R] [Nontrivial R] {P V : R[X]}
    (hP : P.Monic) (hV : V.Monic)
    (hlo : V.natDegree ≤ P.natDegree)
    (hhi : P.natDegree < 2*V.natDegree)
    (hcop : IsCoprime V P) (c v : Rˣ)
    (hshift : IsCoprime V (V.comp (C (c : R)*X))) :
    (P*C (v : R)*P.comp (C (c : R)*X)) %ₘ V ≠
      ((P %ₘ V)*C (v : R)*(P %ₘ V).comp (C (c : R)*X)) %ₘ V := by
  intro he
  let A := P %ₘ V
  let Q := P /ₘ V
  let B := C (c : R)*X
  have hsplit : P=A+V*Q := (modByMonic_add_div P V).symm
  have hdegree : V.degree ≤ P.degree := by
    rw [degree_eq_natDegree hV.ne_zero,degree_eq_natDegree hP.ne_zero]
    exact_mod_cast hlo
  have hQ : Q.Monic := by
    change (P /ₘ V).leadingCoeff=1
    rw [leadingCoeff_divByMonic_of_monic hV hdegree,hP.leadingCoeff]
  have hQsmall : Q.natDegree<V.natDegree := by
    change (P /ₘ V).natDegree<V.natDegree
    rw [natDegree_divByMonic P hV]
    omega
  have herror : P*C (v : R)*P.comp B-A*C (v : R)*A.comp B=
      P*C (v : R)*V.comp B*Q.comp B+V*(Q*C (v : R)*A.comp B) := by
    have hcomp : P.comp B=A.comp B+V.comp B*Q.comp B := by
      rw [hsplit,add_comp,mul_comp]
    rw [hcomp]
    rw [hsplit]
    ring
  have hdifference := dvd_sub_of_equal_remainders hV he
  change V∣P*C (v : R)*P.comp B-A*C (v : R)*A.comp B at hdifference
  rw [herror] at hdifference
  have herr : V∣P*C (v : R)*V.comp B*Q.comp B := by
    have h := hdifference.sub (dvd_mul_right V (Q*C (v : R)*A.comp B))
    simpa only [add_sub_cancel_right] using h
  have hv : IsUnit (C (v : R) : R[X]) := v.isUnit.map C
  have hcop' : IsCoprime V (P*C (v : R)*V.comp B) := by
    apply IsCoprime.mul_right
    · rw [mul_comm P,isCoprime_mul_unit_left_right hv]
      exact hcop
    · exact hshift
  have hdvd : V∣Q.comp B := hcop'.dvd_of_dvd_mul_left herr
  have hscaledDegree : (Q.comp B).natDegree<V.natDegree := by
    have hb : B.natDegree≤1 := by
      simpa only [pow_one] using natDegree_C_mul_X_pow_le (c : R) 1
    exact (natDegree_comp_le.trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left Q.natDegree hb)).trans_lt hQsmall
  have hscaledNonzero : Q.comp B≠0 := by
    intro hz
    have hc := congrArg (fun W : R[X] => W.coeff Q.natDegree) hz
    simp only [B,comp_C_mul_X_coeff,hQ.leadingCoeff,coeff_natDegree,
      coeff_zero,one_mul] at hc
    exact (c.isUnit.pow Q.natDegree).ne_zero hc
  have hself : (Q.comp B) %ₘ V=Q.comp B := by
    apply (modByMonic_eq_self_iff hV).mpr
    rw [degree_eq_natDegree hscaledNonzero,degree_eq_natDegree hV.ne_zero]
    exact_mod_cast hscaledDegree
  have hz := (modByMonic_eq_zero_iff_dvd hV).mpr hdvd
  rw [hself] at hz
  exact hscaledNonzero hz

/-- The same first-overrun statement for the literal geometric source.
A first dyadic length crossing deg V automatically satisfies the two
degree inequalities in this statement. -/
theorem actual_geometric_first_overrun_fails
    {R : Type*} [CommRing R] [Nontrivial R]
    (alpha : Rˣ) (xs : List R) (k t : ℕ)
    (hlo : k*xs.length≤t) (hhi : t<2*(k*xs.length))
    (hprefix : ∀ x∈xs,∀ r<t,IsUnit (x-(alpha : R)^r))
    (hshift : IsCoprime ((targetPolynomial xs)^k)
      (((targetPolynomial xs)^k).comp (C ((((alpha^t)⁻¹ : Rˣ) : R))*X))) :
    rowPolynomial (alpha : R) (t+t) %ₘ ((targetPolynomial xs)^k) ≠
      ((rowPolynomial (alpha : R) t %ₘ ((targetPolynomial xs)^k))*
        C (((alpha : R)^t)^t)*
        (rowPolynomial (alpha : R) t %ₘ ((targetPolynomial xs)^k)).comp
          (C ((((alpha^t)⁻¹ : Rˣ) : R))*X)) %ₘ ((targetPolynomial xs)^k) := by
  have hP : (rowPolynomial (alpha : R) t).Monic := by
    unfold rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
    exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hPd : (rowPolynomial (alpha : R) t).natDegree=t := by
    unfold rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
    rw [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_range]
  have hV := (targetPolynomial_monic xs).pow k
  have hVd : ((targetPolynomial xs)^k).natDegree=k*xs.length := by
    rw [(targetPolynomial_monic xs).natDegree_pow,targetPolynomial_natDegree,mul_comm]
  rw [rowPolynomial_doubling]
  exact first_overrun_reduce_then_shift_fails hP hV
    (by rwa [hPd,hVd]) (by rwa [hPd,hVd])
    ((prefix_coprime_target (alpha : R) xs t hprefix).pow_left)
    ((alpha^t)⁻¹) ((alpha^t)^t) hshift

/-- Literal prefix and shifted-cross units suffice for the actual source,
without any root-distinctness or field premise. -/
theorem actual_geometric_unit_cross_first_overrun_fails
    {R : Type*} [CommRing R] [Nontrivial R]
    (alpha : Rˣ) (xs : List R) (k t : ℕ)
    (hlo : k*xs.length≤t) (hhi : t<2*(k*xs.length))
    (hprefix : ∀ x∈xs,∀ r<t,IsUnit (x-(alpha : R)^r))
    (hcross : ∀ x∈xs,∀ y∈xs,
      IsUnit ((((alpha^t)⁻¹ : Rˣ) : R)*x-y)) :
    rowPolynomial (alpha : R) (t+t) %ₘ ((targetPolynomial xs)^k) ≠
      ((rowPolynomial (alpha : R) t %ₘ ((targetPolynomial xs)^k))*
        C (((alpha : R)^t)^t)*
        (rowPolynomial (alpha : R) t %ₘ ((targetPolynomial xs)^k)).comp
          (C ((((alpha^t)⁻¹ : Rˣ) : R))*X)) %ₘ ((targetPolynomial xs)^k) :=
  actual_geometric_first_overrun_fails alpha xs k t hlo hhi hprefix
    (target_power_coprime_scaled xs k _ hcross)



/-- Literal original-carrier failure at the first degree overrun, with
shifted-cross units supplied by the two retained local envelope exclusions.
The quotient is still short at this stage; an update acquiring it is outside
this statement. No scalar-gcd or first-jet inequality is asserted. -/
theorem original_no_envelope_first_overrun_fails {p q m k t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (ht : 8≤t)
    (hlo : k*(m-1)≤t) (hhi : t<2*(k*(m-1)))
    (hprefix : ∀ x∈seedTargets (projectedUnit g m) m,∀ r<t,
      IsUnit (x-((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^r))
    (hleft : ¬periodEnvelope m t (orderOf (leftUnit (projectedUnit g m))))
    (hright : ¬periodEnvelope m t (orderOf (rightUnit (projectedUnit g m)))) :
    let alpha := seedBase (projectedUnit g m) m
    let V := (targetPolynomial (seedTargets (projectedUnit g m) m))^k
    let A := rowPolynomial (alpha : ZMod (p*q)) t %ₘ V
    rowPolynomial (alpha : ZMod (p*q)) (t+t) %ₘ V ≠
      (A*C (((alpha : ZMod (p*q))^t)^t)*
        A.comp (C ((((alpha^t)⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q)))*X)) %ₘ V := by
  let : Fact (1<p*q) := ⟨by nlinarith [hp.one_lt,hq.one_lt]⟩
  have hcross := cross_units_of_no_local_periodEnvelope hp hq hm hmprime g ht hleft hright
  have hcross' : ∀ x∈seedTargets (projectedUnit g m) m,
      ∀ y∈seedTargets (projectedUnit g m) m,
      IsUnit (((((seedBase (projectedUnit g m) m)^t)⁻¹ : (ZMod (p*q))ˣ) :
        ZMod (p*q))*x-y) := by
    intro x hx y hy
    simp only [seedTargets,progressionSeeds,List.map_map,Function.comp_def] at hx hy
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
    have hu := hcross ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩
    simpa only [shiftedCross,seedPoint,normalizedPoint,one_mul,mul_one,zero_mul,pow_zero,
      inv_one,Units.val_one] using hu
  simpa only [seedTargets_length] using actual_geometric_unit_cross_first_overrun_fails
    (seedBase (projectedUnit g m) m) (seedTargets (projectedUnit g m) m) k t
    (by simpa only [seedTargets_length] using hlo)
    (by simpa only [seedTargets_length] using hhi) hprefix hcross'

/-- A residue progression cannot have zero carry slope unless its endpoints coincide. -/
theorem quadratic_ap_slope_ne_zero {F : Type*} [Field F]
    {s x y z : F} (hs : s≠0) (hxy : x≠y)
    (hquad : s*(x^2-2*x)+s*(y^2-2*y)=2*(s*(z^2-2*z))) :
    x+y-2*z≠0 := by
  intro hlin
  have hsq : s*(x-y)^2=0 := by
    linear_combination 2*hquad-s*(x+y+2*z-4)*hlin
  have hzero : (x-y)^2=0 := (mul_eq_zero.mp hsq).resolve_left hs
  exact hxy (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero))

/-- The original quadratic offset equation is an exact inverse-residue formula. -/
theorem quadratic_offset_formula {F : Type*} [Field F]
    {δ n j : F} (hj : j≠0) (h : δ*j^2=n*(1-2*j)) :
    δ=n*(j⁻¹^2-2*j⁻¹) := by
  apply mul_right_cancel₀ (pow_ne_zero 2 hj)
  calc
    δ*j^2=n*(1-2*j) := h
    _=(n*(j⁻¹^2-2*j⁻¹))*j^2 := by field_simp

/-- The integer coefficient multiplying the input carry in an actual offset AP is a unit. -/
theorem actual_ap_carry_coefficient_ne_zero {s m j k l u : ℕ}
    (hm : m.Prime) (hs : m.Coprime s)
    (hj : 1≤j) (hjm : j < m) (hk : 1≤k) (hkm : k < m)
    (hl : 1≤l) (hlm : l < m) (hjk : j≠k)
    (he : seedOffset (s+m*u) m j+seedOffset (s+m*u) m k=
      2*seedOffset (s+m*u) m l) :
    (((k : ℤ)*l+(j : ℤ)*l-2*(j : ℤ)*k : ℤ) : ZMod m)≠0 := by
  let : Fact m.Prime := ⟨hm⟩
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hkcop : k.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkm)).symm
  have hlcop : l.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hlm)).symm
  have hj0 : (j : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime j m).mpr hjcop).ne_zero
  have hk0 : (k : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime k m).mpr hkcop).ne_zero
  have hl0 : (l : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime l m).mpr hlcop).ne_zero
  have hs0 : (s : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime s m).mpr hs.symm).ne_zero
  have hN0 : ((s+m*u : ℕ) : ZMod m)≠0 := by
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero] using hs0
  have hxy : (j : ZMod m)⁻¹≠(k : ZMod m)⁻¹ := by
    intro h
    have heq : (j : ZMod m)=(k : ZMod m) := inv_injective h
    have hval := congrArg ZMod.val heq
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hjm,Nat.mod_eq_of_lt hkm] at hval
    exact hjk hval
  have hjform := quadratic_offset_formula hj0 (offset_square_residue (N:=s+m*u) hm.pos hjcop)
  have hkform := quadratic_offset_formula hk0 (offset_square_residue (N:=s+m*u) hm.pos hkcop)
  have hlform := quadratic_offset_formula hl0 (offset_square_residue (N:=s+m*u) hm.pos hlcop)
  have hecast := congrArg (fun z : ℤ => (z : ZMod m)) he
  simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] at hecast
  rw [hjform,hkform,hlform] at hecast
  have hslope := quadratic_ap_slope_ne_zero hN0 hxy hecast
  have hcoeff : (k : ZMod m)*l+(j : ZMod m)*l-2*(j : ZMod m)*k=
      (j : ZMod m)*k*l*((j : ZMod m)⁻¹+(k : ZMod m)⁻¹-2*(l : ZMod m)⁻¹) := by
    field_simp
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  rw [hcoeff]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj0 hk0) hl0) hslope

/-- An actual original-row offset AP can occur at only one bounded second carry. -/
theorem actual_ap_unique_carry {s m j k l u v : ℕ}
    (hm : m.Prime) (hs : m.Coprime s)
    (hj : 1≤j) (hjm : j < m) (hk : 1≤k) (hkm : k < m)
    (hl : 1≤l) (hlm : l < m) (hjk : j≠k) (hu : u < m) (hv : v < m)
    (he : seedOffset (s+m*u) m j+seedOffset (s+m*u) m k=
      2*seedOffset (s+m*u) m l)
    (he₀ : seedOffset (s+m*v) m j+seedOffset (s+m*v) m k=
      2*seedOffset (s+m*v) m l) : u=v := by
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hkcop : k.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkm)).symm
  have hlcop : l.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hlm)).symm
  let D : ℤ := ((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)
  let C : ℤ := (k : ℤ)*l+(j : ℤ)*l-2*(j : ℤ)*k
  have hJ := offset_difference_modEq hm.pos hjcop (carry_class (s:=s) (u:=u) (v:=v))
  have hK := offset_difference_modEq hm.pos hkcop (carry_class (s:=s) (u:=u) (v:=v))
  have hL := offset_difference_modEq hm.pos hlcop (carry_class (s:=s) (u:=u) (v:=v))
  have h := ((hJ.mul_left ((k : ℤ)*l)).add (hK.mul_left ((j : ℤ)*l))).sub
    (hL.mul_left (2*(j : ℤ)*k))
  have hmod : (0 : ℤ) ≡ -D*C [ZMOD (m : ℤ)^2] := by
    convert h using 1
    · linear_combination -(j : ℤ)*k*l*(he-he₀)
    · dsimp [D,C]
      ring
  have hprod : (m : ℤ)^2∣C*D := by
    convert hmod.symm.dvd using 1
    ring
  have hC := actual_ap_carry_coefficient_ne_zero hm hs hj hjm hk hkm hl hlm hjk he
  have hD := (integer_coprime_square hm C hC).dvd_of_dvd_mul_left hprod
  have hclass : ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    simpa only [D,neg_sub] using hD.neg_right
  exact equal_input_carry hm.pos hu hv hclass


/-- Monic first carrier: every leading-coefficient factor is exactly one.
The second polynomial is permitted to have smaller degree. -/
theorem finite_root_resultant_eq_eval_product
    {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (x : Fin n→R) (G : R[X]) (hG : G.natDegree≤n) :
    (∏ i : Fin n,(X-C (x i) : R[X])).resultant G n n=
      ∏ i : Fin n,G.eval (x i) := by
  have hd : (∏ i∈(Finset.univ : Finset (Fin n)),(X-C (x i) : R[X])).natDegree=n := by
    rw [natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin]
  have h := resultant_prod_left (Finset.univ : Finset (Fin n))
    (fun i => X-C (x i)) G n (by simp) hG
  rw [hd] at h
  simp only [natDegree_X_sub_C] at h
  simp_rw [resultant_X_sub_C_left G n _ hG] at h
  exact h

/-- Reindex a consecutive list product by its finite row type. -/
theorem list_range_prod_eq_fin_prod
    {R : Type*} [CommMonoid R] (f : ℕ→R) (n : ℕ) :
    ((List.range n).map f).prod=∏ i : Fin n,f i.val := by
  rw [Fin.prod_univ_eq_prod_range]
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ,Finset.prod_range_succ,ih]

/-- The literal source carrier retains all Fin-indexed row labels. -/
theorem original_targetPolynomial_eq_fin_roots
    {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ) :
    targetPolynomial (seedTargets g m)=
      ∏ i : Fin (m-1),(X-C (seedPoint g m 1 (i.val+1) 0) : (ZMod N)[X]) := by
  simp only [targetPolynomial,seedTargets,progressionSeeds,List.map_map,Function.comp_def]
  rw [list_range_prod_eq_fin_prod]
  simp only [seedPoint,normalizedPoint,zero_mul,pow_zero,inv_one,
    Units.val_one,one_mul]

/-- Exact original resultant identity, with no sign or omitted scaling
factor. The scaling coefficient of the second polynomial is included
inside its evaluations at the monic first carrier's roots. -/
theorem original_shifted_resultant_eq_norm
    {N : ℕ} [Nontrivial (ZMod N)] (g : (ZMod N)ˣ) (m t : ℕ) :
    let U := targetPolynomial (seedTargets g m)
    let c := ((((seedBase g m)^t)⁻¹ : (ZMod N)ˣ) : ZMod N)
    U.resultant (U.comp (C c*X)) (m-1) (m-1)=shiftedTargetNorm g m t := by
  let U := targetPolynomial (seedTargets g m)
  let c := ((((seedBase g m)^t)⁻¹ : (ZMod N)ˣ) : ZMod N)
  change U.resultant (U.comp (C c*X)) (m-1) (m-1)=shiftedTargetNorm g m t
  have hdegree : U.natDegree=m-1 := by
    dsimp only [U]
    rw [targetPolynomial_natDegree,seedTargets_length]
  have hlinear : (C c*X : (ZMod N)[X]).natDegree≤1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le c 1
  have hsecond : (U.comp (C c*X)).natDegree≤m-1 :=
    natDegree_comp_le.trans (by
      simpa only [hdegree,mul_one] using Nat.mul_le_mul_left U.natDegree hlinear)
  have hU : U=∏ i : Fin (m-1),(X-C (seedPoint g m 1 (i.val+1) 0) : (ZMod N)[X]) :=
    original_targetPolynomial_eq_fin_roots g m
  have hresultant := finite_root_resultant_eq_eval_product
    (fun i : Fin (m-1) => seedPoint g m 1 (i.val+1) 0) (U.comp (C c*X)) hsecond
  rw [←hU] at hresultant
  have hpoint (j : ℕ) : c*seedPoint g m 1 j 0=seedPoint g m 1 j t := by
    simp only [c,seedPoint,normalizedPoint,pow_zero,inv_one,
      Units.val_one,one_mul,mul_one]
  simp_rw [eval_comp,eval_mul,eval_C,eval_X,hpoint] at hresultant
  exact hresultant


end RiemannGaussian.SemiprimeShiftedNormAcquisitionObstruction
