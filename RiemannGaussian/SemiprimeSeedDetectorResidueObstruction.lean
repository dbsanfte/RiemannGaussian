/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSparseBlockPeriodObstruction

/-!
# Residue fibers of the actual original row-to-baby detector

As the cofactor varies, the actual denominator-one offset is affine modulo
m² within each cofactor class modulo m. Outside at most three original
rows its detector residue map is injective. The exceptional rows have
fibers of size at most m; their aggregate mass is at most 4m.

The investigation journal uses this arithmetic bound to count missed
detector hits on infinitely many actual long-base-2 inputs. The published
analytic density input and that infinitude argument are not Lean axioms
or formalized asymptotics in this module.
-/

namespace RiemannGaussian.SemiprimeSeedDetectorResidueObstruction

open scoped BigOperators
open Polynomial SemiprimeQuotientRows SemiprimeDenseRowCoverage
open SemiprimeDenseRowCarries SemiprimeGlobalPhaseCancellation
open SemiprimeSeedPointRigidity SemiprimeSharedIntervalJet SemiprimeIntervalJet
open SemiprimeSeedSumAcquisition SemiprimeLocalOrderRouting SemiprimeCentreFreeCover

/-- The exact affine coefficient of the cofactor in the lifted residue map. -/
noncomputable def cofactorCoefficient (p m j : ℕ) : ℤ := 1-publicInverse m j*p

/-- The quadratic controlling reduction of that same map modulo m. -/
noncomputable def detectorQuadratic (p j : ℕ) : ℤ := (j : ℤ)^2-2*(p : ℤ)*j+p

/-- Fibers use the actual original seed offset, including its centered carry. -/
noncomputable def detectorResidueFiber (p m j : ℕ) (t : ℤ) : Finset ℕ :=
  (Finset.range (m^2)).filter fun q =>
    ((q : ℤ)+seedOffset (p*q) m j)%(m : ℤ)^2=t%(m : ℤ)^2

/-- Exact lifting retains the carry and exposes its affine cofactor dependence. -/
theorem detector_affine_modEq {p q m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (q : ℤ)+seedOffset (p*q) m j ≡
      cofactorCoefficient p m j*q+
        (1-2*(j : ℤ)+publicInverse m j*(j : ℤ)^2)*representative (p*q) m j 1
      [ZMOD (m : ℤ)^2] := by
  have hr := denseRow_relation (N:=p*q) (j:=j) (t:=1) hm hj false
  change quotientRelation (p*q) m j (seedRow (p*q) m j).a
    (seedRow (p*q) m j).b (seedRow (p*q) m j).c (seedRow (p*q) m j).t at hr
  have ha : (seedRow (p*q) m j).a=(representative (p*q) m j 1 : ℤ) := rfl
  have ht : (seedRow (p*q) m j).t=(1 : ℤ) := rfl
  unfold quotientRelation at hr
  rw [ha,ht,mul_one] at hr
  obtain ⟨v,hv⟩ := (publicInverse_correct hj).symm.dvd
  apply Int.modEq_iff_dvd.mpr
  refine ⟨v*(seedRow (p*q) m j).b-publicInverse m j*(seedRow (p*q) m j).c,?_⟩
  unfold cofactorCoefficient seedOffset
  linear_combination publicInverse m j*hr+(m : ℤ)*(seedRow (p*q) m j).b*hv

/-- The actual map reduces to one monic quadratic multiplier modulo m. -/
theorem detector_quadratic_residue {p q m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (((q : ℤ)+seedOffset (p*q) m j : ℤ) : ZMod m)*(j : ZMod m)^2=
      (detectorQuadratic p j : ZMod m)*(q : ZMod m) := by
  have hs := offset_square_residue (N:=p*q) hm hj
  simp only [Nat.cast_mul] at hs
  simp only [detectorQuadratic,Int.cast_add,Int.cast_sub,Int.cast_mul,
    Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
  linear_combination hs

/-- The affine coefficient can vanish only at the single residue j=p. -/
theorem cofactorCoefficient_zero_iff {p m j : ℕ} (hj : j.Coprime m) :
    (cofactorCoefficient p m j : ZMod m)=0 ↔ (j : ZMod m)=(p : ZMod m) := by
  have hi := (ZMod.intCast_eq_intCast_iff _ _ m).mpr (publicInverse_correct hj)
  simp only [Int.cast_mul,Int.cast_natCast,Int.cast_one] at hi
  have hjunit : IsUnit (j : ZMod m) := (ZMod.isUnit_iff_coprime j m).mpr hj
  have he : (j : ZMod m)*(cofactorCoefficient p m j : ZMod m)=(j : ZMod m)-p := by
    simp only [cofactorCoefficient,Int.cast_sub,Int.cast_mul,Int.cast_one,Int.cast_natCast]
    linear_combination -(p : ZMod m)*hi
  constructor
  · intro h
    rw [h,mul_zero] at he
    exact (sub_eq_zero.mp he.symm)
  · intro h
    rw [h,sub_self] at he
    exact hjunit.mul_left_cancel (by simpa only [h,mul_zero] using he)

/-- Under p≠0,1 modulo m, the affine and quadratic exceptions are disjoint. -/
theorem detector_exceptions_disjoint {p m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hp : (p : ZMod m)≠0) (hp1 : (p : ZMod m)≠1)
    (hC : (cofactorCoefficient p m j : ZMod m)=0) :
    (detectorQuadratic p j : ZMod m)≠0 := by
  let : Fact m.Prime := ⟨hm⟩
  have he := (cofactorCoefficient_zero_iff hj).mp hC
  have hq : (detectorQuadratic p j : ZMod m)=(p : ZMod m)*(1-p) := by
    simp only [detectorQuadratic,Int.cast_add,Int.cast_sub,Int.cast_mul,
      Int.cast_pow,Int.cast_natCast,Int.cast_ofNat,he]
    ring
  rw [hq]
  exact mul_ne_zero hp (sub_ne_zero.mpr (Ne.symm hp1))

/-- Nonvanishing modulo the prime m permits cancellation modulo m². -/
theorem cofactorCoefficient_coprime_square {p m j : ℕ} (hm : m.Prime)
    (hC : (cofactorCoefficient p m j : ZMod m)≠0) :
    IsCoprime ((m : ℤ)^2) (cofactorCoefficient p m j) := by
  apply IsCoprime.pow_left
  apply Int.isCoprime_iff_nat_coprime.mpr
  rw [Int.natAbs_natCast]
  apply hm.coprime_iff_not_dvd.mpr
  intro hd
  exact hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (Int.natCast_dvd.mpr hd))

/-- A nonzero quadratic multiplier forces equality of the cofactor classes. -/
theorem detector_fiber_modEq {p q q₀ m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hP : (detectorQuadratic p j : ZMod m)≠0)
    (he : (q : ℤ)+seedOffset (p*q) m j ≡
      (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2]) :
    (q : ℤ) ≡ (q₀ : ℤ) [ZMOD m] := by
  let : Fact m.Prime := ⟨hm⟩
  have hsmall := he.of_dvd (dvd_pow_self (m : ℤ) (by decide : 2≠0))
  have hefield := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hsmall
  have hq := detector_quadratic_residue (p:=p) (q:=q) hm.pos hj
  have hq₀ := detector_quadratic_residue (p:=p) (q:=q₀) hm.pos hj
  rw [hefield] at hq
  have hcancel : (detectorQuadratic p j : ZMod m)*(q : ZMod m)=
      (detectorQuadratic p j : ZMod m)*(q₀ : ZMod m) := hq.symm.trans hq₀
  exact (ZMod.intCast_eq_intCast_iff _ _ m).mp
    (by simpa only [Int.cast_natCast] using mul_left_cancel₀ hP hcancel)

/-- Canonical row numerators agree for congruent cofactors. -/
theorem representative_eq_of_cofactor_modEq {p q q₀ m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (he : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD m]) :
    representative (p*q) m j 1=representative (p*q₀) m j 1 := by
  let : NeZero m := ⟨hm.ne'⟩
  have hq : (q : ZMod m)=(q₀ : ZMod m) := by
    simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ m).mpr he
  have hs := slope_square_residue (N:=p*q) hm hj
  have hs₀ := slope_square_residue (N:=p*q₀) hm hj
  simp only [Nat.cast_mul,hq] at hs
  simp only [Nat.cast_mul] at hs₀
  have hu := ((ZMod.isUnit_iff_coprime j m).mpr hj).pow 2
  have ha := hu.mul_right_cancel (hs.trans hs₀.symm)
  have hv := congrArg ZMod.val ha
  have hb : representative (p*q) m j 1<m := Nat.mod_lt _ hm
  have hb₀ : representative (p*q₀) m j 1<m := Nat.mod_lt _ hm
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hb₀] using hv

/-- Within one cofactor class, a nonzero affine coefficient gives full injectivity. -/
theorem detector_same_class_modEq_square {p q q₀ m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hC : (cofactorCoefficient p m j : ZMod m)≠0)
    (hclass : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD m])
    (he : (q : ℤ)+seedOffset (p*q) m j ≡
      (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2]) :
    (q : ℤ) ≡ (q₀ : ℤ) [ZMOD (m : ℤ)^2] := by
  have ha := representative_eq_of_cofactor_modEq (p:=p) hm.pos hj hclass
  have hfirst := detector_affine_modEq (p:=p) (q:=q) hm.pos hj
  have hsecond := detector_affine_modEq (p:=p) (q:=q₀) hm.pos hj
  rw [ha] at hfirst
  have hc := (hfirst.symm.trans (he.trans hsecond)).sub (Int.ModEq.refl
    ((1-2*(j : ℤ)+publicInverse m j*(j : ℤ)^2)*representative (p*q₀) m j 1))
  simp only [add_sub_cancel_right] at hc
  apply Int.modEq_iff_dvd.mpr
  apply (cofactorCoefficient_coprime_square hm hC).dvd_of_dvd_mul_left
  convert hc.dvd using 1
  ring

/-- The actual detector map is periodic modulo m², including its centered carry. -/
theorem detector_periodic_modEq {p q q₀ m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (he : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD (m : ℤ)^2]) :
    (q : ℤ)+seedOffset (p*q) m j ≡
      (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2] := by
  have ha := representative_eq_of_cofactor_modEq (p:=p) hm hj
    (he.of_dvd (dvd_pow_self (m : ℤ) (by decide : 2≠0)))
  have hfirst := detector_affine_modEq (p:=p) (q:=q) hm hj
  have hsecond := detector_affine_modEq (p:=p) (q:=q₀) hm hj
  rw [ha] at hfirst
  exact hfirst.trans (((he.mul_left (cofactorCoefficient p m j)).add
    (Int.ModEq.refl _)).trans hsecond.symm)

/-- A good row has at most one cofactor in each actual detector residue fiber. -/
theorem detectorResidueFiber_card_le_one {p m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hC : (cofactorCoefficient p m j : ZMod m)≠0)
    (hP : (detectorQuadratic p j : ZMod m)≠0) (t : ℤ) :
    (detectorResidueFiber p m j t).card≤1 := by
  apply Finset.card_le_one.mpr
  intro q hq q₀ hq₀
  have he : (q : ℤ)+seedOffset (p*q) m j ≡
      (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2] :=
    (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq₀).2.symm
  have hmod := detector_same_class_modEq_square hm hj hC (detector_fiber_modEq hm hj hP he) he
  have hn : q ≡ q₀ [MOD m^2] := by
    simpa only [←Nat.cast_pow,Int.natCast_modEq_iff] using hmod
  have hqb := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
  have hq₀b := Finset.mem_range.mp (Finset.mem_filter.mp hq₀).1
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt hqb,Nat.mod_eq_of_lt hq₀b] using hn

/-- Every row fiber is at most m; the two possible exceptions cannot coincide. -/
theorem detectorResidueFiber_card_le_m {p m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hp : (p : ZMod m)≠0) (hp1 : (p : ZMod m)≠1)
    (t : ℤ) : (detectorResidueFiber p m j t).card≤m := by
  have hf {q q₀ : ℕ} (hq : q∈detectorResidueFiber p m j t)
      (hq₀ : q₀∈detectorResidueFiber p m j t) :
      (q : ℤ)+seedOffset (p*q) m j ≡
        (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2] :=
    (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq₀).2.symm
  have hb {q : ℕ} (hq : q∈detectorResidueFiber p m j t) : q<m^2 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hq).1
  by_cases hP : (detectorQuadratic p j : ZMod m)=0
  · have hC : (cofactorCoefficient p m j : ZMod m)≠0 := by
      intro hC
      exact detector_exceptions_disjoint hm hj hp hp1 hC hP
    have hcard := Finset.card_le_card_of_injOn (fun q : ℕ => q%m)
      (s:=detectorResidueFiber p m j t) (t:=Finset.range m)
      (fun q _ => Finset.mem_range.mpr (Nat.mod_lt q hm.pos)) (by
        intro q hq q₀ hq₀ he
        have hclass : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD m] := by
          simpa only [Int.ModEq,Int.natCast_mod] using congrArg (fun n : ℕ => (n : ℤ)) he
        have hn : q ≡ q₀ [MOD m^2] := by
          simpa only [←Nat.cast_pow,Int.natCast_modEq_iff] using
            detector_same_class_modEq_square hm hj hC hclass (hf hq hq₀)
        simpa only [Nat.ModEq,Nat.mod_eq_of_lt (hb hq),Nat.mod_eq_of_lt (hb hq₀)] using hn)
    simpa only [Finset.card_range] using hcard
  · have hcard := Finset.card_le_card_of_injOn (fun q : ℕ => q/m)
      (s:=detectorResidueFiber p m j t) (t:=Finset.range m) (by
        intro q hq
        apply Finset.mem_range.mpr
        apply (Nat.div_lt_iff_lt_mul hm.pos).mpr
        simpa only [pow_two] using hb hq) (by
        intro q hq q₀ hq₀ he
        have hn : q ≡ q₀ [MOD m] := by
          simpa only [Int.natCast_modEq_iff] using detector_fiber_modEq hm hj hP (hf hq hq₀)
        have hemod : q%m=q₀%m := hn
        have hqeq := Nat.mod_add_div q m
        have hq₀eq := Nat.mod_add_div q₀ m
        change q/m=q₀/m at he
        rw [hemod,he] at hqeq
        omega)
    simpa only [Finset.card_range] using hcard

/-- At most three original rows fail the injective residue-map conditions. -/
theorem detector_exception_rows_card {p m : ℕ} (hm : m.Prime) :
    ((Finset.range (m-1)).filter fun r =>
      (cofactorCoefficient p m (r+1) : ZMod m)=0 ∨
      (detectorQuadratic p (r+1) : ZMod m)=0).card≤3 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let P : (ZMod m)[X] := (X-C (p : ZMod m))*
    (X^2-C (2*(p : ZMod m))*X+C (p : ZMod m))
  have hP : P≠0 := by
    intro hz
    have hc := congrArg (fun Q : (ZMod m)[X] => Q.coeff 3) hz
    norm_num [P,coeff_mul,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero,coeff_X] at hc
  have hdegree : P.natDegree≤3 := by
    dsimp only [P]
    compute_degree!
  let E := (Finset.range (m-1)).filter fun r =>
    (cofactorCoefficient p m (r+1) : ZMod m)=0 ∨
    (detectorQuadratic p (r+1) : ZMod m)=0
  have hb {r : ℕ} (hr : r∈E) : r+1<m := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    omega
  have hmap : Set.MapsTo (fun r : ℕ => ((r+1 : ℕ) : ZMod m)) E P.roots.toFinset := by
    intro r hr
    have hj : (r+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (hb hr))).symm
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hP).mpr
    change P.eval ((r+1 : ℕ) : ZMod m)=0
    simp only [P,eval_mul,eval_sub,eval_add,eval_X,eval_C,eval_pow]
    rcases (Finset.mem_filter.mp hr).2 with hC|hQ
    · rw [(cofactorCoefficient_zero_iff hj).mp hC,sub_self,zero_mul]
    · have hz : ((r+1 : ℕ) : ZMod m)^2-2*(p : ZMod m)*(r+1 : ℕ)+p=0 := by
        simpa only [detectorQuadratic,Int.cast_add,Int.cast_sub,Int.cast_mul,
          Int.cast_pow,Int.cast_natCast,Int.cast_ofNat] using hQ
      rw [hz,mul_zero]
  have hinj : (E : Set ℕ).InjOn (fun r : ℕ => ((r+1 : ℕ) : ZMod m)) := by
    intro r hr s hs he
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb hr),Nat.mod_eq_of_lt (hb hs)] at hv
    omega
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
    ((Multiset.toFinset_card_le P.roots).trans ((Polynomial.card_roots' P).trans hdegree))

/-- The total fiber mass is linear, even with a different target at each row. -/
theorem detector_whole_family_fiber_bound {p m : ℕ} (hm : m.Prime)
    (hp : (p : ZMod m)≠0) (hp1 : (p : ZMod m)≠1) (t : ℕ→ℤ) :
    (∑ r∈Finset.range (m-1), (detectorResidueFiber p m (r+1) (t r)).card)≤4*m := by
  classical
  let bad := fun r : ℕ => (cofactorCoefficient p m (r+1) : ZMod m)=0 ∨
    (detectorQuadratic p (r+1) : ZMod m)=0
  let E := (Finset.range (m-1)).filter bad
  have hE : E.card≤3 := detector_exception_rows_card hm
  have hle : (∑ r∈Finset.range (m-1), (detectorResidueFiber p m (r+1) (t r)).card)≤
      ∑ r∈Finset.range (m-1), (1+if bad r then m else 0) := by
    apply Finset.sum_le_sum
    intro r hr
    have hrm : r+1<m := by have hh := Finset.mem_range.mp hr; omega
    have hj : (r+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrm)).symm
    by_cases hbad : bad r
    · simpa only [ite_eq_left hbad] using
        (detectorResidueFiber_card_le_m hm hj hp hp1 (t r)).trans (Nat.le_add_left m 1)
    · have hgood := not_or.mp hbad
      simpa only [ite_eq_right hbad,add_zero] using
        detectorResidueFiber_card_le_one hm hj hgood.1 hgood.2 (t r)
  have hsum : (∑ r∈Finset.range (m-1), (1+if bad r then m else 0))=
      (m-1)+E.card*m := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one,Finset.card_range]
    rw [←Finset.sum_filter]
    simp only [E,Finset.sum_const,smul_eq_mul]
  rw [hsum] at hle
  have hmul := Nat.mul_le_mul_right m hE
  omega

/-- Equality of an original normalized row target and baby is an order residual. -/
theorem detector_local_hit_iff {N m w j k u : ℕ} {R : Type*} [CommRing R]
    (f : ZMod N→+*R) (g : (ZMod N)ˣ) (hm : 0<m) (hj : j.Coprime m) :
    f (seedPoint g m w j k)=f (((seedBase g m)^u : (ZMod N)ˣ) : ZMod N) ↔
      (orderOf (Units.map f.toMonoidHom g) : ℤ)∣
        (N : ℤ)+seedOffset N m j-(m : ℤ)^2*((w : ℤ)*k+u) := by
  have hb : (((seedBase g m)^u : (ZMod N)ˣ) : ZMod N)=
      ((g^((m : ℤ)^2*u) : (ZMod N)ˣ) : ZMod N) := by
    simp only [seedBase,←zpow_natCast,←zpow_mul,Nat.cast_pow]
  rw [seedPoint_eq_zpow g hm hj,hb]
  have he : f ((g^pointExponent N m w j k : (ZMod N)ˣ) : ZMod N)=
      f ((g^((m : ℤ)^2*u) : (ZMod N)ˣ) : ZMod N) ↔
      Units.map f.toMonoidHom (g^pointExponent N m w j k)=
        Units.map f.toMonoidHom (g^((m : ℤ)^2*u)) := by
    exact ⟨fun h => Units.ext h,fun h => congrArg Units.val h⟩
  rw [he,map_zpow,map_zpow,←orderOf_dvd_sub_iff_zpow_eq_zpow]
  have hex : pointExponent N m w j k-(m : ℤ)^2*u=
      (N : ℤ)+seedOffset N m j-(m : ℤ)^2*((w : ℤ)*k+u) := by
    unfold pointExponent
    ring
  rw [hex]

/-- In the hidden p-field, the exact detector residual uses the cofactor q. -/
theorem detector_prime_hit_iff {p q m w j k u : ℕ}
    (f : ZMod (p*q)→+*ZMod p) (g : (ZMod (p*q))ˣ)
    (hm : 0<m) (hj : j.Coprime m)
    (hperiod : (orderOf (Units.map f.toMonoidHom g) : ℤ)∣(p : ℤ)-1) :
    f (seedPoint g m w j k)=f (((seedBase g m)^u : (ZMod (p*q))ˣ) : ZMod (p*q)) ↔
      (orderOf (Units.map f.toMonoidHom g) : ℤ)∣
        (q : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((w : ℤ)*k+u) := by
  rw [detector_local_hit_iff f g hm hj]
  have hex : ((p*q : ℕ) : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((w : ℤ)*k+u)=
      ((q : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((w : ℤ)*k+u))+((p : ℤ)-1)*q := by
    simp only [Nat.cast_mul]
    ring
  rw [hex]
  exact dvd_add_left (hperiod.mul_right (q : ℤ))

/-- Absent both local residual divisibilities, every tested row-to-baby difference is a unit. -/
theorem detector_sample_differences_units {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : m.Prime) (g : (ZMod (p*q))ˣ)
    (hgapP : ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      ¬(orderOf (Units.map (ZMod.castHom (dvd_mul_right p q) (ZMod p)).toMonoidHom g) : ℤ)∣
        (p*q : ℕ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u))
    (hgapQ : ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      ¬(orderOf (Units.map (ZMod.castHom (dvd_mul_left q p) (ZMod q)).toMonoidHom g) : ℤ)∣
        (p*q : ℕ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u)) :
    ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      IsUnit (seedPoint g m (4*m) j k-(((seedBase g m)^u : (ZMod (p*q))ˣ) : ZMod (p*q))) := by
  intro j hj hjm k hk u hu
  have hjcop : j.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  apply isUnit_of_prime_reductions hp hq
  · rw [map_sub]
    intro he
    apply hgapP j hj hjm k hk u hu
    have hh := (detector_local_hit_iff _ g hm.pos hjcop).mp (sub_eq_zero.mp he)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  · rw [map_sub]
    intro he
    apply hgapQ j hj hjm k hk u hu
    have hh := (detector_local_hit_iff _ g hm.pos hjcop).mp (sub_eq_zero.mp he)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh

/-- Actual prime-field cofactor gaps give the same unit conclusion without an order oracle. -/
theorem detector_cofactor_gaps_units {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : m.Prime) (g : (ZMod (p*q))ˣ)
    (hgapP : ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      ¬(orderOf (leftUnit g) : ℤ)∣
        (q : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u))
    (hgapQ : ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      ¬(orderOf (rightUnit g) : ℤ)∣
        (p : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u)) :
    ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      IsUnit (seedPoint g m (4*m) j k-(((seedBase g m)^u : (ZMod (p*q))ˣ) : ZMod (p*q))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply detector_sample_differences_units hp hq hm g
  · intro j hj hjm k hk u hu hd
    have ho : (orderOf (leftUnit g) : ℤ)∣(p : ℤ)-1 := by
      have hcast : ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 := Nat.cast_sub hp.one_lt.le
      rw [←hcast]
      exact_mod_cast ZMod.orderOf_units_dvd_card_sub_one (leftUnit g)
    have hsub := hd.sub (ho.mul_right (q : ℤ))
    have he : ((p*q : ℕ) : ℤ)+seedOffset (p*q) m j-
        (m : ℤ)^2*((4*m : ℕ)*k+u)-((p : ℤ)-1)*q=
        (q : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u) := by
      simp only [Nat.cast_mul]
      ring
    rw [he] at hsub
    exact hgapP j hj hjm k hk u hu hsub
  · intro j hj hjm k hk u hu hd
    have ho : (orderOf (rightUnit g) : ℤ)∣(q : ℤ)-1 := by
      have hcast : ((q-1 : ℕ) : ℤ)=(q : ℤ)-1 := Nat.cast_sub hq.one_lt.le
      rw [←hcast]
      exact_mod_cast ZMod.orderOf_units_dvd_card_sub_one (rightUnit g)
    have hsub := hd.sub (ho.mul_right (p : ℤ))
    have he : ((p*q : ℕ) : ℤ)+seedOffset (p*q) m j-
        (m : ℤ)^2*((4*m : ℕ)*k+u)-((q : ℤ)-1)*p=
        (p : ℤ)+seedOffset (p*q) m j-(m : ℤ)^2*((4*m : ℕ)*k+u) := by
      simp only [Nat.cast_mul]
      ring
    rw [he] at hsub
    exact hgapQ j hj hjm k hk u hu hsub

/-- Every sampled normalized block product has gcd one; pooling cannot create a factor. -/
theorem detector_sample_product_gcd_one {p q m : ℕ} {blocks : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (g : (ZMod (p*q))ˣ)
    (hunit : ∀ j,1≤j → j<m → ∀ k∈blocks,∀ u<4*m,
      IsUnit (seedPoint g m (4*m) j k-(((seedBase g m)^u : (ZMod (p*q))ˣ) : ZMod (p*q)))) :
    (p*q).gcd
      (∏ r∈Finset.range (m-1), ∏ k∈blocks,
        blockProduct ((seedBase g m : (ZMod (p*q))ˣ) : ZMod (p*q))
          (seedPoint g m (4*m) (r+1) k) 0 (4*m)).val=1 := by
  let : NeZero (p*q) := ⟨(Nat.mul_pos hp.pos hq.pos).ne'⟩
  apply (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr
  apply IsUnit.prod_iff.mpr
  intro r hr
  apply IsUnit.prod_iff.mpr
  intro k hk
  unfold blockProduct
  apply IsUnit.prod_iff.mpr
  intro u hu
  have hrm : r+1<m := by have hh := Finset.mem_range.mp hr; omega
  simpa only [blockFactor,zero_add,Units.val_pow_eq_pow_val] using
    hunit (r+1) (by omega) hrm k hk u (Finset.mem_range.mp hu)

end RiemannGaussian.SemiprimeSeedDetectorResidueObstruction
