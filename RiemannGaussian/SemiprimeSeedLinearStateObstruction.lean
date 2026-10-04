/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAdaptiveSeedAcquisitionObstruction
import RiemannGaussian.SemiprimeQAggregate
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Specialized geometric shifts require a large fixed linear state

The contract concerns only the actual original interval polynomial, at an
original unit target. It does not demand an operator on all polynomials,
an explicit factory source or a canonical quotient remainder. A fixed
linear transition with linear readout still needs at least the interval
length plus one state coordinates. The original dyadic scale preserves
long local order and every original coefficient is a unit. Consequently
every monic constant-coefficient annihilator has quadratic degree.

Direct whole-family scalar aggregation has a second obstruction: a
fixed linear state shorter than the original interval forces its
anchored orbit and original aggregate to be zero, hence completely
saturated. Nonlinear or changing transitions, moving moduli and extra
saturation-recovery information are not ruled out by these contracts.
-/

namespace RiemannGaussian.SemiprimeSeedLinearStateObstruction

open scoped BigOperators
open Polynomial SemiprimeSeedGeometricRecurrence
open SemiprimeSeedShiftClosureObstruction SemiprimeSeedSumAcquisition
open SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeGeometricRows SemiprimeSeedHermiteQuotient SemiprimeIntervalJet
open SemiprimeAdaptiveSeedAcquisitionObstruction
open SemiprimeDenseRowCarries SemiprimeWrapIndexRecovery
open SemiprimeGlobalPhaseCancellation

/-- Proof-side polynomial whose evaluations are the scalar shift
annihilator applied to one PARTICULAR supplied polynomial. -/
noncomputable def shiftAction {R : Type*} [CommRing R]
    (c : R) (A P : R[X]) : R[X] :=
  ∑ i∈Finset.range (A.natDegree+1),C (A.coeff i)*P.comp (C (c^i)*X)

/-- The action acts diagonally on the particular polynomial's original
coefficients. No shift closure of any quotient ring is assumed. -/
theorem shiftAction_coeff {R : Type*} [CommRing R]
    (c : R) (A P : R[X]) (k : ℕ) :
    (shiftAction c A P).coeff k=P.coeff k*A.eval (c^k) := by
  classical
  simp only [shiftAction,finsetSum_coeff,coeff_C_mul,comp_C_mul_X_coeff]
  rw [eval_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←pow_mul, Nat.mul_comm i k,pow_mul]
  ring

/-- The annihilator action does not increase the actual degree. -/
theorem shiftAction_natDegree {R : Type*} [CommRing R]
    (c : R) (A P : R[X]) : (shiftAction c A P).natDegree≤P.natDegree := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i _
  have hlinear : (C (c^i)*X : R[X]).natDegree≤1 := by
    simpa only [pow_one] using natDegree_C_mul_X_pow_le (c^i) 1
  exact natDegree_mul_le.trans (by
    rw [natDegree_C,zero_add]
    exact natDegree_comp_le.trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left P.natDegree hlinear))

/-- Evaluation is exactly the original constant-coefficient recurrence
on scaled target values, including zero or nonunit evaluated products. -/
theorem shiftAction_eval {R : Type*} [CommRing R]
    (c x : R) (A P : R[X]) (r : ℕ) :
    (shiftAction c A P).eval (c^r*x)=
      ∑ i∈Finset.range (A.natDegree+1),A.coeff i*P.eval (c^(r+i)*x) := by
  classical
  simp only [shiftAction,eval_finsetSum,eval_mul,eval_C,eval_comp,eval_X]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [pow_add]
  ring

/-- A recurrence for this one dense polynomial already needs degree
at least its degree plus one. Only the first degree+1 scalar recurrence
equations are used; no universal-polynomial operator is imposed. -/
theorem specialized_annihilator_degree {R : Type*} [CommRing R] [IsDomain R]
    (c x : Rˣ) (A P : R[X]) (hA : A≠0)
    (hcoeff : ∀ k≤P.natDegree,P.coeff k≠0)
    (horder : P.natDegree<orderOf (c : R))
    (hrec : ∀ r≤P.natDegree,
      ∑ i∈Finset.range (A.natDegree+1),A.coeff i*
        P.eval ((c : R)^(r+i)*(x : R))=0) :
    P.natDegree+1≤A.natDegree := by
  classical
  have hinj : Function.Injective (fun i : Fin (P.natDegree+1) =>
      (c : R)^i.val*(x : R)) := by
    intro i j he
    have hi := i.is_lt
    have hj := j.is_lt
    have hp := x.isUnit.mul_right_cancel he
    apply Fin.ext
    have hiorder : i.val<orderOf (c : R) := by omega
    have hjorder : j.val<orderOf (c : R) := by omega
    exact pow_injOn_Iio_orderOf hiorder hjorder hp
  have hz : shiftAction (c : R) A P=0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
      (fun i => (shiftAction_eval (c : R) (x : R) A P i.val).trans (hrec i.val (by omega)))
    simpa only [Fintype.card_fin] using
      (Nat.lt_succ_of_le (shiftAction_natDegree (c : R) A P))
  have hroots (i : Fin (P.natDegree+1)) : A.eval ((c : R)^i.val)=0 := by
    have he := congrArg (fun Q : R[X] => Q.coeff i.val) hz
    rw [shiftAction_coeff,coeff_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (hcoeff i.val (by omega))
  have hcinj : Function.Injective (fun i : Fin (P.natDegree+1) => (c : R)^i.val) := by
    intro i j he
    have hi := i.is_lt
    have hj := j.is_lt
    apply Fin.ext
    have hiorder : i.val<orderOf (c : R) := by omega
    have hjorder : j.val<orderOf (c : R) := by omega
    exact pow_injOn_Iio_orderOf hiorder hjorder he
  by_contra hn
  apply hA
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero A hcinj hroots
  simpa only [Fintype.card_fin] using (show A.natDegree<P.natDegree+1 by omega)

/-- Every fixed finite free linear transition supplies its own monic
annihilator. This includes arbitrary coupled channels and arbitrary
linear readout, without a diagonal or companion-matrix hypothesis. -/
theorem linear_state_charpoly_recurrence {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (T : Module.End R M) (v : M) (readout : M→ₗ[R]R) (r : ℕ) :
    ∑ i∈Finset.range (T.charpoly.natDegree+1),T.charpoly.coeff i*
      readout ((T^(r+i)) v)=0 := by
  classical
  have he := congrArg (fun f : Module.End R M => readout ((T^r*f) v))
    T.aeval_self_charpoly
  rw [aeval_eq_sum_range] at he
  simpa only [Finset.mul_sum,mul_smul_comm,←pow_add,LinearMap.sum_apply,
    LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul,mul_zero,
    LinearMap.zero_apply,map_zero] using he

/-- The ACTUAL original factory at ANY unit target has no recurrence
below its length plus one, throughout the original padded range. Only
this particular family's scalar equations are required. -/
theorem original_factory_annihilator_degree {p q m w : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    (hw : w≤seedLength m) (x : (ZMod (p*q))ˣ)
    (A : (ZMod (p*q))[X]) (hA : A.Monic)
    (hrec : ∀ r≤w,
      ∑ i∈Finset.range (A.natDegree+1),A.coeff i*
        (rowPolynomial ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w).eval
          (((((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) :
            ZMod (p*q))^(r+i))*(x : ZMod (p*q)))=0) :
    w+1≤A.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  let f := ZMod.castHom (dvd_mul_right p q) (ZMod p)
  let H := rowPolynomial ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w
  let c := (seedBase (projectedUnit g m) m)^(2^t)
  let cp := Units.map f.toMonoidHom c
  let xp := Units.map f.toMonoidHom x
  have hH : H.Monic := by
    unfold H rowPolynomial SemiprimeCartesianCompletion.rootPolynomial
    exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hHoriginal : H.natDegree=w := by
    simpa only [H,rowPolynomial,SemiprimeCartesianCompletion.rootPolynomial,Finset.card_range]
      using natDegree_finsetProd_X_sub_C_eq_card (Finset.range w)
        (fun i => (((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^i))
  have hHdegree : (H.map f).natDegree=w := (hH.natDegree_map f).trans hHoriginal
  have hAdegree : (A.map f).natDegree=A.natDegree := hA.natDegree_map f
  have horder : (H.map f).natDegree<orderOf (cp : ZMod p) := by
    rw [hHdegree,orderOf_units]
    change w<orderOf (leftUnit ((seedBase (projectedUnit g m) m)^(2^t)))
    rw [long_dyadic_left_scale_order hm g hlong t]
    have hwidth := hw.trans (seedLength_bounds hm).2
    nlinarith only [hwidth,hlong.2.2.2.1.1]
  have hcoeff : ∀ k≤(H.map f).natDegree,(H.map f).coeff k≠0 := by
    intro k hk
    rw [coeff_map]
    exact ((original_leaf_coefficients_unit hp hq hm g hlong hw k
      (by rwa [hHdegree] at hk)).map f).ne_zero
  have hfieldrec : ∀ r≤(H.map f).natDegree,
      ∑ i∈Finset.range ((A.map f).natDegree+1),(A.map f).coeff i*
        (H.map f).eval ((cp : ZMod p)^(r+i)*(xp : ZMod p))=0 := by
    intro r hr
    rw [hAdegree]
    have he := congrArg f (hrec r (by rwa [hHdegree] at hr))
    rw [show (cp : ZMod p)=f (c : ZMod (p*q)) from rfl,
      show (xp : ZMod p)=f (x : ZMod (p*q)) from rfl]
    simp only [coeff_map,←map_pow,←map_mul,eval_map_apply]
    simpa only [map_sum,map_mul,map_zero] using he
  have hdegree := specialized_annihilator_degree cp xp (A.map f) (H.map f)
    (hA.map f).ne_zero hcoeff horder hfieldrec
  rwa [hHdegree,hAdegree] at hdegree

/-- A fixed linear state specialized to an actual original factory has
at least width+1 coordinates. Its coordinates need not be coefficients,
and its transition may mix all coupled channels arbitrarily. -/
theorem original_factory_linear_state_dimension {p q m w d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    (hw : w≤seedLength m) (x : (ZMod (p*q))ˣ)
    (T : Module.End (ZMod (p*q)) (Fin d→ZMod (p*q)))
    (v : Fin d→ZMod (p*q)) (readout : (Fin d→ZMod (p*q))→ₗ[ZMod (p*q)]ZMod (p*q))
    (hcorrect : ∀ r : ℕ, r≤w+d → readout ((T^r) v)=
      (rowPolynomial ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w).eval
        (((((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) :
          ZMod (p*q))^r)*(x : ZMod (p*q)))) :
    w+1≤d := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  have hdegree : T.charpoly.natDegree=d := by
    simp only [T.charpoly_natDegree,Module.finrank_fin_fun]
  have hrec r (hr : r≤w) :
      ∑ i∈Finset.range (T.charpoly.natDegree+1),T.charpoly.coeff i*
        (rowPolynomial ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q)) w).eval
          (((((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) :
            ZMod (p*q))^(r+i))*(x : ZMod (p*q)))=0 := by
    calc
      _ = ∑ i∈Finset.range (T.charpoly.natDegree+1),T.charpoly.coeff i*
          readout ((T^(r+i)) v) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        have hib := Finset.mem_range.mp hi
        exact (hcorrect (r+i) (by rw [hdegree] at hib; omega)).symm
      _ = 0 := linear_state_charpoly_recurrence T v readout r
  have hd := original_factory_annihilator_degree hp hq hm g hlong t hw x T.charpoly
    T.charpoly_monic hrec
  simpa only [T.charpoly_natDegree,Module.finrank_fin_fun] using hd

/-- Whole-family fixed linear acquisition of the ORIGINAL detector
requires quadratic state dimension. Different transitions, initial
states and linear readouts are allowed for every original seed; sharing
one transition or one state cannot improve the floor. -/
theorem original_family_linear_acquisition_state_floor {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) (t : ℕ)
    (T : ℕ→Module.End (ZMod (p*q)) (Fin d→ZMod (p*q)))
    (initial : ℕ→Fin d→ZMod (p*q))
    (readout : ℕ→(Fin d→ZMod (p*q))→ₗ[ZMod (p*q)]ZMod (p*q))
    (hcorrect : ∀ j,1≤j→j<m→∀ r : ℕ, r≤seedLength m+d → readout j (((T j)^r) (initial j))=
      intervalProduct ((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))
        (((((seedBase (projectedUnit g m) m)^(2^t) : (ZMod (p*q))ˣ) :
          ZMod (p*q))^r)*
            ((progressionSeed (projectedUnit g m) (p*q) m j).step : ZMod (p*q)))
        (seedLength m)) :
    seedLength m+1≤d ∧ 2*m^2+3≤d := by
  have hd := original_factory_linear_state_dimension hp hq hm g hlong t le_rfl
    (progressionSeed (projectedUnit g m) (p*q) m 1).step (T 1) (initial 1) (readout 1)
    (fun r hr => by
      rw [rowPolynomial_eval]
      exact hcorrect 1 le_rfl (by omega) r hr)
  have hlength := (seedLength_bounds hm).1
  exact ⟨hd,by omega⟩

/-- A physically materialized coordinate state inherits the dimension
floor in its slot count and any work clock charging those coordinates.
This does not price compressed encodings of a larger logical state. -/
theorem original_family_linear_state_source_floor {m d slots work : ℕ}
    (hd : 2*m^2+3≤d) (hslots : d≤slots) (hwork : slots≤work) :
    2*m^2+3≤slots ∧ 2*m^2+3≤work :=
  ⟨hd.trans hslots,hd.trans (hslots.trans hwork)⟩

/-- The fixed linear-state obstruction applies to the ACTUAL public
long outcome and ALL original seed labels, without a private order or
a universal-polynomial correctness premise. -/
theorem actual_public_route_linear_acquisition_state_floor {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ (t d : ℕ) (T : ℕ→Module.End (ZMod (p*q)) (Fin d→ZMod (p*q)))
        (initial : ℕ→Fin d→ZMod (p*q))
        (readout : ℕ→(Fin d→ZMod (p*q))→ₗ[ZMod (p*q)]ZMod (p*q)),
        (∀ j,1≤j→j<m→∀ r : ℕ, r≤seedLength m+d → readout j (((T j)^r) (initial j))=
          intervalProduct ((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q))
            (((((seedBase h m)^(2^t) : (ZMod (p*q))ˣ) : ZMod (p*q))^r)*
              ((progressionSeed h (p*q) m j).step : ZMod (p*q))) (seedLength m))→
          seedLength m+1≤d ∧ 2*m^2+3≤d := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  have hN := Nat.mul_pos hp.pos hq.pos
  have hm := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  refine ⟨hc,?_⟩
  dsimp only
  intro t d T initial readout hcorrect
  exact original_family_linear_acquisition_state_floor hp hq hm _ hlong t
    T initial readout hcorrect

/-- A monic constant-coefficient recurrence cannot leave a zero prefix
as long as its degree. This requires no field, unit sample or division. -/
theorem monic_recurrence_zero_prefix {R : Type*} [CommRing R]
    (A : R[X]) (hA : A.Monic) (b : ℕ→R)
    (hrec : ∀ r,∑ i∈Finset.range (A.natDegree+1),A.coeff i*b (r+i)=0)
    (hzero : ∀ i<A.natDegree,b i=0) : ∀ i,b i=0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<A.natDegree
    · exact hzero n hn
    have hd : A.natDegree≤n := by omega
    have he := hrec (n-A.natDegree)
    rw [Finset.sum_range_succ,coeff_natDegree,hA.leadingCoeff,one_mul,
      Nat.sub_add_cancel hd] at he
    have hs : ∑ i∈Finset.range A.natDegree,A.coeff i*b (n-A.natDegree+i)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hilt := Finset.mem_range.mp hi
      rw [ih (n-A.natDegree+i) (by omega),mul_zero]
    rwa [hs,zero_add] at he

/-- The direct product of ALL original seed detectors at one common
phase. It emits no individual row or leaf values and permits arbitrary
coefficient cancellation among the original rows. This is a proof model. -/
noncomputable def seedAggregate {N : ℕ} (g : (ZMod N)ˣ) (m : ℕ)
    (z : ZMod N) : ZMod N :=
  SemiprimeQAggregate.rowAggregate ((seedBase g m : (ZMod N)ˣ) : ZMod N)
    (fun j => z*((progressionSeed g N m (j+1)).step : ZMod N)) (m-1) (seedLength m)

/-- Anchoring the common phase at any retained target supplies a full
zero interval in the WHOLE aggregate, independent of cancellations. -/
theorem seedAggregate_zero_prefix {N m r : ℕ} (g : (ZMod N)ˣ)
    (hm : 1<m) (hr : r<seedLength m) :
    seedAggregate g m
      ((((seedBase g m : (ZMod N)ˣ) : ZMod N)^r)*
        (((progressionSeed g N m 1).step⁻¹ : (ZMod N)ˣ) : ZMod N))=0 := by
  classical
  unfold seedAggregate SemiprimeQAggregate.rowAggregate
  apply Finset.prod_eq_zero (i:=0) (Finset.mem_range.mpr (by omega))
  simp only [Nat.zero_add]
  have hx : (((progressionSeed g N m 1).step⁻¹ : (ZMod N)ˣ) : ZMod N)*
      ((progressionSeed g N m 1).step : ZMod N)=1 :=
    (progressionSeed g N m 1).step.inv_mul
  rw [mul_assoc,hx,mul_one]
  unfold intervalProduct
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hr) (sub_self _)

/-- The retained original anchor seed is an actual power of the interval
base on the long branch. Roughness preserves the generated subgroup;
the power index is only a proof-side witness, never execution advice. -/
theorem original_seed_in_base_powers {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m) :
    ∃ r : ℕ,(seedBase (projectedUnit g m) m)^r=
      (progressionSeed (projectedUnit g m) (p*q) m 1).step := by
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  have hpm := SemiprimeWrapIndexRecovery.rough_coprime_small
    (by omega : 0<m) le_rfl hlong.2.2.2.2.2.1
  have hqm := SemiprimeWrapIndexRecovery.rough_coprime_small
    (by omega : 0<m) le_rfl hlong.2.2.2.2.2.2
  have hcop : (m^2).Coprime (orderOf (projectedUnit g m)) := by
    rw [global_order_eq_lcm hp hq hpq,(hlong.2.2.2.2.1).lcm_eq_mul]
    exact ((hpm.pow_right 2).mul_left (hqm.pow_right 2)).symm
  obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime hcop
  change (seedBase (projectedUnit g m) m)^k=projectedUnit g m at hk
  have hmember := Subgroup.pow_mem (Subgroup.zpowers (seedBase (projectedUnit g m) m))
    (Subgroup.mem_zpowers (seedBase (projectedUnit g m) m)) k
  rw [hk] at hmember
  have hs : (progressionSeed (projectedUnit g m) (p*q) m 1).step∈
      Subgroup.zpowers (seedBase (projectedUnit g m) m) := by
    rw [seed_step_offset _ (by omega) (by simp)]
    exact Subgroup.zpow_mem _ hmember _
  exact mem_powers_iff_mem_zpowers.mpr hs

/-- Direct WHOLE-family aggregation cannot repair a small FIXED linear
state unless the original scalar detector is completely saturated.
No individual leaf outputs or explicit coefficient source is assumed.
Extra recovery information in the saturated case is not obstructed. -/
theorem original_aggregate_linear_state_dichotomy {p q m d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (T : Module.End (ZMod (p*q)) (Fin d→ZMod (p*q)))
    (v : Fin d→ZMod (p*q)) (readout : (Fin d→ZMod (p*q))→ₗ[ZMod (p*q)]ZMod (p*q))
    (hcorrect : ∀ r,readout ((T^r) v)=seedAggregate (projectedUnit g m) m
      (((((seedBase (projectedUnit g m) m : (ZMod (p*q))ˣ) : ZMod (p*q))^r))*
        (((progressionSeed (projectedUnit g m) (p*q) m 1).step⁻¹ : (ZMod (p*q))ˣ) :
          ZMod (p*q)))) :
    seedLength m+1≤d ∨
      (seedAggregate (projectedUnit g m) m 1=0 ∧
        (p*q).gcd (seedAggregate (projectedUnit g m) m 1).val=p*q) := by
  let : Fact (1<p*q) := ⟨by nlinarith only [hp.one_lt,hq.one_lt]⟩
  by_cases hd : seedLength m+1≤d
  · exact Or.inl hd
  have hdegree : T.charpoly.natDegree=d := by
    simp only [T.charpoly_natDegree,Module.finrank_fin_fun]
  have hrec r : ∑ i∈Finset.range (T.charpoly.natDegree+1),T.charpoly.coeff i*
      readout ((T^(r+i)) v)=0 := linear_state_charpoly_recurrence T v readout r
  have hzero i (hi : i<T.charpoly.natDegree) : readout ((T^i) v)=0 := by
    rw [hcorrect]
    apply seedAggregate_zero_prefix _ (by omega)
    rw [hdegree] at hi
    omega
  have hall := monic_recurrence_zero_prefix T.charpoly T.charpoly_monic
    (fun i => readout ((T^i) v)) hrec hzero
  obtain ⟨r,hr⟩ := original_seed_in_base_powers hp hq hpq hm g hlong
  have he := hall r
  rw [hcorrect] at he
  have hscalar := congrArg (fun u : (ZMod (p*q))ˣ => (u : ZMod (p*q))) hr
  rw [Units.val_pow_eq_pow_val] at hscalar
  rw [hscalar] at he
  rw [(progressionSeed (projectedUnit g m) (p*q) m 1).step.mul_inv] at he
  refine Or.inr ⟨he,?_⟩
  simp only [he,ZMod.val_zero,Nat.gcd_zero_right]

/-- The direct aggregate dichotomy also uses the actual N-only public
long outcome. A short fixed linear phase state supplies only a scalar
whose public GCD is the entire input; extra tagged recovery remains open. -/
theorem actual_public_route_aggregate_linear_state_dichotomy {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (hroute : routeAtRowModulus (p*q)=.longBase a) :
    ∃ hc : a.Coprime (p*q),
      let m := SemiprimeEuclidRowBudget.publicRowModulus (p*q)
      let h := projectedUnit (ZMod.unitOfCoprime a hc) m
      ∀ (d : ℕ) (T : Module.End (ZMod (p*q)) (Fin d→ZMod (p*q)))
        (v : Fin d→ZMod (p*q))
        (readout : (Fin d→ZMod (p*q))→ₗ[ZMod (p*q)]ZMod (p*q)),
        (∀ r,readout ((T^r) v)=seedAggregate h m
          (((seedBase h m : (ZMod (p*q))ˣ) : ZMod (p*q))^r*
            (((progressionSeed h (p*q) m 1).step⁻¹ : (ZMod (p*q))ˣ) : ZMod (p*q))))→
          seedLength m+1≤d ∨
            (seedAggregate h m 1=0 ∧ (p*q).gcd (seedAggregate h m 1).val=p*q) := by
  have hd := routeAtRowModulus_semiprime hp hq hpq hB
  rw [hroute] at hd
  obtain ⟨hc,hlong⟩ := hd
  have hN := Nat.mul_pos hp.pos hq.pos
  have hm := hB.trans (SemiprimeEuclidRowBudget.publicRowModulus_bounds hN).1
  refine ⟨hc,?_⟩
  dsimp only
  intro d T v readout hcorrect
  exact original_aggregate_linear_state_dichotomy hp hq hpq.ne hm _ hlong T v readout hcorrect

end RiemannGaussian.SemiprimeSeedLinearStateObstruction
