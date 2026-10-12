/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBalancedAcquisitionObstruction

/-!
# Exact cofactor fibers for scattered original baby columns

The centered offset is exactly periodic under cofactor changes by m squared.
An exact integer detector fiber therefore has at most one lift per residue.
All original rows together have at most 4m exact cofactor solutions for one
fixed column and period multiplier. The investigation journal combines this
with the actual selector envelope to obstruct scattered menus chosen from
m and N modulo m on infinitely many actual long-base-2 inputs. Density, real interval counting
and infinitude remain classical; they are not additional Lean axioms.
-/

namespace RiemannGaussian.SemiprimeScatteredColumnObstruction

open scoped BigOperators
open Classical
open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open SemiprimeGlobalPhaseCancellation SemiprimeSeedDetectorResidueObstruction
open SemiprimeSeedSumAcquisition SemiprimeLocalOrderRouting SemiprimeCentreFreeCover

/-- Centering makes the cofactor-periodic offset exactly equal as an integer. -/
theorem seedOffset_eq_of_cofactor_modEq {p q q₀ m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (he : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD (m : ℤ)^2]) :
    seedOffset (p*q) m j=seedOffset (p*q₀) m j := by
  have ha := representative_eq_of_cofactor_modEq (p:=p) hm hj
    (he.of_dvd (dvd_pow_self (m : ℤ) (by decide : 2≠0)))
  have hr := denseRow_relation (N:=p*q) (j:=j) (t:=1) hm hj false
  have hr₀ := denseRow_relation (N:=p*q₀) (j:=j) (t:=1) hm hj false
  change quotientRelation (p*q) m j (representative (p*q) m j 1)
    (seedRow (p*q) m j).b (seedRow (p*q) m j).c 1 at hr
  change quotientRelation (p*q₀) m j (representative (p*q₀) m j 1)
    (seedRow (p*q₀) m j).b (seedRow (p*q₀) m j).c 1 at hr₀
  unfold quotientRelation at hr hr₀
  rw [ha] at hr
  obtain ⟨z,hz⟩ := (he.mul_left (p : ℤ)).dvd
  have hdiv : (m : ℤ)∣(j : ℤ)*((seedRow (p*q₀) m j).b-(seedRow (p*q) m j).b) := by
    refine ⟨(seedRow (p*q₀) m j).c-(seedRow (p*q) m j).c-z,?_⟩
    apply mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ)≠0)
    linear_combination hr-hr₀-hz
  have hbmod : (seedRow (p*q) m j).b ≡ (seedRow (p*q₀) m j).b [ZMOD m] :=
    Int.modEq_iff_dvd.mpr (hj.symm.isCoprime.dvd_of_dvd_mul_left hdiv)
  have hb := centered_congr hbmod
  simp only [seedRow,denseRow,liftRow,centered_idempotent] at hb
  change (seedRow (p*q) m j).b=(seedRow (p*q₀) m j).b at hb
  unfold seedOffset
  rw [ha,hb]

/-- A finite exact detector fiber, retaining the original centered carry. -/
noncomputable def detectorExactFiber (p m j : ℕ) (Q : Finset ℕ) (T : ℤ) : Finset ℕ :=
  Q.filter fun q => (q : ℤ)+seedOffset (p*q) m j=T

/-- Exact solutions have distinct residues modulo m squared. -/
theorem detector_exact_fiber_injective_residue {p m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (Q : Finset ℕ) (T : ℤ) :
    Set.InjOn (fun q : ℕ => q%m^2) (detectorExactFiber p m j Q T) := by
  intro q hq q₀ hq₀ he
  have hclass : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD (m : ℤ)^2] := by
    simpa only [←Nat.cast_pow,Int.natCast_modEq_iff,Nat.ModEq] using he
  have hδ := seedOffset_eq_of_cofactor_modEq (p:=p) hm hj hclass
  have hfirst := (Finset.mem_filter.mp hq).2
  have hsecond := (Finset.mem_filter.mp hq₀).2
  rw [hδ] at hfirst
  omega

/-- Reducing an exact cofactor solution lands in its literal original residue fiber. -/
theorem detector_exact_fiber_maps_to_residue {p m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (Q : Finset ℕ) (T : ℤ) :
    Set.MapsTo (fun q : ℕ => q%m^2) (detectorExactFiber p m j Q T)
      (detectorResidueFiber p m j T) := by
  intro q hq
  have hclass : (q : ℤ) ≡ ((q%m^2 : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    have hn : q ≡ q%m^2 [MOD m^2] := by simp only [Nat.ModEq,Nat.mod_mod]
    simpa only [←Nat.cast_pow,Int.natCast_modEq_iff] using hn
  have hperiod := detector_periodic_modEq (p:=p) hm hj hclass
  have htarget := (Finset.mem_filter.mp hq).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)),?_⟩
  change ((q%m^2 : ℕ) : ℤ)+seedOffset (p*(q%m^2)) m j ≡ T [ZMOD (m : ℤ)^2]
  rw [htarget] at hperiod
  exact hperiod.symm

/-- The exact integer fiber pays no extra selector-gap or quotient-lift factor. -/
theorem detectorExactFiber_card_le_residue {p m j : ℕ} (hm : 0<m)
    (hj : j.Coprime m) (Q : Finset ℕ) (T : ℤ) :
    (detectorExactFiber p m j Q T).card≤(detectorResidueFiber p m j T).card :=
  Finset.card_le_card_of_injOn _ (detector_exact_fiber_maps_to_residue hm hj Q T)
    (detector_exact_fiber_injective_residue hm hj Q T)

/-- Across every original row, one fixed column/multiplier has at most 4m exact cofactors. -/
theorem detector_exact_whole_family_bound {p m : ℕ} (hm : m.Prime)
    (hp : (p : ZMod m)≠0) (hp1 : (p : ZMod m)≠1)
    (Q : Finset ℕ) (T : ℕ→ℤ) :
    (∑ j∈Finset.range (m-1), (detectorExactFiber p m (j+1) Q (T j)).card)≤4*m := by
  apply (Finset.sum_le_sum ?_).trans (detector_whole_family_fiber_bound hm hp hp1 T)
  intro j hj
  have hjm : j+1<m := by have hh := Finset.mem_range.mp hj; omega
  have hcop : (j+1).Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  exact detectorExactFiber_card_le_residue hm.pos hcop Q (T j)

/-- Fixing the cofactor modulo m leaves at most two original row labels at one column. -/
theorem column_fixed_class_rows_card {p m : ℕ} (hm : m.Prime)
    (hp : (p : ZMod m)≠0) (c : ZMod m) (hc : c≠0) (Q : Finset ℕ) (T : ℤ) :
    ((Finset.range (m-1)).filter fun j =>
      (detectorExactFiber p m (j+1) (Q.filter fun q => (q : ZMod m)=c) T).Nonempty).card≤2 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let P : Polynomial (ZMod m) :=
    Polynomial.C (c-(T : ZMod m))*Polynomial.X^2-
      Polynomial.C (2*(p : ZMod m)*c)*Polynomial.X+Polynomial.C ((p : ZMod m)*c)
  have hP : P≠0 := by
    intro hz
    have hh := congrArg (fun A : Polynomial (ZMod m) => A.coeff 0) hz
    have he : (p : ZMod m)*c=0 := by simpa [P] using hh
    exact (mul_ne_zero hp hc) he
  have hdegree : P.natDegree≤2 := by
    dsimp only [P]
    compute_degree!
  let E := (Finset.range (m-1)).filter fun j =>
    (detectorExactFiber p m (j+1) (Q.filter fun q => (q : ZMod m)=c) T).Nonempty
  have hb {j : ℕ} (hj : j∈E) : j+1<m := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  have hmap : Set.MapsTo (fun j : ℕ => ((j+1 : ℕ) : ZMod m)) E P.roots.toFinset := by
    intro j hj
    obtain ⟨q,hq⟩ := (Finset.mem_filter.mp hj).2
    have hcop : (j+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (hb hj))).symm
    have he := (Finset.mem_filter.mp hq).2
    have hclass := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
    have hrow := detector_quadratic_residue (p:=p) (q:=q) hm.pos hcop
    rw [he] at hrow
    simp only [detectorQuadratic,Int.cast_add,Int.cast_sub,Int.cast_mul,
      Int.cast_pow,Int.cast_natCast,Int.cast_ofNat,hclass] at hrow
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hP).mpr
    change P.eval ((j+1 : ℕ) : ZMod m)=0
    simp only [P,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    linear_combination -hrow
  have hinj : (E : Set ℕ).InjOn (fun j : ℕ => ((j+1 : ℕ) : ZMod m)) := by
    intro j hj k hk he
    have hh := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb hj),Nat.mod_eq_of_lt (hb hk)] at hh
    omega
  exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
    ((Multiset.toFinset_card_le P.roots).trans ((Polynomial.card_roots' P).trans hdegree))

/-- Outside the true residue row, one fixed cofactor class has at most one exact integer solution. -/
theorem column_fixed_class_nontrue_row_card {p m j : ℕ} (hm : m.Prime)
    (hj : j.Coprime m) (hnontrue : (j : ZMod m)≠(p : ZMod m))
    (c : ZMod m) (Q : Finset ℕ) (T : ℤ) :
    (detectorExactFiber p m j (Q.filter fun q => (q : ZMod m)=c) T).card≤1 := by
  apply Finset.card_le_one.mpr
  intro q hq q₀ hq₀
  have hC : (cofactorCoefficient p m j : ZMod m)≠0 := by
    intro hz
    exact hnontrue ((cofactorCoefficient_zero_iff hj).mp hz)
  have hqclass := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hq₀class := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₀).1).2
  have hclass : (q : ℤ) ≡ (q₀ : ℤ) [ZMOD m] :=
    (ZMod.intCast_eq_intCast_iff _ _ m).mp (by
      simpa only [Int.cast_natCast] using hqclass.trans hq₀class.symm)
  have he : (q : ℤ)+seedOffset (p*q) m j ≡
      (q₀ : ℤ)+seedOffset (p*q₀) m j [ZMOD (m : ℤ)^2] := by
    rw [(Finset.mem_filter.mp hq).2,(Finset.mem_filter.mp hq₀).2]
  have hmod := detector_same_class_modEq_square hm hj hC hclass he
  have hδ := seedOffset_eq_of_cofactor_modEq (p:=p) hm.pos hj hmod
  have hfirst := (Finset.mem_filter.mp hq).2
  have hsecond := (Finset.mem_filter.mp hq₀).2
  rw [hδ] at hfirst
  omega

/-- All false residue rows together have at most two exact cofactors in one nonzero class. -/
theorem column_fixed_class_false_whole_family_bound {p m : ℕ} (hm : m.Prime)
    (hp : (p : ZMod m)≠0) (c : ZMod m) (hc : c≠0) (Q : Finset ℕ) (T : ℤ) :
    (∑ j∈(Finset.range (m-1)).filter fun j => ((j+1 : ℕ) : ZMod m)≠p,
      (detectorExactFiber p m (j+1) (Q.filter fun q => (q : ZMod m)=c) T).card)≤2 := by
  classical
  let E := (Finset.range (m-1)).filter fun j =>
    (detectorExactFiber p m (j+1) (Q.filter fun q => (q : ZMod m)=c) T).Nonempty
  let J := (Finset.range (m-1)).filter fun j => ((j+1 : ℕ) : ZMod m)≠p
  have hcE : E.card≤2 := column_fixed_class_rows_card hm hp c hc Q T
  have hle : (∑ j∈J, (detectorExactFiber p m (j+1)
      (Q.filter fun q => (q : ZMod m)=c) T).card)≤∑ j∈J, if j∈E then 1 else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    have hjm : j+1<m := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      omega
    have hcop : (j+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
    by_cases hE : j∈E
    · simpa only [ite_eq_left hE] using column_fixed_class_nontrue_row_card hm hcop
        (Finset.mem_filter.mp hj).2 c Q T
    · have hz : detectorExactFiber p m (j+1) (Q.filter fun q => (q : ZMod m)=c) T=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        exact hE (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,⟨q,hq⟩⟩)
      simp only [hz,Finset.card_empty,ite_eq_right hE,le_refl]
  have hsub : J⊆Finset.range (m-1) := Finset.filter_subset _ _
  have hsum : (∑ j∈Finset.range (m-1), if j∈E then (1 : ℕ) else 0)=E.card := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul,Nat.mul_one]
    rw [Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
  exact hle.trans ((Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)).trans
    (hsum.le.trans hcE))

/-- Clearing the actual selector envelope retains the exact hit, without rounding or division. -/
theorem singleton_column_envelope_identity {p q m v R δ r K : ℤ}
    (hcofactor : p-1=v*R) (hhit : q+δ-m^2*r=K*R) :
    v*(m^6-m^2*r*p)-K*p*(p-1)=v*(m^6-p*q-p*δ) := by
  linear_combination v*p*hhit-K*p*hcofactor

/-- Any global original column hit has the literal factor-sum index, including false row tags. -/
theorem common_seed_column_index_eq_factor_sum {p q m j r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hr : r<seedLength m)
    (hhit : (progressionSeed (projectedUnit g m) (p*q) m j).step=
      (seedBase (projectedUnit g m) m)^r) :
    (m : ℤ)^2*r=(p : ℤ)+q-1+seedOffset (p*q) m j := by
  have hsum := common_seed_sum_exact hp hq hpq hm hmprime hsize g hlong hj hjm hr hhit
  unfold seedSum at hsum
  rw [cachedOffset_seed] at hsum
  linarith only [hsum]

/-- On the balanced range every global shared root lies in the first width-4m column block. -/
theorem balanced_common_seed_column_first_block {p q m j r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hm : 4≤m) (hmprime : m.Prime)
    (hsize : p*q≤m^6) (hpupper : 2*p≤3*m^3) (hqupper : 2*q≤3*m^3)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hr : r<seedLength m)
    (hhit : (progressionSeed (projectedUnit g m) (p*q) m j).step=
      (seedBase (projectedUnit g m) m)^r) : r<4*m := by
  have he := common_seed_column_index_eq_factor_sum hp hq hpq hm hmprime hsize
    g hlong hj hjm hr hhit
  have hδ := (seedOffset_bounds (N:=p*q) (by omega) hj hjm).2
  have hpu : 2*(p : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hpupper
  have hqu : 2*(q : ℤ)≤3*(m : ℤ)^3 := by exact_mod_cast hqupper
  have hmul : (m : ℤ)^2*r≤(m : ℤ)^2*(3*(m : ℤ)+1) := by
    nlinarith only [he,hδ,hpu,hqu]
  have hmsq : (0 : ℤ)<(m : ℤ)^2 := by positivity
  have hb : r≤3*m+1 := by exact_mod_cast le_of_mul_le_mul_left hmul hmsq
  omega

/-- The second repeated-root branch fixes the exact multiplier lift through the centered carry. -/
theorem second_branch_cleared_multiplier_identity {F : Type*} [CommRing F]
    (K v a b m j x n : F) (hx : (2*j-1)*x=j) (hn : n=a*j^2-j*m*b) :
    (2*j-1)^2*(K*x^2-(K+v*(a+m*b-2*a*j))*x-v*n)=
      -j*(j-1)*(K+v*a*(2*j-1)^2-2*v*m*b*(2*j-1)) := by
  calc
    (2*j-1)^2*(K*x^2-(K+v*(a+m*b-2*a*j))*x-v*n)=
        K*((2*j-1)*x)^2-(K+v*(a+m*b-2*a*j))*(2*j-1)*((2*j-1)*x)-
          v*n*(2*j-1)^2 := by ring
    _=K*j^2-(K+v*(a+m*b-2*a*j))*(2*j-1)*j-v*(a*j^2-j*m*b)*(2*j-1)^2 := by rw [hx,hn]
    _=-j*(j-1)*(K+v*a*(2*j-1)^2-2*v*m*b*(2*j-1)) := by ring

end RiemannGaussian.SemiprimeScatteredColumnObstruction
