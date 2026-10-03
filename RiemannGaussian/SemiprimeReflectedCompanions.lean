/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeEuclidRowBudget

/-!
# Shared ordinary polynomial for signed companion recovery

Retain the full ordinary integer companions upstream. One polynomial on
their distinct ordinary residues supplies its derivative and its reflection.
Global negative matches use the already cached ordinary derivative. The
endpoint guard removes only a whole-modulus zero, before nonunit products.
Useful-hit coverage and the complete every-run bit clock remain separate.
-/

namespace RiemannGaussian.SemiprimeReflectedCompanions

open scoped BigOperators
open Polynomial SemiprimeCartesianCompletion SemiprimeRowDerivative
open SemiprimeCompanionRows SemiprimeCompanionCoverage SemiprimeEuclidRowFamily

/-- The public zero endpoint contributes no false nonunit leaf. -/
def guardedEndpoint {R : Type*} [CommRing R] [DecidableEq R] (t : R) : R :=
  if t=0 then 1 else t

/-- Keep the three ordinary signed channels before combining their units.
The reflected factor deflates every exact whole-modulus negative match. -/
noncomputable def reflectedColumn {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) : R :=
  guardedEndpoint t*deflatedColumn S t*deflatedColumn S (-t)

/-- Coefficient reflection evaluates the original polynomial at -t;
there is no second root polynomial or modular division in this identity. -/
theorem reflectedPolynomial_eval {R : Type*} [CommRing R]
    (P : R[X]) (t : R) : (P.comp (-X)).eval t=P.eval (-t) := by
  simp only [eval_comp,eval_neg,eval_X]

/-- The reflected evaluation stream needs only a public coefficient sign
change, preserving the original coefficient vector upstream. -/
theorem reflectedPolynomial_coeff {R : Type*} [CommRing R]
    (P : R[X]) (k : ℕ) : (P.comp (-X)).coeff k=P.coeff k*(-1 : R)^k := by
  simpa only [map_neg,map_one,neg_one_mul] using
    (comp_C_mul_X_coeff (p:=P) (r:=(-1 : R)) (n:=k))

/-- The shared original polynomial has exactly one factor per distinct
ordinary root in every nontrivial coefficient ring. -/
theorem ordinaryPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (S : Finset R) : (rootPolynomial S id).natDegree=S.card :=
  natDegree_finsetProd_X_sub_C_eq_card S id

/-- Reflection changes coefficients but preserves this same degree. -/
theorem reflectedPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (S : Finset R) : ((rootPolynomial S id).comp (-X)).natDegree=S.card := by
  rw [natDegree_eq_of_degree_eq (degree_comp_neg_X),ordinaryPolynomial_natDegree]

/-- At every original root, two evaluation streams and a cached original
derivative realize the exact retained reflected column. -/
theorem reflectedColumn_eq_cached {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) {t : R} (ht : t∈S) :
    reflectedColumn S t=guardedEndpoint t*(rootPolynomial S id).derivative.eval t*
      (if -t∈S then (rootPolynomial S id).derivative.eval (-t)
        else ((rootPolynomial S id).comp (-X)).eval t) := by
  simp only [reflectedColumn,deflatedColumn,if_pos ht,reflectedPolynomial_eval]

/-- Each channel preserves its complete unit test, with zero guarded. -/
theorem guardedEndpoint_isUnit_iff {R : Type*} [CommRing R] [DecidableEq R] (t : R) :
    IsUnit (guardedEndpoint t) ↔ t=0 ∨ IsUnit t := by
  by_cases ht : t=0
  · simp [guardedEndpoint,ht]
  · simp [guardedEndpoint,ht]

/-- A deflated product is a unit exactly when every retained nonzero
whole-ring difference is a unit, without a field or squarefree premise. -/
theorem deflatedColumn_isUnit_iff {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) :
    IsUnit (deflatedColumn S t) ↔ ∀ x∈S, x≠t → IsUnit (t-x) := by
  rw [deflatedColumn_eq_product,IsUnit.prod_iff]
  simp only [Finset.mem_erase,and_imp]
  constructor
  · intro h x hx hne
    exact h x hne hx
  · intro h x hne hx
    exact h x hx hne

/-- Reflection retains nonzero sum information; a globally zero sum is
removed as an exact shared root rather than treated as a useful hit. -/
theorem reflectedDeflation_isUnit_iff {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) :
    IsUnit (deflatedColumn S (-t)) ↔ ∀ x∈S, t+x≠0 → IsUnit (t+x) := by
  rw [deflatedColumn_isUnit_iff]
  constructor
  · intro h x hx hsum
    have hne : x≠-t := by intro he; rw [he,add_neg_cancel] at hsum; contradiction
    have hu := h x hx hne
    rw [show -t-x=-(t+x) by ring] at hu
    exact (IsUnit.neg_iff _).mp hu
  · intro h x hx hne
    have hsum : t+x≠0 := by
      intro hz
      apply hne
      calc x=(t+x)-t := by ring
           _=-t := by rw [hz,zero_sub]
    rw [show -t-x=-(t+x) by ring]
    exact (h x hx hsum).neg

/-- The combined unit test keeps precisely endpoint, difference and sum
channels, despite repeated product factors in the compressed observable. -/
theorem reflectedColumn_isUnit_iff {R : Type*} [CommRing R] [DecidableEq R]
    (S : Finset R) (t : R) :
    IsUnit (reflectedColumn S t) ↔ (t=0 ∨ IsUnit t) ∧
      (∀ x∈S, x≠t → IsUnit (t-x)) ∧
      (∀ x∈S, t+x≠0 → IsUnit (t+x)) := by
  rw [reflectedColumn,IsUnit.mul_iff,IsUnit.mul_iff,guardedEndpoint_isUnit_iff,
    reflectedDeflation_isUnit_iff,deflatedColumn_isUnit_iff,and_assoc]

/-- Lazy canonical endpoint leaves, excluding only an exact global zero. -/
def endpointLeaves {n : ℕ} (t : ZMod n) : List ℕ := if t=0 then [] else [t.val]

/-- Original differences and reflected differences survive in separate
leaf channels; recovery constructs them only on its first saturated row. -/
noncomputable def reflectedLeaves {n : ℕ} (S : Finset (ZMod n)) (t : ZMod n) : List ℕ :=
  endpointLeaves t++residueLeaves S t++residueLeaves S (-t)

theorem reflectedLeaves_length_le {n : ℕ} (S : Finset (ZMod n)) (t : ZMod n) :
    (reflectedLeaves S t).length≤2*S.card+1 := by
  have he : (endpointLeaves t).length≤1 := by
    unfold endpointLeaves
    split_ifs <;> simp
  have hd := residueLeaves_length_le S t
  have hr := residueLeaves_length_le S (-t)
  simp only [reflectedLeaves,List.length_append]
  omega

theorem reflectedLeaves_bounds {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    ∀ v∈reflectedLeaves S t, 0<v ∧ v<n := by
  intro v hv
  rcases List.mem_append.mp hv with hv|hv
  · rcases List.mem_append.mp hv with hv|hv
    · by_cases ht : t=0
      · simp [endpointLeaves,ht] at hv
      · have he : v=t.val := by simpa only [endpointLeaves,if_neg ht,List.mem_singleton] using hv
        rw [he]
        exact ⟨ZMod.val_pos.mpr ht,ZMod.val_lt _⟩
    · exact residueLeaves_bounds S t v hv
  · exact residueLeaves_bounds S (-t) v hv

private theorem residueLeaves_cast_prod {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    ((residueLeaves S t).prod : ZMod n)=deflatedColumn S t := by
  rw [residueLeaves,Finset.prod_map_toList,deflatedColumn_eq_product]
  simp only [Nat.cast_prod,ZMod.natCast_zmod_val]

/-- Polynomial evaluation and the lazy separated leaf channels commute
before GCD projection, including all prime powers and global matches. -/
theorem reflectedColumn_val_eq {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    (reflectedColumn S t).val=(reflectedLeaves S t).prod%n := by
  have he : ((endpointLeaves t).prod : ZMod n)=guardedEndpoint t := by
    by_cases ht : t=0 <;> simp [endpointLeaves,guardedEndpoint,ht]
  have h : ((reflectedLeaves S t).prod : ZMod n)=reflectedColumn S t := by
    simp only [reflectedLeaves,List.prod_append,Nat.cast_mul,
      residueLeaves_cast_prod,he,reflectedColumn]
  rw [←h,ZMod.val_natCast]

theorem reflectedColumn_gcd_eq {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) (t : ZMod n) :
    n.gcd (reflectedColumn S t).val=n.gcd (reflectedLeaves S t).prod := by
  rw [reflectedColumn_val_eq,Nat.gcd_rec n,Nat.gcd_rec n ((reflectedLeaves S t).prod),
    Nat.mod_mod]

/-- One column per ordinary distinct root; both signed channels remain
in the column value without building the union of positive/negative roots. -/
noncomputable def reflectedColumns {n : ℕ} (S : Finset (ZMod n)) : List (ℕ×ℕ) :=
  S.toList.map fun t => (t.val,(reflectedColumn S t).val)

/-- Checked recovery from the shared ordinary polynomial observables. -/
noncomputable def recoverReflectedRows {n : ℕ} (S : Finset (ZMod n)) : Option ℕ :=
  recoverColumns n (fun i => reflectedLeaves S (i : ZMod n)) (reflectedColumns S)

theorem recoverReflectedRows_sound {n d : ℕ} {S : Finset (ZMod n)}
    (hd : recoverReflectedRows S=some d) : SemiprimeGroupSelection.ProperDivisor n d :=
  recoverColumns_sound hd

theorem recoverReflectedRows_succeeds_of_nonunit {n : ℕ} [NeZero n]
    {S : Finset (ZMod n)} {t : ZMod n} (ht : t∈S)
    (hn : n.gcd (reflectedColumn S t).val≠1) : ∃ d, recoverReflectedRows S=some d := by
  apply recoverColumns_succeeds
  · intro c hc
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hc
    simpa only [ZMod.natCast_zmod_val] using reflectedColumn_gcd_eq S u
  · intro c hc
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hc
    exact reflectedLeaves_bounds S (u.val : ZMod n)
  · exact ⟨(t.val,(reflectedColumn S t).val),
      List.mem_map.mpr ⟨t,Finset.mem_toList.mpr ht,rfl⟩,hn⟩

private theorem recoverColumns_none_of_units (n : ℕ) (leaves : ℕ→List ℕ)
    (columns : List (ℕ×ℕ)) (hu : ∀ c∈columns, n.gcd c.2=1) :
    recoverColumns n leaves columns=none := by
  induction columns with
  | nil => rfl
  | cons c tail ih =>
    rcases c with ⟨t,v⟩
    rw [recoverColumns,if_pos (hu (t,v) (by simp))]
    exact ih (fun c hc => hu c (List.mem_cons_of_mem _ hc))

/-- Exhaustion is the complete unit test of the retained columns. -/
theorem recoverReflectedRows_none_iff {n : ℕ} [NeZero n] (S : Finset (ZMod n)) :
    recoverReflectedRows S=none ↔ ∀ t∈S, IsUnit (reflectedColumn S t) := by
  constructor
  · intro hnone t ht
    apply (SemiprimeBulkNorm.gcd_one_iff_unit _).mp
    by_contra hn
    obtain ⟨d,hd⟩ := recoverReflectedRows_succeeds_of_nonunit ht hn
    rw [hnone] at hd
    contradiction
  · intro hu
    apply recoverColumns_none_of_units
    intro c hc
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
    exact (SemiprimeBulkNorm.gcd_one_iff_unit _).mpr (hu t (Finset.mem_toList.mp ht))

/-- Complete hit-union equivalence with the larger signed-root program,
including endpoint, sum/difference and saturated product recovery. -/
theorem recoverReflectedRows_none_iff_signed {n : ℕ} [NeZero n]
    (S : Finset (ZMod n)) :
    recoverReflectedRows S=none ↔ recoverRows (signedRoots S)=none := by
  rw [recoverReflectedRows_none_iff,recoverRows_none_iff]
  simp only [SemiprimeBulkNorm.gcd_one_iff_unit]
  change (∀ t∈S, IsUnit (reflectedColumn S t)) ↔ UnitSeparated (signedRoots S)
  rw [signedRoots_unitSeparated_iff]
  simp only [reflectedColumn_isUnit_iff,UnitSeparated]
  constructor
  · intro h
    exact ⟨fun t ht => (h t ht).1,fun t ht => (h t ht).2.1,
      fun t ht => (h t ht).2.2⟩
  · rintro ⟨he,hd,hs⟩ t ht
    exact ⟨he t ht,hd t ht,hs t ht⟩

/-- One query per ordinary column plus at most one lazy scan of its
two difference channels and one guarded endpoint. This is a query count. -/
theorem recoverReflectedRows_gcd_bound {n : ℕ} (S : Finset (ZMod n)) :
    recoveryGcdCount n (fun i => reflectedLeaves S (i : ZMod n))
      (reflectedColumns S)≤3*S.card+1 := by
  have h := recoveryGcdCount_le (n:=n) (cap:=2*S.card+1)
    (leaves:=fun i => reflectedLeaves S (i : ZMod n)) (columns:=reflectedColumns S)
    (fun c _ => reflectedLeaves_length_le S (c.1 : ZMod n))
  simp only [reflectedColumns,List.length_map,Finset.length_toList] at h ⊢
  omega

/-- The complete public ordinary companions supply both signed channels
without constructing a doubled signed root polynomial. -/
noncomputable def recoverReflectedCompanions (N m : ℕ) : Option ℕ :=
  recoverReflectedRows (publicCompanionRoots N m)

theorem recoverReflectedCompanions_sound {N m d : ℕ}
    (hd : recoverReflectedCompanions N m=some d) :
    SemiprimeGroupSelection.ProperDivisor N d := recoverReflectedRows_sound hd

theorem recoverReflectedCompanions_none_iff_signed {N m : ℕ} [NeZero N] :
    recoverReflectedCompanions N m=none ↔ recoverSignedCompanions N m=none :=
  recoverReflectedRows_none_iff_signed _

/-- The exact signed hit union survives; the first returned divisor may
differ because repeated product factors and recovery order can differ. -/
theorem recoverReflectedCompanions_preserves_signed_success {N m d : ℕ} [NeZero N]
    (hd : recoverSignedCompanions N m=some d) :
    ∃ f, recoverReflectedCompanions N m=some f := by
  cases hs : recoverReflectedCompanions N m with
  | some f => exact ⟨f,rfl⟩
  | none =>
    have hn := recoverReflectedCompanions_none_iff_signed.mp hs
    rw [hd] at hn
    contradiction

theorem recoverReflectedCompanions_gcd_bound (N m : ℕ) :
    recoveryGcdCount N (fun i => reflectedLeaves (publicCompanionRoots N m) (i : ZMod N))
      (reflectedColumns (publicCompanionRoots N m))≤6*(publicPackets N m).length+1 := by
  have h := recoverReflectedRows_gcd_bound (publicCompanionRoots N m)
  have hc := publicCompanionRoots_card_le N m
  omega

theorem recoverReflectedCompanions_gcd_prime_bound (N : ℕ) {m : ℕ} (hm : m.Prime) :
    recoveryGcdCount N (fun i => reflectedLeaves (publicCompanionRoots N m) (i : ZMod N))
      (reflectedColumns (publicCompanionRoots N m))≤48*m*(Nat.log2 m+1)^2+1 := by
  calc
    _ ≤ 6*(publicPackets N m).length+1 := recoverReflectedCompanions_gcd_bound N m
    _ ≤ 6*(8*m*(Nat.log2 m+1)^2)+1 := Nat.add_le_add_right
      (Nat.mul_le_mul_left 6 (SemiprimeEuclidRowBudget.publicPackets_length_le N hm)) 1
    _ = _ := by ring

/-- The literal ordinary failure is repaired by the shared polynomial
source as well, using the already kernel-checked complete signed success. -/
theorem missed_control_reflected_recovers :
    ∃ d, recoverReflectedCompanions 7303 5=some d := by
  obtain ⟨d,hd⟩ := missed_control_signed_recovers
  exact recoverReflectedCompanions_preserves_signed_success hd

/-- The already checked larger ordinary companion recovery transports
through the complete signed union to this compressed public program. -/
theorem derivative_control_reflected_recovers :
    ∃ d, recoverReflectedCompanions 2518766418595894637609 3691=some d := by
  obtain ⟨d,hd⟩ := derivative_control_public_companions_recovers
  obtain ⟨f,hf⟩ := recoverSignedCompanions_preserves_success hd
  exact recoverReflectedCompanions_preserves_signed_success hf

/-- The 90-bit public ordinary recovery is also retained without asking
for either factor as an input to the compressed construction. -/
theorem larger_control_reflected_recovers :
    ∃ d, recoverReflectedCompanions 788096216222522769981991129 30403=some d := by
  obtain ⟨d,hd⟩ := larger_control_public_companions_recovers
  obtain ⟨f,hf⟩ := recoverSignedCompanions_preserves_success hd
  exact recoverReflectedCompanions_preserves_signed_success hf

/-- An exact whole-modulus negative pair supplies no false hit. Its raw
reflected polynomial is zero, but the correctly deflated program exhausts. -/
theorem global_negative_control_none :
    recoverReflectedRows ({1,34} : Finset (ZMod 35))=none := by
  rw [recoverReflectedRows_none_iff_signed,recoverRows_none_iff]
  decide +kernel

/-- Squared moduli and globally zero endpoints do not obstruct saturated
recovery from a proper nonzero leaf of the retained channels. -/
theorem square_saturation_control_recovers :
    ∃ d, recoverReflectedRows ({0,7} : Finset (ZMod 49))=some d := by
  apply recoverReflectedRows_succeeds_of_nonunit (t:=0) (by simp)
  norm_num [reflectedColumn,guardedEndpoint,deflatedColumn_eq_product]
  decide +kernel

end RiemannGaussian.SemiprimeReflectedCompanions
