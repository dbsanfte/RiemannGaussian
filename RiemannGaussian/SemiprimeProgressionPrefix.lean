/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCommonOrder
import Mathlib.Data.List.Sort

/-!
# A common-modulus progression from one degree-B polynomial

A known positive common modulus m with m≥B covers the smaller semiprime
factor in the progression mk+1, 1≤k≤B², when N≤B⁶. One monic degree-B
polynomial and B targets retain this cover without a quadratic candidate
list. After the ordinary prefix clears, every leaf is below N, so even a
whole-modulus column is recovered with one lazy B-leaf scan.
Modulus acquisition and fast-backend bit complexity remain separate.
-/

namespace RiemannGaussian.SemiprimeProgressionPrefix

open scoped BigOperators
open Polynomial SemiprimeCartesianCompletion SemiprimeGroupSelection

/-- One monic polynomial retains all B offsets in each progression block. -/
noncomputable def blockPolynomial {R : Type*} [CommRing R] (m B : ℕ) : R[X] :=
  ∏ i ∈ Finset.range B, (X+C ((m*(i+1)+1 : ℕ) : R))

/-- Every point is the exact original progression block, even if m is
a nonunit or the ring is composite. -/
theorem blockPolynomial_eval {R : Type*} [CommRing R] (m B j : ℕ) :
    (blockPolynomial (R:=R) m B).eval ((m*(j*B) : ℕ) : R)=
      ((∏ i ∈ Finset.range B, (m*(j*B+i+1)+1)) : ℕ) := by
  simp only [blockPolynomial, eval_prod, eval_add, eval_X, eval_C, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring

/-- Canonical leaves are constructed only for the first ambiguous column. -/
def blockLeaves (N m B j : ℕ) : List ℕ :=
  (List.range B).map fun i => (m*(j*B+i+1)+1)%N

/-- Exactly B evaluated column values, labeled by their original block. -/
noncomputable def blockColumns (N m B : ℕ) : List (ℕ×ℕ) :=
  (List.range B).map fun j =>
    (j, ((blockPolynomial (R:=ZMod N) m B).eval ((m*(j*B) : ℕ) : ZMod N)).val)

/-- The scaled prefix receives N, m and B, without hidden prime factors. -/
noncomputable def factorProgression (N m B : ℕ) : Option ℕ :=
  recoverColumns N (blockLeaves N m B) (blockColumns N m B)

theorem factorProgression_sound {N m B d : ℕ}
    (hs : factorProgression N m B=some d) : ProperDivisor N d :=
  recoverColumns_sound hs

/-- The degree is B, including repeated roots and nonunit step sizes. -/
theorem blockPolynomial_degree {R : Type*} [CommRing R] [Nontrivial R] (m B : ℕ) :
    (blockPolynomial (R:=R) m B).natDegree=B := by
  have he : blockPolynomial (R:=R) m B=rootPolynomial (Finset.range B)
      (fun i => -((m*(i+1)+1 : ℕ) : R)) := by
    simp only [blockPolynomial, rootPolynomial, map_neg, sub_neg_eq_add]
  rw [he]
  simpa only [rootPolynomial, Finset.card_range] using
    natDegree_finsetProd_X_sub_C_eq_card (Finset.range B)
      (fun i => -((m*(i+1)+1 : ℕ) : R))

theorem blockLeaves_length (N m B j : ℕ) : (blockLeaves N m B j).length=B := by
  simp only [blockLeaves, List.length_map, List.length_range]

theorem blockColumns_length (N m B : ℕ) : (blockColumns N m B).length=B := by
  simp only [blockColumns, List.length_map, List.length_range]

/-- At most B column and B lazy-leaf GCD queries. Construction of the
single polynomial and its B-point evaluation is charged separately. -/
theorem factorProgression_gcd_count (N m B : ℕ) :
    recoveryGcdCount N (blockLeaves N m B) (blockColumns N m B)≤2*B := by
  have he := recoveryGcdCount_le (n:=N) (cap:=B)
    (columns:=blockColumns N m B) (leaves:=blockLeaves N m B)
    (fun c _ => (blockLeaves_length N m B c.1).le)
  simpa only [blockColumns_length, two_mul] using he

/-- Polynomial evaluation and lazy leaf recovery retain the same exact
GCD; no public column is replaced by an unproved signal. -/
theorem block_column_gcd_eq (N m B j : ℕ) :
    N.gcd ((blockPolynomial (R:=ZMod N) m B).eval
      ((m*(j*B) : ℕ) : ZMod N)).val=N.gcd (blockLeaves N m B j).prod := by
  have he : ((blockLeaves N m B j).prod : ZMod N)=
      (blockPolynomial (R:=ZMod N) m B).eval ((m*(j*B) : ℕ) : ZMod N) := by
    simp only [blockLeaves, Nat.cast_list_prod, List.map_map,
      blockPolynomial, eval_prod, eval_add, eval_X, eval_C]
    rw [← List.prod_toFinset _ (List.nodup_range (n:=B)), List.toFinset_range]
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [Function.comp_apply]
    rw [ZMod.natCast_mod]
    push_cast
    ring
  rw [← he, ZMod.val_natCast, Nat.gcd_rec N,
    Nat.gcd_rec N ((blockLeaves N m B j).prod), Nat.mod_mod]

/-- The full progression lies below N when its public extent does. -/
theorem blockLeaves_bounds {N m B j : ℕ} (hcover : m*B^2+1<N) (hj : j<B) :
    ∀ v∈blockLeaves N m B j, 0<v ∧ v<N := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have hk := (SemiprimeStrassenPrefix.block_integer_bounds (List.mem_range.mp hi) hj).2
  have hv : m*(j*B+i+1)+1<N := by
    have he := Nat.mul_le_mul_left m hk
    omega
  rw [Nat.mod_eq_of_lt hv]
  exact ⟨by omega, hv⟩

/-- Any nonunit represented progression member forces recovery,
including a saturated first column containing both hidden primes. -/
theorem factorProgression_succeeds_of_nonunit {N m B k : ℕ}
    (hcover : m*B^2+1<N) (hk : 0<k) (hkB : k≤B^2)
    (hg : N.gcd (m*k+1)≠1) : ∃ d, factorProgression N m B=some d := by
  obtain ⟨j, i, hj, hi, he⟩ := SemiprimeStrassenPrefix.prefix_integer_decomposition hk hkB
  apply recoverColumns_succeeds
  · intro c hc
    obtain ⟨j', _, rfl⟩ := List.mem_map.mp hc
    exact block_column_gcd_eq N m B j'
  · intro c hc
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hc
    exact blockLeaves_bounds hcover (List.mem_range.mp hj')
  · refine ⟨(j, ((blockPolynomial (R:=ZMod N) m B).eval
        ((m*(j*B) : ℕ) : ZMod N)).val),
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    rw [block_column_gcd_eq]
    intro hunit
    have hv : m*k+1∈blockLeaves N m B j := by
      apply List.mem_map.mpr
      refine ⟨i, List.mem_range.mpr hi, ?_⟩
      rw [← he, Nat.mod_eq_of_lt (by
        have hh := Nat.mul_le_mul_left m hkB
        omega)]
    exact hg (Nat.coprime_list_prod_right_iff.mp hunit _ hv)

/-- The smaller semiprime factor is below B^3 in the sixth-power budget. -/
theorem smaller_factor_le_cube {p q B : ℕ} (hpq : p≤q) (hbudget : p*q≤B^6) : p≤B^3 := by
  apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
  calc
    p^2≤p*q := by simpa only [pow_two] using Nat.mul_le_mul_left p hpq
    _≤B^6 := hbudget
    _=(B^3)^2 := by ring

/-- After the ordinary prefix, an actual common modulus keeps every
new progression leaf below N. This discharges saturated-column recovery. -/
theorem common_progression_extent {p q m B : ℕ} (hp : 1<p) (hpq : p≤q)
    (hmp : m∣p-1) (hsmall : B^2<p) : m*B^2+1<p*q := by
  have hmle := Nat.le_of_dvd (show 0<p-1 by omega) hmp
  have hmul := Nat.mul_le_mul hmle (show B^2≤p-1 by omega)
  have hpp := Nat.mul_le_mul_left p hpq
  have he := Nat.sub_add_cancel (show 1≤p by omega)
  nlinarith

/-- A modulus at least B covers the smaller factor's actual positive
progression index using only B^2 implicit candidates. -/
theorem common_index_le_square {p q m B : ℕ} (hpq : p≤q) (hB : 0<B)
    (hsize : B≤m) (hbudget : p*q≤B^6) {a : ℕ} (hpa : p=m*a+1) : a≤B^2 := by
  have hpB := smaller_factor_le_cube hpq hbudget
  have hmul := Nat.mul_le_mul_right a hsize
  have hprod : B*a≤B*(B^2) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hprod hB

/-- Every prefix-clear semiprime is recovered from an actual common
modulus m≥B, with B roots, B points and at most 2B GCD queries. This is
strictly weaker than the previous m^2≥B^3 recovery size premise. -/
theorem factorProgression_semiprime {p q m B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (hB : 0<B) (hsize : B≤m) (hsmall : B^2<p)
    (hbudget : p*q≤B^6) (hmp : m∣p-1) (hmq : m∣q-1) :
    ∃ d, factorProgression (p*q) m B=some d := by
  have hm : 0<m := hB.trans_le hsize
  obtain ⟨a, _, ha, _, _, hpa, _⟩ :=
    SemiprimeCommonOrder.common_modulus_indices hp.one_lt hq.one_lt hm hpq hmp hmq
  apply factorProgression_succeeds_of_nonunit
    (common_progression_extent hp.one_lt hpq hmp hsmall) ha
    (common_index_le_square hpq hB hsize hbudget hpa)
  rw [← hpa, Nat.gcd_eq_right (dvd_mul_right p q)]
  exact hp.ne_one

/-- An actual known kernel order only needs to reach B for recovery.
The prefix and public group data discharge the common-modulus premises. -/
theorem factorProgression_of_kernel_order {p q m B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p<q) (g : (ZMod (p*q))ˣ) (hraw : g^(p*q-1)=1)
    (hm : orderOf g=m) (hB : 0<B) (hsize : B≤m) (hbudget : p*q≤B^6)
    (hcover : B^2<p*q) (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) :
    ∃ d, factorProgression (p*q) m B=some d := by
  obtain ⟨hmp, hmq⟩ := SemiprimeCommonOrder.kernel_global_order_common hp hq hpq.ne g hraw
  rw [hm] at hmp hmq
  exact factorProgression_semiprime hp hq hpq.le hB hsize
    (SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hp
      (dvd_mul_right p q) hnone) hbudget hmp hmq

/-- Public prime-divisor GCD checks yield the same progression guarantee
without requiring a raw-kernel base or any hidden local-order input. -/
theorem factorProgression_of_public_checks {p q m B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (g : (ZMod (p*q))ˣ) (hB : 0<B) (hsize : B≤m)
    (hbudget : p*q≤B^6) (hcover : B^2<p*q)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) (hpow : g^m=1)
    (hclear : ∀ r, r.Prime → r∣m →
      (p*q).gcd (((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=1) :
    ∃ d, factorProgression (p*q) m B=some d := by
  obtain ⟨hmp, hmq⟩ := SemiprimeCommonOrder.common_modulus_of_public_checks hp hq g
    (hB.trans_le hsize) hpow hclear
  exact factorProgression_semiprime hp hq hpq hB hsize
    (SemiprimeStrassenPrefix.prefix_none_excludes_small_prime hcover hp
      (dvd_mul_right p q) hnone) hbudget hmp hmq

/-- Each prime-divisor test of an actual positive order is globally
nontrivial, so a failed clear check cannot be a whole-modulus residual. -/
theorem order_prime_test_ne_one {G : Type*} [Group G] (g : G) {m r : ℕ}
    (hm : orderOf g=m) (hpos : 0<m) (hr : r.Prime) (hrm : r∣m) :
    g^(m/r)≠1 := by
  intro he
  have hd := orderOf_dvd_of_pow_eq_one he
  rw [hm] at hd
  have hquot : 0<m/r := Nat.div_pos (Nat.le_of_dvd hpos hrm) hr.pos
  have hle := Nat.le_of_dvd hquot hd
  have hlt := Nat.div_lt_self hpos hr.one_lt
  omega

/-- Once an actual known order reaches B, every prefix-clear semiprime
has a factor in its prime-divisor power tests or the compressed
progression. The clear-check assumption is discharged by this dichotomy. -/
theorem known_order_factor_or_progression {p q m B : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≤q) (g : (ZMod (p*q))ˣ) (hm : orderOf g=m)
    (hB : 0<B) (hsize : B≤m) (hbudget : p*q≤B^6) (hcover : B^2<p*q)
    (hnone : SemiprimeStrassenPrefix.factorPrefix (p*q) B=none) :
    (∃ r, r.Prime ∧ r∣m ∧ ∃ d,
      checkedSignal (p*q) (((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=some d) ∨
      ∃ d, factorProgression (p*q) m B=some d := by
  classical
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hmpos := hB.trans_le hsize
  by_cases hclear : ∀ r, r.Prime → r∣m →
      (p*q).gcd (((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1).val=1
  · right
    apply factorProgression_of_public_checks hp hq hpq g hB hsize hbudget hcover hnone _ hclear
    rw [← hm]
    exact pow_orderOf_eq_one g
  · left
    push Not at hclear
    obtain ⟨r, hr, hrm, hnotone⟩ := hclear
    have hne := order_prime_test_ne_one g hm hmpos hr hrm
    let z : ZMod (p*q) := ((g^(m/r) : (ZMod (p*q))ˣ) : ZMod (p*q))-1
    have hnotN : (p*q).gcd z.val≠p*q := by
      intro he
      have hz := SemiprimeSourceHead.residual_zero_of_gcd_eq_modulus z he
      exact hne (Units.ext (sub_eq_zero.mp hz))
    have hNpos := Nat.mul_pos hp.pos hq.pos
    have hle := Nat.gcd_le_left z.val hNpos
    have hpos := Nat.gcd_pos_of_pos_left z.val hNpos
    have hproper : 1<(p*q).gcd z.val ∧ (p*q).gcd z.val<p*q := by
      change (p*q).gcd z.val≠1 at hnotone
      omega
    refine ⟨r, hr, hrm, (p*q).gcd z.val, ?_⟩
    exact if_pos hproper

/-- Retain equal residue labels before any deflation. Ordered merge
uses one comparison per visited pair, without a Cartesian pair scan. -/
def matchSorted : List (ℕ×ℕ) → List (ℕ×ℕ) → Option (ℕ×ℕ)
  | [], _ => none
  | _, [] => none
  | x::xs, y::ys =>
    if x.1=y.1 then some (x.2, y.2)
    else if x.1<y.1 then matchSorted xs (y::ys)
    else matchSorted (x::xs) ys
termination_by xs ys => xs.length+ys.length

/-- Comparisons in the actual ordered merge; sorting is separately charged. -/
def matchComparisons : List (ℕ×ℕ) → List (ℕ×ℕ) → ℕ
  | [], _ => 0
  | _, [] => 0
  | x::xs, y::ys =>
    1+if x.1=y.1 then 0
      else if x.1<y.1 then matchComparisons xs (y::ys)
      else matchComparisons (x::xs) ys
termination_by xs ys => xs.length+ys.length

theorem matchSorted_sound {xs ys : List (ℕ×ℕ)} {i j : ℕ}
    (hs : matchSorted xs ys=some (i,j)) :
    ∃ x∈xs, ∃ y∈ys, x.1=y.1 ∧ x.2=i ∧ y.2=j := by
  induction xs generalizing ys with
  | nil => simp [matchSorted] at hs
  | cons x xs ih =>
    induction ys with
    | nil => simp [matchSorted] at hs
    | cons y ys ihy =>
      by_cases he : x.1=y.1
      · have hh : (x.2,y.2)=(i,j) := by simpa only [matchSorted, if_pos he,
          Option.some.injEq] using hs
        exact ⟨x, by simp, y, by simp, he, (Prod.mk.inj hh).1, (Prod.mk.inj hh).2⟩
      · by_cases hlt : x.1<y.1
        · obtain ⟨u, hu, v, hv, heq, hi, hj⟩ := ih
            (by simpa only [matchSorted, if_neg he, if_pos hlt] using hs)
          exact ⟨u, List.mem_cons_of_mem _ hu, v, hv, heq, hi, hj⟩
        · obtain ⟨u, hu, v, hv, heq, hi, hj⟩ := ihy
            (by simpa only [matchSorted, if_neg he, if_neg hlt] using hs)
          exact ⟨u, hu, v, List.mem_cons_of_mem _ hv, heq, hi, hj⟩

/-- Sorted merge cannot miss an equal retained residue, including
duplicate values within either source list. -/
theorem matchSorted_none_no_common {xs ys : List (ℕ×ℕ)}
    (hx : xs.Pairwise (fun x y => x.1≤y.1))
    (hy : ys.Pairwise (fun x y => x.1≤y.1)) (hn : matchSorted xs ys=none) :
    ∀ x∈xs, ∀ y∈ys, x.1≠y.1 := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      obtain ⟨hxt, hxsorted⟩ := List.pairwise_cons.mp hx
      obtain ⟨hyt, hysorted⟩ := List.pairwise_cons.mp hy
      by_cases he : x.1=y.1
      · simp only [matchSorted, if_pos he] at hn
        contradiction
      · by_cases hlt : x.1<y.1
        · have ht : matchSorted xs (y::ys)=none := by
            simpa only [matchSorted, if_neg he, if_pos hlt] using hn
          intro u hu v hv huv
          rcases List.mem_cons.mp hu with rfl | hu
          · have hle : y.1≤v.1 := by
              rcases List.mem_cons.mp hv with rfl | hv
              · exact le_rfl
              · exact hyt v hv
            omega
          · exact ih hxsorted hy ht u hu v hv huv
        · have ht : matchSorted (x::xs) ys=none := by
            simpa only [matchSorted, if_neg he, if_neg hlt] using hn
          intro u hu v hv huv
          rcases List.mem_cons.mp hv with rfl | hv
          · have hle : x.1≤u.1 := by
              rcases List.mem_cons.mp hu with rfl | hu
              · exact le_rfl
              · exact hxt u hu
            omega
          · exact ihy hysorted ht u hu v hv huv

theorem matchComparisons_le (xs ys : List (ℕ×ℕ)) :
    matchComparisons xs ys≤xs.length+ys.length := by
  induction xs generalizing ys with
  | nil => simp [matchComparisons]
  | cons x xs ih =>
    induction ys with
    | nil => simp [matchComparisons]
    | cons y ys ihy =>
      rw [matchComparisons]
      split_ifs with he hlt
      · simp only [List.length_cons]
        omega
      · have hh := ih (y::ys)
        simp only [List.length_cons] at hh ⊢
        omega
      · simp only [List.length_cons] at ihy ⊢
        omega

/-- Baby and giant indices cover every positive exponent up to b². -/
theorem bounded_exponent_cover {b k : ℕ} (hk : 0<k) (hkB : k≤b^2) :
    ∃ i j, i<b ∧ 0<j ∧ j≤b ∧ k+i=j*b := by
  obtain ⟨h, v, hh, hv, he⟩ := SemiprimeStrassenPrefix.prefix_integer_decomposition hk hkB
  refine ⟨b-(v+1), h+1, by omega, by omega, by omega, ?_⟩
  have hs := Nat.sub_add_cancel (show v+1≤b by omega)
  nlinarith

/-- Any retained equality certifies a positive annihilating exponent
at most b². Later prime-divisor checks recover its exact order or a factor. -/
theorem collision_annihilator {G : Type*} [Group G] (g : G) {b i j : ℕ}
    (hi : i<b) (hj : 0<j) (hjb : j≤b) (he : g^(j*b)=g^i) :
    0<j*b-i ∧ j*b-i≤b^2 ∧ g^(j*b-i)=1 := by
  have hB : 0<b := by omega
  have hlow := Nat.mul_le_mul_right b (show 1≤j by omega)
  have hupper := Nat.mul_le_mul_right b hjb
  have hpos : i<j*b := by omega
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [pow_two] using (Nat.sub_le (j*b) i).trans hupper
  have hidx := Nat.sub_add_cancel hpos.le
  have hh : g^(j*b-i)*g^i=1*g^i := by
    rw [← pow_add, hidx, he, one_mul]
  exact mul_right_cancel hh

/-- Every finite positive order in the bounded interval supplies a
retained baby/giant equality. This does not assert that all orders fit. -/
theorem order_bounded_has_collision {G : Type*} [Group G] (g : G) {b : ℕ}
    (hpos : 0<orderOf g) (hbound : orderOf g≤b^2) :
    ∃ i j, i<b ∧ 0<j ∧ j≤b ∧ g^(j*b)=g^i := by
  obtain ⟨i, j, hi, hj, hjb, he⟩ := bounded_exponent_cover hpos hbound
  refine ⟨i, j, hi, hj, hjb, ?_⟩
  rw [← he, pow_add, pow_orderOf_eq_one, one_mul]

/-- Retain b baby powers and their original exponents. -/
noncomputable def babyRecords (N b : ℕ) (g : (ZMod N)ˣ) : List (ℕ×ℕ) :=
  (List.range b).map fun i => (((g^i : (ZMod N)ˣ) : ZMod N).val, i)

/-- Retain b giant powers and their positive block labels. -/
noncomputable def giantRecords (N b : ℕ) (g : (ZMod N)ˣ) : List (ℕ×ℕ) :=
  (List.range b).map fun j => (((g^((j+1)*b) : (ZMod N)ˣ) : ZMod N).val, j+1)

/-- Sorting preserves the original residue and exponent records. -/
def sortedRecords (records : List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  records.mergeSort (fun x y => decide (x.1≤y.1))

theorem sortedRecords_pairwise (records : List (ℕ×ℕ)) :
    (sortedRecords records).Pairwise (fun x y => x.1≤y.1) := by
  have he := List.pairwise_mergeSort (le:=fun x y : ℕ×ℕ => decide (x.1≤y.1))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _)
    records
  simpa only [sortedRecords, decide_eq_true_eq] using he

theorem mem_sortedRecords {records : List (ℕ×ℕ)} {record : ℕ×ℕ} :
    record∈sortedRecords records ↔ record∈records := List.mem_mergeSort

/-- Search actual retained powers with two sorted lists and one merge. -/
noncomputable def boundedCollision (N b : ℕ) (g : (ZMod N)ˣ) : Option (ℕ×ℕ) :=
  matchSorted (sortedRecords (babyRecords N b g)) (sortedRecords (giantRecords N b g))

/-- There are b baby and b giant records; sorting does not enlarge them. -/
theorem bounded_records_lengths (N b : ℕ) (g : (ZMod N)ˣ) :
    (sortedRecords (babyRecords N b g)).length=b ∧
      (sortedRecords (giantRecords N b g)).length=b := by
  simp only [sortedRecords, List.length_mergeSort, babyRecords, giantRecords,
    List.length_map, List.length_range, and_self]

/-- The actual lookup uses at most 2b merge comparisons. Its two sorts
and residue-power construction are separate, charged setup steps. -/
theorem boundedCollision_merge_count (N b : ℕ) (g : (ZMod N)ˣ) :
    matchComparisons (sortedRecords (babyRecords N b g))
      (sortedRecords (giantRecords N b g))≤2*b := by
  have he := matchComparisons_le (sortedRecords (babyRecords N b g))
    (sortedRecords (giantRecords N b g))
  obtain ⟨hb, hg⟩ := bounded_records_lengths N b g
  simpa only [hb, hg, two_mul] using he

/-- Every returned match from the actual public powers certifies a
positive bounded annihilator before order peeling. -/
theorem boundedCollision_annihilator {N b i j : ℕ} [NeZero N] (g : (ZMod N)ˣ)
    (hs : boundedCollision N b g=some (i,j)) :
    0<j*b-i ∧ j*b-i≤b^2 ∧ g^(j*b-i)=1 := by
  obtain ⟨x, hx, y, hy, hv, hxi, hyj⟩ := matchSorted_sound hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (mem_sortedRecords.mp hx)
  obtain ⟨v, hvb, rfl⟩ := List.mem_map.mp (mem_sortedRecords.mp hy)
  dsimp only at hxi hyj hv
  rw [← hxi, ← hyj]
  apply collision_annihilator g (List.mem_range.mp hu) (by omega) (by
    have hh := List.mem_range.mp hvb; omega)
  apply Units.ext
  exact ZMod.val_injective N hv.symm

/-- Every actual finite global order up to b² is detected by the
implemented ordered lookup. Orders above the bound remain explicit. -/
theorem boundedCollision_succeeds {N b : ℕ} (g : (ZMod N)ˣ)
    (hbound : orderOf g≤b^2) : ∃ pair, boundedCollision N b g=some pair := by
  obtain ⟨i, j, hi, hj, hjb, he⟩ := order_bounded_has_collision g (orderOf_pos g) hbound
  have hbmem : (((g^i : (ZMod N)ˣ) : ZMod N).val, i)∈
      sortedRecords (babyRecords N b g) := by
    apply mem_sortedRecords.mpr
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hgmem : (((g^(j*b) : (ZMod N)ˣ) : ZMod N).val, j)∈
      sortedRecords (giantRecords N b g) := by
    apply mem_sortedRecords.mpr
    apply List.mem_map.mpr
    refine ⟨j-1, List.mem_range.mpr (by omega), ?_⟩
    have hh : j-1+1=j := by omega
    simp only [hh]
  cases hs : boundedCollision N b g with
  | some pair => exact ⟨pair, rfl⟩
  | none =>
    have hn := matchSorted_none_no_common
      (sortedRecords_pairwise (babyRecords N b g))
      (sortedRecords_pairwise (giantRecords N b g)) hs _ hbmem _ hgmem
    apply False.elim
    exact hn (congrArg (fun u : (ZMod N)ˣ => (u : ZMod N).val) he.symm)

/-- Exhausting this actual ordered lookup certifies a genuinely larger
order; it does not infer that the input has been factored. -/
theorem boundedCollision_none_large {N b : ℕ} (g : (ZMod N)ˣ)
    (hn : boundedCollision N b g=none) : b^2<orderOf g := by
  by_contra hh
  obtain ⟨pair, hs⟩ := boundedCollision_succeeds (b:=b) g (by omega)
  rw [hn] at hs
  contradiction

/-- The actual exhaustion outcome is exactly the order-above-cap
condition. Equality labels and their positive distance are retained. -/
theorem boundedCollision_none_iff_large {N b : ℕ} [NeZero N] (g : (ZMod N)ˣ) :
    boundedCollision N b g=none ↔ b^2<orderOf g := by
  constructor
  · exact boundedCollision_none_large g
  · intro hlarge
    cases hs : boundedCollision N b g with
    | none => rfl
    | some pair =>
      obtain ⟨i,j⟩ := pair
      obtain ⟨hpos, hbound, hpow⟩ := boundedCollision_annihilator g hs
      have hd := orderOf_dvd_of_pow_eq_one hpow
      have he := Nat.le_of_dvd hpos hd
      omega

/-- This public order-four base lies below the old wrap size threshold. -/
theorem control_small_common_powers :
    (2535 : ZMod 2929)^4=1 ∧ (2535 : ZMod 2929)^2=2928 := by
  norm_num
  reduce_mod_char
  decide

/-- The complete divisor test is supplied by one public prime check. -/
theorem control_small_common_certificate (g : (ZMod 2929)ˣ)
    (hg : (g : ZMod 2929)=2535) : g^4=1 ∧
      ∀ r, r.Prime → r∣4 →
        (2929 : ℕ).gcd (((g^(4/r) : (ZMod 2929)ˣ) : ZMod 2929)-1).val=1 := by
  obtain ⟨hpw, hpw2⟩ := control_small_common_powers
  constructor
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using hpw
  · intro r hr hd
    have he : r=2 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
      (hr.dvd_of_dvd_pow (by simpa only [show (4 : ℕ)=2^2 from rfl] using hd))
    subst r
    simp only [show (4/2 : ℕ)=2 from rfl, Units.val_pow_eq_pow_val, hg, hpw2]
    decide

set_option maxRecDepth 32768 in
/-- The previous eight carry candidates all miss this prefix-clear
semiprime. The common progression covers it with modulus equal to B. -/
theorem control_small_common_arithmetic :
    Nat.Prime 29 ∧ Nat.Prime 101 ∧ 29*101=2929 ∧
    (4 : ℕ)^2<29 ∧ 2929≤(4 : ℕ)^6 ∧ (4 : ℕ)^2<4^3 ∧
    SemiprimeCommonOrder.recoverWrapped 2929 4 4=none := by
  norm_num [SemiprimeCommonOrder.recoverWrapped, SemiprimeCommonOrder.wrappedCandidate,
    SemiprimeCommonOrder.indexSum, SemiprimeCommonOrder.indexProduct,
    SemiprimeCommonOrder.orderQuotient, scanProper, checkedSignal,
    List.range_eq_range', List.range'_succ]

set_option maxRecDepth 32768 in
/-- The actual public power certificate and failed ordinary prefix
discharge every arithmetic premise of progression recovery. -/
theorem control_small_common_recovers (g : (ZMod 2929)ˣ)
    (hg : (g : ZMod 2929)=2535) : ∃ d, factorProgression 2929 4 4=some d := by
  obtain ⟨hpow, hclear⟩ := control_small_common_certificate g hg
  apply factorProgression_of_public_checks (p:=29) (q:=101)
    (by norm_num) (by norm_num) (by norm_num) g (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) _ hpow hclear
  apply (SemiprimeStrassenPrefix.prefix_none_iff_clear (by norm_num)).mpr
  norm_num [SemiprimeGroupCoverage.prefixProduct_eq_factorial]

set_option maxRecDepth 32768 in
/-- The actual four-point polynomial recovery returns 29. No hidden
factor is supplied to its leaf callback or its column construction. -/
theorem control_small_progression_result : factorProgression 2929 4 4=some 29 := by
  simp only [factorProgression, blockColumns, blockPolynomial_eval, ZMod.val_natCast]
  norm_num [List.range_eq_range', List.range'_succ, Finset.prod_range_succ, recoverColumns]

/-- The formerly active unknown rough control's order is discovered
inside the charged 2B-by-2B exponent cover, without factoring N-1. -/
theorem control_active_rough_bounded (g : (ZMod 13747)ˣ)
    (hg : (g : ZMod 13747)=4) : ∃ pair, boundedCollision 13747 10 g=some pair := by
  have hm := (SemiprimeCommonOrder.control_active_rough_kernel_order g hg).1
  apply boundedCollision_succeeds
  rw [hm]
  norm_num

set_option maxRecDepth 32768 in
/-- The literal ordered search derives exponent 3*10-1=29 itself.
This exact control supplies no proposed order to the search. -/
theorem control_active_rough_collision (g : (ZMod 13747)ˣ)
    (hg : (g : ZMod 13747)=4) : boundedCollision 13747 10 g=some (1,3) := by
  simp only [boundedCollision, babyRecords, giantRecords, Units.val_pow_eq_pow_val, hg]
  have hv (i : ℕ) : ((4 : ZMod 13747)^i).val=(4^i)%13747 := by
    change (((4 : ℕ) : ZMod 13747)^i).val=(4^i)%13747
    rw [← Nat.cast_pow, ZMod.val_natCast]
  simp_rw [hv]
  norm_num [sortedRecords, List.range_eq_range', List.range'_succ, List.mergeSort,
    List.merge, matchSorted]

/-- A literal base with a prime order just beyond the chosen cap. -/
theorem control_large_order_powers : (64 : ZMod 14608133)^1103=1 := by
  reduce_mod_char

set_option maxRecDepth 32768 in
/-- The exhaustion control is an actual prefix-clear semiprime at
B=16, with a public unit base and order exceeding the fixed cap. -/
theorem control_large_arithmetic :
    Nat.Prime 2207 ∧ Nat.Prime 6619 ∧ 2207*6619=14608133 ∧
    (16 : ℕ)^2<2207 ∧ (15 : ℕ)^6<14608133 ∧ 14608133≤(16 : ℕ)^6 ∧
    Nat.gcd 14608133 64=1 ∧ (16 : ℕ)^2*4<1103 := by
  norm_num

/-- The large-order control keeps exhaustion explicit rather than
reporting a factor or accepting its proposed order as algorithm input. -/
theorem control_large_bounded_exhausted (g : (ZMod 14608133)ˣ)
    (hg : (g : ZMod 14608133)=64) : orderOf g=1103 ∧
      boundedCollision 14608133 32 g=none ∧ g^(14608133-1)=1 := by
  have hpow : g^1103=1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, hg, Units.val_one] using control_large_order_powers
  have hm : orderOf g=1103 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hpow
    intro r hr hd he
    have heq : r=1103 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd
    subst r
    have hv := congrArg (fun u : (ZMod 14608133)ˣ => (u : ZMod 14608133)) he
    simp only [hg, Units.val_one,
      Nat.div_self (by decide : 0<1103), pow_one] at hv
    exact (by decide : (64 : ZMod 14608133)≠1) hv
  refine ⟨hm, (boundedCollision_none_iff_large g).mpr ?_, ?_⟩
  · rw [hm]
    norm_num
  · have he : (14608133-1 : ℕ)=1103*13244 := by norm_num
    rw [he, pow_mul, hpow, one_pow]

end RiemannGaussian.SemiprimeProgressionPrefix
