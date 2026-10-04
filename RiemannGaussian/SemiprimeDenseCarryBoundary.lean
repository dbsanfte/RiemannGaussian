/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDenseRowCarries
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Carry boundaries of the actual implicit dense source

An adjacent-product cancellation retains every floor jump and endpoint;
checked unit multipliers preserve the entire public GCD. The public
numerator map has fibers of size at most two at prime auxiliary modulus.
Consequently an explicit boundary-factor construction still has quadratic
total input size, while the initial Euclidean quotient count has a nearly
linear bound. Neither result prices a complete recursive detector. The
input floor restricts that construction, not all Euclidean circuits,
implicit algorithms, or factorization.
-/

namespace RiemannGaussian.SemiprimeDenseCarryBoundary

open SemiprimeQuotientRows SemiprimeDenseRowCoverage SemiprimeDenseRowCarries
open scoped BigOperators
open Polynomial

/-- A single increment of the retained leading floor carry. -/
def carryJump (m u t : ℕ) : ℕ := u*(t+1)/m-u*t/m

/-- The actual implicit curve, including its original orientation. -/
def curveValue {G : Type*} [CommGroup G] (A B : G) (m u : ℕ)
    (negative : Bool) (t : ℕ) : G :=
  A^t*B^(-((u*t/m+(if negative then 1 else 0) : ℕ) : ℤ))

/-- The public descriptor query is this literal curve. -/
theorem progressionValue_curve {G : Type*} [CommGroup G] (m t : ℕ)
    (negative : Bool) (s : ProgressionSeed G) :
    progressionValue m t negative s=
      curveValue s.step s.carryStep m s.slope negative t := rfl

/-- A slope below the modulus has only zero or one carry increments. -/
theorem carryJump_le_one {m u t : ℕ} (hu : u<m) : carryJump m u t≤1 := by
  have h := Nat.add_div_le_div_add_div_add_one (u*t) u m
  rw [Nat.div_eq_of_lt hu] at h
  unfold carryJump
  rw [Nat.mul_succ]
  omega

/-- The next carry retains its whole increment without truncated subtraction. -/
theorem carryJump_add (m u t : ℕ) :
    u*t/m+carryJump m u t=u*(t+1)/m := by
  have h : u*t/m≤u*(t+1)/m :=
    Nat.div_le_div_right (Nat.mul_le_mul_left u (Nat.le_succ t))
  unfold carryJump
  omega

/-- The exact query step includes the carry rather than suppressing it. -/
theorem curveValue_step {G : Type*} [CommGroup G] (A B : G) (m u t : ℕ)
    (negative : Bool) :
    curveValue A B m u negative (t+1)=
      A*curveValue A B m u negative t*B^(-(carryJump m u t : ℤ)) := by
  have hk : u*(t+1)/m+(if negative then 1 else 0)=
      (u*t/m+(if negative then 1 else 0))+carryJump m u t := by
    have h := carryJump_add m u t
    omega
  simp only [curveValue,pow_succ,hk,Nat.cast_add,neg_add,zpow_add]
  ac_rfl

/-- No-jump edges are the exact factors cancelled by an adjacent shift. -/
theorem curveValue_step_no_jump {G : Type*} [CommGroup G] (A B : G)
    {m u t : ℕ} (negative : Bool) (hjump : carryJump m u t=0) :
    curveValue A B m u negative (t+1)=A*curveValue A B m u negative t := by
  rw [curveValue_step,hjump]
  simp

/-- Total carry variation is the actual endpoint floor. -/
theorem carryJump_sum (m u L : ℕ) :
    ∑ t ∈ Finset.range L, carryJump m u t=u*L/m := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,ih]
    exact carryJump_add m u L

/-- The floor jumps retained by a complete curve's boundary polynomial. -/
def jumpSet (m u : ℕ) : Finset ℕ := (Finset.range m).filter (fun t => carryJump m u t=1)

/-- Every slope u<m contributes exactly u boundary factors. -/
theorem jumpSet_card {m u : ℕ} (hm : 0<m) (hu : u<m) :
    (jumpSet m u).card=u := by
  have hsum : (jumpSet m u).card=∑ t ∈ Finset.range m, carryJump m u t := by
    simp only [jumpSet,Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _ht
    have h := carryJump_le_one (t:=t) hu
    by_cases he : carryJump m u t=1
    · simp [he]
    · have hz : carryJump m u t=0 := by omega
      simp [hz]
  rw [hsum,carryJump_sum,Nat.mul_div_cancel _ hm]

/-- The actual seed numerator satisfies its square-residue equation. -/
theorem numerator_square {N m j : ℕ} (hm : 0<m) (hj : j.Coprime m) :
    (representative N m j 1 : ZMod m)*(j : ZMod m)^2=(N : ZMod m) := by
  have hr := representative_congruence (N:=N) (j:=j) (t:=1) hm
  have hi := publicInverse_correct hj
  have hrz := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hr
  have hiz := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hi
  push_cast at hrz hiz
  rw [hrz]
  calc
    _=(N : ZMod m)*((j : ZMod m)*(publicInverse m j : ZMod m))^2 := by ring
    _=_ := by rw [hiz]; ring

/-- A correct public unit prefix ensures the numerator is nonzero modulo m. -/
theorem numerator_ne_zero {N m j : ℕ} (hm : 1<m) (hN : m.Coprime N)
    (hj : j.Coprime m) : (representative N m j 1 : ZMod m)≠0 := by
  intro hz
  have hs := numerator_square (N:=N) (by omega) hj
  rw [hz,zero_mul] at hs
  have hd := (ZMod.natCast_eq_zero_iff N m).mp hs.symm
  have he := Nat.dvd_gcd (dvd_refl m) hd
  rw [hN] at he
  have hmone := Nat.le_of_dvd (by norm_num : 0<1) he
  omega

/-- Only nonzero public residues are included in the descriptor cache. -/
def residues (m : ℕ) : Finset ℕ := (Finset.range m).erase 0

/-- The descriptor residue range retains its exact positive bounds. -/
theorem mem_residues {m j : ℕ} : j∈residues m ↔ 0<j ∧ j<m := by
  simp only [residues,Finset.mem_erase,Finset.mem_range]
  omega

/-- Every retained residue is a unit at prime auxiliary modulus. -/
theorem residue_coprime {m j : ℕ} (hm : m.Prime) (hj : j∈residues m) :
    j.Coprime m :=
  (hm.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (mem_residues.mp hj).1 (mem_residues.mp hj).2)).symm

/-- Equal seed numerators have only the two square-root residue aliases. -/
theorem numerator_fiber_pair {N m i j : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (hi : i∈residues m) (hj : j∈residues m)
    (he : representative N m i 1=representative N m j 1) : i=j ∨ i+j=m := by
  let : Fact m.Prime := ⟨hm⟩
  have his := mem_residues.mp hi
  have hjs := mem_residues.mp hj
  have hiq := numerator_square (N:=N) hm.pos (residue_coprime hm hi)
  have hjq := numerator_square (N:=N) hm.pos (residue_coprime hm hj)
  rw [he] at hiq
  have hs : (i : ZMod m)^2=(j : ZMod m)^2 :=
    mul_left_cancel₀ (numerator_ne_zero hm.one_lt hN (residue_coprime hm hj))
      (hiq.trans hjq.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hz | hz
  · have hr := (ZMod.natCast_eq_natCast_iff' i j m).mp hz
    exact Or.inl (by simpa only [Nat.mod_eq_of_lt his.2,Nat.mod_eq_of_lt hjs.2] using hr)
  · have hz₀ : ((i+j : ℕ) : ZMod m)=0 := by push_cast; rw [hz]; ring
    obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff (i+j) m).mp hz₀
    have hk₀ : 0<k := by
      by_contra hn
      have he₀ : k=0 := by omega
      rw [he₀,mul_zero] at hk
      omega
    have hk₂ : k<2 := by nlinarith [hm.pos]
    have hk₁ : k=1 := by omega
    rw [hk₁,mul_one] at hk
    exact Or.inr hk

/-- Every numerator fiber has size at most two, for the actual public inverse map. -/
theorem numerator_fiber_card {N m v : ℕ} (hm : m.Prime) (hN : m.Coprime N) :
    ((residues m).filter (fun j => representative N m j 1=v)).card≤2 := by
  classical
  let S := (residues m).filter (fun j => representative N m j 1=v)
  change S.card≤2
  by_cases hS : S.Nonempty
  · obtain ⟨j,hj⟩ := hS
    have hs : S⊆({j,m-j} : Finset ℕ) := by
      intro i hi
      have hi₀ := Finset.mem_filter.mp hi
      have hj₀ := Finset.mem_filter.mp hj
      rcases numerator_fiber_pair hm hN hi₀.1 hj₀.1 (hi₀.2.trans hj₀.2.symm) with he | he
      · simp [he]
      · have hei : i=m-j := by omega
        simp [hei]
    have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le j {m-j})
    simpa only [Finset.card_singleton] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- Small numerators occupy at most twice their available value range. -/
theorem small_numerator_card {N m K : ℕ} (hm : m.Prime) (hN : m.Coprime N) :
    ((residues m).filter (fun j => representative N m j 1<K)).card≤2*K := by
  have he := Finset.sum_card_fiberwise_eq_card_filter (residues m) (Finset.range K)
    (fun j => representative N m j 1)
  simp only [Finset.mem_range] at he
  rw [←he]
  calc
    _≤∑ _v ∈ Finset.range K, 2 :=
      Finset.sum_le_sum (fun _ _ => numerator_fiber_card hm hN)
    _=2*K := by simp [Nat.mul_comm]

/-- Nonnegative structural costs transfer to the complete slope range
with multiplicity at most two. This can also fund amortized upper bounds. -/
theorem numerator_weighted_bound {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (w : ℕ→ℕ) :
    (∑ j∈residues m, w (representative N m j 1))≤2*∑ u∈residues m, w u := by
  have hmap : ∀ j∈residues m, representative N m j 1∈residues m := by
    intro j hj
    apply mem_residues.mpr
    refine ⟨?_,Nat.mod_lt _ hm.pos⟩
    have hn := numerator_ne_zero hm.one_lt hN (residue_coprime hm hj)
    by_contra hz
    have he : representative N m j 1=0 := by omega
    rw [he,Nat.cast_zero] at hn
    exact hn rfl
  rw [←Finset.sum_fiberwise_of_maps_to' hmap w,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _hu
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact Nat.mul_le_mul_right (w u) (numerator_fiber_card hm hN)

/-- Initial Euclidean quotient work is bounded by the complete harmonic
integer sum; the quadratic boundary count does not rule out this saving. -/
theorem initial_quotient_sum_bound {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N) :
    (∑ j∈residues m, m/representative N m j 1)≤2*∑ u∈residues m, m/u :=
  numerator_weighted_bound hm hN (fun u => m/u)

/-- The first Euclidean quotient stage has a nearly linear arithmetic
count. Later stages and collision-product evaluation remain separate costs. -/
theorem initial_quotient_log_bound {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N) :
    ((∑ j∈residues m, m/representative N m j 1 : ℕ) : ℝ)≤
      2*(m : ℝ)*(1+Real.log m) := by
  have hb : (∑ j∈residues m, ((m/representative N m j 1 : ℕ) : ℝ))≤
      2*∑ u∈residues m, ((m/u : ℕ) : ℝ) := by
    exact_mod_cast initial_quotient_sum_bound hm hN
  have hf : (∑ u∈residues m, ((m/u : ℕ) : ℝ))≤(m : ℝ)*(harmonic m : ℝ) := by
    calc
      _≤∑ u∈residues m, (m : ℝ)/(u : ℝ) :=
        Finset.sum_le_sum (fun _ _ => Nat.cast_div_le)
      _=(m : ℝ)*∑ u∈residues m, (u : ℝ)⁻¹ := by
        simp only [div_eq_mul_inv,Finset.mul_sum]
      _≤(m : ℝ)*∑ u∈Finset.Icc 1 m, (u : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          have h := mem_residues.mp hu
          exact Finset.mem_Icc.mpr ⟨by omega,h.2.le⟩
        · intro _ _ _
          positivity
      _=(m : ℝ)*(harmonic m : ℝ) := by
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log m)
    (by positivity : (0 : ℝ)≤m)
  push_cast
  nlinarith only [hb,hf,hh]

/-- The public descriptor range has exactly m-1 residues. -/
theorem residues_card {m : ℕ} (hm : 0<m) : (residues m).card=m-1 := by
  simp only [residues,Finset.card_erase_of_mem (Finset.mem_range.mpr hm),Finset.card_range]

/-- One explicit jump factor per edge of every actual cached curve. -/
def boundaryLoad (N m : ℕ) : ℕ :=
  ∑ j ∈ residues m, (jumpSet m (representative N m j 1)).card

/-- The exact boundary input count is the sum of the actual seed numerators. -/
theorem boundaryLoad_eq {N m : ℕ} (hm : 0<m) :
    boundaryLoad N m=∑ j ∈ residues m, representative N m j 1 := by
  unfold boundaryLoad
  apply Finset.sum_congr rfl
  intro j _hj
  exact jumpSet_card hm (Nat.mod_lt _ hm)

/-- Explicit boundary construction has a quadratic whole-source input floor.
This counts retained factors; it does not lower-bound all implicit algorithms. -/
theorem boundaryLoad_quadratic {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (hlarge : 8≤m) : m^2≤32*boundaryLoad N m := by
  let K := m/4
  let S := (residues m).filter (fun j => K≤representative N m j 1)
  have hlow := small_numerator_card (K:=K) hm hN
  have hpart := Finset.card_filter_add_card_filter_not
    (s:=residues m) (fun j => representative N m j 1<K)
  simp only [Nat.not_lt] at hpart
  rw [residues_card hm.pos] at hpart
  have hcount : m≤4*S.card := by dsimp only [S,K] at *; omega
  have hK : m≤8*K := by dsimp only [K]; omega
  have hs : K*S.card≤boundaryLoad N m := by
    rw [boundaryLoad_eq hm.pos]
    calc
      _=∑ _j ∈ S, K := by simp [Nat.mul_comm]
      _≤∑ j ∈ S, representative N m j 1 :=
        Finset.sum_le_sum (fun _ hj => (Finset.mem_filter.mp hj).2)
      _≤∑ j ∈ residues m, representative N m j 1 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hmul := Nat.mul_le_mul hK hcount
  calc
    m^2=m*m := by ring
    _≤(8*K)*(4*S.card) := hmul
    _=32*(K*S.card) := by ring
    _≤32*boundaryLoad N m := Nat.mul_le_mul_left 32 hs

/-- The initial edge is never a carry boundary for a canonical slope. -/
theorem carryJump_zero {m u : ℕ} (hu : u<m) : carryJump m u 0=0 := by
  simp [carryJump,Nat.div_eq_of_lt hu]

/-- Complete carry boundaries lie among the original positive denominators. -/
theorem jumpSet_positive {m u : ℕ} (hu : u<m) :
    jumpSet m u=(residues m).filter (fun t => carryJump m u t=1) := by
  ext t
  by_cases ht : t=0
  · subst t
    simp [jumpSet,residues,carryJump_zero hu]
  · simp [jumpSet,residues,ht]

/-- The original source polynomial retains precisely 1<=t<m. -/
noncomputable def sourcePolynomial {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) : R[X] :=
  ∏ t ∈ residues m, (X-C (curveValue (G:=Rˣ) A B m u negative t : R))

/-- The adjacent shift retains each original root and the public unit A. -/
noncomputable def shiftedPolynomial {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) : R[X] :=
  ∏ t ∈ residues m, (X-C ((A*curveValue A B m u negative t : Rˣ) : R))

/-- Successor roots retain their exact floor carries and endpoint. -/
noncomputable def successorPolynomial {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) : R[X] :=
  ∏ t ∈ residues m, (X-C (curveValue (G:=Rˣ) A B m u negative (t+1) : R))

/-- Before-jump factors required by adjacent-product cancellation. -/
noncomputable def beforePolynomial {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) : R[X] :=
  ∏ t ∈ jumpSet m u, (X-C ((A*curveValue A B m u negative t : Rˣ) : R))

/-- After-jump factors retained on the other side of the same identity. -/
noncomputable def afterPolynomial {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) : R[X] :=
  ∏ t ∈ jumpSet m u, (X-C (curveValue (G:=Rˣ) A B m u negative (t+1) : R))

/-- Boundary products are monic, even over a composite-modulus ring. -/
theorem beforePolynomial_monic {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) :
    (beforePolynomial A B m u negative).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- The second boundary retains the same monic degree. -/
theorem afterPolynomial_monic {R : Type*} [CommRing R]
    (A B : Rˣ) (m u : ℕ) (negative : Bool) :
    (afterPolynomial A B m u negative).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/-- Explicit before-boundary degree is exactly the public numerator. -/
theorem beforePolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (A B : Rˣ) {m u : ℕ} (hm : 0<m) (hu : u<m) (negative : Bool) :
    (beforePolynomial A B m u negative).natDegree=u := by
  unfold beforePolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,Finset.sum_const,nsmul_eq_mul,Nat.mul_one]
  exact jumpSet_card hm hu

/-- Explicit after-boundary degree is also exactly the numerator. -/
theorem afterPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    (A B : Rˣ) {m u : ℕ} (hm : 0<m) (hu : u<m) (negative : Bool) :
    (afterPolynomial A B m u negative).natDegree=u := by
  unfold afterPolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,Finset.sum_const,nsmul_eq_mul,Nat.mul_one]
  exact jumpSet_card hm hu

/-- Products cancel only equal no-jump factors; all boundary factors remain. -/
theorem filtered_product_swap {R : Type*} [CommRing R] {ι : Type*}
    (S : Finset ι) (p : ι→Prop) [DecidablePred p] (f h : ι→R)
    (he : ∀ t∈S, ¬p t→f t=h t) :
    (∏ t∈S, f t)*(∏ t∈S.filter p, h t)=
      (∏ t∈S, h t)*(∏ t∈S.filter p, f t) := by
  simp only [Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  by_cases hp : p t
  · simp only [if_pos hp,mul_comm]
  · simp only [if_neg hp,mul_one,he t ht hp]

/-- Exact adjacent shift of the actual floor-filtered product, before
discarding or dividing by any evaluated boundary factor. -/
theorem adjacent_boundary_swap {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hu : u<m) (negative : Bool) :
    shiftedPolynomial A B m u negative*afterPolynomial A B m u negative=
      successorPolynomial A B m u negative*beforePolynomial A B m u negative := by
  unfold shiftedPolynomial afterPolynomial successorPolynomial beforePolynomial
  rw [jumpSet_positive hu]
  apply filtered_product_swap
  intro t _ht hn
  have hz : carryJump m u t=0 := by have h := carryJump_le_one (t:=t) hu; omega
  rw [curveValue_step_no_jump A B negative hz]

/-- Positive source indices reindex to the original descriptor denominator range. -/
theorem prod_residues_eq {M : Type*} [CommMonoid M] (f : ℕ→M) {m : ℕ} :
    (∏ t∈residues m, f t)=∏ r∈Finset.range (m-1), f (r+1) := by
  have hs : residues m=(Finset.range (m-1)).image (fun r => r+1) := by
    ext t
    rw [mem_residues,Finset.mem_image]
    constructor
    · intro ht
      exact ⟨t-1,Finset.mem_range.mpr (by omega),by omega⟩
    · rintro ⟨r,hr,rfl⟩
      have hb := Finset.mem_range.mp hr
      omega
  rw [hs,Finset.prod_image]
  intro a _ha b _hb hab
  change a+1=b+1 at hab
  omega

/-- A finite adjacent root product telescopes with both endpoints retained. -/
theorem consecutive_product_endpoint {R : Type*} [CommRing R]
    (x : R) (f : ℕ→R) (L : ℕ) :
    (∏ r∈Finset.range L, (x-f (r+2)))*(x-f 1)=
      (∏ r∈Finset.range L, (x-f (r+1)))*(x-f (L+1)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ,Finset.prod_range_succ]
    calc
      _=((∏ r∈Finset.range L, (x-f (r+2)))*(x-f 1))*(x-f (L+2)) := by ring
      _=((∏ r∈Finset.range L, (x-f (r+1)))*(x-f (L+1)))*(x-f (L+2)) := by rw [ih]
      _=_ := by ring

/-- The shifted floor product retains the exact original and final endpoints. -/
theorem successor_endpoint {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hm : 0<m) (negative : Bool) :
    successorPolynomial A B m u negative*(X-C (curveValue (G:=Rˣ) A B m u negative 1 : R))=
      sourcePolynomial A B m u negative*(X-C (curveValue (G:=Rˣ) A B m u negative m : R)) := by
  unfold successorPolynomial sourcePolynomial
  rw [prod_residues_eq,prod_residues_eq]
  have he : m-1+1=m := by omega
  simpa only [Nat.add_assoc,he] using
    consecutive_product_endpoint (X : R[X])
      (fun t => C (curveValue (G:=Rˣ) A B m u negative t : R)) (m-1)

/-- Complete division-free floor-product identity. Evaluated boundary
and endpoint factors may vanish; the theorem does not cancel those zeros. -/
theorem adjacent_polynomial_telescoping {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hm : 0<m) (hu : u<m) (negative : Bool) :
    shiftedPolynomial A B m u negative*afterPolynomial A B m u negative*
        (X-C (curveValue (G:=Rˣ) A B m u negative 1 : R))=
      sourcePolynomial A B m u negative*beforePolynomial A B m u negative*
        (X-C (curveValue (G:=Rˣ) A B m u negative m : R)) := by
  rw [adjacent_boundary_swap A B hu negative]
  calc
    _=(successorPolynomial A B m u negative*
      (X-C (curveValue (G:=Rˣ) A B m u negative 1 : R)))*beforePolynomial A B m u negative := by ring
    _=(sourcePolynomial A B m u negative*
      (X-C (curveValue (G:=Rˣ) A B m u negative m : R)))*beforePolynomial A B m u negative := by
      rw [successor_endpoint A B hm negative]
    _=_ := by ring

/-- The shifted polynomial is the original target shift by a public
unit, with its complete harmless scalar phase made explicit. -/
theorem shiftedPolynomial_rephase {R : Type*} [CommRing R] (A B : Rˣ)
    {m u : ℕ} (hm : 0<m) (negative : Bool) :
    shiftedPolynomial A B m u negative=
      C ((A : R)^(m-1))*(sourcePolynomial A B m u negative).comp (C ((A⁻¹ : Rˣ) : R)*X) := by
  have hi : C (A : R)*C ((A⁻¹ : Rˣ) : R)=(1 : R[X]) := by
    rw [←C_mul]
    simp
  have hf (t : ℕ) : X-C ((A*curveValue A B m u negative t : Rˣ) : R)=
      C (A : R)*(C ((A⁻¹ : Rˣ) : R)*X-C (curveValue (G:=Rˣ) A B m u negative t : R)) := by
    simp only [Units.val_mul,C_mul]
    linear_combination -(X : R[X])*hi
  simp only [shiftedPolynomial,hf,Finset.prod_mul_distrib,Finset.prod_const,
    residues_card hm,sourcePolynomial,Polynomial.prod_comp,Polynomial.sub_comp,
    Polynomial.X_comp,Polynomial.C_comp,map_pow]

/-- Cancelling evaluated boundaries preserves the entire public GCD
only after both complete boundary/endpoint multipliers are units.
These are explicit checkable premises, not an assumed collision detector. -/
theorem checked_boundary_gcd {N m u : ℕ} (A B : (ZMod N)ˣ)
    (hm : 0<m) (hu : u<m) (negative : Bool) (x : ZMod N)
    (hleft : IsUnit ((afterPolynomial A B m u negative).eval x*
      (x-(curveValue (G:=(ZMod N)ˣ) A B m u negative 1 : ZMod N))))
    (hright : IsUnit ((beforePolynomial A B m u negative).eval x*
      (x-(curveValue (G:=(ZMod N)ˣ) A B m u negative m : ZMod N)))) :
    N.gcd ((sourcePolynomial A B m u negative).eval x).val=
      N.gcd ((sourcePolynomial A B m u negative).eval (((A⁻¹ : (ZMod N)ˣ) : ZMod N)*x)).val := by
  obtain ⟨v,hv⟩ := hleft
  obtain ⟨w,hw⟩ := hright
  have he := congrArg (fun Q : (ZMod N)[X] => Q.eval x)
    (adjacent_polynomial_telescoping A B hm hu negative)
  rw [shiftedPolynomial_rephase A B hm negative] at he
  simp only [eval_mul,eval_comp,eval_sub,eval_X,eval_C] at he
  have ht : (((A^(m-1)*v : (ZMod N)ˣ) : ZMod N))*
      (sourcePolynomial A B m u negative).eval (((A⁻¹ : (ZMod N)ˣ) : ZMod N)*x)=
        (w : ZMod N)*(sourcePolynomial A B m u negative).eval x := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val]
    rw [hv,hw]
    linear_combination he
  have hg := congrArg (fun z : ZMod N => N.gcd z.val) ht
  rw [SemiprimeRHCancellation.unit_mul_gcd_eq,SemiprimeRHCancellation.unit_mul_gcd_eq] at hg
  exact hg.symm

/-- Actual cached before-boundary degrees have the same quadratic input floor.
No minimal circuit or bit-complexity lower bound is claimed. -/
theorem public_before_degree_quadratic {R : Type*} [CommRing R] [Nontrivial R]
    (g : Rˣ) {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N) (hlarge : 8≤m)
    (negative : Bool) :
    m^2≤32*∑ j∈residues m,
      (beforePolynomial (progressionSeed g N m j).step
        (progressionSeed g N m j).carryStep m
        (progressionSeed g N m j).slope negative).natDegree := by
  have he : (∑ j∈residues m,
      (beforePolynomial (progressionSeed g N m j).step
        (progressionSeed g N m j).carryStep m
        (progressionSeed g N m j).slope negative).natDegree)=boundaryLoad N m := by
    rw [boundaryLoad_eq hm.pos]
    apply Finset.sum_congr rfl
    intro j _hj
    exact beforePolynomial_natDegree _ _ hm.pos (Nat.mod_lt _ hm.pos) negative
  rw [he]
  exact boundaryLoad_quadratic hm hN hlarge

end RiemannGaussian.SemiprimeDenseCarryBoundary
