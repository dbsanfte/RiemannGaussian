/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeShiftedNormAcquisitionObstruction
import Mathlib.Combinatorics.Additive.Energy

/-!
# Original carry energy obstructs small positive-moment carriers

Every nontrivial four-tag pair-sum of actual original offsets can occur
at only one second carry. Their full carry mass is at most cubic in the
row count. A sufficiently large local period transfers the exact integer
energy to the literal original seed family without losing multiplicities.
Finite group energy bounds then force a large geometric-grid support.
Positive pole retention uses a per-row fiber bound, so it works even
when the total raw grid mass exceeds the field characteristic.

The investigation journal combines these finite source theorems with an
unconditional classical actual-input count. Its all-width dense-carrier
cost obstruction is representation-specific; implicit circuits, signed
weights, internal pivots and general factoring are outside the contract.
No analytic infinitude or bit-cost assertion is a new Lean axiom here.
-/

namespace RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction

open scoped BigOperators Pointwise Combinatorics.Additive
open Polynomial
open SemiprimeGlobalPhaseCancellation SemiprimeDenseRowCarries
open SemiprimeOffsetCarryObstruction SemiprimeShiftedNormAcquisitionObstruction
open SemiprimeSeedMomentPoleRetention

open RiemannGaussian.SemiprimeOffsetCarryObstruction
open RiemannGaussian.SemiprimeGlobalPhaseCancellation

/-- Equal quadratic pair values have nonzero carry slope unless the unordered pairs agree. -/
theorem quadratic_pair_slope_ne_zero {F : Type*} [Field F]
    {s x y z w : F} (hs : s≠0) (htwo : (2 : F)≠0)
    (hnontriv : ¬((x=z ∧ y=w) ∨ (x=w ∧ y=z)))
    (hquad : s*(x^2-2*x)+s*(y^2-2*y)=s*(z^2-2*z)+s*(w^2-2*w)) :
    x+y-z-w≠0 := by
  intro hlin
  have hmul : (2*s)*(x*y-z*w)=0 := by
    linear_combination s*(x+y+z+w-2)*hlin-hquad
  have hprod : x*y=z*w :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero htwo hs))
  have hroot : (x-z)*(x-w)=0 := by
    linear_combination x*hlin-hprod
  rcases mul_eq_zero.mp hroot with hxz | hxw
  · have hxz' := sub_eq_zero.mp hxz
    have hyw : y=w := by linear_combination hlin-hxz'
    exact hnontriv (Or.inl ⟨hxz',hyw⟩)
  · have hxw' := sub_eq_zero.mp hxw
    have hyz : y=z := by linear_combination hlin-hxw'
    exact hnontriv (Or.inr ⟨hxw',hyz⟩)

/-- The source-exact coefficient of a nontrivial original-row pair-sum carry is a unit. -/
theorem actual_pair_carry_coefficient_ne_zero {s m i j k l u : ℕ}
    (hm : m.Prime) (hm2 : 2 < m) (hs : m.Coprime s)
    (hi : 1 ≤ i) (him : i < m) (hj : 1 ≤ j) (hjm : j < m)
    (hk : 1 ≤ k) (hkm : k < m) (hl : 1 ≤ l) (hlm : l < m)
    (hnontriv : ¬((i=k ∧ j=l) ∨ (i=l ∧ j=k)))
    (he : seedOffset (s+m*u) m i+seedOffset (s+m*u) m j=
      seedOffset (s+m*u) m k+seedOffset (s+m*u) m l) :
    (((j : ℤ)*k*l+(i : ℤ)*k*l-(i : ℤ)*j*l-(i : ℤ)*j*k : ℤ) : ZMod m)≠0 := by
  let : Fact m.Prime := ⟨hm⟩
  have hcop {r : ℕ} (hr : 1 ≤ r) (hrm : r < m) : r.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrm)).symm
  have hz {r : ℕ} (hr : 1 ≤ r) (hrm : r < m) : (r : ZMod m)≠0 :=
    ((ZMod.isUnit_iff_coprime r m).mpr (hcop hr hrm)).ne_zero
  have hinv {a b : ℕ} (ham : a < m) (hbm : b < m)
      (h : (a : ZMod m)⁻¹=(b : ZMod m)⁻¹) : a=b := by
    have heq : (a : ZMod m)=(b : ZMod m) := inv_injective h
    have hval := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ham,Nat.mod_eq_of_lt hbm] using hval
  have hi0 := hz hi him
  have hj0 := hz hj hjm
  have hk0 := hz hk hkm
  have hl0 := hz hl hlm
  have hs0 : (s : ZMod m)≠0 := ((ZMod.isUnit_iff_coprime s m).mpr hs.symm).ne_zero
  have hN0 : ((s+m*u : ℕ) : ZMod m)≠0 := by
    simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero] using hs0
  have htwo : (2 : ZMod m)≠0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0<2) hm2
      ((ZMod.natCast_eq_zero_iff 2 m).mp h)
  have hnontriv' : ¬(((i : ZMod m)⁻¹=(k : ZMod m)⁻¹ ∧
        (j : ZMod m)⁻¹=(l : ZMod m)⁻¹) ∨
      ((i : ZMod m)⁻¹=(l : ZMod m)⁻¹ ∧ (j : ZMod m)⁻¹=(k : ZMod m)⁻¹)) := by
    rintro (⟨hik,hjl⟩ | ⟨hil,hjk⟩)
    · exact hnontriv (Or.inl ⟨hinv him hkm hik,hinv hjm hlm hjl⟩)
    · exact hnontriv (Or.inr ⟨hinv him hlm hil,hinv hjm hkm hjk⟩)
  have hiform := quadratic_offset_formula hi0
    (offset_square_residue (N:=s+m*u) hm.pos (hcop hi him))
  have hjform := quadratic_offset_formula hj0
    (offset_square_residue (N:=s+m*u) hm.pos (hcop hj hjm))
  have hkform := quadratic_offset_formula hk0
    (offset_square_residue (N:=s+m*u) hm.pos (hcop hk hkm))
  have hlform := quadratic_offset_formula hl0
    (offset_square_residue (N:=s+m*u) hm.pos (hcop hl hlm))
  have hecast := congrArg (fun z : ℤ => (z : ZMod m)) he
  simp only [Int.cast_add] at hecast
  rw [hiform,hjform,hkform,hlform] at hecast
  have hslope := quadratic_pair_slope_ne_zero hN0 htwo hnontriv' hecast
  have hcoeff : (j : ZMod m)*k*l+(i : ZMod m)*k*l-(i : ZMod m)*j*l-(i : ZMod m)*j*k=
      (i : ZMod m)*j*k*l*((i : ZMod m)⁻¹+(j : ZMod m)⁻¹-
        (k : ZMod m)⁻¹-(l : ZMod m)⁻¹) := by
    field_simp
  simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  rw [hcoeff]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hi0 hj0) hk0) hl0) hslope

/-- A nontrivial pair-sum of four literal row offsets occurs at only one bounded carry. -/
theorem actual_pair_unique_carry {s m i j k l u v : ℕ}
    (hm : m.Prime) (hm2 : 2 < m) (hs : m.Coprime s)
    (hi : 1 ≤ i) (him : i < m) (hj : 1 ≤ j) (hjm : j < m)
    (hk : 1 ≤ k) (hkm : k < m) (hl : 1 ≤ l) (hlm : l < m)
    (hnontriv : ¬((i=k ∧ j=l) ∨ (i=l ∧ j=k))) (hu : u < m) (hv : v < m)
    (he : seedOffset (s+m*u) m i+seedOffset (s+m*u) m j=
      seedOffset (s+m*u) m k+seedOffset (s+m*u) m l)
    (he₀ : seedOffset (s+m*v) m i+seedOffset (s+m*v) m j=
      seedOffset (s+m*v) m k+seedOffset (s+m*v) m l) : u=v := by
  have hcop {r : ℕ} (hr : 1 ≤ r) (hrm : r < m) : r.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrm)).symm
  let D : ℤ := ((s+m*u : ℕ) : ℤ)-(s+m*v : ℕ)
  let C : ℤ := (j : ℤ)*k*l+(i : ℤ)*k*l-(i : ℤ)*j*l-(i : ℤ)*j*k
  have hI := offset_difference_modEq hm.pos (hcop hi him)
    (carry_class (s:=s) (u:=u) (v:=v))
  have hJ := offset_difference_modEq hm.pos (hcop hj hjm)
    (carry_class (s:=s) (u:=u) (v:=v))
  have hK := offset_difference_modEq hm.pos (hcop hk hkm)
    (carry_class (s:=s) (u:=u) (v:=v))
  have hL := offset_difference_modEq hm.pos (hcop hl hlm)
    (carry_class (s:=s) (u:=u) (v:=v))
  have h := (((hI.mul_left ((j : ℤ)*k*l)).add (hJ.mul_left ((i : ℤ)*k*l))).sub
    (hK.mul_left ((i : ℤ)*j*l))).sub (hL.mul_left ((i : ℤ)*j*k))
  have hmod : (0 : ℤ) ≡ -D*C [ZMOD (m : ℤ)^2] := by
    convert h using 1
    · linear_combination -(i : ℤ)*j*k*l*(he-he₀)
    · dsimp [D,C]
      ring
  have hprod : (m : ℤ)^2∣C*D := by
    convert hmod.symm.dvd using 1
    ring
  have hC := actual_pair_carry_coefficient_ne_zero hm hm2 hs
    hi him hj hjm hk hkm hl hlm hnontriv he
  have hD := (integer_coprime_square hm C hC).dvd_of_dvd_mul_left hprod
  have hclass : ((s+m*u : ℕ) : ℤ) ≡ ((s+m*v : ℕ) : ℤ) [ZMOD (m : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    simpa only [D,neg_sub] using hD.neg_right
  exact equal_input_carry hm.pos hu hv hclass

open scoped BigOperators

/-- Original row tags use the same zero-based range as progressionSeeds. -/
noncomputable def rowQuadruples (m : ℕ) : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  ((Finset.range (m-1))×ˢ(Finset.range (m-1)))×ˢ
    ((Finset.range (m-1))×ˢ(Finset.range (m-1)))

/-- Two ordered tag pairs have different unordered tag multisets. -/
abbrev tagPairsDiffer (q : (ℕ×ℕ)×(ℕ×ℕ)) : Prop :=
  ¬((q.1.1=q.2.1 ∧ q.1.2=q.2.2) ∨ (q.1.1=q.2.2 ∧ q.1.2=q.2.1))

/-- Exact original integer pair-sum equality, with all four labels retained. -/
abbrev offsetPairEquality (N m : ℕ) (q : (ℕ×ℕ)×(ℕ×ℕ)) : Prop :=
  seedOffset N m (q.1.1+1)+seedOffset N m (q.1.2+1)=
    seedOffset N m (q.2.1+1)+seedOffset N m (q.2.2+1)

/-- The nontrivial original pair equalities at one exact input residue. -/
noncomputable def nontrivialOffsetQuads (N m : ℕ) : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  (rowQuadruples m).filter fun q => tagPairsDiffer q ∧ offsetPairEquality N m q

/-- Count all nontrivial original tagged pair-sum equalities. -/
noncomputable def nontrivialOffsetEnergy (N m : ℕ) : ℕ :=
  (nontrivialOffsetQuads N m).card

/-- Necessary lower-residue candidates for exact four-tag equalities. -/
noncomputable def residuePairCandidates (s m : ℕ) : Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  (rowQuadruples m).filter fun q => tagPairsDiffer q ∧
    (seedOffset s m (q.1.1+1) : ZMod m)+(seedOffset s m (q.1.2+1) : ZMod m)=
      (seedOffset s m (q.2.1+1) : ZMod m)+(seedOffset s m (q.2.2+1) : ZMod m)

/-- Original tags in an arbitrary lower-offset residue fiber. -/
noncomputable def phaseFiber (s m : ℕ) (δ : ℤ) : Finset ℕ :=
  (Finset.range (m-1)).filter fun r => (seedOffset s m (r+1) : ZMod m)=(δ : ZMod m)

theorem rowQuadruples_mem {m : ℕ} {q : (ℕ×ℕ)×(ℕ×ℕ)} :
    q∈rowQuadruples m ↔ q.1.1+1 < m ∧ q.1.2+1 < m ∧ q.2.1+1 < m ∧ q.2.2+1 < m := by
  simp only [rowQuadruples,Finset.mem_product,Finset.mem_range]
  omega

/-- Every lower-offset fiber, including an arbitrary target phase, has at most two labels. -/
theorem phaseFiber_card_le_two {s m : ℕ} (hm : m.Prime) (hs : m.Coprime s) (δ : ℤ) :
    (phaseFiber s m δ).card≤2 := by
  classical
  let : Fact m.Prime := ⟨hm⟩
  let : NeZero m := ⟨hm.ne_zero⟩
  let P := phasePolynomial s m δ
  have hP : P≠0 := phasePolynomial_ne_zero hm hs δ
  have hb {r : ℕ} (hr : r∈phaseFiber s m δ) :
      r+1 < m ∧ (m : ℤ)∣seedOffset s m (r+1)-δ := by
    have h := Finset.mem_filter.mp hr
    refine ⟨by have hh := Finset.mem_range.mp h.1; omega,?_⟩
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
      (by simpa only [Int.cast_sub] using sub_eq_zero.mpr h.2)
  have hmaps : Set.MapsTo (fun r : ℕ => ((r+1 : ℕ) : ZMod m))
      (phaseFiber s m δ : Set ℕ) P.roots.toFinset := by
    intro r hr
    have hbr := hb hr
    have hcop : (r+1).Coprime m :=
      (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hbr.1)).symm
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr
      (phasePolynomial_root hm.pos hcop hbr.2))
  have hinj : Set.InjOn (fun r : ℕ => ((r+1 : ℕ) : ZMod m))
      (phaseFiber s m δ : Set ℕ) := by
    intro r hr t ht he
    have hval := congrArg ZMod.val he
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (hb hr).1,
      Nat.mod_eq_of_lt (hb ht).1] at hval
    omega
  exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans
    ((Multiset.toFinset_card_le P.roots).trans
      ((Polynomial.card_roots' P).trans (phasePolynomial_degree s m δ)))

/-- The whole original lower-residue quadruple family has only cubic candidate mass. -/
theorem residuePairCandidates_card_le {s m : ℕ} (hm : m.Prime) (hs : m.Coprime s) :
    (residuePairCandidates s m).card≤2*(m-1)^3 := by
  classical
  have hfold : (residuePairCandidates s m).card=
      ∑ i∈Finset.range (m-1),∑ j∈Finset.range (m-1),∑ k∈Finset.range (m-1),
        ((Finset.range (m-1)).filter fun l => tagPairsDiffer ((i,j),(k,l)) ∧
          (seedOffset s m (i+1) : ZMod m)+(seedOffset s m (j+1) : ZMod m)=
            (seedOffset s m (k+1) : ZMod m)+(seedOffset s m (l+1) : ZMod m)).card := by
    simp only [residuePairCandidates,rowQuadruples,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product]
  rw [hfold]
  calc
    _≤∑ _i∈Finset.range (m-1),∑ _j∈Finset.range (m-1),∑ _k∈Finset.range (m-1),2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      let δ := seedOffset s m (i+1)+seedOffset s m (j+1)-seedOffset s m (k+1)
      have hsub : ((Finset.range (m-1)).filter fun l => tagPairsDiffer ((i,j),(k,l)) ∧
          (seedOffset s m (i+1) : ZMod m)+(seedOffset s m (j+1) : ZMod m)=
            (seedOffset s m (k+1) : ZMod m)+(seedOffset s m (l+1) : ZMod m))⊆
          phaseFiber s m δ := by
        intro l hl
        have h := Finset.mem_filter.mp hl
        apply Finset.mem_filter.mpr
        refine ⟨h.1,?_⟩
        dsimp only [δ]
        push_cast
        linear_combination -h.2.2
      exact (Finset.card_le_card hsub).trans (phaseFiber_card_le_two hm hs δ)
    _=2*(m-1)^3 := by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]; ring

theorem carry_offset_residue {s m u r : ℕ} (hm : m.Prime) (hr : r+1 < m) :
    (seedOffset (s+m*u) m (r+1) : ZMod m)=(seedOffset s m (r+1) : ZMod m) := by
  have hcop : (r+1).Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hr)).symm
  have h := offset_residue_of_input_modEq hm.pos hcop (carry_class (s:=s) (u:=u) (v:=0))
  simp only [mul_zero,add_zero] at h
  exact (ZMod.intCast_eq_intCast_iff _ _ m).mpr h

theorem nontrivialOffsetQuads_eq_candidates_filter {s m u : ℕ} (hm : m.Prime) :
    nontrivialOffsetQuads (s+m*u) m=(residuePairCandidates s m).filter
      (offsetPairEquality (s+m*u) m) := by
  classical
  ext q
  simp only [nontrivialOffsetQuads,residuePairCandidates,Finset.mem_filter]
  constructor
  · rintro ⟨hq,hnontriv,he⟩
    refine ⟨⟨hq,hnontriv,?_⟩,he⟩
    have hb := rowQuadruples_mem.mp hq
    have hecast := congrArg (fun z : ℤ => (z : ZMod m)) he
    simp only [Int.cast_add] at hecast
    rw [carry_offset_residue hm hb.1,carry_offset_residue hm hb.2.1,
      carry_offset_residue hm hb.2.2.1,carry_offset_residue hm hb.2.2.2] at hecast
    exact hecast
  · exact fun h => ⟨h.1.1,h.1.2.1,h.2⟩

/-- Exact whole-family cubic nontrivial energy mass across every second carry. -/
theorem nontrivialOffsetEnergy_carry_mass_le {s m : ℕ} (hm : m.Prime) (hm2 : 2 < m)
    (hs : m.Coprime s) :
    ∑ u∈Finset.range m,nontrivialOffsetEnergy (s+m*u) m≤2*(m-1)^3 := by
  classical
  have hrewrite : (∑ u∈Finset.range m,nontrivialOffsetEnergy (s+m*u) m)=
      ∑ q∈residuePairCandidates s m,((Finset.range m).filter fun u =>
        offsetPairEquality (s+m*u) m q).card := by
    simp_rw [nontrivialOffsetEnergy,nontrivialOffsetQuads_eq_candidates_filter hm,
      Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  rw [hrewrite]
  calc
    _≤∑ _q∈residuePairCandidates s m,1 := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.card_le_one.mpr
      intro u hu v hv
      have hb := rowQuadruples_mem.mp (Finset.mem_filter.mp hq).1
      have hnontriv := (Finset.mem_filter.mp hq).2.1
      have htags : ¬((q.1.1+1=q.2.1+1 ∧ q.1.2+1=q.2.2+1) ∨
          (q.1.1+1=q.2.2+1 ∧ q.1.2+1=q.2.1+1)) := by
        simpa only [tagPairsDiffer,Nat.add_right_cancel_iff] using hnontriv
      exact actual_pair_unique_carry hm hm2 hs (by omega) hb.1 (by omega) hb.2.1
        (by omega) hb.2.2.1 (by omega) hb.2.2.2 htags
        (Finset.mem_range.mp (Finset.mem_filter.mp hu).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hv).1)
        (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    _=(residuePairCandidates s m).card := by simp
    _≤2*(m-1)^3 := residuePairCandidates_card_le hm hs

/-- A finite Markov threshold bound for the original energy, not random carry sampling. -/
theorem nontrivialOffsetEnergy_threshold_bound {s m B : ℕ} (hm : m.Prime) (hm2 : 2 < m)
    (hs : m.Coprime s) :
    B*((Finset.range m).filter fun u => B≤nontrivialOffsetEnergy (s+m*u) m).card≤
      2*(m-1)^3 := by
  classical
  let bad := (Finset.range m).filter fun u => B≤nontrivialOffsetEnergy (s+m*u) m
  calc
    B*bad.card=∑ _u∈bad,B := by simp only [Finset.sum_const,smul_eq_mul,mul_comm]
    _≤∑ u∈bad,nontrivialOffsetEnergy (s+m*u) m := by
      apply Finset.sum_le_sum
      exact fun _ hu => (Finset.mem_filter.mp hu).2
    _≤∑ u∈Finset.range m,nontrivialOffsetEnergy (s+m*u) m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    _≤2*(m-1)^3 := nontrivialOffsetEnergy_carry_mass_le hm hm2 hs

section GroupEnergy

open scoped BigOperators Pointwise Combinatorics.Additive

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- Ordered source-ratio multiplicity used only in finite proofs. -/
noncomputable def ratioCount (s : Finset G) (r : G) : ℕ :=
  ((s ×ˢ s).filter fun ab => ab.1 / ab.2 = r).card

theorem energy_eq_ratio_sum (s t : Finset G) :
    s.mulEnergy t = ∑ r : G, ratioCount s r * ratioCount t r := by
  classical
  let Q := (((s ×ˢ s) ×ˢ (t ×ˢ t)).filter fun ab =>
    ab.1.1 / ab.1.2 = ab.2.1 / ab.2.2)
  have hQ : s.mulEnergy t = Q.card := by
    unfold Finset.mulEnergy
    apply Finset.card_bij (fun ab _ => (ab.1, (ab.2.2, ab.2.1)))
    · intro ab hab
      simp only [Q, Finset.mem_filter, Finset.mem_product] at hab ⊢
      exact ⟨⟨hab.1.1, hab.1.2.2, hab.1.2.1⟩,
        div_eq_div_iff_mul_eq_mul.mpr (by simpa [mul_comm] using hab.2)⟩
    · intro a _ b _ h
      have hi := congrArg
        (fun z : (G × G) × (G × G) => (z.1, (z.2.2, z.2.1))) h
      simpa only using hi
    · intro ab hab
      refine ⟨(ab.1, (ab.2.2, ab.2.1)), ?_, ?_⟩
      · simp only [Q, Finset.mem_filter, Finset.mem_product] at hab ⊢
        exact ⟨⟨hab.1.1, hab.1.2.2, hab.1.2.1⟩,
          by simpa [mul_comm] using div_eq_div_iff_mul_eq_mul.mp hab.2⟩
      · simp
  rw [hQ]
  have hf : Q.card = ∑ r : G,
      (Q.filter fun ab => ab.1.1 / ab.1.2 = r).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hf]
  apply Finset.sum_congr rfl
  intro r _
  have he : (Q.filter fun ab => ab.1.1 / ab.1.2 = r) =
      ((s ×ˢ s).filter fun ab => ab.1 / ab.2 = r) ×ˢ
      ((t ×ˢ t).filter fun ab => ab.1 / ab.2 = r) := by
    ext ab
    simp only [Q, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [he, Finset.card_product]
  rfl

theorem mixed_energy_sq_le (s t : Finset G) :
    s.mulEnergy t ^ 2 ≤ s.mulEnergy s * t.mulEnergy t := by
  rw [energy_eq_ratio_sum, energy_eq_ratio_sum s s, energy_eq_ratio_sum t t]
  simpa only [pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) Finset.univ (ratioCount s) (ratioCount t)

theorem product_support_energy_bound (s t : Finset G) :
    (s.card * t.card) ^ 4 ≤ (s * t).card ^ 2 * s.mulEnergy s * t.mulEnergy t := by
  have h := Finset.le_card_mul_mul_mulEnergy s t
  have hs : (s.card * t.card) ^ 2 ≤ (s * t).card * s.mulEnergy t := by
    simpa only [mul_pow] using h
  calc
    _ = ((s.card * t.card) ^ 2) ^ 2 := by ring
    _ ≤ ((s * t).card * s.mulEnergy t) ^ 2 := Nat.pow_le_pow_left hs 2
    _ = (s * t).card ^ 2 * (s.mulEnergy t) ^ 2 := by ring
    _ ≤ (s * t).card ^ 2 * (s.mulEnergy s * t.mulEnergy t) :=
      Nat.mul_le_mul_left _ (mixed_energy_sq_le s t)
    _ = _ := by ring

omit [Fintype G] in
theorem self_energy_le_card_cubed (s : Finset G) :
    s.mulEnergy s ≤ s.card ^ 3 := by
  unfold Finset.mulEnergy
  have h := Finset.card_le_card_of_injOn
    (s := (((s ×ˢ s) ×ˢ (s ×ˢ s)).filter fun ab =>
      ab.1.1 * ab.2.1 = ab.1.2 * ab.2.2))
    (t := (s ×ˢ s) ×ˢ s) (fun ab => (ab.1, ab.2.1))
    (by
      intro ab hab
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1,
          (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2).1⟩)
    (by
      intro a ha b hb he
      have h1 : a.1 = b.1 := congrArg (fun z : (G × G) × G => z.1) he
      have h2 : a.2.1 = b.2.1 := congrArg Prod.snd he
      have haeq := (Finset.mem_filter.mp ha).2
      have hbeq := (Finset.mem_filter.mp hb).2
      have hlast : a.2.2 = b.2.2 := by
        apply mul_left_cancel (a := a.1.2)
        calc
          _ = a.1.1 * a.2.1 := haeq.symm
          _ = b.1.1 * b.2.1 := by rw [h1, h2]
          _ = b.1.2 * b.2.2 := hbeq
          _ = a.1.2 * b.2.2 := by rw [h1]
      exact Prod.ext h1 (Prod.ext h2 hlast))
  have hc : ((s ×ˢ s) ×ˢ s).card = s.card ^ 3 := by
    simp only [Finset.card_product]
    ring
  rw [hc] at h
  exact h

theorem product_support_source_energy_bound (s t : Finset G) :
    (s.card * t.card) ^ 4 ≤ (s * t).card ^ 2 * s.mulEnergy s * t.card ^ 3 := by
  exact (product_support_energy_bound s t).trans
    (Nat.mul_le_mul_left _ (self_energy_le_card_cubed t))

theorem product_support_tradeoff (s t : Finset G) (ht : 0 < t.card)
    (w L D B : ℕ) (hcover : L ≤ w * t.card)
    (hdegree : (s * t).card ≤ D) (henergy : s.mulEnergy s ≤ B) :
    s.card ^ 4 * L ≤ w * D ^ 2 * B := by
  have he := product_support_source_energy_bound s t
  have hbase : s.card ^ 4 * t.card ≤ (s * t).card ^ 2 * s.mulEnergy s := by
    have hh : (s.card ^ 4 * t.card) * t.card ^ 3 ≤
        ((s * t).card ^ 2 * s.mulEnergy s) * t.card ^ 3 := by
      calc
        _ = (s.card * t.card) ^ 4 := by ring
        _ ≤ _ := he
    exact Nat.le_of_mul_le_mul_right hh (pow_pos ht _)
  have hd : s.card ^ 4 * t.card ≤ D ^ 2 * B :=
    hbase.trans (Nat.mul_le_mul (Nat.pow_le_pow_left hdegree 2) henergy)
  calc
    _ ≤ s.card ^ 4 * (w * t.card) := Nat.mul_le_mul_left _ hcover
    _ = w * (s.card ^ 4 * t.card) := by ring
    _ ≤ w * (D ^ 2 * B) := Nat.mul_le_mul_left _ hd
    _ = _ := by ring

omit [Fintype G] in
/-- Multiplicative energy with every original source label retained. -/
noncomputable def labelledEnergy {ι : Type*} (I : Finset ι) (f : ι → G) : ℕ := by
  classical
  exact (((I ×ˢ I) ×ˢ (I ×ˢ I)).filter fun q =>
    f q.1.1 * f q.2.1 = f q.1.2 * f q.2.2).card

omit [Fintype G] in
theorem image_self_energy_le_labelled {ι : Type*} (I : Finset ι) (f : ι → G) :
    (I.image f).mulEnergy (I.image f) ≤ labelledEnergy I f := by
  classical
  let S := (((I ×ˢ I) ×ˢ (I ×ˢ I)).filter fun q =>
    f q.1.1 * f q.2.1 = f q.1.2 * f q.2.2)
  let F := fun q : (ι × ι) × (ι × ι) =>
    ((f q.1.1, f q.1.2), (f q.2.1, f q.2.2))
  have he : S.image F =
      ((((I.image f) ×ˢ (I.image f)) ×ˢ ((I.image f) ×ˢ (I.image f))).filter
        fun q => q.1.1 * q.2.1 = q.1.2 * q.2.2) := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      rcases Finset.mem_filter.mp ha with ⟨ha, heq⟩
      rcases Finset.mem_product.mp ha with ⟨ha1, ha2⟩
      rcases Finset.mem_product.mp ha1 with ⟨hi1, hi2⟩
      rcases Finset.mem_product.mp ha2 with ⟨hi3, hi4⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_image_of_mem f hi1, Finset.mem_image_of_mem f hi2⟩,
            Finset.mem_product.mpr
              ⟨Finset.mem_image_of_mem f hi3, Finset.mem_image_of_mem f hi4⟩⟩,
          heq⟩
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨hq, heq⟩
      rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
      rcases Finset.mem_product.mp hq1 with ⟨hy1, hy2⟩
      rcases Finset.mem_product.mp hq2 with ⟨hy3, hy4⟩
      obtain ⟨i1, hi1, he1⟩ := Finset.mem_image.mp hy1
      obtain ⟨i2, hi2, he2⟩ := Finset.mem_image.mp hy2
      obtain ⟨i3, hi3, he3⟩ := Finset.mem_image.mp hy3
      obtain ⟨i4, hi4, he4⟩ := Finset.mem_image.mp hy4
      refine Finset.mem_image.mpr ⟨((i1, i2), (i3, i4)), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hi1, hi2⟩, Finset.mem_product.mpr ⟨hi3, hi4⟩⟩,
          by simpa only [he1, he2, he3, he4] using heq⟩
      · dsimp only [F]
        exact Prod.ext (Prod.ext he1 he2) (Prod.ext he3 he4)
  have hc := Finset.card_image_le (f := F) (s := S)
  rw [he] at hc
  exact hc

omit [CommGroup G] [Fintype G] in
theorem card_le_fiber_bound_mul_image {ι : Type*} (I : Finset ι) (f : ι → G)
    (C : ℕ) (hcap : ∀ y ∈ I.image f, (I.filter fun i => f i = y).card ≤ C) :
    I.card ≤ C * (I.image f).card := by
  classical
  calc
    _ = ∑ y ∈ I.image f, (I.filter fun i => f i = y).card :=
      Finset.card_eq_sum_card_image f I
    _ ≤ ∑ _y ∈ I.image f, C := Finset.sum_le_sum hcap
    _ = _ := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]

end GroupEnergy

open scoped BigOperators
open Polynomial SemiprimeSeedMomentPoleRetention

/-- Row-injective labelled grids have at most one occurrence per row in
any point fiber, regardless of the grid's total raw label mass. -/
theorem grid_fiber_card_le_rows {G : Type*} [DecidableEq G] {M J : ℕ}
    (point : Fin M × Fin J → G)
    (hrow : ∀ i, Function.Injective (fun k => point (i,k))) (y : G) :
    ((Finset.univ : Finset (Fin M × Fin J)).filter fun ik => point ik=y).card≤M := by
  classical
  have hinj : Set.InjOn (fun ik : Fin M × Fin J => ik.1)
      (((Finset.univ : Finset (Fin M × Fin J)).filter fun ik => point ik=y) : Set _) := by
    intro a ha b hb he
    obtain ⟨i,k⟩ := a
    obtain ⟨j,l⟩ := b
    dsimp only at he
    subst j
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hk := hrow i (ha'.trans hb'.symm)
    exact Prod.ext rfl hk
  have hcard := Finset.card_image_of_injOn hinj
  calc
    _=((Finset.univ.filter fun ik => point ik=y).image Prod.fst).card := hcard.symm
    _≤(Finset.univ : Finset (Fin M)).card := Finset.card_le_card (Finset.subset_univ _)
    _=M := Fintype.card_fin M

/-- Positive local fiber weights below the characteristic retain every
pole, even when the full labelled family has more than p labels. -/
theorem fiberwise_prime_denominator_degree {p : ℕ} {ι : Type*}
    (hp : p.Prime) (I : Finset ι) (x : ι→ZMod p)
    (hfiber : ∀ y∈I.image x,(I.filter fun i => x i=y).card<p)
    (hx : ∀ i∈I,x i≠0) (U V : (ZMod p)[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod p))*(∑ i∈I,positiveMoments (x i))=
      (V : PowerSeries (ZMod p))) : (I.image x).card≤U.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [labelled_moments_group I x] at hUV
  have hpoints : ∀ y∈I.image x,y≠0 := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    exact hx i hi
  have hweights : ∀ y∈I.image x,(((I.filter fun i => x i=y).card : ℕ) : ZMod p)≠0 := by
    intro y hy
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hy
    have hpos : 0<(I.filter fun j => x j=y).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩⟩
    exact fun hz => Nat.not_dvd_of_pos_of_lt hpos (hfiber y (Finset.mem_image.mpr ⟨i,hi,he⟩))
      ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  exact weighted_denominator_degree (I.image x)
    (fun y => (((I.filter fun i => x i=y).card : ℕ) : ZMod p))
    hpoints hweights U V hU hUV

/-- A geometric row is injective before its actual unit period. -/
theorem geometric_grid_fiber_card_le_rows {p M J : ℕ}
    (x : Fin M→(ZMod p)ˣ) (beta : (ZMod p)ˣ)
    (hJ : J≤orderOf beta) (y : ZMod p) :
    ((Finset.univ : Finset (Fin M × Fin J)).filter
      fun ik => (((x ik.1)*beta^ik.2.val : (ZMod p)ˣ) : ZMod p)=y).card≤M := by
  apply grid_fiber_card_le_rows
  intro i k l he
  have he' : x i*beta^k.val=x i*beta^l.val := Units.ext he
  have hpow := mul_left_cancel he'
  apply Fin.ext
  exact pow_injOn_Iio_orderOf (k.is_lt.trans_le hJ) (l.is_lt.trans_le hJ) hpow

/-- All positive geometric-grid poles survive as long as the number of
source rows is below p; no bound on M*J is needed. -/
theorem geometric_grid_denominator_degree {p M J : ℕ}
    (hp : p.Prime) (x : Fin M→(ZMod p)ˣ) (beta : (ZMod p)ˣ)
    (hJ : J≤orderOf beta) (hM : M<p)
    (U V : (ZMod p)[X]) (hU : U.coeff 0=1)
    (hUV : (U : PowerSeries (ZMod p))*(∑ ik : Fin M × Fin J,
      positiveMoments ((((x ik.1)*beta^ik.2.val : (ZMod p)ˣ) : ZMod p)))=
      (V : PowerSeries (ZMod p))) :
    ((Finset.univ : Finset (Fin M × Fin J)).image
      fun ik => (((x ik.1)*beta^ik.2.val : (ZMod p)ˣ) : ZMod p)).card≤U.natDegree := by
  let : Fact p.Prime := ⟨hp⟩
  apply fiberwise_prime_denominator_degree hp Finset.univ
    (fun ik : Fin M × Fin J => (((x ik.1)*beta^ik.2.val : (ZMod p)ˣ) : ZMod p))
    (fun y _ => (geometric_grid_fiber_card_le_rows x beta hJ y).trans_lt hM)
    (fun ik _ => (x ik.1*beta^ik.2.val).isUnit.ne_zero) U V hU
  exact hUV

open SemiprimeGlobalPhaseCancellation SemiprimeDenseRowCarries

/-- The short original four-offset residual lies below the actual local
period. Cancelling the common 2N exponent loses no tagged pair equality. -/
theorem original_pair_product_eq_iff_offset_sum {G : Type*} [CommGroup G]
    (g : G) {N m i j k l : ℕ} (hm : m.Prime)
    (hi : 1 ≤ i) (him : i < m) (hj : 1 ≤ j) (hjm : j < m)
    (hk : 1 ≤ k) (hkm : k < m) (hl : 1 ≤ l) (hlm : l < m)
    (horder : 8*m^2 < orderOf g) :
    (progressionSeed g N m i).step*(progressionSeed g N m j).step=
      (progressionSeed g N m k).step*(progressionSeed g N m l).step ↔
    seedOffset N m i+seedOffset N m j=seedOffset N m k+seedOffset N m l := by
  have hcop {r : ℕ} (hr : 1 ≤ r) (hrm : r < m) : r.Coprime m :=
    (hm.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hrm)).symm
  rw [seed_step_offset g hm.pos (hcop hi him),
    seed_step_offset g hm.pos (hcop hj hjm),
    seed_step_offset g hm.pos (hcop hk hkm),
    seed_step_offset g hm.pos (hcop hl hlm),←zpow_add,←zpow_add]
  constructor
  · intro he
    have hd := (orderOf_dvd_sub_iff_zpow_eq_zpow).mpr he
    have hbI := seedOffset_bounds (N:=N) hm.one_lt hi him
    have hbJ := seedOffset_bounds (N:=N) hm.one_lt hj hjm
    have hbK := seedOffset_bounds (N:=N) hm.one_lt hk hkm
    have hbL := seedOffset_bounds (N:=N) hm.one_lt hl hlm
    have hb : |((N : ℤ)+seedOffset N m i)+((N : ℤ)+seedOffset N m j)-
        (((N : ℤ)+seedOffset N m k)+((N : ℤ)+seedOffset N m l))| ≤ 8*(m : ℤ)^2 := by
      apply abs_le.mpr
      constructor  <;> nlinarith only [hbI.1,hbI.2,hbJ.1,hbJ.2,hbK.1,hbK.2,hbL.1,hbL.2]
    have ho : 8*(m : ℤ)^2 < (orderOf g : ℤ) := by exact_mod_cast horder
    have hn : (((N : ℤ)+seedOffset N m i)+((N : ℤ)+seedOffset N m j)-
        (((N : ℤ)+seedOffset N m k)+((N : ℤ)+seedOffset N m l))).natAbs <
        (orderOf g : ℤ).natAbs := by
      have hh := hb.trans_lt ho
      rw [←Int.natCast_natAbs] at hh
      rw [Int.natAbs_natCast]
      exact_mod_cast hh
    have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hn
    linarith only [hz]
  · intro he
    congr 1
    linarith only [he]

/-- Integer energy of all original row tags, retaining duplicate offsets. -/
noncomputable def offsetEnergy (N m : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin (m-1) × Fin (m-1)) × (Fin (m-1) × Fin (m-1)))).filter
    fun t : ((Fin (m-1) × Fin (m-1)) × (Fin (m-1) × Fin (m-1))) => seedOffset N m (t.1.1.val+1)+seedOffset N m (t.1.2.val+1)=
      seedOffset N m (t.2.1.val+1)+seedOffset N m (t.2.2.val+1)).card

/-- Multiplicative energy uses the identical original row labels. -/
noncomputable def originalSeedEnergy {G : Type*} [CommGroup G] (g : G) (N m : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset ((Fin (m-1) × Fin (m-1)) × (Fin (m-1) × Fin (m-1)))).filter
    fun t : ((Fin (m-1) × Fin (m-1)) × (Fin (m-1) × Fin (m-1))) => (progressionSeed g N m (t.1.1.val+1)).step*
        (progressionSeed g N m (t.1.2.val+1)).step=
      (progressionSeed g N m (t.2.1.val+1)).step*
        (progressionSeed g N m (t.2.2.val+1)).step).card

/-- Exact tagged source-energy transfer at a sufficiently large local
period. The group is proof-side; no local order is supplied to a runtime. -/
theorem originalSeedEnergy_eq_offsetEnergy {G : Type*} [CommGroup G]
    (g : G) {N m : ℕ} (hm : m.Prime) (horder : 8*m^2 < orderOf g) :
    originalSeedEnergy g N m=offsetEnergy N m := by
  classical
  unfold originalSeedEnergy offsetEnergy
  apply congrArg Finset.card
  ext t
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact original_pair_product_eq_iff_offset_sum g hm
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) horder


open scoped BigOperators Pointwise Combinatorics.Additive
open Polynomial RiemannGaussian.SemiprimeSeedMomentPoleRetention
open RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction

theorem geometric_unit_grid_support_eq {G : Type*} [CommGroup G] [DecidableEq G]
    {M J : ℕ} (x : Fin M → G) (beta : G) :
    (Finset.univ.image x) *
      (Finset.univ.image fun k : Fin J => beta ^ k.val) =
    ((Finset.univ : Finset (Fin M × Fin J)).image
      fun ik => x ik.1 * beta ^ ik.2.val) := by
  classical
  ext g
  simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨k, rfl⟩, he⟩
    exact ⟨i, k, he⟩
  · rintro ⟨i, k, he⟩
    exact ⟨x i, ⟨i, rfl⟩, beta ^ k.val, ⟨k, rfl⟩, he⟩

theorem geometric_grid_support_card_eq {p M J : ℕ}
    (x : Fin M → (ZMod p)ˣ) (beta : (ZMod p)ˣ) :
    ((Finset.univ.image x) *
      (Finset.univ.image fun k : Fin J => beta ^ k.val)).card =
    ((Finset.univ : Finset (Fin M × Fin J)).image
      fun ik => (((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p)).card := by
  classical
  rw [geometric_unit_grid_support_eq]
  have hi := Finset.card_image_of_injective
    (s := ((Finset.univ : Finset (Fin M × Fin J)).image
      fun ik => x ik.1 * beta ^ ik.2.val))
    (f := fun u : (ZMod p)ˣ => (u : ZMod p))
    (fun a b h => Units.ext h)
  rw [Finset.image_image] at hi
  exact hi.symm

theorem geometric_moment_source_energy_tradeoff {p M J : ℕ}
    (hp : p.Prime) (x : Fin M → (ZMod p)ˣ) (beta : (ZMod p)ˣ)
    (hsource : ∀ y ∈ Finset.univ.image x,
      ((Finset.univ : Finset (Fin M)).filter fun i => x i = y).card ≤ 2)
    (hJ : J ≤ orderOf beta) (hJpos : 0 < J) (hM : M < p)
    (w L : ℕ) (hcover : L ≤ w * J)
    (H K : (ZMod p)[X]) (hH : H.coeff 0 = 1)
    (hHK : (H : PowerSeries (ZMod p)) * (∑ ik : Fin M × Fin J,
      positiveMoments ((((x ik.1) * beta ^ ik.2.val : (ZMod p)ˣ) : ZMod p))) =
      (K : PowerSeries (ZMod p))) :
    M ^ 4 * L ≤ 16 * w * H.natDegree ^ 2 * labelledEnergy Finset.univ x := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let A := Finset.univ.image x
  let B := Finset.univ.image fun k : Fin J => beta ^ k.val
  have hB : B.card = J := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin J
    · intro k l he
      apply Fin.ext
      exact pow_injOn_Iio_orderOf (k.is_lt.trans_le hJ) (l.is_lt.trans_le hJ) he
  have hrows : M ≤ 2 * A.card := by
    have h := card_le_fiber_bound_mul_image Finset.univ x 2 hsource
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hdeg : (A * B).card ≤ H.natDegree := by
    rw [geometric_grid_support_card_eq]
    exact geometric_grid_denominator_degree hp x beta hJ hM H K hH hHK
  have he := product_support_tradeoff A B (by rw [hB]; exact hJpos)
    w L H.natDegree (labelledEnergy Finset.univ x)
    (by rw [hB]; exact hcover) hdeg (image_self_energy_le_labelled Finset.univ x)
  calc
    _ ≤ (2 * A.card) ^ 4 * L := Nat.mul_le_mul_right L (Nat.pow_le_pow_left hrows 4)
    _ = 16 * (A.card ^ 4 * L) := by ring
    _ ≤ 16 * (w * H.natDegree ^ 2 * labelledEnergy Finset.univ x) :=
      Nat.mul_le_mul_left _ he
    _ = _ := by ring


open SemiprimeGlobalPhaseCancellation SemiprimeDenseRowCarries

/-- At a sufficiently large local order, each original seed fiber retains
at most the two labels in its public quadratic phase fiber. -/
theorem original_seed_fiber_card_le_two {G : Type*} [CommGroup G] [DecidableEq G]
    (g : G) {N m : ℕ} (hm : m.Prime) (hN : m.Coprime N)
    (horder : 8*m^2 < orderOf g) (y : G) :
    ((Finset.univ : Finset (Fin (m-1))).filter
      fun i => (progressionSeed g N m (i.val+1)).step=y).card≤2 := by
  classical
  let S := (Finset.univ : Finset (Fin (m-1))).filter
    fun i => (progressionSeed g N m (i.val+1)).step=y
  change S.card≤2
  by_cases hs : S.Nonempty
  · obtain ⟨i₀,hi₀⟩ := hs
    let δ := seedOffset N m (i₀.val+1)
    have hi₀eq := (Finset.mem_filter.mp hi₀).2
    have hmap : Set.MapsTo (fun i : Fin (m-1) => i.val) S (phaseFiber N m δ) := by
      intro i hi
      have he := (Finset.mem_filter.mp hi).2.trans hi₀eq.symm
      have hprod : (progressionSeed g N m (i.val+1)).step*
          (progressionSeed g N m (i₀.val+1)).step=
          (progressionSeed g N m (i₀.val+1)).step*
          (progressionSeed g N m (i₀.val+1)).step := by rw [he]
      have hoff := (original_pair_product_eq_iff_offset_sum g hm
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) horder).mp hprod
      have hd : seedOffset N m (i.val+1)=δ := by dsimp only [δ]; omega
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr i.is_lt,congrArg (fun z : ℤ => (z : ZMod m)) hd⟩
    have hinj : Set.InjOn (fun i : Fin (m-1) => i.val) S :=
      fun _ _ _ _ he => Fin.ext he
    exact (Finset.card_le_card_of_injOn _ hmap hinj).trans
      (phaseFiber_card_le_two hm hN δ)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]


open SemiprimeSeedEnergyAcquisitionObstruction

/-- The Fin-labelled source energy is exactly the same natural-tag count. -/
theorem offsetEnergy_eq_nat_card (N m : ℕ) :
    offsetEnergy N m=((rowQuadruples m).filter (offsetPairEquality N m)).card := by
  classical
  unfold offsetEnergy
  apply Finset.card_bij
    (fun t _ => ((t.1.1.val,t.1.2.val),(t.2.1.val,t.2.2.val)))
  · intro t ht
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ht
    simp only [Finset.mem_filter,rowQuadruples,Finset.mem_product,Finset.mem_range]
    exact ⟨⟨⟨t.1.1.isLt,t.1.2.isLt⟩,⟨t.2.1.isLt,t.2.2.isLt⟩⟩,ht⟩
  · intro a _ b _ h
    exact Prod.ext
      (Prod.ext (Fin.ext (congrArg (fun q => q.1.1) h))
        (Fin.ext (congrArg (fun q => q.1.2) h)))
      (Prod.ext (Fin.ext (congrArg (fun q => q.2.1) h))
        (Fin.ext (congrArg (fun q => q.2.2) h)))
  · intro q hq
    have hb := (Finset.mem_filter.mp hq).1
    simp only [rowQuadruples,Finset.mem_product,Finset.mem_range] at hb
    let t : ((Fin (m-1)×Fin (m-1))×(Fin (m-1)×Fin (m-1))) :=
      ((⟨q.1.1,hb.1.1⟩,⟨q.1.2,hb.1.2⟩),(⟨q.2.1,hb.2.1⟩,⟨q.2.2,hb.2.2⟩))
    refine ⟨t,?_,rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (Finset.mem_filter.mp hq).2

/-- The two tag-diagonal images bound every trivial unordered pair match. -/
theorem nat_offset_energy_le_nontrivial (N m : ℕ) :
    ((rowQuadruples m).filter (offsetPairEquality N m)).card≤
      nontrivialOffsetEnergy N m+2*(m-1)^2 := by
  classical
  let P := (Finset.range (m-1))×ˢ(Finset.range (m-1))
  let D := (P.image fun a : ℕ×ℕ => (a,a)) ∪
    (P.image fun a : ℕ×ℕ => (a,(a.2,a.1)))
  have hsub : ((rowQuadruples m).filter (offsetPairEquality N m))⊆
      nontrivialOffsetQuads N m ∪ D := by
    intro q hq
    have hb := (Finset.mem_filter.mp hq).1
    have he := (Finset.mem_filter.mp hq).2
    by_cases hn : tagPairsDiffer q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb,hn,he⟩)
    · have hmatch : (q.1.1=q.2.1 ∧ q.1.2=q.2.2) ∨
          (q.1.1=q.2.2 ∧ q.1.2=q.2.1) := by
        simpa only [tagPairsDiffer,not_not] using hn
      have hp : q.1∈P := (Finset.mem_product.mp hb).1
      apply Finset.mem_union_right
      rcases hmatch with ⟨hik,hjl⟩ | ⟨hil,hjk⟩
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr
          ⟨q.1,hp,Prod.ext rfl (Prod.ext hik hjl)⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨q.1,hp,Prod.ext rfl (Prod.ext hjk hil)⟩
  have hD : D.card≤2*(m-1)^2 := by
    calc
      D.card≤(P.image fun a : ℕ×ℕ => (a,a)).card+
          (P.image fun a : ℕ×ℕ => (a,(a.2,a.1))).card := Finset.card_union_le _ _
      _≤P.card+P.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _=2*(m-1)^2 := by simp only [P,Finset.card_product,Finset.card_range]; ring
  calc
    _≤(nontrivialOffsetQuads N m ∪ D).card := Finset.card_le_card hsub
    _≤(nontrivialOffsetQuads N m).card+D.card := Finset.card_union_le _ _
    _≤nontrivialOffsetEnergy N m+2*(m-1)^2 := Nat.add_le_add_left hD _

/-- Source-exact full energy is bounded by the native carry count plus the diagonals. -/
theorem offsetEnergy_le_nontrivial_add (N m : ℕ) :
    offsetEnergy N m≤nontrivialOffsetEnergy N m+2*(m-1)^2 := by
  rw [offsetEnergy_eq_nat_card]
  exact nat_offset_energy_le_nontrivial N m



/-- Transposing two tuple coordinates aligns the generic ratio-energy
count with the literal original seed pair-sum count. -/
theorem labelled_original_seed_energy_eq_offset {p N m : ℕ}
    (gamma : (ZMod p)ˣ) (hm : m.Prime) (horder : 8*m^2 < orderOf gamma) :
    labelledEnergy Finset.univ
      (fun i : Fin (m-1) => (progressionSeed gamma N m (i.val+1)).step)=offsetEnergy N m := by
  classical
  rw [←originalSeedEnergy_eq_offsetEnergy gamma hm horder]
  unfold labelledEnergy originalSeedEnergy
  simp only [Finset.univ_product_univ]
  apply Finset.card_bij (fun q _ => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
  · intro q hq
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hq
  · intro a _ b _ he
    have hi := congrArg (fun q => ((q.1.1,q.2.1),(q.1.2,q.2.2))) he
    exact hi
  · intro q hq
    refine ⟨((q.1.1,q.2.1),(q.1.2,q.2.2)),?_,rfl⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hq

/-- Exact original source tradeoff, with the full energy controlled by the
native nontrivial carry count. The analytic actual-input supply is separate. -/
theorem literal_original_moment_energy_tradeoff {p N m J : ℕ}
    (hp : p.Prime) (hm : m.Prime) (hN : m.Coprime N)
    (gamma beta : (ZMod p)ˣ) (horder : 8*m^2 < orderOf gamma)
    (hJ : J≤orderOf beta) (hJpos : 0<J) (hM : m-1<p)
    (w L : ℕ) (hcover : L≤w*J)
    (H K : (ZMod p)[X]) (hH : H.coeff 0=1)
    (hHK : (H : PowerSeries (ZMod p))*(∑ ik : Fin (m-1) × Fin J,
      positiveMoments (((progressionSeed gamma N m (ik.1.val+1)).step*
        beta^ik.2.val : (ZMod p)ˣ) : ZMod p))=(K : PowerSeries (ZMod p))) :
    (m-1)^4*L≤16*w*H.natDegree^2*(nontrivialOffsetEnergy N m+2*(m-1)^2) := by
  classical
  let x := fun i : Fin (m-1) => (progressionSeed gamma N m (i.val+1)).step
  have hsource : ∀ y∈Finset.univ.image x,
      ((Finset.univ : Finset (Fin (m-1))).filter fun i => x i=y).card≤2 := by
    intro y _
    exact original_seed_fiber_card_le_two gamma hm hN horder y
  have he := geometric_moment_source_energy_tradeoff hp x beta hsource
    hJ hJpos hM w L hcover H K hH hHK
  rw [labelled_original_seed_energy_eq_offset gamma hm horder] at he
  exact he.trans (Nat.mul_le_mul_left _ (offsetEnergy_le_nontrivial_add N m))


end RiemannGaussian.SemiprimeSeedEnergyAcquisitionObstruction
